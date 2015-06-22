
import scala.collection.mutable.{ArrayBuffer, PriorityQueue}

object SolverSimulator {
  
  abstract sealed class StrategyCommand
  case class RunStrategy(strategy : String,
                         initialRuntime : Long,
                         timeout : Long)
             extends StrategyCommand
             
  case class MetaStrategy(commands : List[StrategyCommand],
                          threadNum : Int)

  //////////////////////////////////////////////////////////////////////////////

  def portfolioStatistics(portfolio : Learner.LogPortfolio,
                          strategy : MetaStrategy,
                          timeout : Long) : (Long, Int, Double) = {
    var cost : Long = 0
    var totalTime : Long = 0
    var solvedNum = 0

    for (p <- portfolio.allProblems)
      (new SolverSimulator(strategy, p, portfolio, timeout)).result match {
        case Status.AnyTheoremResult(m) => {
          cost = cost + m
          totalTime = totalTime + m
          solvedNum = solvedNum + 1
        }
        case _ => {
          cost = cost + (timeout * 10)
        }
      }

    val avg =
      if (solvedNum > 0) (totalTime.toDouble / solvedNum.toDouble) else 0.0

    (cost, solvedNum, avg)
  }

  //////////////////////////////////////////////////////////////////////////////

  val Timeslice = 200

  //////////////////////////////////////////////////////////////////////////////

  private abstract sealed class SubProverMessage(num : Int)
  
  private abstract sealed class SubProverResult(_num : Int)
               extends SubProverMessage(_num)
  
  private case class SubProverFinished(_num : Int,
                                       result : Status.StrategyResult)
               extends SubProverResult(_num)
  private case class SubProverKilled(_num : Int)
               extends SubProverResult(_num)
  private case class SubProverException(_num : Int)
               extends SubProverResult(_num)

  private case class SubProverSuspended(_num : Int)
               extends SubProverMessage(_num)

}

////////////////////////////////////////////////////////////////////////////////

class SolverSimulator(strategy : SolverSimulator.MetaStrategy,
                      benchmark : String,
                      portfolio : Learner.LogPortfolio,
                      timeout : Long) {

  import SolverSimulator._

  //////////////////////////////////////////////////////////////////////////////

  private abstract sealed class Activity
  private case object Idle extends Activity
  private case class RunningProver(p : SubProverManager) extends Activity

  private var systemTime : Long = 0
  private var currentActivity : Activity = Idle  

  //////////////////////////////////////////////////////////////////////////////

  val maxParallelProvers = strategy.threadNum

  private class SubProverManager(val num : Int, config : RunStrategy) {
    var result : SubProverResult = null

    val RunStrategy(strategyName, initialRuntime, localTimeout) = config
    val expectedResult = portfolio.strategyResults(strategyName)(benchmark)
      
    def unfinished = (result == null)
      
    var runtime : Long = 0
    var runtimeOffset : Long = 0
    var lastStartTime : Long = 0
    var targetedSuspendTime : Long = 0
    var activationCount : Int = 0

      def resumeTO(maxNextPeriod : Long) : Unit = {
        // First let each prover run for a while by itself,
        // to solve simple problems without any parallelism.
        // Afterwards, use time slices
        val nextDiff =
          if (activationCount == 0) initialRuntime else Timeslice
        resume(nextDiff min maxNextPeriod)
      }
      
      def resume(nextPeriod : Long) : Unit = {
        lastStartTime = systemTime
        targetedSuspendTime = lastStartTime + nextPeriod
        activationCount = activationCount + 1
        currentActivity = RunningProver(this)
      }

      def letTimePass : SubProverMessage = expectedResult match {
        case r@Status.AnyTheoremResult(m)
          if (m <= runtime + (targetedSuspendTime - lastStartTime)) => {
          systemTime = systemTime + (m - runtime)
          SubProverFinished(num, r)
        }
        case r@Status.InconclusiveResult(m)
          if (m <= runtime + (targetedSuspendTime - lastStartTime)) => {
          systemTime = systemTime + (m - runtime)
          SubProverFinished(num, r)
        }
        case _ => {
          systemTime = targetedSuspendTime
          SubProverSuspended(num)
        }
      }

      /**
       * Record that the prover has signalled suspension.
       */
      def suspended(maxNextPeriod : Long) : Boolean = {
        val currentTime = systemTime
        runtime = runtime + (currentTime - lastStartTime)
//        Console.err.println("Prover " + num + " runtime: " + runtime)
        runtime >= localTimeout
      }
  }

  val result = {
    val startTime = systemTime

    val subProversToSpawn =
      for ((s, num) <- strategy.commands.iterator.zipWithIndex)
      yield new SubProverManager(num, s.asInstanceOf[RunStrategy])
  
    // all provers that have been spawned so far
    val spawnedProvers = new ArrayBuffer[SubProverManager]
    
    var completeResult : Status.StrategyResult = null
    var successfulProver : Int = -1

    var runningProverNum = 0

    def remainingTime =
      timeout - (systemTime - startTime)

    def overallTimeout = (remainingTime <= 0)

    var lastOffsetUpdate = systemTime
    var exclusiveRun : Int = -1

    def updateOffset = {
      val currentTime = systemTime
      if (exclusiveRun >= 0) {
        val manager = spawnedProvers(exclusiveRun)
        manager.runtimeOffset =
          manager.runtimeOffset + (currentTime - lastOffsetUpdate)
        exclusiveRun = -1
      } else {
        for (manager <- spawnedProvers)
          if (manager.unfinished)
            manager.runtimeOffset =
              manager.runtimeOffset +
              (currentTime - lastOffsetUpdate) / runningProverNum
      }
      lastOffsetUpdate = currentTime
    }

    // We use a priority queue to store provers that are currently suspended.
    // Provers with the least accumulated runtime are first in the queue
    implicit val statusOrdering = new Ordering[SubProverManager] {
      def compare(a : SubProverManager, b : SubProverManager) : Int =
        (b.runtime - b.runtimeOffset) compare (a.runtime - a.runtimeOffset)
    }

    def spawnNewProver : SubProverManager = {
      updateOffset
      val nextProver = subProversToSpawn.next
      spawnedProvers += nextProver
      runningProverNum = runningProverNum + 1
      nextProver
    }

    def spawnNewProverIfPossible =
      if (runningProverNum < maxParallelProvers && subProversToSpawn.hasNext) {
        val newProver = spawnNewProver
        exclusiveRun = newProver.num
        newProver resumeTO remainingTime
        true
      } else {
        false
      }

    def retireProver(num : Int, res : SubProverResult) = {
      updateOffset
      spawnedProvers(num).result = res
      runningProverNum = runningProverNum - 1
    }

    val pendingProvers = new PriorityQueue[SubProverManager]

    def resumeProver =
      if (!pendingProvers.isEmpty) {
        pendingProvers.dequeue resumeTO remainingTime
        true
      } else {
        false
      }

    def addCompleteResult(res : Status.StrategyResult, proverNum : Int) =
      if (completeResult == null) {
        completeResult = res
        successfulProver = proverNum
        stopAllProvers
      }

    def stopAllProvers = {
      for (manager <- spawnedProvers)
        if (manager.unfinished)
          retireProver(manager.num, SubProverKilled(manager.num))
     //     manager.proofActor ! SubProverStop
          
    }

    def activateNextProver =
      if (overallTimeout)
        stopAllProvers
      else
        spawnNewProverIfPossible || resumeProver

    ////////////////////////////////////////////////////////////////////////////
    
    spawnNewProverIfPossible

    var nextMessage : SubProverMessage = null

    while (runningProverNum > 0) {
      currentActivity match {
        case Idle => assert(false)
        case RunningProver(manager) => nextMessage = manager.letTimePass
      }

      nextMessage match {
      case r @ SubProverFinished(num, res) => {
        retireProver(num, r)
        res match {
          case Status.AnyTheoremResult(_) =>
            addCompleteResult(Status.TheoremResult((systemTime - startTime).toInt), num)
          case _ =>
            activateNextProver
        }
      }
      
      case r @ SubProverException(num) => {
        retireProver(num, r)
        activateNextProver
      }
      
      case SubProverSuspended(num) =>
        if (overallTimeout) {
          stopAllProvers
        } else {
          if (spawnedProvers(num) suspended remainingTime) {
            // kill prover
            retireProver(num, SubProverKilled(num))
          } else {
            pendingProvers += spawnedProvers(num)
            if (exclusiveRun >= 0)
              updateOffset
          }
          spawnNewProverIfPossible || resumeProver
        }

      case _ : SubProverKilled =>
        assert(false)
      }
    }

    if (completeResult == null)
      Status.TimeoutResult((systemTime - startTime).toInt)
    else
      completeResult
  }

}
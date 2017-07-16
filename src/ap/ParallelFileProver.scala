/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011-2017 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap

import ap.parameters.{GlobalSettings, Param}
import ap.proof.certificates.Certificate
import ap.proof.tree.{SeededRandomDataSource, NonRandomDataSource}
import ap.parser.{PartName, IFunction}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import ap.util.{Seqs, Debug, Timeout, RuntimeStatistics}

import scala.concurrent.SyncVar
import scala.collection.mutable.{PriorityQueue, ArrayBuffer}
import java.util.concurrent.LinkedBlockingQueue

object ParallelFileProver {

  private val AC = Debug.AC_MAIN

  //////////////////////////////////////////////////////////////////////////////
  // Strategies used for CASC

  val cascStrategies2016 =
    List(
      ("1110004000",52000,400),   // 0
      ("1001001020",7000,5000),
      ("1200113100",4000,600),    // 2: never gives up (all totality axioms)
      ("1001001110",50000,5000),
      ("1000004020",14000,12000),
      ("1011110101",4000,4000),   // 5: never gives up (complete trigger strategy)
      ("0011105000",6000,6000),
      ("1010114120",18000,1800),
      ("1101001020",30000,200),
      ("1001002110",21000,14000),
      ("1010011120",53000,53000), // 10
      ("1010004120",24000,24000),
      ("0000005001",1000,1000),   // 12: never gives up (complete trigger strategy)
      ("1000011021",3000,3000),
      ("0100102000",18000,18000),
      ("1001105101",100000,22000), // 15: never gives up (complete trigger strategy)
      ("1010111122",4000,4000),
      ("1001005000",13000,4000),
      ("1101001110",11000,11000),
      ("1001001121",3000,2400)//,
      //("1200113100",1000000,1000),  // again try strategy 2, for a long time
      //("1011110101",1000000,1000)  // again try strategy 5, for a long time
    )

  /**
   * Create a parallel prover with the given set of strategies
   */
  def apply(createReader : () => java.io.Reader,
            // a timeout in milliseconds
            timeout : Int,
            output : Boolean,
            userDefStoppingCond : => Boolean,
            baseSettings : GlobalSettings,
            rawStrategies : Seq[(String, Int, Int)],
            repetitions : Int,
            maxParallelProvers : Int,
            runUntilProof : Boolean,
            prelResultPrinter : Prover => Unit) : ParallelFileProver = {

    val randomDataSource = Param.RANDOM_SEED(baseSettings) match {
      case Some(seed) => new SeededRandomDataSource(seed)
      case None =>       NonRandomDataSource
    }

    val strategies =
      for (_ <- (0 until repetitions).iterator;
           (str, to, seq) <- rawStrategies.iterator) yield {
        val seed =
          if (randomDataSource.isRandom)
            Some(randomDataSource.nextInt)
          else
            None
        val seedStr = " -randomSeed=" + (seed match {
          case Some(seed) => "" + seed
          case None => "off"
        })

        val s = Param.RANDOM_SEED.set(
                Param.CLAUSIFIER_TIMEOUT.set(
                  toSetting(str, baseSettings),
                  to min Param.CLAUSIFIER_TIMEOUT(baseSettings)),
                  seed)
        Configuration(s, toOptionList(str) + seedStr, to, seq)
      }
    
    new ParallelFileProver(createReader,
                           timeout,
                           true,
                           userDefStoppingCond,
                           strategies,
                           maxParallelProvers,
                           runUntilProof,
                           prelResultPrinter)
  }

  //////////////////////////////////////////////////////////////////////////////

  def toSetting(str : String, baseSettings : GlobalSettings) = {
    var s = baseSettings
    s = Param.TRIGGERS_IN_CONJECTURE.set(s, str(0) == '1')
    s = Param.GENERATE_TOTALITY_AXIOMS.set(s, str(1) match {
          case '0' => Param.TotalityAxiomOptions.None
          case '1' => Param.TotalityAxiomOptions.Ctors
          case '2' => Param.TotalityAxiomOptions.All
        })
    s = Param.TIGHT_FUNCTION_SCOPES.set(s, str(2) == '1')
    s = Param.CLAUSIFIER.set(s,
        if (str(3) == '0')
          Param.ClausifierOptions.Simple
        else
          Param.ClausifierOptions.None)
    s = Param.REVERSE_FUNCTIONALITY_PROPAGATION.set(s, str(4) == '1')
    s = Param.BOOLEAN_FUNCTIONS_AS_PREDICATES.set(s, str(5) == '1')
    s = Param.TRIGGER_STRATEGY.set(s, str(6) match {
      case '0' => Param.TriggerStrategyOptions.AllMaximal
      case '1' => Param.TriggerStrategyOptions.Maximal
      case '2' => Param.TriggerStrategyOptions.AllMinimal
      case '3' => Param.TriggerStrategyOptions.AllMinimalAndEmpty
      case '4' => Param.TriggerStrategyOptions.AllUni
      case '5' => Param.TriggerStrategyOptions.MaximalOutermost
    })
    s = Param.REAL_RAT_SATURATION_ROUNDS.set(s, (str(7) - '0').toInt)
    s = Param.IGNORE_QUANTIFIERS.set(s, str(8) == '1' || str(8) == '2')
    s = Param.PROOF_CONSTRUCTION_GLOBAL.set(s,
          if (str(8) == '2')
            Param.ProofConstructionOptions.Always
          else
            Param.ProofConstructionOptions.Never)
    s = Param.TRIGGER_GENERATION.set(s, str(9) match {
      case '0' => Param.TriggerGenerationOptions.All
      case '1' => Param.TriggerGenerationOptions.Complete
      case '2' => Param.TriggerGenerationOptions.CompleteFrugal
    })
    s
  }

  def toOptionList(strategy : String) : String = {
    var s = ""
    s = s + " " + (if (strategy.charAt(0)=='0') "-" else "+") + "triggersInConjecture"
    s = s + " -genTotalityAxioms=" + (strategy.charAt(1) match {
                                        case '0' => "none"
                                        case '1' => "ctors"
                                        case '2' => "all"
                                      })
    s = s + " " + (if (strategy.charAt(2)=='0') "-" else "+") + "tightFunctionScopes"
    s = s + " -clausifier=" + (if (strategy.charAt(3)=='0') "simple" else "none")
    s = s + " " + (if (strategy.charAt(4)=='0') "-" else "+") + "reverseFunctionalityPropagation"
    s = s + " " + (if (strategy.charAt(5)=='0') "-" else "+") + "boolFunsAsPreds"
    
    s = s + " -triggerStrategy=" + (
       if(strategy.charAt(6)=='0')
         "allMaximal"
       else if(strategy.charAt(6)=='1')
         "maximal"
       else if(strategy.charAt(6)=='2')
         "allMinimal"
       else if(strategy.charAt(6)=='3')
         "allMinimalAndEmpty"
       else if(strategy.charAt(6)=='4')
         "allUni"
       else
         "maximalOutermost"
    )

    s = s + " -realRatSaturationRounds=" + strategy.charAt(7)
    s = s + " " + (if (strategy.charAt(8)=='0') "-" else "+") + "ignoreQuantifiers"
    s = s + " -constructProofs=" +
              (if (strategy.charAt(8)=='2') "always" else "never")
    s = s + " -generateTriggers=" + (
      if (strategy.charAt(9)=='0')
        "all"
      else if (strategy.charAt(9)=='1')
        "complete"
      else
        "completeFrugal"
    )
    
    s
  }

  //////////////////////////////////////////////////////////////////////////////

  private val Timeslice = 200
  
  //////////////////////////////////////////////////////////////////////////////
  // Commands that can be sent to the provers
  
  private abstract sealed class SubProverCommand
  
  private case object SubProverStop extends SubProverCommand
  private case class SubProverResume(until : Long) extends SubProverCommand
  
  //////////////////////////////////////////////////////////////////////////////
  // Messages sent back by the provers
  
  private abstract sealed class SubProverMessage(num : Int)
  
  private abstract sealed class SubProverResult(_num : Int)
               extends SubProverMessage(_num)
  
  private case class SubProverFinished(_num : Int, prover : Option[Prover])
               extends SubProverResult(_num)
  private case class SubProverKilled(_num : Int, result : Prover.Result)
               extends SubProverResult(_num)
  private case class SubProverException(_num : Int, e : Throwable)
               extends SubProverResult(_num)
  
  private case class SubProverSuspended(_num : Int)
               extends SubProverMessage(_num)
  private case class SubProverPrintln(_num : Int, line : String, stream : Int)
               extends SubProverMessage(_num)

  //////////////////////////////////////////////////////////////////////////////
  // What should be done after a prover has suspended itself
  
  private abstract sealed class ProverSuspensionDecision
  private case object SuspensionIgnored extends ProverSuspensionDecision
  private case object SuspensionTimeout extends ProverSuspensionDecision
  private case object SuspensionGranted extends ProverSuspensionDecision
  
  //////////////////////////////////////////////////////////////////////////////

  case class Configuration(settings : GlobalSettings,
                           name : String,
                           timeout : Long,
                           initialSeqRuntime : Long)

  //////////////////////////////////////////////////////////////////////////////

   private class SubProverManager(val num : Int,
                                  createReader : () => java.io.Reader,
                                  config : Configuration,
                                  messageQueue :
                                    LinkedBlockingQueue[SubProverMessage],
                                  userDefStoppingCond : => Boolean) {
      var result : SubProverResult = null
      
      def unfinished = (result == null)
      var localTimeout = config.timeout
      
      var runtime : Long = 0
      var runtimeOffset : Long = 0
      var lastStartTime : Long = 0
      var targetedSuspendTime : Long = 0
      var activationCount : Int = 0

      def producesProofs : Boolean =
        Param.PROOF_CONSTRUCTION_GLOBAL(config.settings) ==
          Param.ProofConstructionOptions.Always

      def resumeTO(maxNextPeriod : Long) : Unit = {
        // First let each prover run for a while by itself,
        // to solve simple problems without any parallelism.
        // Afterwards, use time slices
        val nextDiff =
          if (activationCount == 0)
            RuntimeStatistics.recommendInitialProofRuntime(
                                 config.initialSeqRuntime)
          else
            Timeslice
        resume(nextDiff min maxNextPeriod)
      }

      val subProverCommands = new SyncVar[SubProverCommand]
      
      def resume(nextPeriod : Long) : Unit = {
        lastStartTime = System.currentTimeMillis
        targetedSuspendTime = lastStartTime + nextPeriod
        activationCount = activationCount + 1
        subProverCommands put SubProverResume(targetedSuspendTime)
      }
      
      def recordRuntime : Unit = {
        val currentTime = System.currentTimeMillis
        val lastRuntime = currentTime - lastStartTime
        runtime = runtime + lastRuntime
//        Console.err.println("Prover " + num + " runtime: " + runtime)

        localTimeout = localTimeout +
          (if (activationCount == 1)
             RuntimeStatistics.recordInitialProofRuntime(lastRuntime)
           else
             RuntimeStatistics.recordProofRuntime(lastRuntime))
      }

      /**
       * Record that the prover has signalled suspension.
       */
      def suspended(maxNextPeriod : Long) : ProverSuspensionDecision = {
        val currentTime = System.currentTimeMillis
        recordRuntime

        if (activationCount == 1 &&
            currentTime >= targetedSuspendTime + 5000 &&
            maxNextPeriod > 0) {
          // If the prover was activated for the first time, and has
          // overrun a lot, it was probably suspended right after parsing
          // and preprocessing. Then it makes sense to give it some more time
          resume((currentTime - targetedSuspendTime) min maxNextPeriod)
          SuspensionIgnored
        } else if (activationCount == 1 &&
                   currentTime >= targetedSuspendTime + 100 &&
                   maxNextPeriod > 0) {
          // make sure that the prover had at least some proving time,
          // after parsing and pre-processing
          resume((currentTime - lastStartTime) min maxNextPeriod)
          SuspensionIgnored
        } else if (runtime > localTimeout) {
          stopSubProver
          SuspensionTimeout
        } else {
          SuspensionGranted
        }
      }

      def stopSubProver : Unit =
        subProverCommands put SubProverStop

      //////////////////////////////////////////////////////////////////////////
      
      private val enabledAssertions = Debug.enabledAssertions.value

      val proofThread = new Thread(new Runnable { def run : Unit = {
        Debug.enabledAssertions.value = enabledAssertions
    
        class MessageOutputStream(stream : Int) extends java.io.OutputStream {
          private val line = new StringBuffer
      
          def write(b : Int) =
            if (b == '\n') {
              messageQueue put SubProverPrintln(num, line.toString, stream)
              line setLength 0
            } else {
              line append b.toChar
            }
          }

          var actorStopped : Boolean = false
          var runUntil : Long = 0
    
          var runtime : Long = 0
          var startTime : Long = 0

          def localStoppingCond : Boolean = actorStopped || {
            if (subProverCommands.isSet) subProverCommands.take match {
              case SubProverStop => actorStopped = true
              case SubProverResume(u) => runUntil = u
            }
      
            actorStopped || userDefStoppingCond || {
              if (System.currentTimeMillis > runUntil) {
//              Console.err.println("suspending " +
//                (runtime + System.currentTimeMillis - startTime))
              messageQueue put SubProverSuspended(num)
          
              runtime = runtime + System.currentTimeMillis - startTime

              var suspended = true
              while (!actorStopped && suspended) subProverCommands.take match {
                case SubProverStop =>
                  actorStopped = true
                case SubProverResume(u) => {
                  runUntil = u
                  suspended = false
//                  Console.err.println("resuming")
                  startTime = System.currentTimeMillis
                }
              }
          
              actorStopped || userDefStoppingCond
            } else {
              false
            }
          }
        }
    
        Console.setOut(new MessageOutputStream(1))
        Console.setErr(new MessageOutputStream(2))
      
        subProverCommands.take match {
          case SubProverStop => {
//            Console.err.println("killed right away")
            messageQueue put SubProverKilled(num, Prover.TimeoutCounterModel)
          }

          case SubProverResume(u) => {
            runUntil = u
            Console.err.println("Options: " + config.name)

            try {
              if (userDefStoppingCond) {
//                Console.err.println("no time to start")
                messageQueue put SubProverFinished(num, None)
              } else {
                startTime = System.currentTimeMillis

                val prover =
                  Timeout.withChecker({case x => ()}) {
                    new IntelliFileProver(createReader(),
                                          Int.MaxValue,
                                          true, localStoppingCond,
                                          config.settings)
                  }
    
                if (actorStopped) {
                  Console.err.println("stopped")
                  messageQueue put SubProverKilled(num, prover.result)
                } else {
                  runtime = runtime + System.currentTimeMillis - startTime

                  Console.err.println(prover.result match {
                    case Prover.ValidResult() =>
                      "proved (" + runtime + "ms)"
                    case Prover.InvalidResult() |
                         Prover.InconclusiveResult() => "gave up"
                    case _ => "terminated"
                  })
                  messageQueue put SubProverFinished(num, Some(prover))
                }
              }
            } catch {
              case t : Throwable => {
                Console.err.println("Exception: " + t.getMessage)
                messageQueue put SubProverException(num, t)
              }
            }
          }
        }
      }})

      def startSubProver : Unit = proofThread.start
    }
  
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Prover that tries to solve a given problem using a number of different
 * strategies in parallel. Each individual strategy is run using the
 * <code>IntelliFileProver</code> class.
 */
class ParallelFileProver(createReader : () => java.io.Reader,
                         // a timeout in milliseconds
                         timeout : Int,
                         output : Boolean,
                         userDefStoppingCond : => Boolean,
                         settings : Iterator[ParallelFileProver.Configuration],
                         maxParallelProvers : Int,
                         runUntilProof : Boolean,
                         prelResultPrinter : Prover => Unit) extends Prover {

  import ParallelFileProver._
  
  //////////////////////////////////////////////////////////////////////////////
  // Definition of the actors running the individual provers
  
  private val enabledAssertions = Debug.enabledAssertions.value
  
  private val startTime = System.currentTimeMillis
  
  //////////////////////////////////////////////////////////////////////////////

  def isPreliminaryResult(res : Prover.Result) = res match {
    case Prover.NoCounterModel |
         Prover.Proof(_, _) |
         Prover.ProofWithModel(_, _, _) => true
    case _ => false
  }

  def isInconclusiveResult(res : Prover.Result) = res match {
    // we currently ignore the NoProof result, since the way in which
    // finite domain guards are introduced destroys completeness in some
    // rare cases
    case Prover.NoProof(_) |
         Prover.Invalid(_) |
         Prover.MaybeCounterModel(_) => true
    case _ => false
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  val (result, successfulProverNum, successfulProver) = {
    
    val messageQueue = new LinkedBlockingQueue[SubProverMessage]

    val subProversToSpawn =
      for ((s, num) <- settings.zipWithIndex)
      yield new SubProverManager(num, createReader, s,
                                 messageQueue, userDefStoppingCond)

    // all provers that have been spawned so far
    val spawnedProvers = new ArrayBuffer[SubProverManager]
    
    var completeResult : Prover.Result = null
    var preliminaryResult : Prover.Result = null
    var successfulProverNum : Int = -1
    var successfulProver : Option[Prover] = None
    var exceptionResult : Throwable = null
    
    var runningProverNum = 0

    def remainingTime =
      timeout - (System.currentTimeMillis - startTime)
    
    def overallTimeout = (remainingTime <= 0)
    
    var lastOffsetUpdate = System.currentTimeMillis
    var exclusiveRun : Int = -1

    def updateOffset = {
      val currentTime = System.currentTimeMillis
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

    def spawnNewProverIfPossible : Boolean =
      if (runningProverNum < maxParallelProvers && subProversToSpawn.hasNext) {
        updateOffset
        val newProver = subProversToSpawn.next
        spawnedProvers += newProver

        if (preliminaryResult != null && !newProver.producesProofs) {
          // provers that do not generate certificates are useless at
          // this point; take the next one
          newProver.result =
            SubProverKilled(spawnedProvers.size - 1, Prover.TimeoutCounterModel)
          return spawnNewProverIfPossible
        }

        newProver.startSubProver   // start the actual prover
        runningProverNum = runningProverNum + 1
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
      
    ////////////////////////////////////////////////////////////////////////////
    
    val pendingProvers = new PriorityQueue[SubProverManager]

    def resumeProver : Boolean =
      if (!pendingProvers.isEmpty) {
        val p = pendingProvers.dequeue
        if (p.unfinished) {
          p resumeTO remainingTime
          true
        } else {
          // discard the head element of the queue and go on
          resumeProver
        }
      } else {
        false
      }
    
    def addResult(res : Prover.Result,
                  prover : Option[Prover],
                  proverNum : Int) : Boolean =
      if (completeResult == null) {
        if (isInconclusiveResult(res)) {
          true
        } else if (runUntilProof && isPreliminaryResult(res)) {
          preliminaryResult = res
          successfulProverNum = proverNum
          successfulProver = prover
          stopNonProofProducingProvers
          prelResultPrinter(prover.get)
          true
        } else {
          completeResult = res
          successfulProverNum = proverNum
          successfulProver = prover
          stopAllProvers
          false
        }
      } else {
        false
      }
    
    def addExceptionResult(res : Throwable) =
      if (exceptionResult == null)
        exceptionResult = res
    
    def stopAllProvers =
      for (manager <- spawnedProvers)
        if (manager.unfinished)
          manager.stopSubProver

    def stopNonProofProducingProvers =
      for (manager <- spawnedProvers)
        if (manager.unfinished && !manager.producesProofs)
          manager.stopSubProver

    def activateNextProver =
      if (overallTimeout)
        stopAllProvers
      else
        spawnNewProverIfPossible || resumeProver

    ////////////////////////////////////////////////////////////////////////////
    
    spawnNewProverIfPossible
//    resumeProver
    
    // the main loop of the controller    
    while (runningProverNum > 0) messageQueue.take match {
      case r @ SubProverFinished(num, prover) => {
        spawnedProvers(num).recordRuntime
        retireProver(num, r)

        val res = prover match {
          case Some(p) => p.result
          case None => Prover.TimeoutCounterModel
        }
        if (addResult(res, prover, num))
          activateNextProver
      }
      
      case r @ SubProverException(num, t) => {
        spawnedProvers(num).recordRuntime
        retireProver(num, r)
//        t.printStackTrace
        addExceptionResult(t)
        activateNextProver
      }
      
      case r @ SubProverKilled(num, res) => {
        spawnedProvers(num).recordRuntime
        retireProver(num, r)
      }
      
      case SubProverSuspended(num) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC,
                        !(pendingProvers.iterator contains spawnedProvers(num)))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        if (overallTimeout) {
          stopAllProvers
        } else {
          (spawnedProvers(num) suspended remainingTime) match {
            case SuspensionIgnored => // nothing
            case SuspensionGranted => {
              pendingProvers += spawnedProvers(num)
              if (exclusiveRun >= 0)
                updateOffset
              spawnNewProverIfPossible || resumeProver
            }
            case SuspensionTimeout => {
              if (exclusiveRun >= 0)
                updateOffset
              spawnNewProverIfPossible || resumeProver
            }
          }
        }
      }

      case SubProverPrintln(num, line, 1) =>
        Console.out.println("Prover " + num + ": " + line)
      case SubProverPrintln(num, line, _) =>
        Console.err.println("Prover " + num + ": " + line)
    }
    
    (completeResult, preliminaryResult, exceptionResult) match {
      case (null, null, null) =>
        // no conclusive result could be derived, return something inconclusive
        if (overallTimeout)
          (Prover.TimeoutCounterModel, -1, None)
        else
          (Prover.NoProof(null), -1, None)
      case (null, null, t) => throw t
      case (null, res, _)  =>
        (res, successfulProverNum, successfulProver)
      case (res, _, _) =>
        (res, successfulProverNum, successfulProver)
    }
  }

  override def getFormulaParts : Map[PartName, Conjunction] =
    successfulProver.get.getFormulaParts

  override def getAssumedFormulaParts(certificate : Certificate)
                                     : Set[PartName] =
    successfulProver.get getAssumedFormulaParts certificate

  override def getPredTranslation : Map[Predicate, IFunction] =
    successfulProver.get.getPredTranslation
}

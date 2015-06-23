import java.io.{File, FilenameFilter}
import scala.collection.mutable.{HashMap => MHashMap}


////////////////////////////////////////////////////////////////////////////////


object CCUSimulatingMetaStrategyLearner extends App {
  

  import SAnnealing._
  import CCUPortfolios.{selStrategies, selPortfolios}
  
  val consideredStrategies = selStrategies
  val timeout : Long = 240000
  val threadNum = 3

  val metaStrategyRand = new Randomiser[SolverSimulator.MetaStrategy] {
    import SolverSimulator._

    private val rand = new scala.util.Random(1233)

    private def roundTimeout(r : Long) : Long =
      if (r <= 1000)
        1000.toLong
      else if (r >= 45000)
        45000.toLong
      else
        (r / 1000) * 1000
    
    private def randomTimeout =
      ((rand nextInt 45) * 1000).toLong

    private def roundInitial(r : Long) : Long =
      if (r <= 200)
        200.toLong
      else if (r >= 45000)
        45000.toLong
      else if (r <= 3000)
        (r / 200) * 200
      else
        (r / 1000) * 1000

    private def randomInitial =
      roundInitial(((rand nextInt 450) * 100).toLong)

    private def randomStrategy =
      consideredStrategies.iterator.drop(rand nextInt consideredStrategies.size).next
    
    def initialObject : MetaStrategy =
      MetaStrategy(for (s <- consideredStrategies.toList.sorted take 20)
                     yield RunStrategy(s, 1000, 10000),
                   threadNum)

    def mutate(s : MetaStrategy) : MetaStrategy = {
      val MetaStrategy(cmds, threadNum) = s
      var newCmds : List[StrategyCommand] = null

      while (newCmds == null) {
        (rand nextInt 5) match {
          case 0 if (!cmds.isEmpty) => { // change initial runtime
            val index = rand nextInt cmds.size
            val RunStrategy(oldStrategy, oldInitial, oldTimeout) = cmds(index)
            val newInitial = randomInitial
            if (newInitial <= oldTimeout)
              newCmds = cmds.updated(index, RunStrategy(oldStrategy, newInitial, oldTimeout))
          }
          case 1 if (!cmds.isEmpty) => { // change timeout
            val index = rand nextInt cmds.size
            val RunStrategy(oldStrategy, oldInitial, oldTimeout) = cmds(index)
            val newTimeout = randomTimeout
            if (oldInitial <= newTimeout)
              newCmds = cmds.updated(index, RunStrategy(oldStrategy, oldInitial, newTimeout))
          }
          case 2 if (!cmds.isEmpty) => { // increase/decrease initial runtime and timeout
            val index = rand nextInt cmds.size
            val RunStrategy(oldStrategy, oldInitial, oldTimeout) = cmds(index)
            val newInitial = roundInitial(oldInitial + ((rand nextInt 11) * 100 - 500))
            val newTimeout = roundTimeout(oldTimeout + ((rand nextInt 11) * 1000 - 5000))
            if (newInitial <= newTimeout)
              newCmds = cmds.updated(index, RunStrategy(oldStrategy, newInitial, newTimeout))
          }
          case 3 if (!cmds.isEmpty) => { // change strategy
            val index = rand nextInt cmds.size
            val newStrategy = randomStrategy
            if (!(cmds exists { case RunStrategy(s, _, _) => s == newStrategy }))
            newCmds = cmds(index) match {
              case RunStrategy(oldStrategy, oldInitial, oldTimeout) =>
                cmds.updated(index, RunStrategy(newStrategy, oldInitial, oldTimeout))
            }
          }
          case 4 if (cmds.size >= 2) => { // swap strategies
            val index = rand nextInt (cmds.size-1)
            val s1 :: s2 :: tail = cmds drop index
            newCmds = (cmds take index) ::: List(s2, s1) ::: tail
          }
          
          case _ => // nothing
        }

        if (cmds == newCmds)
          newCmds = null
      }

      MetaStrategy(newCmds, threadNum)
    }
  }
  
  def printMetaStrategyInfo(s : SolverSimulator.MetaStrategy) = {
    println(s)

    for (port <- selPortfolios) {
      val (_, solvedNum, avg) = SolverSimulator.portfolioStatistics(port, s, timeout)
      println("Solves " + solvedNum + "/" + port.allProblems.size +
              " " + port + " problems, average time " + avg)
    }
  }
  
  val annealer = new Annealer[SolverSimulator.MetaStrategy] {
    import SolverSimulator._

    val randomiser = metaStrategyRand
    def cost(s : MetaStrategy) = {

      val solvedTimeCost =
        (for (port <- selPortfolios) yield (
           SolverSimulator.portfolioStatistics(port, s, timeout)._1
         )).sum

     solvedTimeCost

/*
      val staticCost =
        (for (port <- selPortfolios;
              b <- port.allProblems) yield {
           var offset : Long = 0
           val solving =
             for (RunStrategy(strat, initial, timeout) <- s.commands) yield {
               val c =
                 port.strategyResults(strat)(b) match {
                   case Status.AnyTheoremResult(m) if (m <= timeout) =>
                     ((-(timeout - m) * 1000) / timeout + offset / 1000).toInt
                   case _ => Int.MaxValue
                 }
               offset = offset + timeout
               c
             }

           (solving.sorted filterNot (_ == Int.MaxValue) take 6).sum
         }).sum

      solvedTimeCost + staticCost */
    }
    def printObj(obj : MetaStrategy) = printMetaStrategyInfo(obj)
  }
  
//  val s = annealer.optimise(2000000, 0.9999, 100000, 0.4)
  val s = annealer.optimise(500000, 0.99987, 80000, 0.4)

  println("Best strategy found:")
  printMetaStrategyInfo(s)
  
}


////////////////////////////////////////////////////////////////////////////////


object CCUCoarseStrategySelector extends App {

  import SAnnealing._
  import Learner._
  import CCUPortfolios._
  import Status._

  val strategyNum = 48

//  val fixedStrategies = List[String]()

  val fixedStrategies =
    List[String]()
//     List("0011111.log", "1200113.log", "1001001.log", "1011004.log", "1201003.log", "1101001.log", "0210101.log", "1011010.log", "1110003.log", "1101011.log")

  val portfolioRand = new Randomiser[List[String]] {
    private val rand = new scala.util.Random(1234)
    
    private def randomStrategy =
      allStrategies.iterator.drop(rand nextInt allStrategies.size).next
    
    def initialObject : List[String] =
      fixedStrategies :::
      (allStrategies.toSet -- fixedStrategies).toList.sortWith(_ < _).take(strategyNum - fixedStrategies.size)
//      allStrategies.toList.sortWith(_ < _).take(strategyNum)

    def mutate(s : List[String]) : List[String] = {
      var newStrat = randomStrategy
      while (s contains newStrat)
        newStrat = randomStrategy
      val pos = fixedStrategies.size + (rand nextInt (strategyNum - fixedStrategies.size))
      s.updated(pos, newStrat)
    }
  }
  
  val annealer = new Annealer[List[String]] {
    val randomiser = portfolioRand
    
    private def cost(strategies : List[String],
                     portfolio : LogPortfolio) =
      (for (p <- portfolio.allProblems.iterator) yield {
         val theoremTimes =
           for (s <- strategies;
                r = portfolio.strategyResults(s)(p);
                t <- r match {
                  case AnyTheoremResult(m) => List(m)
                  case _ => List()
                }) yield t
         val sortedTimes = theoremTimes.sorted take 10
         val score =
           (for (t <- sortedTimes) yield (10000.0 / (2000.0 + t.toDouble))).sum

         -(scala.math.log1p(score) * 1000.0).toLong
       }).sum
    
    def cost(s : List[String]) =
      cost(s, fofPortfolio)
      // + cost(s, cnfPortfolio)

    def printObj(obj : List[String]) = {
      println(obj)
      println(  "FOF: " + fofPortfolio.solvedProblemsSimple(obj).size)
//      println(  "CNF: " + ccuPortfolio.solvedProblemsSimple(obj).size)
    }
  }

  def printPortfolioInfo(strategies : List[String],
                         portfolio : LogPortfolio) : Unit = {
    var totalNum = 0
    for (p <- portfolio.allProblems) {
      val num =
        (for (s <- strategies.iterator) yield portfolio.strategyResults(s)(p) match {
           case AnyTheoremResult(_) => 1
           case _                   => 0
         }).sum
      println("" + p + "\t" + num)
      if (num > 0)
        totalNum = totalNum + 1
    }
    println("Solved problems: " + totalNum)
  }
  
  def printPortfolioInfo(s : List[String]) : Unit = {
    println
    println(s)

    println
    printPortfolioInfo(s, fofPortfolio)
//    println
//    printPortfolioInfo(s, cnfPortfolio)

    println

    for (t <- allStrategies.toSeq.sorted) {
      if (s contains t)
        print(" * ")
      else
        print("   ")

      print(t)
      print("\t")
      for (port <- List(fofPortfolio /* , cnfPortfolio, */)) {
        print((for ((_, AnyTheoremResult(_)) <-
                      port.strategyResults(t).iterator) yield 1).sum)
        print("\t")
      }

      println
    }
  }

  val s = annealer.optimise(200000, 0.9999, 100000, 0.4)
//  val s = annealer.optimise(300000, 0.9999, 60000, 0.4)
  
  println("Best selection found:")
  printPortfolioInfo(s)
}


////////////////////////////////////////////////////////////////////////////////


object StrategyPortfolioLearner extends App {
  
  import SAnnealing._
  import Learner._
  import FullPortfolios._
  import Status._

  val strategyNum = 16
  
  val portfolioRand = new Randomiser[List[(String, Int)]] {
    private val rand = new scala.util.Random(1234)
    
    private def randomStrategy =
      allStrategies.iterator.drop(rand nextInt allStrategies.size).next
    
    def initialObject : List[(String, Int)] =
      for (s <- allStrategies.toList.sortWith(_ < _).take(strategyNum)) yield (s, 75000)
    def mutate(s : List[(String, Int)]) : List[(String, Int)] =
    (rand nextInt 2) match {
      case 0 => {
        val index = rand nextInt s.size
        s.updated(index, (randomStrategy, 1000 * (rand nextInt 100)))
      }
      case 1 => {
        val index = rand nextInt s.size
        s.updated(index, (s(index)._1,
                          (s(index)._2 + 1000 * ((rand nextInt 20) - 10)) max 0))
      }
    }
  }
  
  def printPortfolioInfo(s : List[(String, Int)]) = {
    println(s)
    println("Solves " + (fofPortfolio solvedProblems s).size + " FOF problems")
    println("Solves " + (cnfPortfolio solvedProblems s).size + " CNF problems")
    println("Solves " + (tfaPortfolio solvedProblems s).size + " TFA problems")
  }
  
  printPortfolioInfo(portfolioRand.initialObject)
  
  val annealer = new Annealer[List[(String, Int)]] {
    val randomiser = portfolioRand
    
    private def cost(strategies : List[(String, Int)],
                     portfolio : LogPortfolio) =
      (for (p <- portfolio.allProblems.iterator) yield {
         val strategySum =
           (for ((s, to) <- strategies.iterator) yield portfolio.strategyResults(s)(p) match {
              case AnyTheoremResult(m) if (m < 10000 && m <= to) => 2
              case AnyTheoremResult(m) if (m <= to)              => 1
              case _                                             => 0
            }).sum
          (5000 / (1 + 5 * strategySum)).toLong
       }).sum
    
    def cost(s : List[(String, Int)]) =
      3*cost(s, fofPortfolio) + 7*cost(s, cnfPortfolio) + cost(s, tfaPortfolio) +
      // prevent strategies from occurring multiple times
      (s.size - s.map(_._1).toSet.size) * 100000 +
      // sum of all timeouts should be 85000 * strategyNum
//      (s.map(_._2).sum - 85000 * strategyNum).abs
      s.map(_._2).sum / 400
    def printObj(obj : List[(String, Int)]) = printPortfolioInfo(obj)
  }
  
  val s = annealer.optimise(1000000, 0.9999, 60000, 0.4)
  
  println("Best portfolio found:")
  printPortfolioInfo(s)
}


////////////////////////////////////////////////////////////////////////////////


object Learner extends App {

  println("Learner")
  val baseDir = "/home/ptr/Princess/unification-modulo/strategy-learner/scripts"
//  val baseDir = "/tmp/cluster-results"
  
  //////////////////////////////////////////////////////////////////////////////

  import Status._
    
  abstract sealed class StrategyCommand
  case class TryStrategyCommand(strategy : String, timeout : Int)
             extends StrategyCommand
             
  type MetaStrategy = List[StrategyCommand]
    
  //////////////////////////////////////////////////////////////////////////////
    
  class LogPortfolio(logFileDir : File) {
    import Status._
  
    def strategyNamer(fileName : String) : Seq[String] = List(fileName)
    
    println("Reading " + logFileDir + " ...")
    
    override def toString = logFileDir.getName

    val strategyResults =
      (for (logFile <- logFileDir.listFiles;
            if (logFile.getName matches """[0-9]+\.log""");
            rawConts = (new LogReader(logFile)).results;
            conts = rawConts - "warmup.p";
            strategy <- strategyNamer(logFile.getName))
       yield (strategy -> conts)).toMap
  
    val allStrategies =
      strategyResults.keySet
    val allProblems =
      if (strategyResults.isEmpty)
        Set()
      else
        (for (m <- strategyResults.valuesIterator) yield m.keySet) reduceLeft (_ & _)
    
    println("Full information for " + allProblems.size + " problems: " + (allProblems mkString ", "))

    ////////////////////////////////////////////////////////////////////////////
    
    def evaluate(strategy : MetaStrategy,
                 overallTimeout : Int,
                 problem : String) : StrategyResult = {
      var time = 0
      for (cmd <- strategy) cmd match {
        case TryStrategyCommand(subStrategy, timeout) => {
          (strategyResults(subStrategy)(problem)) match {
            case res if (time + res.millis > overallTimeout) =>
              return TimeoutResult(overallTimeout)
            case res if (res.millis > timeout) =>
              time = time + timeout
            case AnyTheoremResult(millis) =>
              return TheoremSlackResult(time + millis, timeout - millis)
            case InconclusiveResult(millis) =>
              time = time + millis
            case ErrorResult(millis) =>
              time = time + millis
            case TimeoutResult(millis) => // if (millis >= timeout) =>
              time = time + timeout
          }
        }
      }
    
      InconclusiveResult(time)
    }
  
    def solvedProblemNum(strategy : MetaStrategy) : Int =
      (for (p <- allProblems.iterator) yield evaluate(strategy, 600000, p) match {
        case AnyTheoremResult(_)  => 1
        case _                    => 0
      }).sum
    
    def avgTime(strategy : MetaStrategy) : Int = {
      var totalTime = 0
      var solvedNum = 0
      
      for (p <- allProblems) evaluate(strategy, 600000, p) match {
        case AnyTheoremResult(millis) => {
          totalTime = totalTime + millis
          solvedNum = solvedNum + 1
        }
        case _ => // nothing
      }
      
      if (solvedNum == 0)
        0
      else
        totalTime / solvedNum
    }
    
    def cost(s : MetaStrategy) : Long =
      (for (p <- allProblems.iterator) yield evaluate(s, 600000, p) match {
        case TheoremSlackResult(millis, rem)   => millis// - rem / 2
        case res                               => (1l << 40) + res.millis
//        case TheoremResult(millis)      => 0
//        case res                        => 1
      }).sum
    
    def totalSlack(s : MetaStrategy) : Long =
      (for (p <- allProblems.iterator;
            TryStrategyCommand(strategy, timeout) <- s.iterator) yield
        (strategyResults(strategy)(p) match {
           case AnyTheoremResult(millis)
             if (millis <= timeout) => timeout - millis
           case _ => 0
         })).sum
      
    def solvedProblems(strategies : Iterable[(String, Int)]) =
      for (p <- allProblems;
           if (strategies exists {
                 case (s, to) => strategyResults(s)(p) match {
                   case AnyTheoremResult(millis) if (millis <= to) => true
                   case _ => false
                 }
               })) yield p

    def solvedProblemsSimple(strategies : Iterable[String]) =
      for (p <- allProblems;
           if (strategies exists {
                 case s => strategyResults(s)(p) match {
                   case AnyTheoremResult(_) => true
                   case _ => false
                 }
               })) yield p
  }

  //////////////////////////////////////////////////////////////////////////////

  trait AddRealRatSaturation extends LogPortfolio {
    override def strategyNamer(fileName : String) : Seq[String] =
      for (fileName <- super.strategyNamer(fileName);
           n <- List(fileName.substring(0, 7) + "0" + fileName.substring(7),
                     fileName.substring(0, 7) + "1" + fileName.substring(7)))
      yield n
  }

}

////////////////////////////////////////////////////////////////////////////////

object CCUPortfolios {
  import Learner._

  val ccuBaseDir = "/home/philipp/tmp/newbeans/princess/strategy-learner/scripts-ccu"

  val fofPortfolio = new LogPortfolio(new File(ccuBaseDir + "/logs3"))
//  val fof2Portfolio = new LogPortfolio(new File(ccuBaseDir + "/logs2"))

//  assert(fofPortfolio.allStrategies == fof2Portfolio.allStrategies)
  
  val allStrategies = fofPortfolio.allStrategies
  val selStrategies = allStrategies
  println("Loaded information about " + selStrategies.size + " strategies")

  val selPortfolios = List(fofPortfolio)
}

////////////////////////////////////////////////////////////////////////////////

object FullPortfolios {
  import Learner._

  val baseDir = "/home/philipp/tmp/newbeans/princess/strategy-learner/scripts"

  val fofPortfolio = new LogPortfolio(new File(baseDir + "/logs-fof-all"))
  val cnfPortfolio = new LogPortfolio(new File(baseDir + "/logs-empty"))
  val tffPortfolio = new LogPortfolio(new File(baseDir + "/logs-tff-all"))
  val tfaPortfolio = new LogPortfolio(new File(baseDir + "/logs-empty"))
  val tfaNonlinPortfolio = new LogPortfolio(new File(baseDir + "/logs-empty"))
  
//  assert(fofPortfolio.allStrategies == cnfPortfolio.allStrategies &&
//         fofPortfolio.allStrategies == tfaPortfolio.allStrategies)
  
  val allStrategies = fofPortfolio.allStrategies
}

object FullPortfoliosOld {
  import Learner._

  val fofPortfolio = new LogPortfolio(new File(baseDir + "/logs-fof-all"))
/*  val cnfPortfolio = new LogPortfolio(new File(baseDir + "/log-cnf-all")) {
    override def strategyNamer(fileName : String) : Seq[String] =
      List(fileName, fileName.updated(3, '0'))
  } */
  val tffPortfolio = new LogPortfolio(new File(baseDir + "/logs-tff-all"))
//  val tfaPortfolio = new LogPortfolio(new File(baseDir + "/log-tfa"))
//  val tfaNonlinPortfolio = new LogPortfolio(new File(baseDir + "/log-tfa-nonlin"))
  
//  assert(fofPortfolio.allStrategies == cnfPortfolio.allStrategies &&
//         fofPortfolio.allStrategies == tfaPortfolio.allStrategies)
  
  val allStrategies = fofPortfolio.allStrategies
}

////////////////////////////////////////////////////////////////////////////////

object SelectPortfolios {
  import Learner._

  val baseDir = "/home/philipp/tmp/newbeans/princess/strategy-learner/scripts"

  val fofPortfolio = new LogPortfolio(new File(baseDir + "/logs-fof-all"))
  val tffPortfolio = new LogPortfolio(new File(baseDir + "/logs-tff-all"))

//  val selStrategies = fofPortfolio.allStrategies

  val selStrategies =
    List("0110102000.log", "1210004000.log", "1101003000.log", "1110004000.log", "0001014000.log", "0011005000.log", "1100112000.log", "0010005000.log", "1011110001.log", "1011004000.log", "1200113000.log", "1001001001.log", "1001005000.log", "0101002000.log", "0000105000.log", "0000005000.log", "0111002000.log", "0100004000.log", "1000015000.log", "1110111000.log", "0001005000.log", "1101113000.log", "0001105000.log", "0010004000.log", "1210113000.log", "0011105000.log", "1001111001.log", "1201011000.log", "1000112000.log", "1001000000.log", "1211004000.log", "1111113000.log", "1101011000.log", "0110004000.log", "1000112010.log", "1010004000.log", "1110113000.log", "1100111000.log", "1001001002.log", "1101001010.log", "1001001010.log", "1101005000.log", "1201003000.log", "1001015000.log", "1000005001.log", "1010004010.log", "1100113000.log", "1211002000.log")

  println("Loaded information about " + selStrategies.size + " strategies")

  val selPortfolios = List(fofPortfolio,
                           tffPortfolio)
}

object SelectPortfoliosOld {
  import Learner._

  val fofPortfolio = new LogPortfolio(new File(baseDir + "/log-fof-all"))
                     with AddRealRatSaturation
  val cnfPortfolio = new LogPortfolio(new File(baseDir + "/log-cnf-all"))
                     with AddRealRatSaturation {
    override def strategyNamer(fileName : String) : Seq[String] =
      for (fileName <- super.strategyNamer(fileName);
           n <- List(fileName, fileName.updated(3, '0')))
      yield n
  }
  val tffPortfolio = new LogPortfolio(new File(baseDir + "/log-tff"))
                     with AddRealRatSaturation
  val tfaPortfolio = new LogPortfolio(new File(baseDir + "/log-tfa"))
                     with AddRealRatSaturation
  val tfaNonlinPortfolio = new LogPortfolio(new File(baseDir + "/log-tfa-nonlin"))
                           with AddRealRatSaturation
  
  val allStrategies = tfaNonlinPortfolio.allStrategies

  val fofSelPortfolio = new LogPortfolio(new File(baseDir + "/log-fof-sel"))
                           with AddRealRatSaturation
  val fofSel2Portfolio = new LogPortfolio(new File(baseDir + "/log-fof-sel2"))
                           with AddRealRatSaturation
  val tfaSelPortfolio = new LogPortfolio(new File(baseDir + "/log-tfa-sel"))
                           with AddRealRatSaturation
  val tfaNonlinSelPortfolio = new LogPortfolio(new File(baseDir + "/log-tfa-nonlin-sel"))
                           with AddRealRatSaturation
  val tfaNonIntSelPortfolio = new LogPortfolio(new File(baseDir + "/log-tfa-non-int-sel"))

  val selStrategies = tfaNonIntSelPortfolio.allStrategies
  println("Loaded information about " + selStrategies.size + " strategies")

  val selPortfolios = List(fofPortfolio, fofSelPortfolio, fofSel2Portfolio,
                           cnfPortfolio,
                           tffPortfolio,
                           tfaPortfolio, tfaSelPortfolio,
                           tfaNonlinPortfolio, tfaNonlinSelPortfolio,
                           tfaNonIntSelPortfolio)
}

////////////////////////////////////////////////////////////////////////////////

object SAnnealing {
  
  trait Randomiser[D] {
    def initialObject : D
    def mutate(d : D) : D
  }
  
  abstract class Annealer[D] {
    private val rand = new scala.util.Random(1235)
    
    val randomiser : Randomiser[D]
    def cost(d : D) : Long
    def printObj(obj : D) : Unit
    
    def optimise(iterations : Int, cooling : Double,
                 rewarmingPeriod : Int, rewarming : Double) : D = {
      var obj = randomiser.initialObject
      var bestObj = obj

      var c = cost(obj)
      var bestCost = c
      
      var lastBest = 0
      
      var threshold : Double = 1.0
      for (i <- 0 until iterations) {
        val newObj = randomiser mutate obj
        val newC = cost(newObj)
        if (newC < c || (rand nextDouble) < threshold) {
          obj = newObj
          c = newC
          
          if (c < bestCost) {
            bestObj = obj
            bestCost = c
            Console.withOut(Console.err) {
              print("New best: ")
              printObj(bestObj)
              println("  Cost: " + c)
              println("  Current temp: " + threshold)
              println("  Iteration: " + i)
            }
            lastBest = i
          }
        }

        if ((i - lastBest) % 1000 == 0 && i > lastBest)
          Console.err.println(i)
        
        if (i - lastBest > rewarmingPeriod) {
          Console.err.println("Rewarming ... (" + threshold + ", " + i + ")")
          lastBest = i
          threshold = rewarming
        }
        
        threshold = threshold * cooling
      }
      
      bestObj
    }
  }
  
}

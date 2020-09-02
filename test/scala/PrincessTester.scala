import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.parameters.Param.InputFormat
import ap.parser._

import scala.util.matching.Regex.Match

class PrincessTester (p : SimpleAPI, var printModels : Boolean = true,
                      var printModelOnlyOnFail : Boolean = true,
                      var printOnlyOnFail : Boolean = true,
                      var printProofOnlyOnFail : Boolean = true,
                      var printProofs : Boolean = true) {
  import p._
  private var testCaseCounter : Int = 1
  private var successCounter : Int = 0
  private var totalTestCounter : Int = 0

  def reset {
    testCaseCounter = 1
    successCounter = 0
    totalTestCounter = 0
  }

  def getRes = (successCounter, totalTestCounter)

  private def expect[A](x : A, expected : A) : (A, Boolean) = {
    val res = x == expected
    if (res) successCounter = successCounter + 1
    totalTestCounter = totalTestCounter + 1
    val color = if (x == expected) Console.GREEN else Console.RED_B
    println(color + x + Console.RESET)
    (x, res)
  }

  abstract sealed class TestStep (val fs : IFormula*)
  case class SatStep(override val fs : IFormula*) extends TestStep
  case class UnsatStep(override val fs : IFormula*) extends TestStep
  case class CommonAssert (override val fs : IFormula*) extends TestStep

  private def printModel {
    val newLine = "\n" + " "*2
    val colors = List(Console.WHITE, Console.YELLOW).toArray
    var currentColorFlag = false
    println {"Model:" + newLine +
             (for ((l, v) <- partialModel.interpretation.iterator)
               yield {
                 currentColorFlag = !currentColorFlag
                 val str = LongLines.processLine(l + " -> " + v)
                 val curColor = if (currentColorFlag) colors(0) else colors(1)
                 curColor + str + Console.RESET
               }).mkString(newLine)
    }
  }

  private def justAssert(s : TestStep) = {
    for (f <- s.fs) {
      addAssertion(f)
      print("  ")
      PrincessLineariser printExpression f
      println
    }
  }

  private def executeStep(ps : ProverStatus.Value, s : TestStep) : Boolean = {
    var res = false
    scope {
      for (f <- s.fs) {
        addAssertion(f)
        print("  ")
        PrincessLineariser printExpression f
        if (s.fs.last != f) println(" &")
      }
      print(" --> ")
      val (proverResult, passed) = expect(???, ps)
      res = passed
      if (printModels && !(printModelOnlyOnFail && passed) &&
          proverResult == ProverStatus.Sat) printModel
      else if (printProofs && !(printProofOnlyOnFail && passed) &&
               proverResult == ProverStatus.Unsat)
        println(certificateAsString(Map.empty,
          InputFormat.Princess))
    }
    res
  }

  def TestCase(name : String, steps : TestStep*) {
    var anyFail = false
    val out = ap.DialogUtil.asString {
      println("=" * 80)
      println(
        Console.BOLD + "Test " + testCaseCounter + ": " + name + Console.RESET)
      println("-" * 80)
      var stepNo = 1;
      scope {
        for (s <- steps) {
          if (s.isInstanceOf[CommonAssert]) {
            println("-" * 80)
            println("Common assertion: ")
            justAssert(s)
            println("-" * 80)
          } else {
            print("Step " + testCaseCounter + "." + stepNo + " (expected: ")
            stepNo = stepNo + 1
            s match {
              case _ : SatStep => println("Sat)")
                if (!executeStep(ProverStatus.Sat, s)) anyFail = true
              case _ : UnsatStep => println("Unsat)")
                if (!executeStep(ProverStatus.Unsat, s)) anyFail = true
              case _ => // do nothing as CommonAssert step is already handled
            }
            if (steps.last != s) println("-" * 80)
          }
        }
        println("=" * 80)
        testCaseCounter = testCaseCounter + 1
      }
    }
    if(anyFail || !printOnlyOnFail) println(out)
  }
}


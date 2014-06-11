package ap.theories


import ap.basetypes.IdealInt
import ap.terfor.TermOrder
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{TerForConvenience, TermOrder, ConstantTerm}
import ap.SimpleAPI
import ap.parser._
import ap.terfor.preds.Atom
import ap.terfor.TerForConvenience._
import ap.terfor.linearcombination.LinearCombination



// Assuming rectangular matrix
class Gaussian(var array : Array[Array[IdealInt]])
{
  val rows = array.length
  val cols = array(0).length


  override def toString : String =
  {
    (for (a <- array)
      yield
        a.mkString(" ")).mkString("\n")
  }

  //
  //  GAUSSIAN ELIMINATION PART
  // 


  def getRows() : List[Array[IdealInt]] =
  {
    // Startup engine
    SimpleAPI.withProver { p =>
    // val p = SimpleAPI.spawnWithAssertions
    import p._

    // Create temporary constants
    val vars = createExistentialConstants(cols)
    val constants = vars.map(x => x match { case (c : IConstant) => c.c }).toList
    setMostGeneralConstraints(true)

    // Convert each row to a formula
    for (r <- 0 until rows)
    {
      var formula = 0 : ap.parser.ITerm
      for (c <- 0 until cols)
        if (array(r)(c) != 0)
          formula = formula + array(r)(c)*vars(c)

      !! (formula === 0)
    }

    // Run system
    ???

    // Flattens an IFormula to a list, this needs further work TODO
    def bintoformula(constraints : IFormula) : List[IFormula] =
    {
      constraints match
      {
        case (c : IBinFormula) => bintoformula(c.f1) ++ bintoformula(c.f2)
        case (c : IFormula) => List(c)
      }
    }

    // Converts an iterm to an lc, needs further work TODO
    def termToList(term : ITerm) : List[(IdealInt, IdealInt)] =
    {
      term match
      {
        case (constant : IConstant) => List((vars indexOf constant, 1))
        case (times : ITimes) => (termToList(times.subterm)).map( t => (t._1, t._2*times.coeff.intValue) )
        case (plus : IPlus) => termToList(plus.t1) ++ termToList(plus.t2)
      }
    }

    def expToList(exp : IExpression) : List[(IdealInt, IdealInt)] =
    {
      exp match
      {
        case (f : IIntFormula) => termToList(f.t)
      }
    }

    def expToRow(exp : IExpression) : Array[IdealInt] =
    {
      val list = expToList(exp)
      val a = Array.ofDim[IdealInt](cols)
      for (i <- 0 until cols)
        a(i.intValue) = 0
      for ((i, m) <- list)
        a(i.intValue) = m
      a
    }

    // Convert constraints into polynomials
    val constraint = getConstraint    

//    p.shutDown

    val clist = bintoformula(constraint)
    (for (c <- clist)
      yield
        for (e <- c.subExpressions)
        yield
          expToRow(e)).flatten
    }
  }
}


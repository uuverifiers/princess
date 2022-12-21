
import ap.SimpleAPI
import ap.parser._
import ap.basetypes.IdealInt
import ap.theories.ADT
import ADT.BoolADT.{True, False}
import ap.theories.arrays._

object ComplexTest extends App {

  val debug = true // change to false for much faster solving

  ap.util.Debug.enableAllAssertions(debug)

  import IExpression._

  val (complexSort, complex, Seq(a, b, c, d, k)) =
    ADT.createRecordType("Complex", List(("a", Sort.Integer),
                                         ("b", Sort.Integer),
                                         ("c", Sort.Integer),
                                         ("d", Sort.Integer),
                                         ("k", Sort.Nat)))

  // This just assumes (and does not verify) that the k's are consistent
  def complexPlus(s : ITerm, t : ITerm) : ITerm =
    complex(a(s) + a(t), b(s) + b(t), c(s) + c(t), d(s) + d(t), k(s))

  // This just assumes (and does not verify) that the k's are consistent
  def complexMinus(s : ITerm, t : ITerm) : ITerm =
    complex(a(s) - a(t), b(s) - b(t), c(s) - c(t), d(s) - d(t), k(s))

  def omegaMult(s : ITerm) : ITerm =
    complex(-d(s), a(s), b(s), c(s), k(s))

  def intMult(s : ITerm, n : IdealInt) : ITerm =
    complex(a(s) * n, b(s) * n, c(s) * n, d(s) * n, k(s))

  def sqrt2Div(s : ITerm) : ITerm =
    complex(a(s), b(s), c(s), d(s), k(s) + 1)

  def kInc2(s : ITerm) : ITerm =
    complex(a(s) * 2, b(s) * 2, c(s) * 2, d(s) * 2, k(s) + 2)

  def setK1(s : ITerm) : ITerm =
    complex(a(s), b(s), c(s), d(s), 1)

  val N = 10

  val vectorOps = Vector(
    CombArray.CombinatorSpec("vec_plus", List(0, 0), 0,
                             v(2, complexSort) === complexPlus(v(0, complexSort), v(1, complexSort))),
    CombArray.CombinatorSpec("vec_minus", List(0, 0), 0,
                             v(2, complexSort) === complexMinus(v(0, complexSort), v(1, complexSort))),
    CombArray.CombinatorSpec("vec_omegaMult", List(0), 0,
                             v(1, complexSort) === omegaMult(v(0, complexSort))),
    CombArray.CombinatorSpec("vec_negate", List(0), 0,
                             v(1, complexSort) === intMult(v(0, complexSort), -1)),
    CombArray.CombinatorSpec("vec_sqrt2Div", List(0), 0,
                             v(1, complexSort) === sqrt2Div(v(0, complexSort))),
    CombArray.CombinatorSpec("vec_setK1", List(0), 0,
                             v(1, complexSort) === setK1(v(0, complexSort)))
  )

  def bools(n : Int) = for (_ <- 0 until n) yield Sort.Bool

  def nFalse(n : Int) = (for (_ <- 0 until n) yield False).toList

  val CartTheory =
    new CartArray(bools(N), complexSort, 1, vectorOps)
  
  val arrayN  = CartTheory.extTheories(bools(N))
  val arrayN1 = CartTheory.extTheories(bools(N - 1))

  def projN(k : Int)  = CartTheory.projections((bools(N), k))

  val arrayNComb = CartTheory.combTheories(bools(N))
  val Seq(vec_plusN, vec_minusN,
          vec_omegaMultN, vec_negateN,
          vec_sqrt2DivN, vec_setK1N) = arrayNComb.combinators

  val arrayN1Comb = CartTheory.combTheories(bools(N - 1))
  val Seq(vec_plusN1, vec_minusN1,
          vec_omegaMultN1, vec_negateN1,
          vec_sqrt2DivN1, vec_setK1N1) = arrayN1Comb.combinators

  def selectN(ar : ITerm, indexes : ITerm*) : ITerm =
    IFunApp(arrayN.select, List(ar) ++ indexes)

  def hadam(k : Int, x : ITerm, hx : ITerm) : IFormula =
    arrayN1.sort.ex( (p0, p1) => {
      p0 === projN(k)(x, False) & p1 === projN(k)(x, True) &
      projN(k)(hx, False) === vec_sqrt2DivN1(vec_plusN1(p0, p1)) &
      projN(k)(hx, True)  === vec_sqrt2DivN1(vec_minusN1(p0, p1))
    })

  SimpleAPI.withProver(enableAssert = debug) { p =>
    import p._

    addTheory(CartTheory)

    val x0 = createConstant("x0", arrayN.sort)
    val x = createConstant("x", arrayN.sort)
    val y = createConstant("y", arrayN.sort)
    val z = createConstant("z", arrayN.sort)
    val y1 = createConstant("y1", arrayN.sort)
    val z1 = createConstant("z1", arrayN.sort)

    val comp0 = createConstant("comp0", complexSort)
    val comp1 = createConstant("comp1", complexSort)

    scope {
      !! (hadam(0, x, y))
      !! (hadam(0, y, z))
      !! (selectN(x, False :: nFalse(N - 1) : _*) === complex(1, 1, 1, 1, 1))
      !! (selectN(x, True  :: nFalse(N - 1) : _*) === complex(2, 2, 2, 2, 1))
      !! (selectN(z, False :: nFalse(N - 1) : _*) === comp0)
      !! (selectN(z, True  :: nFalse(N - 1) : _*) === comp1)
      println(???) // sat
      println(evalToTerm(comp0))
      println(evalToTerm(comp1))
    }

    scope {
      val qbits = createConstants(N, Sort.Bool)

      // Assert that all k-components are initially 1
      !! (x === vec_setK1N(x0))

      // Encoding of the circuit
      !! (hadam(1, x, y))
      !! (hadam(1, y, z))
      !! (hadam(2, z, y1))
      !! (hadam(2, y1, z1))

      // Assertion: x, z coincide modulo normalization
      ?? (kInc2(kInc2(selectN(x, qbits : _*))) === selectN(z1, qbits : _*))

      println(???) // valid
    }


  }

}

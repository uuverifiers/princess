import ap._
import ap.parser._

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._

val x = createConstant("x")
!! (x < 100)

val Seq(f) = extractSMTLIBAssertions(new java.io.FileReader("testfile.smt2"))
println(pp(f))

!! (f)
println(???) // sat

!! (x < 50)
println(???) // unsat
}

/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2026 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package ap.api

import ap._
import ap.parser._
import ap.theories.ADT
import ap.basetypes.IdealInt
import SimpleAPI.ProverStatus

import org.scalacheck.Properties
import ap.util.ExtraAssertions
import ap.util.Prop._

class APIBugs extends Properties("APIBugs") with ExtraAssertions {

      // calling eval without previously pushing any formulas previously
      // led to an exception
  property("bug1") = {
    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._
      import IExpression._

      val x = createConstant
      ???
      eval(x)

      true
    }
  }



// case that previously led to an exception, since a
// formula with incompatible term order was added to
// the ModelSearchProver

  property("bug2") = {
SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._

{


scope {

val A2_0_2 = createConstant("A2_0_2") // addConstantRaw(A2_0_2)
val N = createConstant("N") // addConstantRaw(N)
val __eval0 = createConstant("__eval0") // addConstantRaw(__eval0)

???
//println("59: " + ???)

eval(A2_0_2)
//println("72: " + eval(A2_0_2))

?? ((((__eval0 + 1) + ((N + 1) * -1)) === 0))
checkSat(true)
//println("73: " + checkSat(true)) // checkSat(false)

} // pop scope


}} // withProver
    true
  }



// This example previously led to a hanging prover when
// calling "partialModel"

property("bug3") = {
// println("starting")

val p = SimpleAPI.spawnWithAssertions
import p._

val x = createBooleanVariable

push

???
//println(???)

//println("getting model ...")
partialModel
//println(partialModel)
//println("finished")

p.shutDown

true
}



 // A case that previously led to an exception
property("bug4") = {

val p = SimpleAPI.spawnWithAssertions
import p._

val x = createBooleanVariable

push

???

//println("x")
partialModel
//println(partialModel)
//println("y")

!! (x)
???              // here we got an exception

p.shutDown

true
}
 


/**
 * This example previously lead to the exception

     scala.MatchError: null
        at ap.parser.Internal2InputAbsy.ap$parser$Internal2InputAbsy$$convert(Internal2InputAbsy.scala:78)
        at ap.parser.Internal2InputAbsy$.apply(Internal2InputAbsy.scala:45)
        at ap.SimpleAPI.asIFormula(SimpleAPI.scala:1421)
        at ap.SimpleAPI.getConstraint(SimpleAPI.scala:2297)
     [...]
 */

property("bug5") = {

SimpleAPI.withProver { p =>
import p._
import IExpression._
{


reset
}
{


scope {
val headVar0 = createConstant("headVar0")
val headVar1 = createConstant("headVar1")
val headVar2 = createConstant("headVar2")
val headVar3 = createConstant("headVar3")
val headVar4 = createConstant("headVar4")
val headVar5 = createConstant("headVar5")
val headVar6 = createConstant("headVar6")
val headVar7 = createConstant("headVar7")
val headVar8 = createConstant("headVar8")
val headVar9 = createConstant("headVar9")
val headVar10 = createConstant("headVar10")
val headVar11 = createConstant("headVar11")
val headVar12 = createConstant("headVar12")
val headVar13 = createConstant("headVar13")
val headVar14 = createConstant("headVar14")
val headVar15 = createConstant("headVar15")
val headVar16 = createConstant("headVar16")
val headVar17 = createConstant("headVar17")
val headVar18 = createConstant("headVar18")
val headVar19 = createConstant("headVar19")
val headVar20 = createConstant("headVar20")
val headVar21 = createConstant("headVar21")
val headVar22 = createConstant("headVar22")
val headVar23 = createConstant("headVar23")
val headVar24 = createConstant("headVar24")
val headVar25 = createConstant("headVar25")
val headVar26 = createConstant("headVar26")
val headVar27 = createConstant("headVar27")
val headVar28 = createConstant("headVar28")
val headVar29 = createConstant("headVar29")
val headVar30 = createConstant("headVar30")
val headVar31 = createConstant("headVar31")
val headVar32 = createConstant("headVar32")
val headVar33 = createConstant("headVar33")
val headVar34 = createConstant("headVar34")
val headVar35 = createConstant("headVar35")
val headVar36 = createConstant("headVar36")
val headVar37 = createConstant("headVar37")
val c0 = createConstant("c0") // addConstantRaw(c0)
val c1 = createConstant("c1") // addConstantRaw(c1)
val c10 = createConstant("c10") // addConstantRaw(c10)
val c11 = createConstant("c11") // addConstantRaw(c11)
val c12 = createConstant("c12") // addConstantRaw(c12)
val c13 = createConstant("c13") // addConstantRaw(c13)
val c14 = createConstant("c14") // addConstantRaw(c14)
val c15 = createConstant("c15") // addConstantRaw(c15)
val c16 = createConstant("c16") // addConstantRaw(c16)
val c17 = createConstant("c17") // addConstantRaw(c17)
val c18 = createConstant("c18") // addConstantRaw(c18)
val c19 = createConstant("c19") // addConstantRaw(c19)
val c2 = createConstant("c2") // addConstantRaw(c2)
val c20 = createConstant("c20") // addConstantRaw(c20)
val c21 = createConstant("c21") // addConstantRaw(c21)
val c22 = createConstant("c22") // addConstantRaw(c22)
val c23 = createConstant("c23") // addConstantRaw(c23)
val c24 = createConstant("c24") // addConstantRaw(c24)
val c25 = createConstant("c25") // addConstantRaw(c25)
val c26 = createConstant("c26") // addConstantRaw(c26)
val c27 = createConstant("c27") // addConstantRaw(c27)
val c28 = createConstant("c28") // addConstantRaw(c28)
val c29 = createConstant("c29") // addConstantRaw(c29)
val c3 = createConstant("c3") // addConstantRaw(c3)
val c30 = createConstant("c30") // addConstantRaw(c30)
val c31 = createConstant("c31") // addConstantRaw(c31)
val c32 = createConstant("c32") // addConstantRaw(c32)
val c33 = createConstant("c33") // addConstantRaw(c33)
val c34 = createConstant("c34") // addConstantRaw(c34)
val c35 = createConstant("c35") // addConstantRaw(c35)
val c36 = createConstant("c36") // addConstantRaw(c36)
val c37 = createConstant("c37") // addConstantRaw(c37)
val c4 = createConstant("c4") // addConstantRaw(c4)
val c5 = createConstant("c5") // addConstantRaw(c5)
val c55 = createConstant("c55") // addConstantRaw(c55)
val c56 = createConstant("c56") // addConstantRaw(c56)
val c6 = createConstant("c6") // addConstantRaw(c6)
val c7 = createConstant("c7") // addConstantRaw(c7)
val c8 = createConstant("c8") // addConstantRaw(c8)
val c9 = createConstant("c9") // addConstantRaw(c9)

scope {
makeExistential(headVar0)
makeExistential(headVar1)
makeExistential(headVar2)
makeExistential(headVar3)
makeExistential(headVar4)
makeExistential(headVar5)
makeExistential(headVar6)
makeExistential(headVar7)
makeExistential(headVar8)
makeExistential(headVar9)
makeExistential(headVar10)
makeExistential(headVar11)
makeExistential(headVar12)
makeExistential(headVar13)
makeExistential(headVar14)
makeExistential(headVar15)
makeExistential(headVar16)
makeExistential(headVar17)
makeExistential(headVar18)
makeExistential(headVar19)
makeExistential(headVar20)
makeExistential(headVar21)
makeExistential(headVar22)
makeExistential(headVar23)
makeExistential(headVar24)
makeExistential(headVar25)
makeExistential(headVar26)
makeExistential(headVar27)
makeExistential(headVar28)
makeExistential(headVar29)
makeExistential(headVar30)
makeExistential(headVar31)
makeExistential(headVar32)
makeExistential(headVar33)
makeExistential(headVar34)
makeExistential(headVar35)
makeExistential(headVar36)
makeExistential(headVar37)
setMostGeneralConstraints(true)
?? (!((!(c36 === 0) & (((c37 === 0) & (c36 === 0)) & (c25 === 0))) & ((((((((((((((((((((((((((((((((((((((c0 === headVar0) & (c1 === headVar1)) & (c2 === headVar2)) & (c3 === headVar3)) & (c4 === headVar4)) & (c5 === headVar5)) & (c6 === headVar6)) & (c7 === headVar7)) & (c8 === headVar8)) & (c9 === headVar9)) & (c10 === headVar10)) & (c11 === headVar11)) & (c12 === headVar12)) & (c13 === headVar13)) & (c14 === headVar14)) & (c15 === headVar15)) & (c16 === headVar16)) & (c17 === headVar17)) & (c18 === headVar18)) & (c19 === headVar19)) & (c20 === headVar20)) & (c21 === headVar21)) & (c22 === headVar22)) & (c23 === headVar23)) & (c24 === headVar24)) & (c25 === headVar25)) & (c26 === headVar26)) & (c27 === headVar27)) & (c28 === headVar28)) & (c29 === headVar29)) & (c30 === headVar30)) & (c31 === headVar31)) & (c32 === headVar32)) & (c33 === headVar33)) & (c34 === headVar34)) & (c35 === headVar35)) & (c36 === headVar36)) & (c37 === headVar37))))
???
//println("39: " + ???)
getConstraint
//println("40: " + getConstraint)
} // pop scope

} // pop scope


}} // withProver

true
}


// Check that incrementally added formulae are handled
// correctly, even if formulae are eliminated from the proof

property("bug6") = {

val p = SimpleAPI.spawnWithAssertions
import p._

val a = createBooleanVariable("a")
val x = createConstant("x")
val y = createConstant("y")
val z = createConstant("z")

!! (a <=> (x > 1))
!! (x === y + 1)
!! (z === x + 3)

assert(??? == ProverStatus.Sat)
assert(partialModel.toString == "{z -> 3, y -> -1, x -> 0, a -> false}")

scope {
  !! (a)

  assert(??? == ProverStatus.Sat)
  assert(partialModel.toString == "{z -> 5, y -> 1, x -> 2, a -> true}")
}

assert(??? == ProverStatus.Sat)

scope {
  !! (z === 5)

  assert(??? == ProverStatus.Sat)
  assert(partialModel.toString == "{z -> 5, y -> 1, x -> 2, a -> true}")
}

p.shutDown

true

}



// Previous interpolation bug
property("bug7") = {

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._


reset
val exit_fwd = createBooleanVariable("exit_fwd")
val r115__1 = createConstant("r115__1")
val knull__0 = createConstant("$null__0")
val kr321__1 = createConstant("$r321__1")
val javauiouPrintStreamkjavaulanguSystemkerr231__0 = createConstant("java.io.PrintStream$java.lang.System$err231__0")
val kheap__0 = createConstant("$heap__0")
val kfreshglobal_0__1 = createConstant("$freshglobal_0__1")
val kalloc__0 = createConstant("$alloc__0")
val kheap__1 = createConstant("$heap__1")
val kheap__2 = createConstant("$heap__2")
val ktype__0 = createConstant("$type__0")
val javaulanguStringBuilder__0 = createConstant("java.lang.StringBuilder__0")
val kr217__1 = createConstant("$r217__1")
val kr524__1 = createConstant("$r524__1")
val kr626__1 = createConstant("$r626__1")
val kreturn__1 = createConstant("$return__1")
val rootjthen_fwd = createBooleanVariable("root#then_fwd")
val r014__1 = createConstant("r014__1")
val kthis__0 = createConstant("$this__0")
val kin_parameter__0__0 = createConstant("$in_parameter__0__0")
val root_fwd = createBooleanVariable("root_fwd")

setConstructProofs(true)
setPartitionNumber(0)
!! (((!root_fwd | (((r014__1 === kthis__0) & (r115__1 === kin_parameter__0__0)) & rootjthen_fwd)) & root_fwd))

setPartitionNumber(1)
!! (((!rootjthen_fwd | (((((((((((((((((((((r115__1 === knull__0) & (kr321__1 === javauiouPrintStreamkjavaulanguSystemkerr231__0)) & true) & !(select(kheap__0, kfreshglobal_0__1, kalloc__0) === 0)) & (kheap__1 === store(kheap__0, kfreshglobal_0__1, kalloc__0, ITermITE(true, 0, 1)))) & (kheap__2 === store(kheap__1, kfreshglobal_0__1, ktype__0, javaulanguStringBuilder__0))) & (kr217__1 === kfreshglobal_0__1)) & !(kr217__1 === knull__0)) & true) & !(r115__1 === knull__0)) & true) & !(kr217__1 === knull__0)) & true) & !(kr524__1 === knull__0)) & true) & !(kr626__1 === knull__0)) & true) & !(kr321__1 === knull__0)) & true) & (kreturn__1 === 2)) & exit_fwd)) & (!rootjthen_fwd | root_fwd)))

setPartitionNumber(2)
!! (((!exit_fwd | true) & (!exit_fwd | rootjthen_fwd)))

assert(checkSat(true) == ProverStatus.Unsat)
assert(getInterpolants(List(Set(0), Set(1), Set(2))).toVector.toString ==
         "Vector(rootjthen_fwd, false)")
}

true

}



/**
 * Example that previously led to an exception in SimpleAPI.projectEx
 */
property("bug8") = {

ap.util.Debug.enableAllAssertions(true)
val p = SimpleAPI.spawnWithAssertions
  import p._
import IExpression._


val quans = List(
  (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Bool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.Integer),
 (Quantifier.EX, Sort.MultipleValueBool),
 (Quantifier.EX, Sort.MultipleValueBool)).reverse



val f = quanWithSorts(quans,

  (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((ADT.BoolADT.False === IVariable(8, Sort.Bool)) & !(IVariable(6, Sort.MultipleValueBool) === 0)) & !(IVariable(39, Sort.MultipleValueBool) === 0)) & (IVariable(39, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(53, Sort.MultipleValueBool) === 0)) & !(IVariable(41, Sort.MultipleValueBool) === 0)) & (IVariable(41, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(28, Sort.MultipleValueBool) === 0)) & !(IVariable(14, Sort.MultipleValueBool) === 0)) & (IVariable(14, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(45, Sort.MultipleValueBool) === 0)) & !(IVariable(31, Sort.MultipleValueBool) === 0)) & (IVariable(31, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(29, Sort.MultipleValueBool) === 0)) & !(IVariable(4, Sort.MultipleValueBool) === 0)) & (IVariable(4, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(33, Sort.MultipleValueBool) === 0)) & !(0 === IVariable(34))) & !(IVariable(20, Sort.MultipleValueBool) === 0)) & (IVariable(20, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(3, Sort.MultipleValueBool) === 0)) & !(IVariable(9, Sort.MultipleValueBool) === 0)) & (IVariable(9, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(25, Sort.MultipleValueBool) === 0)) & !(IVariable(1, Sort.MultipleValueBool) === 0)) & (IVariable(1, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(22, Sort.MultipleValueBool) === 0)) & !(IVariable(19, Sort.MultipleValueBool) === 0)) & (IVariable(19, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(36, Sort.MultipleValueBool) === 0)) & !(IVariable(49, Sort.MultipleValueBool) === 0)) & (IVariable(49, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(18, Sort.MultipleValueBool) === 0)) & !(0 === IVariable(11))) & !(IVariable(52, Sort.MultipleValueBool) === 0)) & (IVariable(52, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(38, Sort.MultipleValueBool) === 0)) & !(IVariable(5, Sort.MultipleValueBool) === 0)) & (IVariable(5, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(7, Sort.MultipleValueBool) === 0)) & !(IVariable(27, Sort.MultipleValueBool) === 0)) & (IVariable(27, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(13, Sort.MultipleValueBool) === 0)) & !(IVariable(35, Sort.MultipleValueBool) === 0)) & (IVariable(35, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(16, Sort.MultipleValueBool) === 0)) & !(IVariable(0, Sort.MultipleValueBool) === 0)) & (IVariable(0, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(46, Sort.MultipleValueBool) === 0)) & !(IVariable(40, Sort.MultipleValueBool) === 0)) & (IVariable(40, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(51, Sort.MultipleValueBool) === 0)) & !(IVariable(44, Sort.MultipleValueBool) === 0)) & (IVariable(44, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(43, Sort.MultipleValueBool) === 0)) & (((IVariable(57) === 0) & (IVariable(15) === 0)) | (!(IVariable(57) === 0) & !(IVariable(15) === 0)))) & (((IVariable(56) === 0) & (IVariable(42) === 0)) | (!(IVariable(56) === 0) & !(IVariable(42) === 0)))) & (((IVariable(60) === 0) & (IVariable(10) === 0)) | (!(IVariable(60) === 0) & !(IVariable(10) === 0)))) & (((IVariable(58) === 0) & (IVariable(37) === 0)) | (!(IVariable(58) === 0) & !(IVariable(37) === 0)))) & (((IVariable(59) === 0) & (IVariable(47) === 0)) | (!(IVariable(59) === 0) & !(IVariable(47) === 0)))) & (((IVariable(61) === 0) & (IVariable(2) === 0)) | (!(IVariable(61) === 0) & !(IVariable(2) === 0)))) & !(IVariable(21, Sort.MultipleValueBool) === 0)) & (IVariable(43, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(30, Sort.MultipleValueBool) === 0)) & !(0 === IVariable(54))) & !(IVariable(12, Sort.MultipleValueBool) === 0)) & (IVariable(12, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(50, Sort.MultipleValueBool) === 0)) & !(IVariable(23, Sort.MultipleValueBool) === 0)) & (IVariable(23, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(32, Sort.MultipleValueBool) === 0)) & !(IVariable(24, Sort.MultipleValueBool) === 0)) & (IVariable(24, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(26, Sort.MultipleValueBool) === 0)) & !(IVariable(17, Sort.MultipleValueBool) === 0)) & (IVariable(17, Sort.MultipleValueBool) === IVariable(8, Sort.Bool))) & !(IVariable(48, Sort.MultipleValueBool) === 0)))

assert(simplify(f).toString == "true")

p.shutDown

true
}



// Previous bug related to scopes
property("bug9") = {

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._


reset
val c0 = createConstant("c0")
val c1 = createConstant("c1")
val c2 = createConstant("c2")
!! (!(((c0 === 0) & (c1 === 0)) & (c2 === 0)))

scope {
!! (((((c0 * 0) + (c1 * 0)) + (c2 * 0)) === 0))

scope {
!! (((((c1 * 1) - (c0*3)) + (c2 * 0)) === 0))
// ???
assert(checkSat(true) == ProverStatus.Sat)

scope {
!! (((((c0 * 2) + (c1 * 0)) - c2) === 0))
// ???
assert(checkSat(true) == ProverStatus.Sat)

scope {
!! (((((c1 * 1) - (c0*3)) + (c2 * 0)) === 0))
// ???
assert(checkSat(true) == ProverStatus.Sat)

scope {
!! (((((c0 * 0) - (c1*2)) + (c2 * 3)) === 0))
// ???
assert(checkSat(true) == ProverStatus.Sat)
// ???
assert(eval(c0).toString == "1")
assert(eval(c1).toString == "3")
assert(eval(c2).toString == "2")
} // pop scope

} // pop scope

} // pop scope

!! (((((c0 * 1) + (c1 * 3)) + (c2 * 2)) === 0))
// ???
assert(checkSat(true) == ProverStatus.Sat)

scope {
!! (((((c0 * 2) + (c1 * 0)) - c2) === 0))
// ???
assert(checkSat(true) == ProverStatus.Unsat)
} // pop scope

assert(checkSat(true) == ProverStatus.Sat)
assert(eval(c0).toString == "1")
assert(eval(c1).toString == "3")
assert(eval(c2).toString == "-5")

}}}

true
}



// Previous bug related to the simplifier
property("bug10") = {

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._

val c = createConstant("c")

assert((new Simplifier)(ex(x => x === 0)).toString == "true")
assert((new Simplifier)(ex(x => x =/= 0)).toString == "true")   // this was simplified to false
assert((new Simplifier)(all(x => x === 0)).toString == "false")
assert((new Simplifier)(all(x => x =/= 0)).toString == "false")

assert((new Simplifier)(ex(x => x === c)).toString == "true")
assert((new Simplifier)(ex(x => x =/= c)).toString == "true")   // this was simplified to false
assert((new Simplifier)(all(x => x === c)).toString == "false")
assert((new Simplifier)(all(x => x =/= c)).toString == "false")

}

true
}



/**
 * This problem should be sat, but previously gave the result unsat
 * since some of the monomial orderings relied on distinct variable names
 */
property("bug11") = {

SimpleAPI.withProver(enableAssert = true) { p =>
import p._
import IExpression._
{


reset
}
{

scope {

val Xs = for (_ <- 0 until 2) yield createConstant("X")
// val Xs = for (n <- 0 until 2) yield createConstant("X" + n)

// addConstantRaw(x)
val x = createConstant("x")
// addConstantRaw(y)
val y = createConstant("y")
!! (IBoolLit(true))
!! (IBoolLit(true))
!! (Xs === List(x, y))
// addConstantRaw(__eval0)
val __eval0 = createConstant("__eval0")
// addConstantRaw(arg0)
val arg0 = createConstant("arg0")
!! ((((((mult(__eval0, __eval0) - __eval0) >= 1) & (IIntLit(IdealInt("100")) >= __eval0)) & (__eval0 >= 1)) & (mult(__eval0, __eval0) === arg0)))
!! (Xs === List(__eval0, arg0))
??? == ProverStatus.Sat
} // pop scope


}} // withProver


}
}

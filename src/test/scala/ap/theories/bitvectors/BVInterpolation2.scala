/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2026 Daniel Raffler, Philipp Ruemmer
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

package ap.theories.bitvectors

import ap.SimpleAPI
import ap.api.SimpleAPI.ProverStatus
import ap.parser.IExpression.{Sort, ite}
import ap.parser.{IFormula, ITerm}
import ap.util.Debug
import ap.parameters._
import ap.util.{IdealRange, Combinatorics}
import ap.terfor.linearcombination.LinearCombination

import org.scalacheck.Properties

class BVInterpolation2 extends Properties("BVInterpolation2") {
  import ModuloArithmetic._
  import ap.parser.IExpression.{Sort => _}

  val withAssertions = false

  property("interpolation bug") = {
    Debug.enableAllAssertions(withAssertions)
    SimpleAPI.withProver(enableAssert = withAssertions, sanitiseNames = false) { aprover =>

      object BooleanExpr {
        def and(a: IFormula, b: IFormula): IFormula = a &&& b
        def not(a: IFormula): IFormula = !a
        def ifThenElse(a: IFormula, b: ITerm, c: ITerm): ITerm = ite(a, b, c)
      }

      object BitvectorExpr {
        def makeBitvector(width: Integer, value: Long): ITerm = bv(width, value)
        def makeVariable(sort: Sort, name: String): ITerm = aprover.createConstant(name, sort)
        def add(a: ITerm, b: ITerm): ITerm = bvadd(a, b)
        def equal(a: ITerm, b: ITerm): IFormula = a === b
        def greaterThan(a: ITerm, b: ITerm, signed: Boolean): IFormula = if (signed) bvsgt(a, b) else bvugt(a, b)
        def lessThan(a: ITerm, b: ITerm, signed: Boolean): IFormula = if (signed) bvslt(a, b) else bvult(a, b)
      }

      val bv32 = UnsignedBVSort(32)

      val var1 = BitvectorExpr.makeBitvector(32, 0L)
      val var119 = BitvectorExpr.makeBitvector(32, -50)
      val var122 = BitvectorExpr.makeVariable(bv32, "main::main__x@3")
      val var125 = BitvectorExpr.equal(var122, var119)
      val var139 = BitvectorExpr.makeVariable(bv32, "main::main__y@3")
      val var152 = BitvectorExpr.makeBitvector(32, -1000)
      val var154 = BitvectorExpr.lessThan(var152, var139, true)
      val var155 = BitvectorExpr.makeBitvector(32, 1L)
      val var172 = BooleanExpr.and(var125, var154)
      val var219 = BitvectorExpr.makeBitvector(32, 1000000)
      val var220 = BitvectorExpr.lessThan(var139, var219, true)
      val var238 = BooleanExpr.and(var172, var220)
      val var383 = BitvectorExpr.makeVariable(bv32, "main::__tmp_1@3")
      val var412 = BitvectorExpr.makeVariable(bv32, "main::__VERIFIER_assert__cond@3")
      val var415 = BitvectorExpr.equal(var412, var383)
      val var427 = BitvectorExpr.equal(var412, var1)
      val var523 = BitvectorExpr.add(var122, var139)
      val var527 = BitvectorExpr.makeVariable(bv32, "main::main__x@4")
      val var530 = BitvectorExpr.equal(var527, var523)
      val var549 = BitvectorExpr.add(var139, var155)
      val var553 = BitvectorExpr.makeVariable(bv32, "main::main__y@4")
      val var556 = BitvectorExpr.equal(var553, var549)
      val var562 = BooleanExpr.and(var530, var556)
      val var871 = BitvectorExpr.add(var527, var553)
      val var875 = BitvectorExpr.makeVariable(bv32, "main::main__x@5")
      val var878 = BitvectorExpr.equal(var875, var871)
      val var897 = BitvectorExpr.add(var553, var155)
      val var901 = BitvectorExpr.makeVariable(bv32, "main::main__y@5")
      val var904 = BitvectorExpr.equal(var901, var897)
      val var910 = BooleanExpr.and(var878, var904)
      val var932 = BitvectorExpr.lessThan(var875, var1, true)
      val var971 = BooleanExpr.not(var932)
      val var1377 = BitvectorExpr.greaterThan(var901, var1, true)
      val var1381 = BooleanExpr.ifThenElse(var1377, var155, var1)
      val var1388 = BitvectorExpr.equal(var383, var1381)
      val var1394 = BooleanExpr.and(var971, var1388)
      val var1423 = BooleanExpr.and(var1394, var415)
      val var1447 = BooleanExpr.and(var1423, var427)
      val var1645 = BooleanExpr.and(var910, var1447)

      SimpleAPI.withProver(enableAssert = withAssertions, sanitiseNames = false) { prover =>
        prover.addConstant(var901)
        prover.addConstant(var122)
        prover.addConstant(var139)
        prover.addConstant(var527)
        prover.addConstant(var553)
        prover.addConstant(var875)
        prover.addConstant(var383)
        prover.addConstant(var412)

        val A = var238
        val B = var562
        val C = var1645

        val itps = prover.scope {
          prover.setConstructProofs(true)

          prover.setPartitionNumber(0)
          prover.!!(A)
          prover.setPartitionNumber(1)
          prover.!!(B)
          prover.setPartitionNumber(2)
          prover.!!(C)

          assert(prover.??? == ProverStatus.Unsat)

          prover.getInterpolants(Seq(Set(0), Set(1), Set(2)), 1000)
        }

        val I = itps(0)
        val J = itps(1)

/*
        println(s"A: $A")
        println(s"B: $B")
        println(s"C: $C")

        println(s"I: $I")
        println(s"J: $J")
*/

        SimpleAPI.withProver(enableAssert = withAssertions, sanitiseNames = false) { validator =>
        validator.addConstant(var901)
        validator.addConstant(var122)
        validator.addConstant(var139)
        validator.addConstant(var527)
        validator.addConstant(var553)
        validator.addConstant(var875)
        validator.addConstant(var383)
        validator.addConstant(var412)

          validator.scope {
            //println("A => I")
            validator.??(A ===> I)
            validator.??? match {
              case ProverStatus.Valid =>
                // println("verified")
              case ProverStatus.Invalid => {
                // println("Condition violated: " + validator.partialModel)
                assert(false)
              }
            }
          }
          validator.scope {
            //println("B & I => J")
            validator.??((B & I) ===> J)
            validator.??? match {
              case ProverStatus.Valid =>
                //println("verified")
              case ProverStatus.Invalid => {
                //println("Condition violated: " + validator.partialModel)
                assert(false)
              }
            }
          }
          validator.scope {
            //println("C & J => false")
            validator.??((C & J) ===> false)
            validator.??? match {
              case ProverStatus.Valid =>
                //println("verified")
              case ProverStatus.Invalid => {
                //println("Condition violated: " + validator.partialModel)
                assert(false)
              }
            }
          }

        }
      }
    }

    true
  }
}
/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.substitutions;

import ap.terfor._
import ap.util.{Debug, Logic, PlainRange}
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.EquationConj

import org.scalacheck.Properties
import ap.util.Prop._

class TestSubst extends Properties("TestSubst") {

  Debug.enableAllAssertions(true)

  private val consts = for (i <- Array.range(0, 10)) yield new ConstantTerm("c" + i)
  private val constsOne = consts ++ List(OneTerm)
  private val to = (TermOrder.EMPTY /: consts)((o, c) => o.extend(c))
  private val constsLC = for (t <- consts) yield LinearCombination(t, to)

  property("testPseudoSubst") = {
    implicit val order = to
    
    val lc0 = (constsLC(0) scale 5) + constsLC(1) + 6
    val subst0 = new PseudoConstantSubst(3, consts(1), constsLC(2) scale 2, to)
    
    assertEquals(subst0(EquationConj(lc0, to)),
                 EquationConj((constsLC(0) scale 15) + (constsLC(2) scale 2) + 18, to))

    val subst1 = new PseudoConstantSubst(3, consts(1), constsLC(2) scale 5, to)
                 
    assertEquals(subst1(EquationConj(lc0, to)),
                 EquationConj.FALSE)

    val lc1 = (constsLC(0) scale 5) + (constsLC(1) scale 3) + 6
    assertEquals(subst0(EquationConj(lc1, to)),
                 EquationConj((constsLC(0) scale 5) + (constsLC(2) scale 2) + 6, to))

    true
  }

}

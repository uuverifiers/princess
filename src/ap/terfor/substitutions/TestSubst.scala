/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

package ap.terfor.substitutions;

import ap.terfor._
import ap.util.{Debug, Logic, APTestCase, PlainRange}
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.EquationConj

class TestSubst(n : String) extends APTestCase(n) {

  def runTest = {
    n match {
      case "testPseudoSubst" => testPseudoSubst
    }
  }

  private val consts = for (i <- Array.range(0, 10)) yield new ConstantTerm("c" + i)
  private val constsOne = consts ++ List(OneTerm)
  private val to = (TermOrder.EMPTY /: consts)((o, c) => o.extend(c))
  private val constsLC = for (t <- consts) yield LinearCombination(t, to)

  def testPseudoSubst = {
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
  }
  
}

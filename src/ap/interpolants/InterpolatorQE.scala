/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *                    Angelo Brillout <bangelo@inf.ethz.ch>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.interpolants

import ap.proof.certificates._
import ap.terfor.conjunctions.Conjunction
import ap.parser.{IInterpolantSpec, PartName}
import ap.terfor.TerForConvenience._
import ap.terfor.TermOrder
import ap.proof.ModelSearchProver
import ap.proof.ConstraintSimplifier
import ap.basetypes.IdealInt
import ap.util.{Debug, Seqs}

object InterpolatorQE
{
  
  private val AC = Debug.AC_INTERPOLATION
  
  private val simplifier = ConstraintSimplifier.LEMMA_SIMPLIFIER_NON_DNF
  
  def apply(implicit o : TermOrder, 
            iContext: InterpolationContext) : Conjunction = {
    
    val res = simplifier(
      exists(o sort iContext.leftLocalConstants, certConj(iContext.leftFormulae)), o)
    
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(
      AC,
      {
        res.variables.isEmpty &&
        (res.constants subsetOf iContext.globalConstants) &&
        (res.predicates subsetOf iContext.globalPredicates) &&
        ModelSearchProver(certConj(iContext.leftFormulae) ==> res, o).isFalse &&
        ModelSearchProver(!(certConj(iContext.rightFormulae) & res), o).isFalse
      })
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  private def certConj(fors : Iterable[CertFormula])
                      (implicit o : TermOrder) : Conjunction =
    conj(for (f <- fors.iterator) yield f.toConj)

}

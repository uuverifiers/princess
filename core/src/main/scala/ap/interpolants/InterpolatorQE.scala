/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *                    Angelo Brillout <bangelo@inf.ethz.ch>
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

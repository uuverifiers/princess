/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.tree;

import ap.proof._
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import ap.util.Debug

object ProofTree {
  
  private val AC = Debug.AC_PROOF_TREE
  
}

trait ProofTree {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(ProofTree.AC,
                   (constantFreedom freeConstsAreUniversal bindingContext) &&
                   (closingConstantFreedom freeConstsAreUniversal bindingContext) &&
                   closingConstantFreedom <= constantFreedom)
// The following condition sometimes takes very long to check, since
// it will trigger computation of the actual constraint; so it has been
// moved to the lazy val's actually computing the constraint
//                   (order isSortingOf closingConstraint) &&
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  val subtrees : Seq[ProofTree]
  
  /**
   * The fully simplified closing constraint
   */
  val closingConstraint : Conjunction

  /**
   * The constants that can be considered free (resp., that have to be
   * considered non-free) in this proof tree.
   */
  val closingConstantFreedom : ConstantFreedom
  
  /**
   * <code>true</code> if it is possible to apply rules to any goal in this
   * tree
   */
  val stepPossible : Boolean
  
  /**
   * <code>true</code> if there are chances that the
   * <code>closingConstraint</code> of this tree changes by applying rules
   * to any goal
   */
  val stepMeaningful : Boolean
  
  /**
   * <code>true</code> if the sets of free constants have reached a fixed point
   */
  val fixedConstantFreedom : Boolean
  
  /**
   * the vocabulary available at a certain node in the proof
   */
  val vocabulary : Vocabulary
  
  def order : TermOrder = vocabulary.order
  def bindingContext : BindingContext = vocabulary.bindingContext
  def constantFreedom : ConstantFreedom = vocabulary.constantFreedom
  
}

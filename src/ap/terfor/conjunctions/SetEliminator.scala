/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.conjunctions;

import scala.collection.mutable.ArrayBuffer

import ap.parameters.Param
import ap.terfor.{TermOrder, ConstantTerm, TerForConvenience}
import ap.terfor.preds.{Predicate, Atom}
import ap.util.Debug

object SetEliminator {
  
  val AC = Debug.AC_ELIM_CONJUNCTS
  
  /**
   * Data structure to provide the chosen predicates for sets (BAPA)
   * to the prover
   */
  case class SetPredicates(intersection : Predicate,
                           union : Predicate,
                           complement : Predicate,
                           empty : ConstantTerm)
}

/**
 * Elimination rules specific for the theory of sets (as part of the BAPA
 * logic). This class removes redundant predicates from a conjunction, e.g.,
 * expressions that are not sorted or not left-associative.
 */
class SetEliminator(oriConj : Conjunction,
                    predicates : SetEliminator.SetPredicates,
                    order : TermOrder) {

  import predicates._
  import TerForConvenience._
  
  private var conj = oriConj

  def eliminate : Conjunction = {
    var oldconj = conj
    do {
      oldconj = conj

      val newPosPreds = conj.predConj.positiveLits filterNot {
        
        // Idempotence: intersection(x, x, x) can be removed
        case a@Atom(`intersection`, Seq(left, right, res))
          if (left == right && left == res) => {
            println("dropping " + a)
            true
          }
          
        case _ => false
      }

      val newPredConj =
        conj.predConj.updateLitsSubset(newPosPreds,
                                       conj.predConj.negativeLits,
                                       order)
      conj = conj.updatePredConj(newPredConj)(order)
      
    } while (oldconj != conj)

    conj
  }
  
}
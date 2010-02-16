/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

package ap;

import ap.proof.{ModelSearchProver, Timeout}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.util.{Debug, Seqs}
import ap.parameters.{GoalSettings, PreprocessingSettings}

object FileModelSearcher {
  
  private val AC = Debug.AC_PROVER
  
}

class FileModelSearcher(reader : java.io.Reader, output : Boolean,
                        preprocSettings : PreprocessingSettings,
                        goalSettings : GoalSettings)
      extends AbstractFileProver(reader, output, Math.MAX_INT, false,
                                 preprocSettings, goalSettings) {

  //////////////////////////////////////////////////////////////////////////////
  Debug.assertCtor(FileModelSearcher.AC, (formulas forall ((f:Conjunction) =>
                   Seqs.disjoint(f.constants, signature.existentialConstants) &&
                   (Conjunction.collectQuantifiers(f) subsetOf Set(Quantifier.ALL)))))
  //////////////////////////////////////////////////////////////////////////////
  
  val counterModel : Conjunction =
    Timeout.catchTimeout {
      findCounterModelTimeout.left.get
    } {
      case _ => Conjunction.FALSE
    }
  
}

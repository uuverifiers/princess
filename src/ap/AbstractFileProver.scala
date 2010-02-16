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

import ap.parameters.{GoalSettings, PreprocessingSettings, Param}
import ap.parser.{InputAbsy2Internal, Parser2InputAbsy, Preprocessing, IExpression, INamedPart}
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.proof.{ModelSearchProver, ExhaustiveProver, ConstraintSimplifier,
                 Timeout}
import ap.proof.tree.ProofTree
import ap.proof.goal.{Goal, SymbolWeights}
import ap.proof.certificates.Certificate
import ap.util.Debug

abstract class AbstractFileProver(reader : java.io.Reader, output : Boolean,
                                  timeout : Int, userDefStoppingCond : => Boolean,
                                  preprocSettings : PreprocessingSettings,
                                  initialGoalSettings : GoalSettings) {

  protected def println(str : => String) : Unit = (if (output) Predef.println(str))
  
  val (inputFormulas, interpolantSpecs, signature) = {
    val (f, interpolantSpecs, signature) = Parser2InputAbsy(reader)
    reader.close
    println("Preprocessing ...")
    Preprocessing(f, interpolantSpecs, signature, preprocSettings)
  }
  
  val order = signature.order
  
  val formulas =
    for (f <- inputFormulas) yield
      Conjunction.conj(InputAbsy2Internal(IExpression removePartName f, order), order)

  protected val goalSettings =
    Param.SYMBOL_WEIGHTS.set(initialGoalSettings,
                             SymbolWeights.normSymbolFrequencies(formulas, 1000))
  
  lazy val namedParts =
  Map() ++ (for ((INamedPart(name, _), f) <-
                   inputFormulas.elements zip formulas.elements)
            yield (name -> f))
  
  protected def findModelTimeout : Either[Conjunction, Certificate] = {
    println("Constructing satisfying assignment for the existential constants ...")
    findCounterModelTimeout(List(Conjunction.disj(formulas, order).negate))
  }
  
  protected def findCounterModelTimeout : Either[Conjunction, Certificate] = {
    println("Constructing countermodel ...")
    findCounterModelTimeout(if (formulas exists (_.isTrue))
                              List(Conjunction.TRUE)
                            else
                              formulas)
  }
  
  protected def findCounterModelTimeout(f : Seq[Conjunction]) = {
    val timeBefore = System.currentTimeMillis
    val stoppingCond = () => {
      if ((System.currentTimeMillis - timeBefore > timeout) || userDefStoppingCond)
        Timeout.raise
    }

    Timeout.withChecker(stoppingCond) {
      ModelSearchProver(f, order, goalSettings)
    }
  }
  
  protected def findModel(f : Conjunction) : Conjunction =
    ModelSearchProver(f.negate, f.order)
  
  protected def constructProofTree(mostGeneralConstraint : Boolean)
                                  : (ProofTree, Boolean) = {
    // explicitly quantify all universal variables
    
    val closedFor = Conjunction.quantify(Quantifier.ALL,
                                         order sort signature.nullaryFunctions,
                                         Conjunction.disj(formulas, order), order)
    
    println("Proving ...")
    
    val timeBefore = System.currentTimeMillis
    val stoppingCond = () => {
      if ((System.currentTimeMillis - timeBefore > timeout) ||
          userDefStoppingCond)
        Timeout.raise
    }

    Timeout.withChecker(stoppingCond) {
      val prover = new ExhaustiveProver(!mostGeneralConstraint, goalSettings)
      val tree = prover(closedFor, signature)
      val validConstraint = prover.isValidConstraint(tree.closingConstraint, signature)
      (tree, validConstraint)
    }
  }
}

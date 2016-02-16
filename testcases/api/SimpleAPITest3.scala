/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
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

import ap._
import ap.parser._
import ap.proof.goal.Goal
import ap.terfor.preds.{Atom, Predicate}
import ap.terfor.conjunctions.Conjunction
import ap.proof.theoryPlugins.Plugin

object SimpleAPITest3 extends App {
  ap.util.Debug.enableAllAssertions(true)
  val p = SimpleAPI.spawnWithAssertions
  
  import IExpression._
  import SimpleAPI.ProverStatus
  import p._

  val a, b, c, d = p.createBooleanVariable
  
  // Add a theory plugin that implements the implication
  //   a & b ==> c
  // by checking whether a, b are known, and in this case
  // adding also the fact c
  setupTheoryPlugin(new Plugin {
    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = {
      val knownPosLits =
        (for (atom <- goal.facts.predConj.positiveLits)
           yield atom.pred().asInstanceOf[IFormula]).toSet
      if ((Set(a, b) subsetOf knownPosLits) && !(knownPosLits contains c))
        Some((asConjunction(c), Conjunction.TRUE))
      else
        None
    }
  })
  
  !! (a & b)
  ?? (d)

  println(???)  // Invalid

  !! (c ==> d)

  println(???)  // Valid

  p.shutDown
}

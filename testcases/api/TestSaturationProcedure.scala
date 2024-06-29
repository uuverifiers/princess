/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2024 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.theories._
import ap.{Signature, SimpleAPI}
import ap.parser._
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TerForConvenience
import ap.terfor.preds.Atom
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.Conjunction

/**
 * A simple theory of a function f that only produces non-negative values.
 * The instantiation of this axiom is implemented using a
 * <code>SaturationProcedure</code>.
 */
object SimpleTheory extends Theory {

  val f = new IFunction("f", 1, true, false)
  val functions = List(f)

  val (predicates, axioms, _, functionTranslation) =
    Theory.genAxioms(theoryFunctions = functions)
  val Seq(_f) = predicates
  val totalityAxioms = Conjunction.TRUE

  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions : Set[IFunction] = Set()
  val functionalPredicates = predicates.toSet
  val functionPredicateMapping = List(f -> _f)

  def plugin = None
  
  /**
   * Saturate: add instances of the axiom that the result of f is non-negative
   */
  object PosSaturator extends SaturationProcedure("f_pos") {
    type ApplicationPoint = Atom

    def extractApplicationPoints(goal : Goal) : Iterator[ApplicationPoint] =
      goal.facts.predConj.positiveLitsWithPred(_f).iterator

    def applicationPriority(goal : Goal, p : ApplicationPoint) : Int =
      p(1).size
    
    def handleApplicationPoint(goal : Goal, fAtom : Atom) : Seq[Plugin.Action]=
      if (goal.facts.predConj.positiveLitsAsSet contains fAtom) {
        import TerForConvenience._
        implicit val order = goal.order
        List(Plugin.AddAxiom(List(fAtom), fAtom(1) >= 0, SimpleTheory.this))
      } else {
        List()
      }
  }

  override val dependencies = List(PosSaturator)

  TheoryRegistry register this

}

object TestSaturationProcedure extends App {

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._
    import IExpression._

    addTheory(SimpleTheory)

    val c = createConstant("c")
    val d = createConstant("d")
    val e = createConstant("e")

    import SimpleTheory.f

    scope {
      !! (f(c) + f(d) + f(e) <= 1)
      ?? (f(d) <= 1)
      println(???) // Valid
    }

    scope {
      !! (f(f(d)) === 2)
      !! (f(d) <= 0)
      !! (d === 0)
      println(???) // Unsat
    }
  }

}

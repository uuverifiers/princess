/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.util.Seqs

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 ArrayBuffer}

/**
 * Class to inline equivalences of the form <code>p <-> f</code>, for
 * some Boolean variable p.
 */
object EquivInliner {
  import IExpression._

  val INLINE_SIZE_BOUND = 16
  val INLINE_NUM_BOUND  = 16

  def apply(f : IFormula) : IFormula = {

    val inlinedVars  = new MHashSet[Predicate]

    var inlinedF = f
    var cont     = true
    while (cont) {
      val newF = inlineDefinitions(inlinedF, inlinedVars)
      cont     = !(newF eq inlinedF)
      inlinedF = newF
    }

    inlinedF
  }

  private def inlineDefinitions(f            : IFormula,
                                inlinedVars  : MHashSet[Predicate]) : IFormula ={
    val occs =
      new BooleanVarOccurrenceCounter
    occs.visitWithoutResult(f, ())

    val defColl =
      new DefinitionCollector(occs.occurrences, freshBooleanVars, inlinedVars)
    val newF =
      defColl.visit(f, false).asInstanceOf[IFormula]

    if (defColl.definitions.isEmpty) {
      f
    } else {
      inlinedVars ++= defColl.definitions.keysIterator
      UniformSubstVisitor(newF, defColl.definitions)
    }
  }

  private val freshBooleanVars =
    for (n <- Stream.iterate(0){_ + 1}) yield new Predicate("p" + n, 0)

  private def alwaysInline(body : IFormula) : Boolean = body match {
    case LeafFormula(_) => true
    case INot(f)        => alwaysInline(f)
    case _              => false
  }

  private class DefinitionCollector(occurrenceNums : MHashMap[Predicate, Int],
                                    freshVars      : Stream[Predicate],
                                    inlinedVars    : MHashSet[Predicate])
                extends CollectingVisitor[Boolean, IExpression] {

    val definitions    = new MHashMap[Predicate, IFormula]
    val bodyPredicates = new MHashSet[Predicate]
    var nextBooleanVar = freshVars

    def possibleInlineDef(p : Predicate, body : IFormula) : Boolean = {
      !(definitions contains p) &&
      !(inlinedVars contains p) &&
      occurrenceNums(p) > 1 &&
      !(bodyPredicates contains p) && {

        val bodyPreds = SymbolCollector.nullaryPredicates(body)

        !(bodyPreds contains p) &&
        Seqs.disjoint(bodyPreds, definitions.keySet) &&
        Seqs.disjoint(bodyPreds, inlinedVars)

      } && {

        occurrenceNums(p) <= 2 ||
        alwaysInline(body) ||
        (occurrenceNums(p) <= INLINE_NUM_BOUND &&
           SizeVisitor(body) <= INLINE_SIZE_BOUND)

      }
    }

    def addDef(p       : Predicate,
               body    : IFormula,
               negated : Boolean) : PreVisitResult = {
      val defVar     = nextBooleanVar.head
      nextBooleanVar = nextBooleanVar.tail

      definitions.put(p, body <===> negated)
      definitions.put(defVar, p() <=> body)

      bodyPredicates ++= SymbolCollector.nullaryPredicates(body)

      ShortCutResult(defVar())
    }

    override def preVisit(t : IExpression,
                          negated : Boolean) : PreVisitResult = t match {
      case t@IBinFormula(IBinJunctor.Eqv, IAtom(p, Seq()), body)
          if possibleInlineDef(p, body) =>
        addDef(p, body, negated)
      case t@IBinFormula(IBinJunctor.Eqv, body, IAtom(p, Seq()))
          if possibleInlineDef(p, body) =>
        addDef(p, body, negated)
      case t@IBinFormula(IBinJunctor.Eqv, INot(IAtom(p, Seq())), body)
          if possibleInlineDef(p, body) =>
        addDef(p, ~body, negated)
      case t@IBinFormula(IBinJunctor.Eqv, body, INot(IAtom(p, Seq())))
          if possibleInlineDef(p, body) =>
        addDef(p, ~body, negated)

      case IBinFormula(IBinJunctor.Or, _, _) if !negated =>
        KeepArg
      case IBinFormula(IBinJunctor.And, _, _) if negated =>
        KeepArg
      case _ : INamedPart =>
        KeepArg
      case _ : INot =>
        UniSubArgs(!negated)
      case _ =>
        ShortCutResult(t)
    }

    def postVisit(t : IExpression, negated : Boolean,
                  subres : Seq[IExpression]) : IExpression =
      t update subres

  }

  private class BooleanVarOccurrenceCounter
                extends CollectingVisitor[Unit, Unit] {

    val occurrences = new MHashMap[Predicate, Int]

    override def preVisit(t : IExpression,
                          arg : Unit) : PreVisitResult = {
      t match {
        case IAtom(p, Seq()) =>
          occurrences.put(p, occurrences.getOrElse(p, 0) + 1)
        case _ =>
          // nothing
      }

      KeepArg
    }

    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[Unit]) : Unit = ()

  }

}

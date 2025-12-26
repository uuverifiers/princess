/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2022-2025 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.arrays

import ap.basetypes.IdealInt
import ap.Signature
import ap.types.{Sort, ProxySort, MonoSortedIFunction, MonoSortedPredicate}
import ap.theories.{Theory, TheoryRegistry, ADT}
import ap.parser._
import ap.terfor.conjunctions.Conjunction
import ADT.BoolADT

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashMap => MHashMap, Map => MMap, Set => MSet}

object SetTheory {

  import CombArray.CombinatorSpec
  import IExpression._

  /**
   * Combinators on sets, represented as Boolean-valued
   * arrays. Booleans are represented as numbers <code>{0, 1}</code>,
   * with <code>0</code> representing <code>true</code>.
   */
  def setOps(suffix : String) = Vector(
    CombinatorSpec("union_" + suffix, List(0, 0), 0,
                   (v(2) <= v(0)) & (v(2) <= v(1)) & (v(0) + v(1) <= v(2) + 1)),
    CombinatorSpec("isect_" + suffix, List(0, 0), 0,
                   (v(0) <= v(2)) & (v(1) <= v(2)) & (v(0) + v(1) >= v(2))),
    CombinatorSpec("minus_" + suffix, List(0, 0), 0,
                   (v(0) <= v(2)) & (v(1) + v(2) >= 1) &
                     (v(0) + 1 >= v(1) + v(2))),
    CombinatorSpec("compl_" + suffix, List(0), 0,
                   v(0) + v(1) === 1)
  )

  private val instances = new MHashMap[Sort, SetTheory]

  /**
   * Get a unique instance of the set theory with the element sort.
   */
  def apply(elSort : Sort) : SetTheory = synchronized {
    instances.getOrElseUpdate(elSort, new SetTheory(elSort))
  }

}

/**
 * A theory of typed sets, implementing using combinatorial arrays.
 */
class SetTheory(val elementSort : Sort)
      extends Theory with SMTLinearisableTheory {

  val arTheory = new ExtArray(List(elementSort), Sort.Bool)
  val combArTheory = new CombArray(Vector(arTheory),
                                   SetTheory.setOps(elementSort.name))
  import arTheory.{select, store, const}
  import combArTheory.combinators

  override val dependencies = List(combArTheory)

  object SetSort extends ProxySort(arTheory.sort) with Theory.TheorySort {
    import IExpression._
    val theory = SetTheory.this

    // TODO: implement further methods. In particular, we have to translate
    // back array terms to set terms, similar to how it is done in
    // ArraySeqTheory

    override def decodeToTerm(
                   id : IdealInt,
                   amt : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      super.decodeToTerm(id, amt).map(translateArrayTerm _)
    
    private def translateArrayTerm(t : ITerm) : ITerm =
      t match {
        case IFunApp(`const`, Seq(BoolADT.False)) =>
          SetTheory.this.emptySet()
        case IFunApp(`const`, Seq(BoolADT.True)) =>
          SetTheory.this.all()
        case IFunApp(`store`, Seq(sub, el, BoolADT.True)) =>
          insert(el, translateArrayTerm(sub))
        case IFunApp(`store`, Seq(sub, el, BoolADT.False)) =>
          remove(el, translateArrayTerm(sub))
        case _ =>
          t
      }
  }

  val sort = SetSort

  /**
   * <code>{}</code>.
   */
  val emptySet =
    new MonoSortedIFunction("emptySet",
                            List(), SetSort, true, false)

  /**
   * Set of all elements.
   */
  val all =
    new MonoSortedIFunction("all",
                            List(), SetSort, true, false)

  /**
   * <code>union(set, {el})</code>.
   */
  val insert =
    new MonoSortedIFunction("insert",
                            List(elementSort, SetSort), SetSort, true, false)

  /**
   * <code>set \ {el}</code>.
   */
  val remove =
    new MonoSortedIFunction("remove",
                            List(elementSort, SetSort), SetSort, true, false)

  /**
   * <code>el in set</code>
   */
  val member =
    new MonoSortedPredicate("member",
                            List(elementSort, SetSort))

  def including(set : ITerm, el : ITerm) : ITerm = {
    import IExpression._
    insert(el, set)
  }

  def excluding(set : ITerm, el : ITerm) : ITerm = {
    import IExpression._
    remove(el, set)
  }

  val functions = List(emptySet, all, insert, remove)
  val predefPredicates = List(member)

  val (predicates, axioms, _, funPredMap) =
    Theory.genAxioms(theoryFunctions = functions,
                     otherTheories   = dependencies,
                     extraPredicates = predefPredicates)

  val functionPredicateMapping =
    for (f <- functions) yield (f -> funPredMap(f))
  val functionalPredicates =
    (functions map funPredMap).toSet
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val totalityAxioms = Conjunction.TRUE
  val triggerRelevantFunctions : Set[IFunction] = Set()

  def plugin = None

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary |
           Theory.SatSoundnessConfig.Existential => true
      case Theory.SatSoundnessConfig.General     => false
    }

  /**
   * Visitor called during pre-processing to eliminate symbols.
   */
  private object Preproc extends CollectingVisitor[Unit, IExpression] {
    import IExpression._

    def postVisit(t : IExpression,
                  arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IFunApp(`emptySet`, _) =>
        const(1)
      case IFunApp(SetTheory.this.all, _) =>
        const(0)
      case IFunApp(`insert`, _) =>
        store(subres(1).asInstanceOf[ITerm], subres(0).asInstanceOf[ITerm], 0)
      case IFunApp(`remove`, _) =>
        store(subres(1).asInstanceOf[ITerm], subres(0).asInstanceOf[ITerm], 1)
      case IAtom(`member`, _) =>
        eqZero(select(subres(1).asInstanceOf[ITerm],
                      subres(0).asInstanceOf[ITerm]))
      case t =>
        t update subres
    }
  }

  override def iPreprocess(f : IFormula, signature : Signature)
                          : (IFormula, Signature) = {
//    println("before: " + f)
    val res = Preproc.visit(f, ()).asInstanceOf[IFormula]
//    println("after: " + res)
    (res, signature)
  }

  /**
   * <code>{el1, ..., eln}</code>.
   */
  def set(els : ITerm*) : ITerm = {
    import IExpression._
    var res : ITerm = emptySet()
    for (el <- els)
      res = including(res, el)
    res
  }

  /**
   * <code>el in set</code>.
   * TODO: turn this into a proper predicate.
   */
  def contains(set : ITerm, el : ITerm) : IFormula = {
    import IExpression._
    member(el, set)
  }

  /**
   * <code>set1</code> is a subset of <code>set2</code>.
   * TODO: turn this into a proper predicate.
   */
  def subsetOf(set1 : ITerm, set2 : ITerm) : IFormula = {
    import IExpression._
    minus(set1, set2) === emptySet()
  }

  val Seq(union, isect, minus, compl) = combinators

  override def sort2SMTType(s : Sort) : Option[SMTTypes.SMTType] =
    s match {
      case SetSort => Some(SMTTypes.SMTSet(SMTTypes.sort2SMTType(elementSort)._1))
      case _ => None
    }

  override def fun2SMTString(f : IFunction) : Option[String] =
    f match {
      case `emptySet` =>
        Some(f"(as set.empty ${sort2SMTType(SetSort).get.toSMTLIBString})")
      case this.all =>
        Some(f"(as set.all ${sort2SMTType(SetSort).get.toSMTLIBString})")
      case `insert` =>
        Some("set.insert")
      case `remove` =>
        Some("set.remove")
      case _ =>
        None
    }

  override def pred2SMTString(p : IExpression.Predicate) : Option[String] =
    p match {
      case `member` =>
        Some("set.member")
      case _ =>
        None
    }

  override def toString = "SetTheory[" + elementSort + "]"
  TheoryRegistry register this

}

/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2019 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor

import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.{Conjunction, Quantifier, NegatedConjunctions}
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.arithconj.ArithConj
import ap.terfor.preds.{PredConj, Predicate, Atom}
import ap.types.Sort

/**
 * Collection of functions that makes it easier to use the term/formula
 * datastructures by adding lots of syntactic sugar
 */
object TerForConvenience {

  implicit def l(i: Int) : LinearCombination = LinearCombination(IdealInt(i))

  implicit def l(i: IdealInt) : LinearCombination = LinearCombination(i)

  implicit def l(t: Term)(implicit order : TermOrder) : LinearCombination =
    LinearCombination(t, order)

  def v(index : Int) : VariableTerm = VariableTerm(index)
  
  implicit def eqConj2Conj(eqs : EquationConj) =
    Conjunction.conj(eqs, eqs.order)
  
  implicit def negEqConj2Conj(eqs : NegEquationConj) =
    Conjunction.conj(eqs, eqs.order)
  
  implicit def negEqConj2ArithConj(eqs : NegEquationConj) =
    ArithConj.conj(eqs, eqs.order)

  implicit def eqConj2ArithConj(eqs : EquationConj) =
    ArithConj.conj(eqs, eqs.order)

  implicit def inEqConj2ArithConj(eqs : InEqConj) =
    ArithConj.conj(eqs, eqs.order)

  implicit def inEqConj2Conj(eqs : InEqConj) =
    Conjunction.conj(eqs, eqs.order)
  
  implicit def arithConj2Conj(ac : ArithConj) =
    Conjunction.conj(ac, ac.order)

  implicit def predConj2Conj(pc : PredConj) =
    Conjunction.conj(pc, pc.order)

  implicit def negatedConjs2Conj(conjs : NegatedConjunctions) =
    Conjunction(List(), ArithConj.TRUE, PredConj.TRUE, conjs, conjs.order)

  implicit def term2RichLC(lc : Term)(implicit order : TermOrder) =
    new RichLinearCombination(lc, order)

  implicit def termSeq2RichLCSeq(lcs : Seq[Term])(implicit order : TermOrder) =
    new RichLinearCombinationSeq(for (lc <- lcs) yield l(lc), order)

  implicit def pred2RichPred(pred : Predicate)(implicit order : TermOrder) =
    new RichPredicate(pred, order)

  implicit def pred2Conj(p : Predicate)(implicit order : TermOrder) =
    Conjunction.conj(pred2PredConj(p), order)

  implicit def pred2PredConj(p : Predicate)(implicit order : TermOrder) =
    atom2PredConj(Atom(p, Seq(), order))

  implicit def atom2Conj(atom : Atom) =
    Conjunction.conj(atom2PredConj(atom), atom.order)

  implicit def atom2PredConj(atom : Atom) =
    PredConj(List(atom), List(), atom.order)

  //////////////////////////////////////////////////////////////////////////////
  
  def conj(formulas : Iterator[Formula])(implicit order : TermOrder) =
    Conjunction.conj(formulas, order)
  
  def conj(formulas : Iterable[Formula])(implicit order : TermOrder) =
    Conjunction.conj(formulas, order)
  
  def conj(formulas : Formula*)(implicit order : TermOrder) =
    Conjunction.conj(formulas, order)
  
  def disj(formulas : Iterator[Conjunction])(implicit order : TermOrder) =
    Conjunction.disj(formulas, order)
  
  def disj(formulas : Iterable[Conjunction])(implicit order : TermOrder) =
    Conjunction.disj(formulas, order)
  
  def disj(formulas : Conjunction*)(implicit order : TermOrder) =
    Conjunction.disj(formulas, order)
  
  def disjFor(formulas : Iterator[Formula])(implicit order : TermOrder) =
    Conjunction.disjFor(formulas, order)
  
  def disjFor(formulas : Iterable[Formula])(implicit order : TermOrder) =
    Conjunction.disjFor(formulas, order)
  
  def disjFor(formulas : Formula*)(implicit order : TermOrder) =
    Conjunction.disjFor(formulas, order)
  
  def arithConj(formulas : Iterator[Formula])(implicit order : TermOrder) =
    ArithConj.conj(formulas, order)
  
  def arithConj(formulas : Iterable[Formula])(implicit order : TermOrder) =
    ArithConj.conj(formulas, order)
  
  def arithConj(formulas : Formula*)(implicit order : TermOrder) =
    ArithConj.conj(formulas, order)
  
  def quantify(quan : Quantifier, constants : Seq[ConstantTerm],
               f : Formula)(implicit order : TermOrder) : Conjunction =
    Conjunction.quantify(quan, constants, f, order)
  
  def forall(constants : Seq[ConstantTerm], f : Formula)
            (implicit order : TermOrder) : Conjunction =
    Conjunction.quantify(Quantifier.ALL, constants, f, order)

  def forall(constant : ConstantTerm, f : Formula)
            (implicit order : TermOrder) : Conjunction =
    forall(List(constant), f)

  /**
   * Quantify the variable with De Brujin-index 0
   */
  def forall(f : Formula)(implicit order : TermOrder) : Conjunction =
    Conjunction.quantify(List(Quantifier.ALL), f, order)

  /**
   * Quantify the variables with De Brujin-index [0, ..., n)
   */
  def forall(n : Int, f : Formula)(implicit order : TermOrder) : Conjunction =
    Conjunction.quantify(for (_ <- 0 until n) yield Quantifier.ALL,
                         f, order)

  /**
   * Quantify the variables with De Brujin-index
   * <code>[0, ..., sorts.size)</code>, assuming they have the given sorts
   */
  def forallSorted(sorts : Seq[Sort], f : Formula)
                  (implicit order : TermOrder) : Conjunction =
    Conjunction.quantify(
      for (_ <- sorts) yield Quantifier.ALL,
      Conjunction.implies(
        Conjunction.conj(for ((s, ind) <- sorts.iterator.zipWithIndex)
                         yield (s membershipConstraint v(ind)),
                         order),
        f, order),
      order)

  def exists(constants : Seq[ConstantTerm], f : Formula)
            (implicit order : TermOrder) : Conjunction =
    Conjunction.quantify(Quantifier.EX, constants, f, order)

  def exists(constant : ConstantTerm, f : Formula)
            (implicit order : TermOrder) : Conjunction =
    exists(List(constant), f)

  /**
   * Quantify the variable with De Brujin-index 0
   */
  def exists(f : Formula)(implicit order : TermOrder) : Conjunction =
    Conjunction.quantify(List(Quantifier.EX), f, order)

  /**
   * Quantify the variables with De Brujin-index <code>[0, ..., n)</code>
   */
  def exists(n : Int, f : Formula)(implicit order : TermOrder) : Conjunction =
    Conjunction.quantify(for (_ <- 0 until n) yield Quantifier.EX,
                         f, order)

  /**
   * Quantify the variables with De Brujin-index
   * <code>[0, ..., sorts.size)</code>, assuming they have the given sorts
   */
  def existsSorted(sorts : Seq[Sort], f : Formula)
                  (implicit order : TermOrder) : Conjunction =
    Conjunction.quantify(
      for (_ <- sorts) yield Quantifier.EX,
      Conjunction.conj((for ((s, ind) <- sorts.iterator.zipWithIndex)
                        yield (s membershipConstraint v(ind))) ++
                       (Iterator single f),
                       order),
      order)

  //////////////////////////////////////////////////////////////////////////////

  def eqZ(lcs : Iterable[LinearCombination])(implicit order : TermOrder) =
    EquationConj(lcs, order)

  def eqZ(lcs : Iterator[LinearCombination])(implicit order : TermOrder) =
    EquationConj(lcs, order)

  def unEqZ(lcs : Iterable[LinearCombination])(implicit order : TermOrder) =
    NegEquationConj(lcs, order)

  def unEqZ(lcs : Iterator[LinearCombination])(implicit order : TermOrder) =
    NegEquationConj(lcs, order)

  def geqZ(lcs : Iterable[LinearCombination])(implicit order : TermOrder) =
    InEqConj(lcs, order)

  def geqZ(lcs : Iterator[LinearCombination])(implicit order : TermOrder) =
    InEqConj(lcs, order)

  def sum(lcs : Seq[(IdealInt, LinearCombination)])(implicit order : TermOrder) =
    LinearCombination.sum(lcs, order)

  def sum(lcs : Iterator[(IdealInt, LinearCombination)])(implicit order : TermOrder) =
    LinearCombination.sum(lcs, order)

  def lcSum(lcs : Iterable[LinearCombination])(implicit order : TermOrder) =
    LinearCombination.sum(for (lc <- lcs.iterator) yield (IdealInt.ONE, lc), order)

  def lcSum(lcs : Iterator[LinearCombination])(implicit order : TermOrder) =
    LinearCombination.sum(for (lc <- lcs) yield (IdealInt.ONE, lc), order)

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Various infix operators terms and linear combinations
 */
class RichLinearCombination(lc : LinearCombination, order : TermOrder) {
  import TerForConvenience._
  implicit val o = order

  // various component-wise operations
  def +++(that : Seq[Term]) : Seq[LinearCombination] =
    for (lc2 <- that) yield (lc + lc2)
  def ---(that : Seq[Term]) : Seq[LinearCombination] =
    for (lc2 <- that) yield (lc - lc2)
  
  def ===(that : Term) = EquationConj(lc - that, order)
  def ===(that : Seq[Term]) = EquationConj(this --- that, order)
  def >=(that : Term) = InEqConj(lc - that, order)
  def >=(that : Seq[Term]) = InEqConj(this --- that, order)
  def >(that : Term) = InEqConj(lc - that - 1, order)
  def >(that : Seq[Term]) = InEqConj(this --- that --- 1, order)
  def <=(that : Term) = InEqConj(that - lc, order)
  def <=(that : Seq[Term]) = InEqConj(that --- lc, order)
  def <(that : Term) = InEqConj(that - lc - 1, order)
  def <(that : Seq[Term]) = InEqConj(that --- lc --- 1, order)

  def =/=(that : Term) = NegEquationConj(lc - that, order)
  /** Disequation of vectors (vector differs in at least one component) */
  def =/=(that : Seq[Term]) =
    Conjunction.negate(EquationConj(this --- that, order), order)

  /** Component-wise disequation of vectors
    * (all components of the vector are different from a linear combination) */
  def =/=/=(that : Seq[Term]) =
    NegEquationConj(this --- that, order)
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Various functions to work with vectors of terms
 */
class RichLinearCombinationSeq(lcs : Seq[LinearCombination], order : TermOrder) {
  import TerForConvenience._
  implicit val o = order
  
  // various component-wise operations
  def +++(that : Seq[Term]) : Seq[LinearCombination] =
    (for ((lc1, lc2) <- lcs.iterator zip that.iterator) yield (lc1 + lc2)).toList
  def +++(that : Term) : Seq[LinearCombination] =
    for (lc <- lcs) yield (lc + that)
  def ---(that : Seq[Term]) : Seq[LinearCombination] =
    (for ((lc1, lc2) <- lcs.iterator zip that.iterator) yield (lc1 - lc2)).toList
  def ---(that : Term) : Seq[LinearCombination] =
    for (lc <- lcs) yield (lc - that)
  def ***(that : Seq[Term]) : Seq[LinearCombination] =
    (for ((lc1, lc2) <- lcs.iterator zip that.iterator) yield (lc1 * lc2)).toList
  def ***(that : Term) : Seq[LinearCombination] =
    for (lc <- lcs) yield (lc * that)
  
  /** The dot-product of two vectors */
  def *:*(that : Seq[Term]) : LinearCombination =
    lcSum(for ((lc1, lc2) <- lcs.iterator zip that.iterator) yield (lc1 * lc2))

  def unary_- : Seq[LinearCombination] =
    for (lc <- lcs) yield -lc

  /** Equation of two vectors */
  def ===(that : Seq[Term]) = EquationConj(this --- that, order)
  /** Component-wise equation */
  def ===(that : Term) = EquationConj(this --- that, order)
  def >=(that : Seq[Term]) = InEqConj(this --- that, order)
  def >=(that : Term) = InEqConj(this --- that, order)
  def >(that : Seq[Term]) = InEqConj(this --- that --- 1, order)
  def >(that : Term) = InEqConj(this --- that --- 1, order)
  def <=(that : Seq[Term]) = InEqConj(that --- lcs, order)
  def <=(that : Term) = InEqConj(that --- lcs, order)
  def <(that : Seq[Term]) = InEqConj(that --- lcs --- 1, order)
  def <(that : Term) = InEqConj(that --- lcs --- 1, order)

  /** Disequation of vectors (vectors differ in at least one component) */
  def =/=(that : Seq[Term]) =
    Conjunction.negate(EquationConj(this --- that, order), order)
  /** Disequation of vectors (vector differs in at least one component) */
  def =/=(that : Term) =
    Conjunction.negate(EquationConj(this --- that, order), order)

  /** Component-wise disequation of vectors
    * (all components of the vectors are different) */
  def =/=/=(that : Seq[Term]) =
    NegEquationConj(this --- that, order)
  /** Component-wise disequation of vectors
    * (all components of the vectors are different) */
  def =/=/=(that : Term) =
    NegEquationConj(this --- that, order)
}


////////////////////////////////////////////////////////////////////////////////

/**
 * A few functions to work with predicates
 */
class RichPredicate(pred : Predicate, order : TermOrder) {
  implicit val o = order

  def apply(args : Seq[LinearCombination]) : Atom = Atom(pred, args, order)

  def apply(args : Iterator[LinearCombination]) : Atom = Atom(pred, args, order)
}

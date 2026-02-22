/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C)      2014-2025 Philipp Ruemmer <ph_r@gmx.net>
 *                    2014 Peter Backeman <peter.backeman@it.uu.se>
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

package ap.theories.nia

import ap.basetypes.IdealInt
import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.preds.{Atom, Predicate, PredConj}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.TerForConvenience._
import ap.util.{Timeout, Seqs, Debug, LRUCache, IdealRange}

import scala.collection.mutable.{HashSet => MHashSet, ArrayBuffer, LinkedHashSet}

object Buchberger {
  import GroebnerMultiplication.AC

  /**
   * Conversion functions
   */
  def genMonomialOrder(predicates : Seq[Atom],
                       baseOrder  : TermOrder)
                                  : MonomialOrdering = {
    val inputConsts = new MHashSet[ConstantTerm]

    // We first compute the "defined" symbols, which are the symbols
    // occurring in the terms c of multiplication atoms mul(a, b, c).

    // Consider the symbols in the terms a, b as "input symbols"
    for (a <- predicates) {
      inputConsts ++= a(0).constants
      inputConsts ++= a(1).constants
    }

    // Remove the constants that were generated internally
    // TODO: this should not be done based on the name
    for (a <- predicates.iterator)
      for (x <- a(2).constants.iterator)
        if ((x.name startsWith "all") ||
            (x.name startsWith "ex") ||
            (x.name startsWith "sc"))
          inputConsts -= x

    // Fix-point computation to find the defined constants in the c terms
    val definedConsts = new LinkedHashSet[ConstantTerm]
    val remainingPreds = new LinkedHashSet[Atom]

    for (a <- predicates)
      if (!a(2).isConstant)
        remainingPreds += a

    var cont = true
    while (cont) {
      cont = false

      val predIt = remainingPreds.iterator
      while (!cont && predIt.hasNext) {
        val a = predIt.next()
        val lhsDefined =
          (a(0).constants.iterator ++ a(1).constants.iterator) forall inputConsts

        if (lhsDefined) {
          remainingPreds -= a
          val x = a(2).leadingTerm.asInstanceOf[ConstantTerm]
          inputConsts += x
          definedConsts += x
          cont = true // exit the inner loop, continue in the outer loop
        }
      }
    }

    val orderList = definedConsts.toIndexedSeq
    new PartitionOrdering(orderList,
                          new GrevlexOrdering(baseOrder.constOrdering))
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Buchberger algorithm
   * This function will modify the contents of the argument
   * <code>unprocessed</code>
   */
  def buchberger(unprocessed : Basis) : Basis = {
    implicit val _ = unprocessed.ordering

    // First move from unprocessed =>
    //   passive - reducing all polynomials in active
    // Then move from passive to active =>
    //   adding all s-polynomials to unprocessed

    val active, passive = new Basis

    while (!unprocessed.isEmpty || !passive.isEmpty) {
      Timeout.check

/*
println("======================")

println()
println("Active:")
println(active)

println()
println("Passive:")
println(passive)

println()
println("Unproc:")
println(unprocessed)
*/

      if (!unprocessed.isEmpty) {

        // Move one polynomial from unprocessed to passive
        val (chosen, chosenLabel) = unprocessed.get
//println("next: " + chosen)
        val (newPoly, newLabel) =
          active.reducePolynomial(passive, chosen, chosenLabel)

        // If the new polynomial is reduced to zero, reiterate
        if (!newPoly.isZero) {
          val reducedActive  = active.reduceBy(newPoly, newLabel)
          val reducedPassive = passive.reduceBy(newPoly, newLabel)

          unprocessed add reducedActive
          unprocessed add reducedPassive

          passive.add(newPoly, newLabel)
        }

      } else if (!passive.isEmpty) {

        val (newPoly, newLabel) = passive.get

        for (p <- active.polyIterator)
          if (newPoly.lt hasCommonVariables p.lt) {
            val spol = newPoly spol p
            if (!spol.isZero)
              unprocessed.add(spol, newLabel | (active labelFor p))
          }

        active.add(newPoly, newLabel)

      }
    }

    active
  }

  /**
   * Converts Polynomial (Groebner) to an Atom (Princess)
   * PRE: p is linear
   */
  def polynomialToAtom(p : Polynomial)
                      (implicit order : TermOrder) : Conjunction = {
    def termToLc(t : CoeffMonomial) : LinearCombination = {
      //-BEGIN-ASSERTION-//////////////////////////////////////////////////////
      Debug.assertInt(AC, t.m.isLinear)
      //-END-ASSERTION-////////////////////////////////////////////////////////
      if (t.m.pairs == Nil)
        t.c
      else
        l(t.c) * t.m.pairs.head._1
    }

    val terms =
      for (t <- p.terms; if (!t.isZero))
      yield termToLc(t)

    val LHS = (terms.tail).foldLeft(terms.head) ((t1,t2) => t1 + t2)
    conj(LHS === 0)
  }

  def makeMap(polylist : Seq[Polynomial]) : List[Monomial] = {
      var newmap = List[Monomial]()

      for (p <- polylist)
        for (t <- p.terms)
          if (!(newmap contains t.m)) {
            if (t.m.isLinear)
              newmap = t.m :: newmap
            else
              newmap = newmap ++ List(t.m)
          }
      newmap
    }

  def polyToRow(poly : Polynomial, map : List[Monomial]) : List[IdealInt] = {
    for (m <- map)
    yield {
      val termOpt = poly.terms find (_.m == m)
      termOpt match {
        case Some(term) => term.c
        case None => IdealInt.ZERO
      }
    }
  }

  def makeMatrix(polylist : Seq[Polynomial]) : Vector[Vector[IdealInt]] = {
    var monomialMap = makeMap(polylist)
    (for (p <- polylist) yield polyToRow(p, monomialMap).toVector).toVector
  }

  def rowToPolynomial(map : List[Monomial], row : Array[IdealInt])
                      (implicit monOrder : MonomialOrdering) = {
    var retPoly = Polynomial(List())
    for (i <- 0 until row.length;
      if (!row(i).isZero))
      retPoly += new CoeffMonomial(row(i), map(i))

    retPoly
  }
}
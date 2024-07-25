/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

import ap.parser._
import ap.terfor.TermOrder
import ap.types.Sort

import scala.collection.mutable.{HashSet => MHashSet, ArrayBuffer}

/**
 * Class to find out which theories where used in a given set
 * of formulae/expressions
 */
class TheoryCollector extends CollectingVisitor[Unit, Unit]
                      with    Cloneable {

  private val symbolsSeen  = new MHashSet[AnyRef]
  private val theoriesSeen = new MHashSet[Theory]

  private var theoriesList = new ArrayBuffer[Theory]
  private var theoriesDiff = new ArrayBuffer[Theory]

  def theories : Seq[Theory] = theoriesList.toSeq

  def reset       = theoriesDiff.clear
  def newTheories : Seq[Theory] = theoriesDiff.toSeq

  override def clone : TheoryCollector = {
    val res = new TheoryCollector
    
    res.symbolsSeen  ++= this.symbolsSeen
    res.theoriesSeen ++= this.theoriesSeen
    res.theoriesList ++= this.theoriesList
    res.theoriesDiff ++= this.theoriesDiff
    
    res
  }

  //////////////////////////////////////////////////////////////////////////////

  def addTheory(t : Theory) : Unit =
    if (theoriesSeen add t) {
      for (s <- t.dependencies)
        addTheory(s)
      theoriesList += t
      theoriesDiff += t
    }

  def addTheoryFront(t : Theory) : Unit =
    if (theoriesSeen add t) {
      theoriesList.insert(0, t)
      for (s <- t.dependencies)
        addTheory(s)
      theoriesDiff += t
    }

  def includes(t : Theory) = theoriesSeen contains t

  //////////////////////////////////////////////////////////////////////////////

  def apply(expr : IExpression) : Unit =
    this.visitWithoutResult(expr, {})

  def postVisit(t : IExpression, arg : Unit,
                subres : Seq[Unit]) : Unit = t match {
    case IFunApp(f, _)              => apply(f)
    case IAtom(p, _)                => apply(p)
    case ISortedQuantified(_, s, _) => apply(s)
    case ISortedEpsilon(s, _)       => apply(s)
    case _ => // nothing
  }
  
  def apply(f : IFunction) : Unit =
    if (symbolsSeen add f) {
      for (t <- TheoryRegistry lookupSymbol f)
        addTheory(t)
    }
    
  def apply(p : IExpression.Predicate) : Unit =
    if (symbolsSeen add p) {
      for (t <- TheoryRegistry lookupSymbol p)
        addTheory(t)
    }

  def apply(order : TermOrder) : Unit =
    for (p <- order sortPreds order.orderedPredicates)
      apply(p)

  def apply(s : Sort) : Unit =
    if (symbolsSeen add s) {
      for (t <- TheoryRegistry lookupSort s)
        addTheory(t)
    }

}

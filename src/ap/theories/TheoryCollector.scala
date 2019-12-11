/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2019 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

import ap.parser._
import ap.terfor.TermOrder

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

  def theories : Seq[Theory] = theoriesList

  def reset       = theoriesDiff.clear
  def newTheories : Seq[Theory] = theoriesDiff

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
    case IFunApp(f, _) => apply(f)
    case IAtom(p, _)   => apply(p)
    case _ => // nothing
  }
  
  def apply(f : IFunction) : Unit =
    if (!(symbolsSeen contains f)) {
      symbolsSeen += f
      for (t <- TheoryRegistry lookupSymbol f)
        addTheory(t)
    }
    
  def apply(p : IExpression.Predicate) : Unit =
    if (!(symbolsSeen contains p)) {
      symbolsSeen += p
      for (t <- TheoryRegistry lookupSymbol p)
        addTheory(t)
    }

  def apply(order : TermOrder) : Unit =
    for (p <- order sortPreds order.orderedPredicates)
      apply(p)

}

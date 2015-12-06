/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof


import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier

import scala.collection.mutable.ArrayBuffer

object BindingContext {
  
  val EMPTY = new BindingContext(List())
  
}

/**
 * Class to represent the context of constants bound above a certain node in the
 * proof tree. This constant can be seen as a partial ordering on constants:
 * inner bound constants are bigger than outer bound constants 
 */
case class BindingContext private (// the groups of constants that are bound in this
                                   // context, starting with the innermost one
                                   constantSeq : List[(Quantifier, Set[ConstantTerm])])
      extends PartialOrdering[ConstantTerm] {
  
  private val constantPos : scala.collection.Map[ConstantTerm, Int] = {
    val res = new scala.collection.mutable.HashMap[ConstantTerm, Int]
    res ++= (for (((_, consts), num) <- constantSeq.iterator.zipWithIndex;
                  c <- consts.iterator)
             yield (c, -num))
    res
  }

  private val quantifiers : scala.collection.Map[ConstantTerm, Quantifier] = {
    val res = new scala.collection.mutable.HashMap[ConstantTerm, Quantifier]
    res ++= (for ((q, consts) <- constantSeq.iterator; c <- consts.iterator)
             yield (c, q))
    res    
  }
  
  def binder(c : ConstantTerm) : Option[Quantifier] = quantifiers get c
  
  def tryCompare(x : ConstantTerm, y : ConstantTerm) : Option[Int] =
    throw new UnsupportedOperationException

  def lteq (x : ConstantTerm, y : ConstantTerm) : Boolean =
    (constantPos get x, constantPos get y) match {
      case (None, _) => true
      case (Some(xPos), Some(yPos)) => xPos <= yPos
      case _ => false
    }
  
  /**
   * Add a new innermost bound constant to the binding context.
   * If the quantifier of the new constant is the same as of the innermost
   * constant group, just add the constant to the group
   */
  def addAndContract(c : ConstantTerm, q : Quantifier) : BindingContext =
    addAndContract(List(c), q)

  /**
   * Add new innermost bound constants to the binding context.
   * If the quantifier of the new constants is the same as of the innermost
   * constant group, just add the constants to the group
   */
  def addAndContract(c : Iterable[ConstantTerm], q : Quantifier) : BindingContext = {
    constantSeq match {
      case (`q`, consts) :: rem => new BindingContext ((q, consts ++ c) :: rem)
      case _ => new BindingContext ((q, Set() ++ c) :: constantSeq)
    }
  }
  
  /**
   * Filter out and return the maximum elements of a given collection of
   * constants
   */
  def maximumConstants(consts : Iterable[ConstantTerm]) : Seq[ConstantTerm] = {
    val res = new ArrayBuffer [ConstantTerm]
    
    for (c <- consts) {
      if (res.isEmpty || equiv(res(0), c)) {
        res += c
      } else if (lt(res(0), c)) {
        res.clear
        res += c
      }
    }
    
    res
  }
  
  def containsMaximumConstantWith(consts : Iterable[ConstantTerm],
                                  p : ConstantTerm => Boolean) : Boolean = {
    var foundConstant : ConstantTerm = null
    var maxConstantLevel : Option[Int] = None
    
    val constIt = consts.iterator
    
    while (constIt.hasNext) {
      val c = constIt.next
      val cLevel = constantPos get c

      val cIsGreater = (maxConstantLevel, cLevel) match {
        case (None, Some(_)) => true
        case (Some(x), Some(y)) => x < y
        case _ => false
      }
      
      if (cIsGreater) {
        foundConstant = (if (p(c)) c else null)
        maxConstantLevel = cLevel
      } else if (foundConstant == null && maxConstantLevel == cLevel && p(c)) {
        foundConstant = c
      }
    }
    
    foundConstant != null
  }

}

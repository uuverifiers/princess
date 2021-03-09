/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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
    
    res.toSeq
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

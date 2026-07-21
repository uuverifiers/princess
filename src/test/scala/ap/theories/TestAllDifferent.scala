/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2026 Philipp Ruemmer <ph_r@gmx.net>
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

import ap._
import ap.basetypes.IdealInt
import ap.util.Timer

import org.scalacheck.{Properties, Gen, Prop}
import org.scalacheck.Test.Parameters

class TestAllDifferent extends Properties("TestAllDifferent") {
  import AllDifferent._

  type CompleteBlock = (Set[IdealInt], // Classes involved
                        IdealInt,      // Lower bound
                        IdealInt)      // Upper bound

  val genTermTuple : Gen[TermTuple] =
    for(cl <- Gen.choose(0, 10);
        lb <- Gen.choose(0, 10);
        ub <- Gen.choose(lb, 10))
    yield (IdealInt(cl), IdealInt(lb), IdealInt(ub))

  val genTermList =
    for (s <- Gen.choose(0, 20);
         elems <-  Gen.listOfN(s, genTermTuple))
    yield elems

  def hasConflicts(terms         : List[TermTuple],
                   usedClasses   : Set[IdealInt],
                   selectedTerms : List[TermTuple]) : Boolean = {
    isConflict(selectedTerms) ||
    (terms match {
      case List() => false
      case (cl, _, _) :: otherTerms if usedClasses(cl) =>
        hasConflicts(otherTerms, usedClasses, selectedTerms)
      case (t@(cl, _, _)) :: otherTerms =>
        hasConflicts(otherTerms, usedClasses, selectedTerms) ||
        hasConflicts(otherTerms, usedClasses + cl, t :: selectedTerms)
    })
  }

  def allCompleteBlocks(terms           : List[TermTuple],
                        idx             : Int,
                        usedClasses     : Set[IdealInt],
                        selectedTerms   : List[TermTuple],
                        selectedIndexes : List[Int]) : Set[Set[Int]] =
    terms match {
      case List() =>
        if (isCompleteBlock(selectedTerms))
          Set(selectedIndexes.toSet)
        else
          Set()
      case (cl, _, _) :: otherTerms if usedClasses(cl) =>
        allCompleteBlocks(otherTerms, idx + 1, usedClasses,
                          selectedTerms, selectedIndexes)
      case (t@(cl, _, _)) :: otherTerms =>
        allCompleteBlocks(otherTerms, idx + 1, usedClasses,
                          selectedTerms, selectedIndexes) ++
        allCompleteBlocks(otherTerms, idx + 1, usedClasses + cl,
                          t :: selectedTerms, idx :: selectedIndexes)
    }

  def allCompleteBlocks2(terms : List[TermTuple]) : Set[CompleteBlock] = {
    val blocks = allCompleteBlocks(terms, 0, Set(), List(), List())
    blocks.map(indexes => {
      val selTerms =
        terms.zipWithIndex.filter(p => indexes.contains(p._2)).unzip._1
      val (cls, lbs, ubs) =
        selTerms.unzip3
      (cls.toSet, lbs.min, ubs.max)
    })
  }

  def isConflict(selectedTerms : List[TermTuple]) : Boolean = {
    val (cls, lbs, ubs) = selectedTerms.unzip3
    !cls.isEmpty &&
    cls.toSet.size == cls.size &&
    IdealInt(selectedTerms.size) > (ubs.max - lbs.min + 1)
  }

  def isConflict(terms : List[TermTuple], c : Seq[Int]) : Boolean =
    isConflict(terms.zipWithIndex.filter(p => c.contains(p._2)).unzip._1)

  def isCompleteBlock(selectedTerms : List[TermTuple]) : Boolean = {
    val (cls, lbs, ubs) = selectedTerms.unzip3
    !cls.isEmpty &&
    cls.toSet.size == cls.size &&
    IdealInt(selectedTerms.size) == (ubs.max - lbs.min + 1)
  }

//  override def overrideParameters(p: Parameters) = 
//    p.withMinSuccessfulTests(10000)

  property("correct conflict detection") = {
    Prop.forAllNoShrink(genTermList) { l => 
      val conflict = findConflicts(l)
      Prop.classify(conflict.isInstanceOf[Conflict], "conflict") {
        conflict match {
          case NoConflict(blocks) => {
            !hasConflicts(l, Set(), List()) &&
            blocks.toSet.size == blocks.size &&
            blocks.toSet == allCompleteBlocks2(l)
          }
          case Conflict(indexes) =>
            hasConflicts(l, Set(), List()) &&
            isConflict(l, indexes)
        }
      }
    }
  }

}
/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2023-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser;

import ap.basetypes.IdealInt
import ap.DialogUtil
import ap.types.Sort
import ap.theories.{ADT, Heap, ModuloArithmetic, TheoryRegistry}
import ap.theories.sequences.SeqTheory
import ap.theories.arrays.{ExtArray, SimpleArray}
import ap.theories.strings.StringTheory
import ap.theories.rationals.Rationals
import ap.types.UninterpretedSortTheory

/**
 * Representation of SMT-LIB types. Those are essentially just
 * wrappers around the corresponding sorts.
 */
object SMTTypes {

  import SMTParser2InputAbsy.toNormalBool

  abstract class SMTType {
    def toSort : Sort
    def toSMTLIBString : String
  }

  case object SMTBool                              extends SMTType {
    def toSort = Sort.MultipleValueBool
    def toSMTLIBString = "Bool"
  }

  case object SMTInteger                           extends SMTType {
    def toSort = Sort.Integer
    def toSMTLIBString = "Int"
  }

  case class  SMTReal(sort : Sort)                extends SMTType {
    def toSort = sort
    def toSMTLIBString = "Real"
  }

  case class  SMTArray(arguments : List[SMTType],
                       result : SMTType)           extends SMTType {
    val theory = ExtArray(arguments map { t => toNormalBool(t.toSort) },
                          toNormalBool(result.toSort))
    def toSort = theory.sort
    def toSMTLIBString = DialogUtil asString {
      print("(Array")
      for (s <- arguments) {
        print(" ")
        print(s.toSMTLIBString)
      }
      print(" ")
      print(result.toSMTLIBString)
      print(")")
    }
  }

  case class SMTBitVec(width : Int)                extends SMTType {
    def toSort = ModuloArithmetic.UnsignedBVSort(width)
    val modulus = IdealInt(2) pow width
    def toSMTLIBString = "(_ BitVec " + width + ")"
  }

  case class SMTFF(card : IdealInt)                extends SMTType {
    def toSort = ModuloArithmetic.ModSort(IdealInt.ZERO, card - 1)
    def toSMTLIBString = "(_ FiniteField " + card + ")"
  }

  object SMTADT {
    val POLY_PREFIX = "$poly:"
  }

  case class SMTADT(adt : ADT, sortNum : Int)      extends SMTType {
    def toSort = adt sorts sortNum
    override def toString = (adt sorts sortNum).name
    def toSMTLIBString = {
      val str = this.toString
      if (str startsWith SMTADT.POLY_PREFIX)
        // TODO: this won't correctly add quotes
        str substring SMTADT.POLY_PREFIX.size
      else
        SMTLineariser.quoteIdentifier(str)
    }
  }

  case class SMTHeap(heap : Heap) extends SMTType {
    def toSort = heap.HeapSort
    override def toString = heap.HeapSort.name
    def toSMTLIBString = heap.HeapSort.name
  }

  case class SMTHeapAddress(heap : Heap) extends SMTType {
    def toSort = heap.AddressSort
    override def toString = heap.AddressSort.name
    def toSMTLIBString = heap.AddressSort.name
  }

  case class SMTUnint(sort : Sort)                extends SMTType {
    def toSort = sort
    override def toString = sort.name
    def toSMTLIBString = sort.name
  }

  case class SMTString(sort : Sort)               extends SMTType {
    def toSort = sort
    override def toString = "String"
    def toSMTLIBString = "String"
  }

  case class SMTChar(sort : Sort)                 extends SMTType {
    def toSort = sort
    override def toString = "Char"
    def toSMTLIBString = "Char"
  }

  case class SMTRegLan(sort : Sort)               extends SMTType {
    def toSort = sort
    override def toString = "RegLan"
    def toSMTLIBString = "RegLan"
  }

  case class SMTSeq(theory : SeqTheory,
                    elementType : SMTType)         extends SMTType {
    def toSort = theory.sort
    override def toString = theory.toString
    def toSMTLIBString = DialogUtil asString {
      print("(Seq ")
      print(elementType.toSMTLIBString)
      print(")")
    }
  }

  def sort2SMTType(sort : Sort) : (SMTType,
                                   Option[ITerm => IFormula]) = sort match {
    case Sort.Integer =>
      (SMTInteger, None)
    case Sort.Nat =>
      (SMTInteger, Some(_ >= 0))
    case sort : Sort.Interval =>
      (SMTInteger, Some(sort.membershipConstraint _))
    case Sort.Bool | Sort.MultipleValueBool =>
      (SMTBool, None)
    case sort if (StringTheory lookupStringSort sort).isDefined =>
      (SMTString(sort), None)
    case sort if (SeqTheory lookupSeqSort sort).isDefined => {
      val Some(theory) = SeqTheory lookupSeqSort sort
      (SMTSeq(theory, sort2SMTType(theory.ElementSort)._1), None)
    }
    case sort : ADT.ADTProxySort =>
      (SMTADT(sort.adtTheory, sort.sortNum), None)
    case ModuloArithmetic.UnsignedBVSort(width) =>
      (SMTBitVec(width), None)
    case ModuloArithmetic.ModSort(IdealInt.ZERO, card) =>
      (SMTFF(card + 1), None)
    case SimpleArray.ArraySort(arity) =>
      (SMTArray((for (_ <- 0 until arity) yield SMTInteger).toList, SMTInteger),
       None)
    case ExtArray.ArraySort(theory) =>
      (SMTArray((for (s <- theory.indexSorts) yield sort2SMTType(s)._1).toList,
                sort2SMTType(theory.objSort)._1),
       None)
    case Rationals.FractionSort =>
      (SMTReal(sort), None)
    case sort : UninterpretedSortTheory.UninterpretedSort =>
      (SMTUnint(sort), None)
    case sort : UninterpretedSortTheory.InfUninterpretedSort =>
      (SMTUnint(sort), None)
    case sort : Heap.HeapSort =>
      (SMTHeap(sort.heapTheory), None)
    case sort : Heap.AddressSort =>
      (SMTHeapAddress(sort.heapTheory), None)
    case Sort.AnySort =>
      (SMTInteger, None)

    case s => {
      // check whether the theory can resolve this sort
      val typ =
        (TheoryRegistry lookupSort s) match {
          case Some(t : SMTLinearisableTheory) => t.sort2SMTType(s)
          case _                               => None
        }
      typ match {
        case Some(t) => (t, None)
        case None =>
          throw new Exception (
            "do not know how to translate " + s + " to an SMT-LIB type")
      }
    }
  }

}

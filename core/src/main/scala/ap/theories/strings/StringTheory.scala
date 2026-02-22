/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018-2025 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.strings

import ap.basetypes.IdealInt
import ap.algebra.Monoid
import ap.parser.{IFunction, ITerm, IFunApp, IIntLit, IExpression}
import ap.parser.IExpression.Predicate
import ap.theories.{Theory, ModuloArithmetic}
import ap.types.Sort
import ap.terfor.conjunctions.Conjunction


import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 ArrayBuffer}

object StringTheory {

  private val representationFunctions = new MHashMap[IFunction, StringTheory]

  private val stringSorts = new MHashMap[Sort, StringTheory]

  def lookupRepresentationFunction(f : IFunction) : Option[StringTheory] =
    synchronized { representationFunctions get f }

  def lookupStringSort(s : Sort) : Option[StringTheory] =
    synchronized { stringSorts get s }

  def register(t : StringTheory) : Unit = synchronized {
    representationFunctions.put(t.str_empty, t)
    representationFunctions.put(t.str_cons,  t)
    representationFunctions.put(t.str_head,  t)
    representationFunctions.put(t.str_tail,  t)
    stringSorts.put(t.StringSort, t)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Extractor to recognise the string <code>str.empty</code> function.
   */
  object StrEmpty {
    def unapply(f : IFunction) : Option[StringTheory] =
      for (t <- lookupRepresentationFunction(f); if f == t.str_empty) yield t
  }

  /**
   * Extractor to recognise the string <code>str.cons</code> function.
   */
  object StrCons {
    def unapply(f : IFunction) : Option[StringTheory] =
      for (t <- lookupRepresentationFunction(f); if f == t.str_cons) yield t
  }

  /**
   * Translate a concrete string in term representation to a list of integers.
   */
  def term2List(t : ITerm) : List[Int] = t match {
    case IFunApp(StrEmpty(_), Seq()) =>
      List()
    case IFunApp(StrCons(_), Seq(IIntLit(value), tail)) =>
      value.intValueSafe :: term2List(tail)
    case IFunApp(StrCons(_), Seq(IFunApp(ModuloArithmetic.mod_cast,
                                         Seq(IIntLit(lower), IIntLit(upper),
                                             IIntLit(value))),
                                 tail))
      if lower <= value && value <= upper =>
      value.intValueSafe :: term2List(tail)
    case _ =>
      throw NotAStringException
  }

  private object NotAStringException
          extends IllegalArgumentException("not a string")

  /**
   * Translate a concrete string in term representation to a string.
   */
  def term2String(t : ITerm) : String =
    (for (c <- term2List(t)) yield c.toChar).mkString

  /**
   * Extractor to recognise terms that represent concrete strings.
   */
  object ConcreteString {
    def unapply(t : ITerm) : Option[String] =
      try {
        Some(term2String(t))
      } catch {
        case NotAStringException => None
      }
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Generic class describing string theories.
 */
trait StringTheory extends Theory {

  val alphabetSize   : Int

  /**
   * Sort representing characters
   */
  val CharSort       : Sort

  /**
   * Sort representing strings
   */
  val StringSort     : Sort

  /**
   * Sort representing regular expressions
   */
  val RegexSort      : Sort

  /**
   * Convert an integer term to a character term
   */
  def int2Char(t : ITerm) : ITerm

  /**
   * Convert an integer term to a singleton string
   */
  def int2String(t : ITerm) : ITerm = {
    import IExpression._
    str_cons(int2Char(t), str_empty())
  }

  /**
   * Convert a character term to an integer term
   */
  def char2Int(t : ITerm) : ITerm

  // Character functions

  val char_is_digit  : Predicate    // CharSort -> Boolean

  // Representation functions

  val str_empty      : IFunction    // -> StringSort
  val str_cons       : IFunction    // CharSort x StringSort -> StringSort

  val str_head       : IFunction    // StringSort -> CharSort
  val str_head_code  : IFunction    // StringSort -> Nat
  val str_tail       : IFunction    // StringSort -> StringSort

  // SMT-LIB String functions

  val str_from_char  : IFunction    // CharSort -> StringSort

  val str_from_code  : IFunction    // Int -> StringSort
  val str_to_code    : IFunction    // StringSort -> Int

  val str_++         : IFunction    // StringSort x StringSort -> StringSort

  val str_len        : IFunction    // StringSort -> Nat

  // Conversion between strings and numbers in decimal notation
  val str_to_int     : IFunction    // StringSort -> Int
  val int_to_str     : IFunction    // Int -> StringSort

  val str_is_digit   : Predicate    // StringSort -> Boolean

  val str_<=         : Predicate    // StringSort x StringSort -> Boolean
  val str_<          : Predicate    // StringSort x StringSort -> Boolean
  val str_at         : IFunction    // StringSort x Nat -> StringSort
  val str_char       : IFunction    // StringSort x Nat -> CharSort

  val str_substr     : IFunction    // StringSort x Nat x Nat -> StringSort
  val str_prefixof   : Predicate    // StringSort x StringSort -> Boolean
  val str_suffixof   : Predicate    // StringSort x StringSort -> Boolean
  
  val str_contains   : Predicate    // StringSort x StringSort -> Boolean
  val str_indexof    : IFunction    // StringSort x StringSort x Int -> Int
  
  val str_replace    : IFunction    // StringSort x StringSort x StringSort
                                    //  -> StringSort
  val str_replacere  : IFunction    // StringSort x RegexSort x StringSort
                                    //  -> StringSort
  val str_replaceall : IFunction    // StringSort x StringSort x StringSort
                                    //  -> StringSort
  val str_replaceallre : IFunction  // StringSort x RegexSort x StringSort
                                    //  -> StringSort

  // Regex functions

  val str_in_re      : Predicate    // StringSort x RegexSort -> Boolean

  val str_to_re      : IFunction    // StringSort -> RegexSort

  val re_from_str    : IFunction    // StringSort -> RegexSort

  val re_none        : IFunction    // -> RegexSort
  val re_eps         : IFunction    // -> RegexSort
  val re_all         : IFunction    // -> RegexSort
  val re_allchar     : IFunction    // -> RegexSort

  val re_charrange   : IFunction    // CharSort x CharSort -> RegexSort
  val re_range       : IFunction    // StringSort x StringSort -> RegexSort

  val re_++          : IFunction    // RegexSort x RegexSort -> RegexSort
  val re_union       : IFunction    // RegexSort x RegexSort -> RegexSort
  val re_inter       : IFunction    // RegexSort x RegexSort -> RegexSort
  val re_diff        : IFunction    // RegexSort x RegexSort -> RegexSort

  val re_*           : IFunction    // RegexSort -> RegexSort
  val re_+           : IFunction    // RegexSort -> RegexSort
  val re_opt         : IFunction    // RegexSort -> RegexSort
  val re_comp        : IFunction    // RegexSort -> RegexSort

  val re_loop        : IFunction    // Int x Int x RegexSort -> RegexSort

  // Further functions or predicates that a string theory might define

  val extraOps        : Map[String, Either[IFunction, Predicate]]

  // Further indexed functions
  val extraIndexedOps : Map[(String, Int), Either[IFunction, Predicate]]

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Helper class providing string infix operators
   */
  class RichWord(t : ITerm) {
    /**
     * Concatenate two words
     */
    def ++(that : ITerm) : ITerm =
      IFunApp(str_++, List(t, that))
  }

  /**
   * Convert a term to a rich term, providing some infix operators
   */
  implicit def term2RichWord(t : ITerm) : RichWord = new RichWord(t)

  /**
   * Convert a string to a term
   */
  implicit def string2Term(str : String) : ITerm =
    (str :\ IFunApp(str_empty, List())) {
      case (c, s) => IFunApp(str_cons, List(int2Char(c), s))
    }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * The predicate corresponding to <code>str_empty</code>
   */
  val _str_empty : Predicate

  /**
   * The predicate corresponding to <code>str_cons</code>
   */
  val _str_cons : Predicate

  /**
   * The predicate corresponding to <code>str_++</code>
   */
  val _str_++ : Predicate

  /**
   * Translate a numeric value from a model to a string.
   */
  val asString : Theory.Decoder[String]

  /**
   * Translate a numeric value from a model to a string.
   */
  val asStringPartial : Theory.Decoder[Option[String]]

}

/**
 * Every string theory gives rise to a monoid.
 */
case class StringMonoid(stringTheory : StringTheory) extends Monoid {

  val dom =
    stringTheory.StringSort

  def op(s : ITerm, t : ITerm) : ITerm =
    IFunApp(stringTheory.str_++, List(s, t))
  
  def identity : ITerm =
    IFunApp(stringTheory.str_empty, List())

}

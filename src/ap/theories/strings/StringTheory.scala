/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.strings

import ap.parser.{IFunction, ITerm}
import ap.parser.IExpression.Predicate
import ap.theories.Theory
import ap.types.{Sort, MonoSortedPredicate, MonoSortedIFunction}

object StringTheory {

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Generic class describing string theories.
 */
trait StringTheory extends Theory {

  val bitWidth       : Int

  val CharSort       : Sort
  val StringSort     : Sort
  val RegexSort      : Sort

  def int2Char(t : ITerm) : ITerm
  def char2Int(t : ITerm) : ITerm

  // Character functions

  val char_is_digit  : Predicate    // CharSort -> Boolean

  // Representation functions

  val str_empty      : IFunction    // -> StringSort
  val str_cons       : IFunction    // CharSort x StringSort -> StringSort

  val str_head       : IFunction    // StringSort -> CharSort
  val str_tail       : IFunction    // StringSort -> StringSort

  // SMT-LIB String functions

  val str            : IFunction    // CharSort -> StringSort

  val str_++         : IFunction    // StringSort x StringSort -> StringSort

  val str_len        : IFunction    // StringSort -> Nat

  val str_<=         : Predicate    // StringSort x StringSort -> Boolean
  val str_at         : IFunction    // StringSort x Nat -> StringSort
  val str_char       : IFunction    // StringSort x Nat -> CharSort

  val str_substr     : IFunction    // StringSort x Nat x Nat -> StringSort
  val str_prefixof   : Predicate    // StringSort x StringSort -> Boolean
  val str_suffixof   : Predicate    // StringSort x StringSort -> Boolean
  
  val str_contains   : Predicate    // StringSort x StringSort -> Boolean
  val str_indexof    : IFunction    // StringSort x StringSort x Int -> Int
  
  val str_replace    : IFunction    // StringSort x StringSort x StringSort
                                    //  -> StringSort
  val str_replaceall : IFunction    // StringSort x StringSort x StringSort
                                    //  -> StringSort
  val str_replaceallre : IFunction  // StringSort x RegexSort x StringSort
                                    //  -> StringSort

  // Regex functions

  val str_in_re      : Predicate    // StringSort x RegexSort -> Boolean

  val str_to_re      : IFunction    // StringSort -> RegexSort

  val re_none        : IFunction    // -> RegexSort
  val re_all         : IFunction    // -> RegexSort
  val re_allchar     : IFunction    // -> RegexSort

  // val re_range       : IFunction    // ???

  // re_^, re_loop

  val re_++          : IFunction    // RegexSort x RegexSort -> RegexSort
  val re_union       : IFunction    // RegexSort x RegexSort -> RegexSort
  val re_inter       : IFunction    // RegexSort x RegexSort -> RegexSort
  
  val re_*           : IFunction    // RegexSort -> RegexSort
  val re_+           : IFunction    // RegexSort -> RegexSort
  val re_opt         : IFunction    // RegexSort -> RegexSort

  // Transducer pool

  val transducers : Map[String, Predicate]

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Abstract class defining relevant string operations as sorted
 * functions/predicates
 */
abstract class AbstractStringTheory extends StringTheory {

  private val CSo = CharSort
  private val SSo = StringSort
  private val RSo = RegexSort
  import Sort.{Nat, Integer}

  val char_is_digit =
    new MonoSortedPredicate("char_is_digit", List(CSo))

  val str =
    new MonoSortedIFunction("str", List(SSo), SSo, true, false)

  val str_++ =
    new MonoSortedIFunction("str_++", List(SSo, SSo), SSo, true, false)
  val str_len =
    new MonoSortedIFunction("str_len", List(SSo), Nat, true, false)

  val str_<= =
    new MonoSortedPredicate("char_<=", List(SSo, SSo))
  val str_at =
    new MonoSortedIFunction("str_at", List(SSo, Nat), SSo, true, false)
  val str_char =
    new MonoSortedIFunction("str_char", List(SSo, Nat), CSo, true, false)
    
  val str_substr =
    new MonoSortedIFunction("str_substr", List(SSo, Nat, Nat), SSo, true, false)
  val str_prefixof =
    new MonoSortedPredicate("str_prefixof", List(SSo, SSo))
  val str_suffixof =
    new MonoSortedPredicate("str_suffixof", List(SSo, SSo))

  val str_contains =
    new MonoSortedPredicate("str_contains", List(SSo, SSo))
  val str_indexof =
    new MonoSortedIFunction("str_indexof",
                            List(SSo, SSo, Integer), Integer, true, false)

  val str_replace =
    new MonoSortedIFunction("str_replace",
                            List(SSo, SSo, SSo), CSo, true, false)
  val str_replaceall =
    new MonoSortedIFunction("str_replaceall",
                            List(SSo, SSo, SSo), CSo, true, false)
  val str_replaceallre =
    new MonoSortedIFunction("str_replaceallre",
                            List(SSo, RSo, SSo), CSo, true, false)

  val str_in_re =
    new MonoSortedPredicate("str_in_re", List(SSo, RSo))

  val str_to_re =
    new MonoSortedIFunction("str_to_re", List(SSo), RSo, true, false)

  val re_none =
    new MonoSortedIFunction("re_none", List(), RSo, true, false)
  val re_all =
    new MonoSortedIFunction("re_all", List(), RSo, true, false)
  val re_allchar =
    new MonoSortedIFunction("re_allchar", List(), RSo, true, false)

  // re_range, re_^, re_loop

  val re_++ =
    new MonoSortedIFunction("re_++", List(RSo, RSo), RSo, true, false)
  val re_union =
    new MonoSortedIFunction("re_union", List(RSo, RSo), RSo, true, false)
  val re_inter =
    new MonoSortedIFunction("re_inter", List(RSo, RSo), RSo, true, false)

  val re_* =
    new MonoSortedIFunction("re_*", List(RSo), RSo, true, false)
  val re_+ =
    new MonoSortedIFunction("re_+", List(RSo), RSo, true, false)
  val re_opt =
    new MonoSortedIFunction("re_opt", List(RSo), RSo, true, false)

  protected val predefFunctions =
    List(str, str_++, str_len, str_at, str_char,
         str_substr, str_indexof,
         str_replace, str_replaceall, str_replaceallre,
         str_to_re, re_none, re_all, re_allchar, re_++,
         re_union, re_inter, re_*, re_+, re_opt)

  protected val predefPredicates =
    List(char_is_digit, str_<=, str_prefixof,
         str_suffixof, str_contains, str_in_re)

}
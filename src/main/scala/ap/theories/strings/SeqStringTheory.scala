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

import ap.Signature
import ap.basetypes.IdealInt
import ap.parser._
import ap.parser.IExpression.Predicate
import ap.theories.{Theory, ADT, ModuloArithmetic, TheoryRegistry,
                    Incompleteness}
import ap.types.{Sort, MonoSortedIFunction}
import ap.terfor.{TermOrder, TerForConvenience, Term, Formula,
                  ComputationLogger}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction,
                               ReducerPlugin, ReducerPluginFactory}
import ap.terfor.preds.{PredConj, Atom}
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.substitutions.VariableShiftSubst
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal
import ap.util.Seqs

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 Stack, ArrayBuffer}

object SeqStringTheory {

  private val instances = new MHashMap[Int, SeqStringTheory]

  def apply(alphabetSize : Int) : SeqStringTheory = synchronized {
    instances.getOrElseUpdate(alphabetSize, new SeqStringTheory(alphabetSize))
  }

}

/**
 * String theory implemented using a list ADT.
 */
class SeqStringTheory private (val alphabetSize : Int) extends {

  val upperBound = IdealInt(alphabetSize - 1)
  val CharSort = ModuloArithmetic.ModSort(IdealInt.ZERO, upperBound)
  val RegexSort = Sort.createInfUninterpretedSort("RegLan")

  val seqADT =
    new ADT (List("String"),
             List(("str_empty", ADT.CtorSignature(List(), ADT.ADTSort(0))),
                  ("str_cons",  ADT.CtorSignature(
                                  List(("str_head", ADT.OtherSort(CharSort)),
                                       ("str_tail", ADT.ADTSort(0))),
                                ADT.ADTSort(0)))),
             measure = ADT.TermMeasure.Size)

  val StringSort = seqADT.sorts.head

} with AbstractStringTheory {

  val Seq(str_empty, str_cons)        = seqADT.constructors
  val Seq(_, Seq(str_head, str_tail)) = seqADT.selectors

  private val adtSize                 = seqADT.termSize.head
  private val _adtSize                = seqADT.termSizePreds.head
  
  def int2Char(t : ITerm) : ITerm =
    ModuloArithmetic.cast2Interval(IdealInt.ZERO, upperBound, t)

  def char2Int(t : ITerm) : ITerm = t

  val extraOps : Map[String, Either[IFunction, Predicate]] = Map()
  val extraIndexedOps : Map[(String, Int), Either[IFunction, Predicate]] = Map()

  private def isEmptyString(t : ITerm) : IFormula = seqADT.hasCtor(t, 0)

  private val CSo = CharSort
  private val SSo = StringSort
  private val RSo = RegexSort
  import Sort.{Nat, Integer}

  // str_to_int_help(a, b) = a * 10^b.len + b.toInt
  val str_to_int_help =
    new MonoSortedIFunction("str_to_int_help", List(Integer, SSo),
                            Integer, true, false)

  val int_to_str_help =
    new MonoSortedIFunction("int_to_str_help", List(Integer, SSo),
                            SSo, true, false)

  // str_indexof_help(s, t, i, k)
  //    = str_indexof(s, t, i) + k if str_indexof(...) >= 0
  //    = -1                       otherwise
  val str_indexof_help =
    new MonoSortedIFunction("str_indexof_help",
                            List(SSo, SSo, Integer, Integer),
                            Integer, true, false)

  // Determine whether a regular expression matches a string
  val re_matches_str_help =
    new MonoSortedIFunction("re_matches_str_help",
                            List(RSo, SSo), Sort.Bool, true, false)

  // Map a regular expression to re.eps if it accepts the empty string,
  // to re.none otherwise
  val re_nullable_help =
    new MonoSortedIFunction("re_nullable_help",
                            List(RSo), RSo, true, false)

  // Compute the Brzozowski derivative of a regular expression
  val re_derivative_help =
    new MonoSortedIFunction("re_derivative_help",
                            List(CSo, RSo), RSo, true, false)

  //////////////////////////////////////////////////////////////////////////////

  // Version of the axioms with non-strict triggers

  val strAtAxioms = {
    import IExpression._

    StringSort.all(str => all(n =>
      ITrigger(List(str_at(str, n)),
               ite(n >= 0 & n < adtSize(str) - 1,
                   StringSort.ex(str1 => CharSort.ex(c =>
                                   (str === str_cons(c, str1)) &
                                   str_at(str, n) ===
                                     ite(n === 0,
                                         str_cons(c, ""),
                                         str_at(str1, n - 1))
                                 )),
                   str_at(str, n) === ""))))
  }

  val strSubstrAxioms = {
    import IExpression._

    StringSort.all(str => all((start, len) =>
      ITrigger(List(str_substr(str, start, len)),
               ite(start >= 0 & len > 0 & start < adtSize(str) - 1,
                   ite(start === 0 & len >= adtSize(str) - 1,
                       str_substr(str, start, len) === str,
                       StringSort.ex(str1 => CharSort.ex(c =>
                                       (str === str_cons(c, str1)) &
                                       str_substr(str, start, len) ===
                                         ite(start > 0,
                                             str_substr(str1, start - 1, len),
                                             str_cons(
                                               c,str_substr(str1, 0, len - 1))
                                             )))),
                   str_substr(str, start, len) === ""))))
  }

  val strToIntAxioms = {
    import IExpression._

    StringSort.all(str => all(n =>
      ITrigger(List(str_to_int_help(n, str)),
               ite(isEmptyString(str),
                   str_to_int_help(n, str) === n,
                   StringSort.ex(str1 => CharSort.ex(c =>
                                   (str === str_cons(c, str1)) &
                                   (str_to_int_help(n, str) === 
                                    ite(c >= 48 & c <= 57,
                                        str_to_int_help(n*10 + c - 48, str1),
                                        -1))
                                 )))))) &
    StringSort.all(str => all(n =>
      ITrigger(List(str_to_int_help(n, str)),
               (str_to_int_help(n, str) === -1) |
               (str_to_int_help(n, str) >= n))))
  }

  val intToStrAxioms = {
    import IExpression._

    all(n => StringSort.all(tail =>
      trig(ite(n <= -1,
               int_to_str_help(n, tail) === "",
               ite(n <= 9,
                   int_to_str_help(n, tail) === str_cons(n + 48, tail),
                   ex((n1, n2) => (n === 10*n1 + n2) &
                                  (n2 >= 0) & (n2 <= 9) &
                                  (int_to_str_help(n, tail) === 
                                   int_to_str_help(n1, str_cons(n2 + 48, tail)))
                   ))),
           int_to_str_help(n, tail)))) &
    all(n => StringSort.all(tail =>
      trig(adtSize(int_to_str_help(n, tail)) >= adtSize(tail),
           int_to_str_help(n, tail))))
  }

  val strIndexofAxioms = {
    import IExpression._

    StringSort.all((str, searchStr) => all((start, offset) =>
      ITrigger(List(str_indexof_help(str, searchStr, start, offset)),
               ite((start <= 0) &
                     (searchStr === str_substr(str, 0, adtSize(searchStr) - 1)),
                   str_indexof_help(str, searchStr, start, offset) === offset,
                   StringSort.ex(str1 => CharSort.ex(c =>
                     (str === str_cons(c, str1)) &
                     str_indexof_help(str, searchStr, start, offset) ===
                       str_indexof_help(str1, searchStr, start - 1, offset + 1)
                                 )) |
                   ((str === str_empty()) &
                    (str_indexof_help(str, searchStr, start, offset) === -1))
               ))))
  }

/*
  val strReplaceAxioms = {
    import IExpression._

    StringSort.all((str, searchStr, replStr) =>
      ITrigger(List(str_replace(str, searchStr, replStr)),
                 ite(searchStr === str_substr(str, 0, adtSize(searchStr) - 1),
                     str_replace(str, searchStr, replStr) ===
                       str_++(replStr,
                              str_substr(str,
                                         adtSize(searchStr) - 1, adtSize(str))),
                     ite(isEmptyString(str),
                         str_replace(str, searchStr, replStr) === "",
                         StringSort.ex(str1 => CharSort.ex(c =>
                           (str === str_cons(c, str1)) &
                             (str_replace(str, searchStr, replStr) ===
                              str_cons(c, str_replace(str1, searchStr, replStr))
                             )))))))
  }
 */

  val strReplaceAxioms = {
    import IExpression._

    StringSort.all((str, searchStr, replStr) =>
      ITrigger(List(str_replace(str, searchStr, replStr)),
               ite(adtSize(searchStr) > adtSize(str),
                   str_replace(str, searchStr, replStr) === str,
                   ite(searchStr === str_substr(str, 0, adtSize(searchStr) - 1),
                       str_replace(str, searchStr, replStr) ===
                       str_++(replStr,
                              str_substr(str,
                                         adtSize(searchStr) - 1, adtSize(str))),
                       StringSort.ex(str1 => CharSort.ex(c =>
                         (str === str_cons(c, str1)) &
                           (str_replace(str, searchStr, replStr) ===
                              str_cons(c, str_replace(str1, searchStr, replStr))
                           )))))))
  }


  // Version of the axioms with strict triggers

/*
  val strConcatAxioms = {
    import IExpression._

    StringSort.all(str =>
      ITrigger(List(str_++(str_empty(), str)),
               str_++(str_empty(), str) === str)) &
    StringSort.all((str1, str2) => CharSort.all(c =>
      ITrigger(List(str_++(str_cons(c, str1), str2)),
               str_++(str_cons(c, str1), str2) ===
                  str_cons(c, str_++(str1, str2))
      )))
  }

  val strAtAxioms = {
    import IExpression._

    StringSort.all(str1 => CharSort.all(c => all(n =>
      ITrigger(List(str_at(str_cons(c, str1), n)),
               str_at(str_cons(c, str1), n) ===
                 ite(n >= 0 & n < adtSize(str1),
                     ite(n === 0, str_cons(c, ""), str_at(str1, n - 1)),
                     ""))))) &
    StringSort.all(str => all(n =>
      ITrigger(List(str_at(str_empty(), n)),
               str_at(str_empty(), n) === "")))
  }

  val strSubstrAxioms = {
    import IExpression._

    StringSort.all(str => all((start, len) =>
      ITrigger(List(str_substr(str_empty(), start, len)),
               str_substr(str_empty(), start, len) === ""))) &
    StringSort.all(str1 => CharSort.all(c => all((start, len) =>
      ITrigger(List(str_substr(str_cons(c, str1), start, len)),
               str_substr(str_cons(c, str1), start, len) ===
                 ite(start >= 0 & len > 0 & start < adtSize(str1),
                     ite(start === 0 & len >= adtSize(str1),
                         str_cons(c, str1),
                         ite(start > 0,
                             str_substr(str1, start - 1, len),
                             str_cons(c, str_substr(str1, 0, len - 1))
                         )),
                     "")))))
  }

  val strToIntAxioms = {
    import IExpression._

    all(n =>
      ITrigger(List(str_to_int_help(n, str_empty())),
               str_to_int_help(n, str_empty()) === n)) &
    StringSort.all(str1 => CharSort.all(c => all(n =>
      ITrigger(List(str_to_int_help(n, str_cons(c, str1))),
               str_to_int_help(n, str_cons(c, str1)) ===
                  ite(c >= 48 & c <= 57,
                      str_to_int_help(n*10 + c - 48, str1),
                      -1))))) &
    StringSort.all(str => all(n =>
      ITrigger(List(str_to_int_help(n, str)),
               (str_to_int_help(n, str) === -1) |
               (str_to_int_help(n, str) >= n))))
  }

  val strIndexofAxioms = {
    import IExpression._

    StringSort.all(searchStr => all((start, offset) =>
      ITrigger(List(str_indexof_help(str_empty(), searchStr, start, offset)),
               str_indexof_help(str_empty(), searchStr, start, offset) === 
                 ite((start <= 0) & (searchStr === str_empty()), offset, -1)
               ))) &
    StringSort.all((str1, searchStr) => CharSort.all(c => all((start, offset) =>
      ITrigger(List(str_indexof_help(str_cons(c, str1),
                                     searchStr, start, offset)),
               str_indexof_help(str_cons(c, str1),
                                searchStr, start, offset) ===
                 ite((start + adtSize(searchStr) <= adtSize(str1) + 1) &
                     (adtSize(searchStr) <= adtSize(str1) + 1),
                     ite((start <= 0) &
                           (searchStr ===
                              str_substr(str_cons(c, str1),
                                         0, adtSize(searchStr) - 1)),
                         offset,
                         str_indexof_help(str1, searchStr, start - 1, offset +1)
                     ),
                     -1)))))
  }
 */

  private class RichTerm(t : ITerm) {
    def ~~>(s : ITerm) = IExpression.trig(t === s, t)
  }

  private implicit def toRichTerm(t : ITerm) : RichTerm = new RichTerm(t)

  val reMatchingAxioms = {
    import IExpression._

    CharSort.all(c => StringSort.all(str => RegexSort.all(re =>
      re_matches_str_help(re, str_cons(c, str)) ~~>
        re_matches_str_help(re_derivative_help(c, re), str)
    ))) &
//
    StringSort.all(str =>
      re_matches_str_help(re_none(), str) ~~>
        1
    ) &
    StringSort.all(str =>
      re_matches_str_help(re_all(), str) ~~>
        0
    ) &
//
    StringSort.all(str =>                               // str.to_re
      re_matches_str_help(str_to_re(str), str_empty()) ~~>
        ite(isEmptyString(str), 0, 1)
    ) &
    CharSort.all((c1, c2) =>                            // re.charrange
      re_matches_str_help(re_charrange(c1, c2), str_empty()) ~~>
        1
    ) &
    RegexSort.all((re1, re2) =>                         // re.++
      re_matches_str_help(re_++(re1, re2), str_empty()) ~~>
        ADT.BoolADT.And(re_matches_str_help(re1, str_empty()),
                        re_matches_str_help(re2, str_empty()))
    ) &
    RegexSort.all((re1, re2) =>                         // re.union
      re_matches_str_help(re_union(re1, re2), str_empty()) ~~>
        ADT.BoolADT.Or(re_matches_str_help(re1, str_empty()),
                       re_matches_str_help(re2, str_empty()))
    ) &
    RegexSort.all((re1, re2) =>                         // re.inter
      re_matches_str_help(re_inter(re1, re2), str_empty()) ~~>
        ADT.BoolADT.And(re_matches_str_help(re1, str_empty()),
                        re_matches_str_help(re2, str_empty()))
    ) &
    RegexSort.all((re1, re2) =>                         // re.diff
      re_matches_str_help(re_diff(re1, re2), str_empty()) ~~>
        ADT.BoolADT.And(
          re_matches_str_help(re1, str_empty()),
          ADT.BoolADT.Not(re_matches_str_help(re2, str_empty())))
    ) &
    RegexSort.all(re =>                                 // re.*
      re_matches_str_help(re_*(re), str_empty()) ~~>
        0
    ) &
    RegexSort.all(re =>                                 // re.+
      re_matches_str_help(re_+(re), str_empty()) ~~>
        re_matches_str_help(re, str_empty())
    ) &
    RegexSort.all(re =>                                 // re.opt
      re_matches_str_help(re_opt(re), str_empty()) ~~>
        0
    ) &
    RegexSort.all(re =>                                 // re.comp
      re_matches_str_help(re_comp(re), str_empty()) ~~>
        ADT.BoolADT.Not(re_matches_str_help(re, str_empty()))
    )
  }

  val reSimpAxioms = {
    import IExpression._

    RegexSort.all(re =>
      re_++(re_none(), re) ~~> re_none()
    ) &
    RegexSort.all(re =>
      re_++(re, re_none()) ~~> re_none()
    ) &
    RegexSort.all(re =>
      re_union(re_none(), re) ~~> re
    ) &
    RegexSort.all(re =>
      re_union(re, re_none()) ~~> re
    ) &
    RegexSort.all(re =>
      re_inter(re_none(), re) ~~> re_none()
    ) &
    RegexSort.all(re =>
      re_inter(re, re_none()) ~~> re_none()
    ) &
//
    RegexSort.all(re =>
      re_union(re_all(), re) ~~> re_all()
    ) &
    RegexSort.all(re =>
      re_union(re, re_all()) ~~> re_all()
    ) &
    RegexSort.all(re =>
      re_inter(re_all(), re) ~~> re
    ) &
    RegexSort.all(re =>
      re_inter(re, re_all()) ~~> re
    ) &
//
    RegexSort.all(re =>
      re_++(re_eps(), re) ~~> re
    ) &
    RegexSort.all(re =>
      re_++(re, re_eps()) ~~> re
    ) &
    RegexSort.all(re =>
      re_++(str_to_re(str_empty()), re) ~~> re
    ) &
    RegexSort.all(re =>
      re_++(re, str_to_re(str_empty())) ~~> re
    )
  }

  val reNullableAxioms = {
    import IExpression._

    CharSort.all(c => StringSort.all(str =>        // str.to_re
      re_nullable_help(str_to_re(str_cons(c, str))) ~~>
        re_none())) &
    CharSort.all((c1, c2) =>                       // re.charrange
      re_nullable_help(re_charrange(c1, c2)) ~~>
        re_none()) &
    RegexSort.all((re1, re2) =>                    // re.++
      re_nullable_help(re_++(re1, re2)) ~~>
        re_inter(re_nullable_help(re1), re2)) &
    RegexSort.all((re1, re2) =>                    // re.union
      re_nullable_help(re_union(re1, re2)) ~~>
        re_union(re_nullable_help(re1), re_nullable_help(re2))) &
    RegexSort.all((re1, re2) =>                    // re.inter
      re_nullable_help(re_inter(re1, re2)) ~~>
        re_inter(re_nullable_help(re1), re2)) &
    RegexSort.all((re1, re2) =>                    // re.diff
      re_nullable_help(re_diff(re1, re2)) ~~>
        re_diff(re_nullable_help(re1), re2)) &
    RegexSort.all(re =>                            // re.*
      re_nullable_help(re_*(re)) ~~>
        re_eps()) &
    RegexSort.all(re =>                            // re.+
      re_nullable_help(re_+(re)) ~~>
        re_nullable_help(re)) &
    RegexSort.all(re =>                            // re.opt
      re_nullable_help(re_opt(re)) ~~>
        re_eps()) &
    RegexSort.all(re =>                            // re.comp
      re_nullable_help(re_comp(re)) ~~>
        re_diff(re_eps(), re))
  }

  val reDerivativeAxioms = {
    import IExpression._

    CharSort.all(c =>                              // re.none
      re_derivative_help(c, re_none()) ~~>
        re_none()) &
    CharSort.all(c =>                              // re.eps
      re_derivative_help(c, re_eps()) ~~>
        re_none()) &
    CharSort.all(c =>                              // re.all
      re_derivative_help(c, re_all()) ~~>
        re_all()) &
    CharSort.all(c =>                              // re.allchar
      re_derivative_help(c, re_allchar()) ~~>
        re_eps()) &
    CharSort.all(c =>                              // str.to_re ""
      re_derivative_help(c, str_to_re(str_empty())) ~~>
        re_none()) &
    CharSort.all((c1, c2) => StringSort.all(str => // str.to_re
      re_derivative_help(c1, str_to_re(str_cons(c2, str))) ~~>
        ite(c1 === c2, str_to_re(str), re_none()))) &
    CharSort.all((c, c1, c2) =>                    // re.charrange
      re_derivative_help(c, re_charrange(c1, c2)) ~~>
        ite(c1 <= c & c <= c2, re_eps(), re_none())) &
    CharSort.all(c => RegexSort.all((re1, re2) =>  // re.++
      re_derivative_help(c, re_++(re1, re2)) ~~>
        re_union(re_++(re_derivative_help(c, re1), re2),
                 re_++(re_nullable_help(re1), re_derivative_help(c, re2))))) &
    CharSort.all(c => RegexSort.all((re1, re2) =>  // re.union
      re_derivative_help(c, re_union(re1, re2)) ~~>
        re_union(re_derivative_help(c, re1), re_derivative_help(c, re2)))) &
    CharSort.all(c => RegexSort.all((re1, re2) =>  // re.inter
      re_derivative_help(c, re_inter(re1, re2)) ~~>
        re_inter(re_derivative_help(c, re1), re_derivative_help(c, re2)))) &
    CharSort.all(c => RegexSort.all((re1, re2) =>  // re.diff
      re_derivative_help(c, re_diff(re1, re2)) ~~>
        re_diff(re_derivative_help(c, re1), re_derivative_help(c, re2)))) &
    CharSort.all(c => RegexSort.all(re =>          // re.*
      re_derivative_help(c, re_*(re)) ~~>
        re_++(re_derivative_help(c, re), re_*(re)))) &
    CharSort.all(c => RegexSort.all(re =>          // re.+
      re_derivative_help(c, re_+(re)) ~~>
        re_++(re_derivative_help(c, re), re_*(re)))) &
    CharSort.all(c => RegexSort.all(re =>          // re.opt
      re_derivative_help(c, re_opt(re)) ~~>
        re_derivative_help(c, re))) &
    CharSort.all(c => RegexSort.all(re =>          // re.comp
      re_derivative_help(c, re_comp(re)) ~~>
        re_comp(re_derivative_help(c, re))))
  }

  val allAxioms =
//    strConcatAxioms &
    strAtAxioms &
    strSubstrAxioms &
    strToIntAxioms &
    intToStrAxioms &
    strIndexofAxioms &
    strReplaceAxioms &
    reMatchingAxioms &
    reSimpAxioms &
    reNullableAxioms &
    reDerivativeAxioms

  //////////////////////////////////////////////////////////////////////////////

  val functions =
    predefFunctions ++ List(str_to_int_help, int_to_str_help, str_indexof_help,
                            re_matches_str_help,
                            re_nullable_help, re_derivative_help)
  
  val (funPredicates, axioms1, order, funPredMap) =
    Theory.genAxioms(theoryFunctions = functions,
                     theoryAxioms    = allAxioms,
                     otherTheories   = List(seqADT))
  val predicates = predefPredicates ++ funPredicates
  val functionPredicateMapping = functions zip funPredicates

//  private val funPredMap = functionPredicateMapping.toMap

  val reMatchingAxioms2 : Formula = {
    import TerForConvenience._
    implicit val o : TermOrder = order

    forall(forall(forall(                              // re.none
      (Atom(funPredMap(re_matches_str_help),
            List(l(v(0)), l(v(1)), l(v(2))), o) &
       Atom(funPredMap(re_none), List(l(v(0))), o) &
       Atom(funPredMap(str_empty), List(l(v(1))), o)) ==>
        (v(2) === 1)))) &
    forall(forall(forall(                              // re.none
      (Atom(funPredMap(re_matches_str_help),
            List(l(v(0)), l(v(1)), l(v(2))), o) &
       Atom(funPredMap(re_eps), List(l(v(0))), o) &
       Atom(funPredMap(str_empty), List(l(v(1))), o)) ==>
        (v(2) === 0)))) &
    forall(forall(forall(                              // re.all
      (Atom(funPredMap(re_matches_str_help),
            List(l(v(0)), l(v(1)), l(v(2))), o) &
       Atom(funPredMap(re_all), List(l(v(0))), o) &
       Atom(funPredMap(str_empty), List(l(v(1))), o)) ==>
        (v(2) === 0)))) &
    forall(forall(forall(                              // re.allchar
      (Atom(funPredMap(re_matches_str_help),
            List(l(v(0)), l(v(1)), l(v(2))), o) &
       Atom(funPredMap(re_allchar), List(l(v(0))), o) &
       Atom(funPredMap(str_empty), List(l(v(1))), o)) ==>
        (v(2) === 1))))
  }

  val reDerivativeAxioms2 : Formula = {
    import TerForConvenience._
    implicit val o : TermOrder = order

    forall(forall(                                     // re.none
      (Atom(funPredMap(re_nullable_help), List(l(v(0)), l(v(1))), o) &
       Atom(funPredMap(re_none), List(l(v(0))), o)) ==>
        (v(0) === v(1)))) &
    forall(forall(                                     // re.eps
      (Atom(funPredMap(re_nullable_help), List(l(v(0)), l(v(1))), o) &
       Atom(funPredMap(re_eps), List(l(v(0))), o)) ==>
        (v(0) === v(1)))) &
    forall(forall(forall(                              // str.to_re ""
      (Atom(funPredMap(re_nullable_help), List(l(v(0)), l(v(1))), o) &
       Atom(funPredMap(str_to_re), List(l(v(2)), l(v(0))), o) &
       Atom(funPredMap(str_empty), List(l(v(2))), o)) ==>
        (v(0) === v(1))))) &
    forall(forall(                                     // re.all
      (Atom(funPredMap(re_nullable_help), List(l(v(0)), l(v(1))), o) &
       Atom(funPredMap(re_all), List(l(v(0))), o)) ==>
        Atom(funPredMap(re_eps), List(l(v(1))), o))) &
    forall(forall(                                     // re.allchar
      (Atom(funPredMap(re_nullable_help), List(l(v(0)), l(v(1))), o) &
       Atom(funPredMap(re_allchar), List(l(v(0))), o)) ==>
        Atom(funPredMap(re_none), List(l(v(1))), o)))
  }

  val axioms = Conjunction.conj(List(axioms1,
                                     reMatchingAxioms2,
                                     reDerivativeAxioms2),
                                order)

  val functionalPredicates = funPredicates.toSet
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val totalityAxioms = Conjunction.TRUE
  val triggerRelevantFunctions : Set[IFunction] = Set()

  override val dependencies : Iterable[Theory] = List(seqADT, ModuloArithmetic)

  //////////////////////////////////////////////////////////////////////////////

  val _str_empty = seqADT.constructorPreds(0)
  val _str_cons  = seqADT.constructorPreds(1)
  val _str_++    = funPredMap(str_++)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Visitor called during pre-processing.
   */
  private object Preproc extends ContextAwareVisitor[Unit, IExpression] {
    import IExpression._

    def postVisit(t : IExpression,
                  ctxt : Context[Unit],
                  subres : Seq[IExpression]) : IExpression = t match {
      case IFunApp(`str_from_char`, _) =>
        str_cons(subres.head.asInstanceOf[ITerm], str_empty())
      case IFunApp(`str_len`, _) =>
        adtSize(subres.head.asInstanceOf[ITerm]) - 1
      case IFunApp(`str_head_code`, _) =>
        str_head(subres.head.asInstanceOf[ITerm])
      case IFunApp(`str_to_code`, _) =>
        subres.head match {
          case IFunApp(`str_cons`, Seq(c, IFunApp(`str_empty`, Seq()))) =>
            c
          case t : ITerm =>
            ite(adtSize(t) === 2, str_head(t), -1)
        }
      case IFunApp(`str_from_code`, _) => {
        val code = subres.head.asInstanceOf[ITerm]
        ite(code >= 0 & code <= upperBound,
            str_cons(code, str_empty()),
            str_empty())
      }
      case IAtom(`str_prefixof`, _) => {
        val fst = subres(0).asInstanceOf[ITerm]
        val snd = subres(1).asInstanceOf[ITerm]
        fst === str_substr(snd, 0, adtSize(fst) - 1)
      }
      case IAtom(`str_suffixof`, _) => {
        val fst = subres(0).asInstanceOf[ITerm]
        val snd = subres(1).asInstanceOf[ITerm]
        fst === str_substr(snd, adtSize(snd) - adtSize(fst), adtSize(fst) - 1)
      }
      case IAtom(`str_contains`, _) if ctxt.polarity < 0 => {
        StringSort.ex((a, b) =>
          subres(0).asInstanceOf[ITerm] ===
            str_++(str_++(a, subres(1).asInstanceOf[ITerm]), b))
      }
      case IAtom(`str_contains`, _) => {
        geqZero(str_indexof_help(subres(0).asInstanceOf[ITerm],
                                 subres(1).asInstanceOf[ITerm],
                                 0, 0))
      }
      case IFunApp(`str_to_int`, _) => {
        val fst = subres(0).asInstanceOf[ITerm]
        ite(isEmptyString(fst), -1, str_to_int_help(0, fst))
      }
      case IFunApp(`int_to_str`, _) => {
        int_to_str_help(subres(0).asInstanceOf[ITerm], str_empty())
      }
      case IFunApp(`str_indexof`, _) => {
        val start = subres(2).asInstanceOf[ITerm]
        ite(start < 0,
            -1,
            str_indexof_help(subres(0).asInstanceOf[ITerm],
                             subres(1).asInstanceOf[ITerm],
                             start,
                             0))
      }
      case IAtom(`str_in_re`, _) => {
        eqZero(re_matches_str_help(subres(1).asInstanceOf[ITerm],
                                   subres(0).asInstanceOf[ITerm]))
      }
      case IFunApp(`re_range`, _) =>
        subres match {
          case Seq(IFunApp(`str_cons`, Seq(lower, IFunApp(`str_empty`, _))),
                   IFunApp(`str_cons`, Seq(upper, IFunApp(`str_empty`, _)))) =>
            re_charrange(lower, upper)
          case _ =>
            t update subres
        }
      case t =>
        t update subres
    }
  }

  override def iPreprocess(f : IFormula, signature : Signature)
                         : (IFormula, Signature) = {
    val f1 = Preproc.visit(f, Context(())).asInstanceOf[IFormula]
    val f2 = Rewriter.rewrite(f1, iPreprocRewriteVal).asInstanceOf[IFormula]
    (f1, signature)
  }

  private def iPreprocRewriteFun(t : IExpression) : IExpression = t match {
    case IFunApp(`re_++`, Seq(IFunApp(`re_++`, Seq(re1, re2)), re3)) =>
      IFunApp(re_++, List(re1, IFunApp(re_++, List(re2, re3))))
    case t => t
  }

  private def iPreprocRewriteVal = iPreprocRewriteFun _

  //////////////////////////////////////////////////////////////////////////////

  private val predFunctionMap =
    (for ((a, b) <- functionPredicateMapping.iterator) yield (b, a)).toMap

  private object StringPred {
    def unapply(p : Predicate) : Option[IFunction] = predFunctionMap get p
  }

  override def preprocess(f : Conjunction, order : TermOrder) : Conjunction = {
    implicit val o = order
    import TerForConvenience._

    if (!Seqs.disjoint(f.predicates, unsupportedPreds)) {
      Console.err.println(
        "Warning: string predicates not supported: " +
          (f.predicates & unsupportedPreds).toSeq.sortBy(_.name).mkString(", "))
      Incompleteness.set
    }

//    println("init: " + f)

    val after1 = Theory.rewritePreds(f, order) { (a, negated) =>
      a.pred match {
        case StringPred(`str_++`) if negated => {
          val shiftedA = VariableShiftSubst(0, 2, order)(a)
          exists(2, shiftedA &
                    _adtSize(List(shiftedA(0), l(v(0)))) &
                    _adtSize(List(shiftedA(1), l(v(1)))) &
                    _adtSize(List(shiftedA(2), v(0) + v(1) - 1)))
        }
        case StringPred(`str_at`) if negated => {
          val shiftedA = VariableShiftSubst(0, 2, order)(a)
          exists(2, shiftedA & (v(1) >= 1) & (v(1) <= 2) & (v(1) <= v(0)) &
                    _adtSize(List(shiftedA(0), l(v(0)))) &
                    _adtSize(List(shiftedA(2), l(v(1)))))
        }
        case StringPred(`str_substr`) if negated => {
          val shiftedA = VariableShiftSubst(0, 2, order)(a)
          exists(2, shiftedA &
                    (v(1) >= 1) &
                    (v(1) <= v(0)) &
                    ((v(1) <= shiftedA(2) + 1) | (v(1) <= 1)) &
                    _adtSize(List(shiftedA(0), l(v(0)))) &
                    _adtSize(List(shiftedA(3), l(v(1)))))
        }
        case StringPred(`str_to_int_help`) if negated => {
          val shiftedA = VariableShiftSubst(0, 1, order)(a)
          exists(1, shiftedA &
                    (v(0) >= 1) & _adtSize(List(shiftedA(1), l(v(0)))))
        }
        case StringPred(`str_indexof_help`) if negated => {
          val shiftedA = VariableShiftSubst(0, 3, order)(a)
          exists(3, shiftedA &
                    (v(2) >= -1) &
                    (v(2) <= v(0) - 1) &
                    ((v(2) >= shiftedA(2)) | (v(2) === -1)) &
                    ((v(2) <= v(0) - v(1)) | (v(2) === -1)) &
                    _adtSize(List(shiftedA(0), l(v(0)))) &
                    _adtSize(List(shiftedA(1), l(v(1)))) &
                    (shiftedA(4) === v(2)))
        }
        case StringPred(`str_replace`) if negated => {
          val shiftedA = VariableShiftSubst(0, 4, order)(a)
          exists(4, shiftedA &
                    ((v(3) === v(0)) | (v(3) + v(1) === v(0) + v(2))) &
                    _adtSize(List(shiftedA(0), l(v(0)))) &
                    _adtSize(List(shiftedA(1), l(v(1)))) &
                    _adtSize(List(shiftedA(2), l(v(2)))) &
                    _adtSize(List(shiftedA(3), l(v(3)))))
        }
        case StringPred(`re_matches_str_help`) if negated => {
          val shiftedA = VariableShiftSubst(0, 1, order)(a)
          exists(1, shiftedA & _adtSize(List(shiftedA(1), l(v(0)))))
        }
        case _ =>
          a
      }
    }

//    println("after1: " + after1)
    after1
  }

  //////////////////////////////////////////////////////////////////////////////

/*
  object ReducerFactory extends ReducerPluginFactory {
    def apply(conj : Conjunction, order : TermOrder) = {
      val words = new MHashMap[Term, SymWord]
      val defTerms = new MHashSet[Term]
      val todo = new Stack[LinearCombination]

      for (a <- conj.predConj.positiveLitsWithPred(_str_empty)) {
        words.put(a.last, EmptyWord)
        defTerms += a.last
        todo push a.last
      }

      for (a <- conj.predConj.positiveLitsWithPred(_str_cons))
        defTerms += a.last

      for (a <- conj.predConj.positiveLitsWithPred(_str_cons).iterator;
           if !(defTerms contains a(1)))
        todo push a(1)

      val term2Cons =
        conj.predConj.positiveLitsWithPred(_str_cons) groupBy { a => a(1) }

      while (!todo.isEmpty) {
        val nextTerm = todo.pop()
        val baseWord =
          words.getOrElse(nextTerm, SymWord(List(), Some(nextTerm)))
        for (a <- term2Cons.getOrElse(nextTerm, List()))
          if (!(words contains a.last)) {
            words.put(a.last, baseWord prepend a.head)
            todo push a.last
          }
      }

      println(words.size)

      new Reducer(words.toMap, false, order)
    }
  }

  class Reducer(knownStrings : Map[Term, SymWord],
                containsVariables : Boolean,
                order : TermOrder) extends ReducerPlugin {
    val factory = ReducerFactory

    def passQuantifiers(num : Int) = this

    def addAssumptions(arithConj : ArithConj,
                       mode : ReducerPlugin.ReductionMode.Value) = this

    def addAssumptions(predConj : PredConj,
                       mode : ReducerPlugin.ReductionMode.Value) = this

    def reduce(predConj : PredConj,
               reducer : ReduceWithConjunction,
               logger : ComputationLogger,
               mode : ReducerPlugin.ReductionMode.Value)
             : ReducerPlugin.ReductionResult = ReducerPlugin.UnchangedResult

    def finalReduce(conj : Conjunction) : Conjunction = conj

  }
*/

  private def atomsContainVars(atoms : Seq[Atom]) : Boolean =
    atoms exists { a => !a.variables.isEmpty }

/*
  object ReducerFactory extends ReducerPluginFactory {
    def apply(conj : Conjunction, order : TermOrder) = {
      val consAtoms = conj.predConj.positiveLitsWithPred(_str_cons)
      val emptAtoms = conj.predConj.positiveLitsWithPred(_str_empty)
      val conses =
        (for (a <- consAtoms.iterator ++ emptAtoms.iterator)
         yield (a.last.asInstanceOf[Term], a)).toMap
      new Reducer(conses get _,
                  atomsContainVars(consAtoms) || atomsContainVars(emptAtoms),
                  order)
    }
  }

  class Reducer(knownConses : Term => Option[Atom],
                containsVariables : Boolean,
                order : TermOrder) extends ReducerPlugin {
    val factory = ReducerFactory

    private def extendConsMap(predConj : PredConj) : Term => Option[Atom] = {
      val consAtoms = predConj.positiveLitsWithPred(_str_cons)
      val emptAtoms = predConj.positiveLitsWithPred(_str_empty)
      val conses =
        (for (a <- consAtoms.iterator ++ emptAtoms.iterator)
         yield (a.last.asInstanceOf[Term], a)).toMap
      t => knownConses(t) orElse (conses get t)
    }

    def passQuantifiers(num : Int) =
      if (containsVariables && num > 0) {
        val downShifter = VariableShiftSubst.downShifter[Term](num, order)
        val upShifter =   VariableShiftSubst.upShifter[Atom](num, order)
        new Reducer((t:Term) =>
                    if (downShifter isDefinedAt t)
                      for (a <- knownConses(downShifter(t))) yield upShifter(a)
                    else
                      None,
                    true,
                    order)
      } else {
        this
      }

    def addAssumptions(arithConj : ArithConj,
                       mode : ReducerPlugin.ReductionMode.Value) = this

    def addAssumptions(predConj : PredConj,
                       mode : ReducerPlugin.ReductionMode.Value) = mode match {
      case ReducerPlugin.ReductionMode.Contextual => {
        val consAtoms = predConj.positiveLitsWithPred(_str_cons)
        val emptAtoms = predConj.positiveLitsWithPred(_str_empty)
        if (!consAtoms.isEmpty || !emptAtoms.isEmpty)
          new Reducer (extendConsMap(predConj),
                       containsVariables ||
                       atomsContainVars(consAtoms) ||
                       atomsContainVars(emptAtoms),
                       order)
        else
          this
      }      
      case ReducerPlugin.ReductionMode.Simple =>
        this
    }

    def reduce(predConj : PredConj,
               reducer : ReduceWithConjunction,
               logger : ComputationLogger,
               mode : ReducerPlugin.ReductionMode.Value)
             : ReducerPlugin.ReductionResult = try {
      if (logger.isLogging) {
        ReducerPlugin.UnchangedResult
      } else {
        import TerForConvenience._
        implicit val _ = order
//println("red " + predConj)

        lazy val allConses = extendConsMap(predConj)

        ReducerPlugin.rewritePreds(predConj, List(_str_++), order) {
          a => a.pred match {
            case `_str_++` =>
              extractWord(a(1), allConses) match {
                case EmptyWord =>
                  a(0) === a(2)
                case _ => extractWord(a(0), allConses) match {
                  case EmptyWord =>
                    a(1) === a(2)
                  case SymWord(Seq(), _) =>
                    a
                  case SymWord(a0Chars, a0Tail) => {
                    val quanNum = a0Chars.size
                    val subst = VariableShiftSubst(0, quanNum, order)
                    val shiftedA = subst(a)
                    val conses =
                      for ((t, n) <- a0Chars.iterator.zipWithIndex)
                      yield _str_cons(List(
                                subst(l(t)), l(v(n)),
                                if (n == 0) shiftedA(2) else l(v(n - 1))))
                    val tail =
                      a0Tail match {
                        case Some(c) =>
                          Iterator(_str_++(
                            List(subst(l(c)), shiftedA(1), l(v(quanNum - 1)))))
                        case None =>
                          Iterator(v(quanNum - 1) === shiftedA(1))
                      }
                    val matrix = conj(conses ++ tail)
                    exists(quanNum, matrix)
                  }
                }
              }
          }
        }
      }
    } catch {
      case InconsistentStringsException => ReducerPlugin.FalseResult
    }

    def finalReduce(conj : Conjunction) : Conjunction = conj

  }

  override val reducerPlugin : ReducerPluginFactory = ReducerFactory
*/

  //////////////////////////////////////////////////////////////////////////////

  def plugin = Some(new Plugin {

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      val facts = goal.facts
      implicit val order = goal.order
      import TerForConvenience._

      def prepareFormula(f : Conjunction) : Conjunction =
        goal reduceWithFacts seqADT.rewriteADTFormula(f, order)

      val concatAtoms = facts.predConj.positiveLitsWithPred(_str_++)

      if (!concatAtoms.isEmpty) {
        import WordExtractor.{SymWord, EmptyWord}

        val extractor = WordExtractor(goal)
        val actions = new ArrayBuffer[Plugin.Action]

        for (a <- concatAtoms) {
          extractor.extractWord(a(1)) match {
            case EmptyWord =>
              actions ++= List(Plugin.AddFormula(a(0) =/= a(2)),
                               Plugin.RemoveFacts(a))
            case _ => extractor.extractWord(a(0)) match {
              case EmptyWord =>
                actions ++= List(Plugin.AddFormula(a(1) =/= a(2)),
                                 Plugin.RemoveFacts(a))
              case SymWord(Seq(), _) =>
                // nothing
              case w@SymWord(a0Chars, a0Tail) => {
                val quanNum = a0Chars.size
                val newConses =
                  for ((t, n) <- a0Chars.iterator.zipWithIndex)
                  yield _str_cons(List(l(t), l(v(n)),
                                       if (n == 0) a(2) else l(v(n - 1))))
                val tail =
                  a0Tail match {
                    case Some(c) =>
                      Iterator(_str_++(List(l(c), a(1), l(v(quanNum - 1)))))
                    case None =>
                      Iterator(v(quanNum - 1) === a(1))
                  }
                  
                val matrix = conj(newConses ++ tail)
                val newFormula = prepareFormula(!exists(quanNum, matrix))

                actions ++= List(Plugin.AddFormula(newFormula),
                                 Plugin.RemoveFacts(a))
              }
            }
          }
        }

        actions.toSeq
      } else {
        List()
      }
    }
  })

  //////////////////////////////////////////////////////////////////////////////

  val asString = new Theory.Decoder[String] {
    def apply(d : IdealInt)
             (implicit ctxt : Theory.DecoderContext) : String =
      asStringPartial(d).get
  }

  val asStringPartial = new Theory.Decoder[Option[String]] {
    def apply(d : IdealInt)
             (implicit ctxt : Theory.DecoderContext) : Option[String] =
      (ctxt getDataFor SeqStringTheory.this) match {
        case DecoderData(m) =>
          for (s <- m get d)
          yield ("" /: s) { case (res, c) => res + c.intValueSafe.toChar }
      }
  }

  case class DecoderData(m : Map[IdealInt, Seq[IdealInt]])
       extends Theory.TheoryDecoderData

  override def generateDecoderData(model : Conjunction)
                                  : Option[Theory.TheoryDecoderData] = {
    val atoms = model.predConj

    val stringMap = new MHashMap[IdealInt, List[IdealInt]]

    for (a <- atoms positiveLitsWithPred _str_empty)
      stringMap.put(a(0).constant, List())

    var oldMapSize = 0
    while (stringMap.size != oldMapSize) {
      oldMapSize = stringMap.size
      for (a <- atoms positiveLitsWithPred _str_cons) {
        for (s1 <- stringMap get a(1).constant)
          stringMap.put(a(2).constant, a(0).constant :: s1)
      }
    }

    Some(DecoderData(stringMap.toMap))
  }

  //////////////////////////////////////////////////////////////////////////////

  override def isSoundForSat(
                 theories : Seq[Theory],
                 config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary  => true
      case Theory.SatSoundnessConfig.Existential => true
      case _                                     => false
    }

  // Set of the predicates that are fully supported at this point
  private val supportedPreds : Set[Predicate] =
    (for (f <- Set(str_++, str_len, str_at, str_substr, int_to_str_help,
                   str_to_int_help, str_indexof_help, str_replace,
                   re_matches_str_help, re_nullable_help, re_derivative_help,
                   re_none, re_eps, re_all, re_allchar, str_to_re,
                   re_charrange, re_++, re_union, re_inter,
                   re_diff, re_*, re_+, re_opt, re_comp))
     yield funPredMap(f)) ++ seqADT.predicates

  private val unsupportedPreds = predicates.toSet -- supportedPreds
  
  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this
  StringTheory register this

}

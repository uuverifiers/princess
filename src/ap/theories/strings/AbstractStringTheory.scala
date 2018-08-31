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

import ap.basetypes.IdealInt
import ap.proof.goal.Goal
import ap.parser.{IFunction, ITerm, IFunApp, IIntLit}
import ap.parser.IExpression.Predicate
import ap.theories.{Theory, ModuloArithmetic}
import ap.types.{Sort, MonoSortedPredicate, MonoSortedIFunction, ProxySort}
import ap.terfor.{Term, Formula, TermOrder, TerForConvenience}
import ap.terfor.preds.{Atom, PredConj}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 ArrayBuffer, Map => MMap, ArrayStack}

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
    new MonoSortedIFunction("str", List(CSo), SSo, true, false)

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
  val str_replacere =
    new MonoSortedIFunction("str_replacere",
                            List(SSo, RSo, SSo), CSo, true, false)
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
  val re_eps =
    new MonoSortedIFunction("re_eps", List(), RSo, true, false)
  val re_all =
    new MonoSortedIFunction("re_all", List(), RSo, true, false)
  val re_allchar =
    new MonoSortedIFunction("re_allchar", List(), RSo, true, false)
  val re_charrange =
    new MonoSortedIFunction("re_charrange", List(CSo, CSo), RSo, true, false)

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

  protected def predefFunctions =
    List(str, str_++, str_len, str_at, str_char,
         str_substr, str_indexof,
         str_replace, str_replaceall, str_replaceallre,
         str_to_re, re_none, re_eps, re_all, re_allchar, re_charrange, re_++,
         re_union, re_inter, re_*, re_+, re_opt)

  protected def predefPredicates =
    List(char_is_digit, str_<=, str_prefixof,
         str_suffixof, str_contains, str_in_re)

  private lazy val predFunMap =
    (for ((f, p) <- functionPredicateMapping) yield (p, f)).toMap

  //////////////////////////////////////////////////////////////////////////////
  // Helper classes to reconstruct strings and regexes from the facts in a goal

  val _str_empty : Predicate
  val _str_cons : Predicate
  val _str_++ : Predicate

  object WordExtractor {
    case class SymWord(chars : IndexedSeq[Term], tail : Option[Term]) {
      def prepend(t : Term) = SymWord(Vector(t) ++ chars, tail)
      def map(f : Term => Term) = SymWord(chars map f, tail map f)
      def asConcreteWord : Seq[Int] = {
        if (tail.isDefined)
          throw new IllegalArgumentException("not a concrete string")
        chars map {
          case LinearCombination.Constant(IdealInt(v)) => v
          case _ =>
            throw new IllegalArgumentException("not a concrete string")
        }
      }
    }

    val EmptyWord = SymWord(Vector(), None)

    object InconsistentStringsException extends Exception

    def apply(goal : Goal) : WordExtractor =
      apply(goal.facts.predConj)

    def apply(predConj : PredConj) : WordExtractor = {
      val consAtoms = predConj.positiveLitsWithPred(_str_cons)
      val emptAtoms = predConj.positiveLitsWithPred(_str_empty)

      val conses = new MHashMap[Term, Atom]
      for (a <- consAtoms.iterator ++ emptAtoms.iterator)
        conses.put(a.last.asInstanceOf[Term], a)

      new WordExtractor(conses get _)
    }
  }

  class WordExtractor private (allConses : Term => Option[Atom]) {
    import WordExtractor._

    def extractWord(t : Term) : SymWord = {
      val chars = new ArrayBuffer[Term]
      val seenNodes = new MHashSet[Term]
      
      var curT = t
      seenNodes += t

      while (true) {
        allConses(curT) match {
          case Some(a) if a.pred == _str_empty =>
            return SymWord(chars, None)
          case Some(a) if a.pred == _str_cons => {
            chars += a(0)
            curT = a(1)
            if (!(seenNodes add curT))
              throw InconsistentStringsException
          }
          case _ =>
            return SymWord(chars, Some(curT))
        }
      }

      SymWord(Vector(), Some(t))
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  object RegexExtractor {
    private val regexFunctions =
      Set(str_empty, str_cons, re_none, str_to_re, re_all, re_allchar,
          re_++, re_union, re_inter, re_*, re_+, re_opt)
    private lazy val regexPredicates =
      regexFunctions map functionPredicateMapping.toMap

    def apply(goal : Goal) : RegexExtractor =
      apply(goal.facts.predConj)

    def apply(predConj : PredConj) : RegexExtractor = {
      val atoms =
        (for (p <- regexPredicates.iterator;
              a <- (predConj positiveLitsWithPred p).iterator)
         yield (a.last.asInstanceOf[Term], a)).toMap
      new RegexExtractor (atoms get _)
    }
  }

  class IllegalRegexException extends Exception

  /**
   * Translator from atoms representing regexes in a goal to the corresponding
   * term.
   */
  class RegexExtractor private (atoms : Term => Option[Atom]) {
    def regexAsTerm(t : Term) : ITerm =
      t match {
        case LinearCombination.Constant(v) => IIntLit(v)
        case t => atoms(t) match {
          case Some(a) =>
            IFunApp(predFunMap(a.pred), for (s <- a.init) yield regexAsTerm(s))
          case None =>
            throw new IllegalRegexException
        }
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Augment goal facts with the given assignment of strings to terms.
   * At the moment this assumes that all string terms are constants.
   */
  protected def assignStringValues(
                  facts : Conjunction,
                  assignment : Map[Term, Seq[Int]],
                  order : TermOrder) : Conjunction = {
    import TerForConvenience._
    implicit val _ = order

    val epsId = 0
    val stringIds = new MHashMap[(Int, Int), Int]
    val extraFors = new ArrayBuffer[Formula]

    extraFors += Atom(_str_empty, List(LinearCombination.ZERO), order)

    def idFor(c : Int, tail : Int) : Int =
      stringIds.getOrElseUpdate((c, tail), {
        val id = stringIds.size + 1
        extraFors += Atom(_str_cons,
                          List(LinearCombination(c),
                               LinearCombination(tail),
                               LinearCombination(id)),
                          order)
        id
      })

    for (t <- order sort assignment.keySet) {
      val str = assignment(t)
      extraFors += (t === (str :\ epsId)(idFor _))
    }

    extraFors += facts

    Conjunction.conj(extraFors, order)
  }

}

////////////////////////////////////////////////////////////////////////////////

object AbstractStringTheoryWithSort {

  /**
   * Sort for strings that will reconstruct terms with the help of the
   * <code>str_empty</code> and <code>str_cons</code> functions.
   */
  class AbstractStringSort extends ProxySort(Sort.Integer) {
    override val name = "String"

    private var theory : AbstractStringTheoryWithSort = null

    protected[strings] def setTheory(
                             _theory : AbstractStringTheoryWithSort) : Unit =
      theory = _theory

    override def individuals : Stream[ITerm] = Sort.Integer.individuals

    override def augmentModelTermSet(
                   model : Conjunction,
                   terms : MMap[(IdealInt, Sort), ITerm]) : Unit = {
      val t = theory
      import t.{str_empty, str_cons, _str_empty, _str_cons, CharSort}

      val predConj = model.predConj
      
      for (lc <- predConj.lookupFunctionResult(_str_empty, List())) {
        val emptyIndex = lc.constant
        val emptyString = IFunApp(str_empty, List())
        terms.put((emptyIndex, this), emptyString)

        val todo = new ArrayStack[(IdealInt, ITerm)]
        todo push ((emptyIndex, emptyString))

        val conses =
          (for (a <- predConj positiveLitsWithPred _str_cons) yield
             (a(1).constant, (a(0).constant, a(2).constant))) groupBy (_._1)

        while (!todo.isEmpty) {
          val (nextIndex, nextString) = todo.pop
          for (consedStrings <- conses get nextIndex) {
            for ((_, (char, stringIndex)) <- consedStrings)
              for (charTerm <- terms get ((char, CharSort))) {
                val consedString =
                  IFunApp(str_cons, List(charTerm, nextString))
                if (terms.put((stringIndex, this), consedString).isEmpty)
                  todo push (stringIndex, consedString)
              }
          }
        }
      }
    }
  }

}

/**
 * Abstract class defining relevant string operations as sorted
 * functions/predicates, as well as an infinite string sort together
 * with constructor and selector operations.
 */
abstract class AbstractStringTheoryWithSort extends {

  val StringSort = new AbstractStringTheoryWithSort.AbstractStringSort

} with AbstractStringTheory {

  private val CSo = CharSort
  private val SSo = StringSort

  val str_empty =
    new MonoSortedIFunction("str_empty", List(), SSo, true, false)
  val str_cons =
    new MonoSortedIFunction("str_cons", List(CSo, SSo), SSo, true, false)
  val str_head =
    new MonoSortedIFunction("str_head", List(SSo), CSo, true, false)
  val str_tail =
    new MonoSortedIFunction("str_tail", List(SSo), SSo, true, false)

  StringSort setTheory this

  protected override def predefFunctions =
    super.predefFunctions ++ List(str_empty, str_cons, str_head, str_tail)

}

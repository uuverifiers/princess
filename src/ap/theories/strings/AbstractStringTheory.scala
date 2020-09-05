/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018-2020 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.proof.theoryPlugins.Plugin
import ap.parser.{IFunction, ITerm, IFunApp, IIntLit}
import ap.parser.IExpression.Predicate
import ap.theories.{Theory, ModuloArithmetic}
import ap.types.{Sort, MonoSortedPredicate, MonoSortedIFunction, ProxySort}
import ap.terfor.{Term, Formula, TermOrder, TerForConvenience}
import ap.terfor.preds.{Atom, PredConj}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.util.Seqs

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 ArrayBuffer, Map => MMap, ArrayStack,
                                 LinkedHashMap, LinkedHashSet, Set => MSet}

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

  val str_head_code =
    new MonoSortedIFunction("str_head_code", List(SSo), Integer, true, false)

  val str =
    new MonoSortedIFunction("str", List(CSo), SSo, true, false)

  val str_from_code =
    new MonoSortedIFunction("str_from_code", List(Integer), SSo, true, false)
  val str_to_code =
    new MonoSortedIFunction("str_to_code", List(SSo), Integer, true, false)

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
                            List(SSo, SSo, SSo), SSo, true, false)
  val str_replacere =
    new MonoSortedIFunction("str_replacere",
                            List(SSo, RSo, SSo), SSo, true, false)
  val str_replacecg =
    new MonoSortedIFunction("str_replacecg",
                            List(SSo, RSo, RSo), SSo, true, false)
  val str_replaceall =
    new MonoSortedIFunction("str_replaceall",
                            List(SSo, SSo, SSo), SSo, true, false)
  val str_replaceallre =
    new MonoSortedIFunction("str_replaceallre",
                            List(SSo, RSo, SSo), SSo, true, false)
  val str_replaceallcg =
    new MonoSortedIFunction("str_replaceallcg",
                            List(SSo, RSo, RSo), SSo, true, false)

  val str_in_re =
    new MonoSortedPredicate("str_in_re", List(SSo, RSo))

  val str_to_re =
    new MonoSortedIFunction("str_to_re", List(SSo), RSo, true, false)
  val re_from_str =
    new MonoSortedIFunction("re_from_str", List(SSo), RSo, true, false)

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
  val re_range =
    new MonoSortedIFunction("re_range", List(SSo, SSo), RSo, true, false)

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
  val re_comp =
    new MonoSortedIFunction("re_comp", List(RSo), RSo, true, false)

  val re_loop =
    new MonoSortedIFunction("re_loop", List(Integer, Integer, RSo), RSo,
                            true, false)

  val re_capture =
    new MonoSortedIFunction("re_capture", List(Integer, RSo), RSo,
                            true, false)

  val re_reference =
    new MonoSortedIFunction("re_reference", List(Integer), RSo,
                            true, false)

  val str_match =
    new MonoSortedIFunction("str_match", List(Integer, Integer, SSo, RSo), SSo,
                            true, false)
  val str_extract =
    new MonoSortedIFunction("str_extract", List(Integer, SSo, RSo), SSo,
                            true, false)

  protected def predefFunctions =
    List(str_head_code, str, str_from_code, str_to_code,
         str_++, str_len, str_at, str_char,
         str_substr, str_indexof,
         str_replace, str_replacere, str_replacecg,
         str_replaceall, str_replaceallre, str_replaceallcg,
         str_to_re, re_from_str, re_none, re_eps, re_all, re_allchar,
         re_charrange, re_range, re_++,
         re_union, re_inter, re_*, re_+, re_opt, re_comp, re_loop,
         re_capture, re_reference, str_match, str_extract)

  protected def predefPredicates =
    List(char_is_digit, str_<=, str_prefixof,
         str_suffixof, str_contains, str_in_re)

  private lazy val predFunMap =
    (for ((f, p) <- functionPredicateMapping) yield (p, f)).toMap

  //////////////////////////////////////////////////////////////////////////////
  // Helper classes to reconstruct strings and regexes from the facts in a goal

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
      Set(str_empty, str_cons, re_none, str_to_re, re_from_str, re_all,
          re_allchar, re_charrange, re_range, re_++, re_union, re_inter,
          re_*, re_+, re_opt, re_comp, re_loop, re_capture, re_reference)
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

////////////////////////////////////////////////////////////////////////////////

  /**
   * Check for cyclic word equations induced by <code>str_++</code>
   * or <code>str_cons</code>, and break those.
   * e.g., equations x = yz & y = ax  ->  z = eps & a = eps & y = ax
   * Tarjan's algorithm is used to find all strongly connected components
   */
  protected def breakCyclicEquations(goal : Goal)
                    : Option[Seq[Plugin.Action]] = {

      import TerForConvenience._
      implicit val _ = goal.order
      val predConj = goal.facts.predConj

      val newAtoms = new ArrayBuffer[Formula]
      val removedAtoms = new ArrayBuffer[Atom]

      {
        val successors =
          ((predConj positiveLitsWithPred _str_++) ++
           (predConj positiveLitsWithPred _str_cons)) groupBy (_.last)

        def successorsOf(a : Atom) : Iterator[LinearCombination] =
          a.pred match {
            case `_str_cons` => Iterator single a(1)
            case `_str_++`   => Seqs.doubleIterator(a(0), a(1))
          }

        val index, lowlink = new MHashMap[LinearCombination, Int]
        val stack = new LinkedHashSet[LinearCombination]
        val component = new MHashSet[LinearCombination]
        val cycle = new LinkedHashMap[LinearCombination,
                                      (Atom, LinearCombination)]

        def connect(v : LinearCombination) : Unit = {
          val vIndex = index.size
          index.put(v, vIndex)
          lowlink.put(v, vIndex)
          stack += v

          for (a <- successors.getOrElse(v, List()).iterator;
               w <- successorsOf(a))
            (index get w) match {
              case Some(wIndex) =>
                if (stack contains w)
                  lowlink.put(v, lowlink(v) min index(w))
              case None => {
                connect(w)
                lowlink.put(v, lowlink(v) min lowlink(w))
              }
            }

          if (lowlink(v) == vIndex) {
            // found a strongly connected component
            var next = stack.last
            stack remove next
            component += next
            while (next != v) {
              next = stack.last
              stack remove next
              component += next
            }

//              println(component.toList)

            // check whether we can construct a cycle within the
            // component
            var curNode = v
            while (curNode != null && !(cycle contains curNode)) {
              val it = successors.getOrElse(curNode, List()).iterator
              var atom : Atom = null
              var nextNode : LinearCombination = null

              while (atom == null && it.hasNext) {
                val a = it.next
                val argIt = successorsOf(a)

                val arg1 = argIt.next
                if (component contains arg1) {
                  atom = a
                  nextNode = arg1
                } else if (argIt.hasNext) {
                  val arg2 = argIt.next
                  if (component contains arg2) {
                    atom = a
                    nextNode = arg2
                  }
                }
              }

              if (atom != null)
                cycle.put(curNode, (atom, nextNode))
              curNode = nextNode
            }

            if (curNode != null) {
              // then we have found a cycle
              var started = false
              for ((v, (a, w)) <- cycle) {
                if (!started && v == curNode) {
                  removedAtoms += a
                  started = true
                }

                if (started)
                  a.pred match {
                    case `_str_cons` =>
                      // an immediate contradiction
                      newAtoms += Conjunction.FALSE
                    case `_str_++` =>
                      newAtoms += _str_empty(List(a(if (w == a(0)) 1 else 0)))
                  }
              }
            }

            component.clear
            cycle.clear
          }
        }

        for (v <- successors.keysIterator)
          if (!(index contains v))
            connect(v)
      }

      ////////////////////////////////////////////////////////////////////////

      if (newAtoms.nonEmpty || removedAtoms.nonEmpty)
        Some(List(Plugin.RemoveFacts(conj(removedAtoms)),
                  Plugin.AddFormula(!conj(newAtoms))))
      else
        None

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

    override lazy val individuals : Stream[ITerm] =
      IFunApp(theory.str_empty, List()) #::
      (for (t <- individuals;
            n <- theory.CharSort.individuals)
       yield IFunApp(theory.str_cons, List(n, t)))

    override def decodeToTerm(
                   d : IdealInt,
                   assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      assignment get ((d, this))

    override def augmentModelTermSet(
                            model : Conjunction,
                            terms : MMap[(IdealInt, Sort), ITerm],
                            allTerms : Set[(IdealInt, Sort)],
                            definedTerms : MSet[(IdealInt, Sort)]) : Unit = {
      val t = theory
      import t.{str_empty, str_cons, _str_empty, _str_cons, CharSort}

      val predConj = model.predConj
      
      val conses =
        (for (a <- predConj positiveLitsWithPred _str_cons) yield
           (a(1).constant, (a(0).constant, a(2).constant))) groupBy (_._1)

      for (lc <- predConj.lookupFunctionResult(_str_empty, List())) {
        val emptyIndex = lc.constant
        val emptyString = IFunApp(str_empty, List())
        terms.put((emptyIndex, this), emptyString)

        val todo = new ArrayStack[(IdealInt, ITerm)]
        todo push ((emptyIndex, emptyString))

        while (!todo.isEmpty) {
          val (nextIndex, nextString) = todo.pop
          for (consedStrings <- conses get nextIndex) {
            for ((_, (char, stringIndex)) <- consedStrings)
              for (charTerm <- CharSort.decodeToTerm(char, terms)) {
                val consedString =
                  IFunApp(str_cons, List(charTerm, nextString))
                if (terms.put((stringIndex, this), consedString).isEmpty)
                  todo push (stringIndex, consedString)
              }
          }
        }
      }

      // check whether any of the terms to be constructed are blocked by
      // missing character terms
      for (ind <- conses.keysIterator) {
        val p = (ind, this.asInstanceOf[Sort])
        if (!(terms contains p))
          definedTerms += p
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

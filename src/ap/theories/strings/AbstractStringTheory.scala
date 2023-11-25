/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018-2021 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.parser.{IFunction, ITerm, IExpression, IFunApp, IIntLit,
                  CollectingVisitor}
import ap.parser.IExpression.Predicate
import ap.theories.{Theory, ModuloArithmetic}
import ap.types.{Sort, MonoSortedPredicate, MonoSortedIFunction, ProxySort}
import ap.terfor.{Term, Formula, TermOrder, TerForConvenience}
import ap.terfor.preds.{Atom, PredConj}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Seqs, Tarjan}

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 ArrayBuffer, Map => MMap, ArrayStack,
                                 LinkedHashMap, Set => MSet}

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

  val str_from_char =
    new MonoSortedIFunction("str_from_char", List(CSo), SSo, true, false)

  val str_from_code =
    new MonoSortedIFunction("str_from_code", List(Integer), SSo, true, false)
  val str_to_code =
    new MonoSortedIFunction("str_to_code", List(SSo), Integer, true, false)

  val str_++ =
    new MonoSortedIFunction("str_++", List(SSo, SSo), SSo, true, false)
  val str_len =
    new MonoSortedIFunction("str_len", List(SSo), Nat, true, false)

  val str_to_int =
    new MonoSortedIFunction("str_to_int", List(SSo), Integer, true, false)
  val int_to_str =
    new MonoSortedIFunction("int_to_str", List(Integer), SSo, true, false)

  val str_<= =
    new MonoSortedPredicate("char_<=", List(SSo, SSo))
  val str_< =
    new MonoSortedPredicate("char_<", List(SSo, SSo))
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
  val str_replaceall =
    new MonoSortedIFunction("str_replaceall",
                            List(SSo, SSo, SSo), SSo, true, false)
  val str_replaceallre =
    new MonoSortedIFunction("str_replaceallre",
                            List(SSo, RSo, SSo), SSo, true, false)

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
  val re_diff =
    new MonoSortedIFunction("re_diff", List(RSo, RSo), RSo, true, false)

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

  protected def predefFunctions =
    List(str_head_code, str_from_char, str_from_code, str_to_code,
         str_++, str_len, str_to_int, int_to_str, str_at, str_char,
         str_substr, str_indexof,
         str_replace, str_replacere, str_replaceall, str_replaceallre,
         str_to_re, re_from_str, re_none, re_eps, re_all, re_allchar,
         re_charrange, re_range, re_++,
         re_union, re_inter, re_diff, re_*, re_+, re_opt, re_comp, re_loop)

  protected def predefPredicates =
    List(char_is_digit, str_<=, str_<, str_prefixof,
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

  private lazy val regexFunctions =
    Set(str_empty, str_cons, re_none, str_to_re, re_from_str, re_all,
        re_allchar, re_charrange, re_range, re_++, re_union, re_inter, re_diff,
        re_*, re_+, re_opt, re_comp, re_loop, re_eps) ++
    (for ((_, Left(f : MonoSortedIFunction)) <- extraOps.iterator;
          if f.resSort == RegexSort)
     yield f) ++
    (for ((_, Left(f : MonoSortedIFunction)) <- extraIndexedOps.iterator;
          if f.resSort == RegexSort)
     yield f)

  object RegexExtractor {
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

  class IllegalRegexException extends Exception("illegal regular expression")

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

  /**
   * Extractor to identify regular expressions that are completely defined,
   * i.e., in which no sub-terms are left symbolic.
   */
  object ConcreteRegex {
    def unapply(t : ITerm) : Option[ITerm] =
      try {
        ConcreteRegexVisitor.visitWithoutResult(t, ())
        Some(t)
      } catch {
        case NonConcreteRegexException => None
      }
  }

  private object NonConcreteRegexException extends Exception

  private object ConcreteRegexVisitor extends CollectingVisitor[Unit, Unit] {
    override def preVisit(t : IExpression,
                          arg : Unit) : PreVisitResult = t match {
      case IFunApp(f, _) if regexFunctions contains f =>
        KeepArg
      case IFunApp(ModuloArithmetic.mod_cast, _) =>
        KeepArg
      case t : IIntLit =>
        KeepArg
      case _ =>
        throw NonConcreteRegexException
    }

    def postVisit(t : IExpression, arg : Unit, subres : Seq[Unit]) : Unit = ()
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
        val successorsMap =
          ((predConj positiveLitsWithPred _str_++) ++
           (predConj positiveLitsWithPred _str_cons)) groupBy (_.last)

        def successorsOf(a : Atom) : Iterator[LinearCombination] =
          a.pred match {
            case `_str_cons` => Iterator single a(1)
            case `_str_++`   => Seqs.doubleIterator(a(0), a(1))
          }

        val graph = new Tarjan.Graph[LinearCombination] {
          val nodes = successorsMap.keys
          def successors(lc : LinearCombination) =
            for (a <- successorsMap.getOrElse(lc, List()).iterator;
                 w <- successorsOf(a))
            yield w
        }

        val components = (new Tarjan (graph)).components
        val cycle = new LinkedHashMap[LinearCombination,
                                      (Atom, LinearCombination)]

        for (component <- components) {
          // check whether we can construct a cycle within the
          // component
          var curNode = component.head
          while (curNode != null && !(cycle contains curNode)) {
            val it = successorsMap.getOrElse(curNode, List()).iterator
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
        }
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

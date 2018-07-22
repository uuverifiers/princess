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

import ap.Signature
import ap.parser._
import ap.parser.IExpression.Predicate
import ap.theories.{Theory, ADT, ModuloArithmetic, TheoryRegistry}
import ap.types.Sort
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction,
                               ReducerPlugin, ReducerPluginFactory}
import ap.terfor.preds.{PredConj, Atom}
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{TermOrder, TerForConvenience, Term, ComputationLogger}
import ap.terfor.substitutions.VariableShiftSubst
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal
import ap.util.Seqs

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 ArrayStack, ArrayBuffer}

object SeqStringTheory {

  private val instances = new MHashMap[Int, SeqStringTheory]

  def apply(bitWidth : Int) : SeqStringTheory = synchronized {
    instances.getOrElseUpdate(bitWidth, new SeqStringTheory(bitWidth))
  }

}

/**
 * Generic class describing string theories.
 */
class SeqStringTheory private (val bitWidth : Int) extends {

  val CharSort = ModuloArithmetic.UnsignedBVSort(bitWidth)
  val RegexSort = new Sort.InfUninterpreted("RegLan")

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

  val Seq(str_empty, str_cons) =        seqADT.constructors
  val Seq(_, Seq(str_head, str_tail)) = seqADT.selectors

  def int2Char(t : ITerm) : ITerm =
    ModuloArithmetic.cast2UnsignedBV(bitWidth, t)

  def char2Int(t : ITerm) : ITerm = t

  val transducers : Map[String, Predicate] = Map()
  
  //////////////////////////////////////////////////////////////////////////////

  val functions = predefFunctions
  
  val (funPredicates, axioms, _, funPredMap) =
    Theory.genAxioms(theoryFunctions = functions)

  val predicates = predefPredicates ++ funPredicates

  val functionPredicateMapping = functions zip funPredicates
  val functionalPredicates = funPredicates.toSet
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val totalityAxioms = Conjunction.TRUE
  val triggerRelevantFunctions : Set[IFunction] = Set()

  override val dependencies : Iterable[Theory] = List(seqADT, ModuloArithmetic)

  //////////////////////////////////////////////////////////////////////////////

  private val adtSize    = seqADT.termSize.head
  private val _adtSize   = seqADT.termSizePreds.head
  private val _str_empty = seqADT.constructorPreds(0)
  private val _str_cons  = seqADT.constructorPreds(1)
  private val _str_++    = funPredMap(str_++)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Visitor called during pre-processing to eliminate symbols
   * <code>str, str_len</code>
   */
  private object Preproc extends CollectingVisitor[Unit, IExpression] {
    import IExpression._

    def postVisit(t : IExpression,
                  arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IFunApp(`str`, _) =>
        str_cons(subres.head.asInstanceOf[ITerm], str_empty())
      case IFunApp(`str_len`, _) =>
        adtSize(subres.head.asInstanceOf[ITerm])
      case t =>
        t update subres
    }
  }

  override def iPreprocess(f : IFormula, signature : Signature)
                          : (IFormula, Signature) =
    (Preproc.visit(f, ()).asInstanceOf[IFormula], signature)

  //////////////////////////////////////////////////////////////////////////////

  private val predFunctionMap =
    (for ((a, b) <- functionPredicateMapping.iterator) yield (b, a)).toMap

  private object StringPred {
    def unapply(p : Predicate) : Option[IFunction] = predFunctionMap get p
  }

  override def preprocess(f : Conjunction, order : TermOrder) : Conjunction = {
    implicit val _ = order
    import TerForConvenience._

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
        case _ =>
          a
      }
    }

//    println("after1: " + after1)
    after1
  }

  //////////////////////////////////////////////////////////////////////////////

  case class SymWord(chars : IndexedSeq[Term], tail : Option[Term]) {
    def prepend(t : Term) = SymWord(Vector(t) ++ chars, tail)
    def map(f : Term => Term) = SymWord(chars map f, tail map f)
  }

  val EmptyWord = SymWord(Vector(), None)

  private object InconsistentStringsException extends Exception

  private def extractWord(t : Term,
                         allConses : Term => Option[Atom]) : SymWord = {
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
    null
  }

/*
  object ReducerFactory extends ReducerPluginFactory {
    def apply(conj : Conjunction, order : TermOrder) = {
      val words = new MHashMap[Term, SymWord]
      val defTerms = new MHashSet[Term]
      val todo = new ArrayStack[LinearCombination]

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
        val nextTerm = todo.pop
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
    // not used
    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = None

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
      val facts = goal.facts
      implicit val order = goal.order
      import TerForConvenience._

      def prepareFormula(f : Conjunction) : Conjunction =
        goal reduceWithFacts seqADT.rewriteADTFormula(f, order)

      val concatAtoms = facts.predConj.positiveLitsWithPred(_str_++)

      if (!concatAtoms.isEmpty) {
        val consAtoms = facts.predConj.positiveLitsWithPred(_str_cons)
        val emptAtoms = facts.predConj.positiveLitsWithPred(_str_empty)
        val conses =
          (for (a <- consAtoms.iterator ++ emptAtoms.iterator)
           yield (a.last.asInstanceOf[Term], a)).toMap

        val actions = new ArrayBuffer[Plugin.Action]

        for (a <- concatAtoms) {
          extractWord(a(1), conses get _) match {
            case EmptyWord =>
              actions ++= List(Plugin.AddFormula(a(0) =/= a(2)),
                               Plugin.RemoveFacts(a))
            case _ => extractWord(a(0), conses get _) match {
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

        actions
      } else {
        List()
      }
    }
  })

  //////////////////////////////////////////////////////////////////////////////

  override def isSoundForSat(
                 theories : Seq[Theory],
                 config : Theory.SatSoundnessConfig.Value) : Boolean =
    config == Theory.SatSoundnessConfig.Existential
  
  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

}

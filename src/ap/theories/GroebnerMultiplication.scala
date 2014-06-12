/**
  * This file is part of Princess, a theorem prover for Presburger
  * arithmetic with uninterpreted predicates.
  * <http://www.philipp.ruemmer.org/princess.shtml>
  *
  * Copyright (C) 2013-2014 Philipp Ruemmer <ph_r@gmx.net>
  *
  * Princess is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License as published by
  * the Free Software Foundation, either version 3 of the License, or
  * (at your option) any later version.
  *
  * Princess is distributed in the hope that it will be useful,
  * but WITHOUT ANY WARRANTY; without even the implied warranty of
  * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  * GNU General Public License for more details.
  *
  * You should have received a copy of the GNU General Public License
  * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
  */

package ap.theories

import ap._
import ap.parser._
import ap.theories._
import ap.parameters.Param
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{TerForConvenience, TermOrder, ConstantTerm}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import ap.terfor.OneTerm
import ap.util.Timeout

import ap.proof.goal.Goal

import ap.basetypes.IdealInt

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}



/**
  * Extremely naive implementation of a theory of non-linear integer arithmetic.
  * Currently the theory only does AC-congruence reasoning for multiplication.
  */

object GroebnerMultiplication extends MulTheory {

  val mul = new IFunction("mul", 2, true, false)
  val functions = List(mul)

  val (predicates, axioms, totalityAxioms, _mul) = {
    val functionEnc = new FunctionEncoder (true, false, Map())
    val predicates =
      for (f <- functions) yield (functionEnc addFunction f)

    val (axioms, _, functionTranslation) =
      Theory.toInternal(true,
        false,
        TermOrder.EMPTY extendPred predicates,
        functionEnc)

    (predicates,
      axioms, Conjunction.TRUE,
      functionTranslation(mul))
  }

  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()
  val functionalPredicates = predicates.toSet
  override val singleInstantiationPredicates = predicates.toSet
  val functionPredicateMapping = List(mul -> _mul)

  // Conversion functions between Princess' LinearCombinations and Groebner's Polynomials
  def lcToPolynomial(lc : LinearCombination)(implicit ordering : monomialOrdering) : Polynomial =
  {
    var retPoly = new Polynomial(List())

    for (llcc <- lc)
    {
      retPoly +=
      (if (llcc._2.toString == "1")
        new Term(llcc._1.intValue, new Monomial(List()))
      else
      {
        (llcc._2) match
        {
          case (x : ConstantTerm) => new Term(llcc._1.intValue, new Monomial(List((x, 1))))
        }
      })

    }

    retPoly
  }

  def atomToPolynomial(a : Atom)(implicit ordering : monomialOrdering) : Polynomial =
  {
    val a0 = lcToPolynomial(a(0))
    val a1 = lcToPolynomial(a(1))
    val a2 = lcToPolynomial(a(2))

    val aa = a0*a1 - a2

    aa
  }



  /**
   * Splitter handles the case-analysis of intervals
   */

  object Splitter extends TheoryProcedure 
  {
    def handleGoal(goal : Goal) : Seq[Plugin.Action] = 
    {
      implicit val _ = goal.order
      implicit val monOrder = new GrevlexOrdering(new StringOrdering)
      implicit val ctOrder = monOrder.termOrdering
      import TerForConvenience._

      // Extract all predicates
      val predicates = goal.facts.predConj.positiveLitsWithPred(_mul)
      val preds = predicates.map(atomToPolynomial).toList
      val ineqs = goal.facts.arithConj.inEqs
      val negeqs = goal.facts.arithConj.negativeEqs


      /**

        Here follows the different splitting strategies

       */

      // We have to find sets of ConstantTerms such that all predicates are linearized
      // Since we have predicates of the form a(0)*a(1)=a(2), a simple (but incomplete?)
      // method is to ...
      def linearizers(predicates : List[ap.terfor.preds.Atom]) : Set[Set[ConstantTerm]] =
      {


        // Given the List [({x11, x12, ...}, {y11, y12, ...}), ({x21, ....]
        // returns {{x1*, x2*, x3* ...xn*}, {x1*, x2*, ... yn*}, ..., {y1*, y2*, ... yn*}}
        def helper(list : List[(Set[ConstantTerm], Set[ConstantTerm])]) : Set[Set[ConstantTerm]] =
        {
          list match
          {
            case Nil => Set(Set()) : Set[Set[ConstantTerm]]
            case (xSet, ySet) :: rest =>
              {
                val recur = helper(rest)
                val xRes = recur.map (x => x ++ xSet)
                val yRes = recur.map (y => y ++ ySet)
                (xRes ++ yRes)
              }
          }
        }

        val predSet =
          for (p <- predicates)
          yield
          {
            (p(0).constants, p(1).constants)
          }

        helper(predSet)
      }


      def sphericalSplit(predicates : List[ap.terfor.preds.Atom], intervalSet : IntervalSet) : List[(ap.terfor.Formula, ap.terfor.Formula, String)] = 
      {

        println("sphericalSplit not enabled!")
        return List()

        println("sphericalSplit(" + predicates + ")")

        // CHAngE
        val ls = linearizers(predicates).toList.sortWith((s1, s2) => s1.size > s2.size)


        // Just take the smallest set
        val targetSet = ls.head.toList.sorted

        // What is the current lower bound of the set?

        val lbs = 
          (for (ct <- targetSet)
          yield
          {
            intervalSet.lowerLimit(new Monomial(List((ct, 2))))
          })

        val sum = (lbs.tail :\ lbs.head) ((s, lb) => s + lb)
        val min = (lbs.tail :\ lbs.head) ((m, lb) => m.min(lb)).max(sum)
        val actualMin = 
          if (min.isNegative)
            IdealInt(0)
          else
            min.get

        def calcNewLimit(ack : Int, size : Int, curMin : IdealInt) : IdealInt =
        {
          val newLim = IdealInt((scala.math.pow(ack, 2)*size).toInt)
          if (newLim > curMin)
            newLim
          else
            calcNewLimit(ack+1, size, curMin)
        }

        import ap.terfor.conjunctions.Quantifier
        import ap.terfor.VariableTerm

        var i = 0
        var newVariablesUsed = false
        var varSet = Set() : Set[LinearCombination]

        val mulEqs = 
          for (t <- targetSet)
          yield
          {
            // Is there already such a predicate?
            def findMatchingPredicate(t : LinearCombination) : Option[LinearCombination] =
            {
              for (p <- predicates)
              {
                if ((p(0) == l(t)) && (p(1) == l(t)))
                {
                  if (p(2).lcSize == 1)
                    return Some(p(2))
                }
              }
              None
            }

            val newVar = 
              (findMatchingPredicate(l(t)) match
              {
                case None => 
                  {
                    i = i + 1
                    newVariablesUsed = true
                    v(i - 1)
                  }
                case Some(v) => v
              }) : LinearCombination

            varSet = varSet + newVar
            (_mul(List(l(t), l(t), newVar)))
          }

        val varList = varSet.toList
        val helperSum = l(varList.foldLeft(l(0)) ((t1, t2) => t1 +t2))

        println("varList: " + varList)
        println("helperSum (" + helperSum.getClass + "): " + helperSum)
        println("newVariablesUsed: " + newVariablesUsed)
        val helperSumLowerBound = 
          if (newVariablesUsed)
            IdealInt(0)
          else
            PresburgerTools.lowerBound(helperSum, goal.facts) match
            {
              case None => IdealInt(0)
              case Some(x) => x
            }

        val newLimit = 
            calcNewLimit(2, lbs.size, helperSumLowerBound)

        val lteq =  helperSum < newLimit
        val geeq = helperSum >= newLimit

        var ltFinal = conj(List(lteq, (conj(mulEqs.toList))))
        var gtFinal = conj(List(geeq, (conj(mulEqs.toList))))

        for (ii <- 0 until i)
        {
          ltFinal = forall(ltFinal)
          gtFinal = forall(gtFinal)
        }

        val opt1 = ltFinal
        val opt2 = gtFinal
        val msg = "Spherical split: " + opt1 + ", " + opt2

        List((opt1.negate, opt2.negate, msg))
      }



      def infinitySplit(intervalSet : IntervalSet, targetSet : Set[ConstantTerm]) : List[(ap.terfor.Formula, ap.terfor.Formula, String)] =
      {


        var alternatives = List() : List[(ap.terfor.Formula, ap.terfor.Formula, String)]

        val allIntervals = 
          if (targetSet.isEmpty)
            intervalSet.getAllIntervals()
          else
            (for (ct <- targetSet)
            yield
              intervalSet.getTermInterval(ct)).toList

        for ((c, i) <- intervalSet.getAllIntervals())
        {
          (i.lower, i.upper) match
          {
            // if x = [-, +], split at zero
            case (IntervalNegInf, IntervalPosInf) =>
              {
                val opt1 = (c < 0)
                val opt2 = (c >= 0)
                val msg = "[-Inf, +Inf] split: " + opt1 + ", " + opt2
                alternatives = (opt1.negate, opt2.negate, msg) :: alternatives
              }
            case _ =>
          }
        }

        alternatives
      }

      def desperateSplit(intervalSet : IntervalSet, targetSet : Set[ConstantTerm]) : List[(ap.terfor.Formula, ap.terfor.Formula, String)] =
      {
        var alternatives = List() : List[(ap.terfor.Formula, ap.terfor.Formula, String)]

        val symbols =
          if (targetSet.isEmpty)
            intervalSet.symbols
          else
            targetSet.toList

        for (x <- symbols)
        {
          val i = intervalSet.getTermInterval(x)
            (i.lower, i.upper) match
            {
              case (IntervalVal(ll), _) =>
                {
                  val opt1 = (x === ll)
                  val opt2 = (x > ll)
                  val msg = "LowerBound split: " + opt1 + ", " + opt2
                  alternatives = (opt1.negate, opt2.negate, msg) :: alternatives
                }
              case (_, IntervalVal(ul)) =>
                {
                  val opt1 = (x === ul)
                  val opt2 = (x < ul)
                  val msg = "UpperBound split: " + opt1 + ", " + opt2
                  alternatives = (opt1.negate, opt2.negate, msg) :: alternatives
                }
              case _ => 
            }
        }

        alternatives
      }


      def negeqSplit(negeqs : ap.terfor.equations.NegEquationConj) : List[(ap.terfor.Formula, ap.terfor.Formula, String)] =
      {
        var alternatives = List() : List[(ap.terfor.Formula, ap.terfor.Formula, String)]

        // Lets try FIFO!
        for (negeq <- negeqs)
        {
          val negeq = negeqs.head
          val opt1 = (negeq > 0)
          val opt2 = (negeq < 0)
          val msg = "Negeq split on: " + negeq
          alternatives = (opt1.negate, opt2.negate, msg) :: alternatives
        }

        alternatives
      }

      def gapSplit(intervalSet : IntervalSet) : List[(ap.terfor.Formula, ap.terfor.Formula, String)] =
      {
        var alternatives = List() : List[(ap.terfor.Formula, ap.terfor.Formula, String)]
      
        val gaps = intervalSet.getGaps()
        for (gap <- gaps)
        {
          val (term, interval) = gap
          val opt1 = (term < interval.gap.get._1)
          val opt2 = (term > interval.gap.get._2)
          val msg = "Gap split on: " + gap
          alternatives = (opt1.negate, opt2.negate, msg) :: alternatives
        }

        alternatives
      }


      def doSplit(splitparams : (ap.terfor.Formula, ap.terfor.Formula, String)) : List[Plugin.Action] =
      {
        val (opt1, opt2, msg) = splitparams
        val opt1act = Conjunction.conj(List(opt1, Conjunction.TRUE), goal.order)
        val opt2act = Conjunction.conj(List(opt2, Conjunction.TRUE), goal.order)
        val splitgoal = Plugin.SplitGoal(List(List(Plugin.AddFormula(opt1act)), List(Plugin.AddFormula(opt2act))))
        return List(splitgoal)
      }

      /*
       
       END OF SPLITTING STRATEGIES

       */

      val intervalSet = new IntervalSet(
        preds,
        ineqs.map(lcToPolynomial).toList,
        negeqs.map(lcToPolynomial).toList)

      intervalSet.propagate()

      val targetSet = linearizers(predicates.toList).toList.sortWith((s1, s2) => s1.size > s2.size).head

      val negAlternatives = negeqSplit(negeqs)
      if (!negAlternatives.isEmpty)
        return doSplit(negAlternatives.head)

/*
      val gapAlternatives = gapSplit(intervalSet)
      if (!gapAlternatives.isEmpty)
        return doSplit(gapAlternatives.head)
*/

      // Removed parameters since we do not want to do spherical anywas

      val infdespAlternatives = infinitySplit(intervalSet, targetSet) ++ desperateSplit(intervalSet, targetSet)
      if (!infdespAlternatives.isEmpty)
      {
        // Let's try to find a decent splitting target
        for ((opt1, opt2, msg) <- infdespAlternatives)
        {
          val allFormulas = goal reduceWithFacts conj(List(opt1, opt2)).negate
          if (!allFormulas.isFalse)
          {
            return doSplit((opt1, opt2, msg))
          }
        }
      }

      List()
    }
  }



  //////////////////////////////////////////////////////////////////////////////

  val plugin = Some(new Plugin {

    var oldGBSrc = None : Option[Basis]
    var oldGBRes = None : Option[Basis]

    def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] =
    {
      println("GENERATE AXIOMS?")
      None
    }


    override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
    {
      import TerForConvenience._

      import scala.collection.mutable.Map
      implicit val _ = goal.order

      // First move from unprocessed => passive - reducing all polynomials in active
      // Then move from passive to active => adding all s-polynomials to unprocessed
      def Buchberger_improved_aux(active : Basis, passive : Basis, unprocessed
          : Basis) : Basis =
      {
        Timeout.check

        implicit val _ = active.ordering

        if (!unprocessed.isEmpty)
        {
          val reducingBasis = active.copy()
          reducingBasis.addBasis(passive)

          val newPoly = reducingBasis.ReducePolynomial(unprocessed.get())

          val restPoly = unprocessed

          if (newPoly.isZero)
          {
            return Buchberger_improved_aux(active, passive, restPoly)
          }


          // Reduce all polynomials in active w.r.t. newPoly
          val activeReduced =
            for (pA <- active.toList;
              if (pA.LT.isDividedBy(newPoly.LT) && pA.ReduceBy(newPoly) != pA))
            yield
              pA

          val newActive = new Basis()
          for (pA <- active.toList;
            if (!(pA.LT.isDividedBy(newPoly.LT) && pA.ReduceBy(newPoly) != pA)))
            newActive.add(pA)

          // Reduce all polynomials in passive w.r.t. newPoly
          val passiveReduced =
            for (pA <- passive.toList;
              if (pA.LT.isDividedBy(newPoly.LT) && pA.ReduceBy(newPoly) != pA))
            yield
              pA

          val newPassive = new Basis()
          for (pA <- passive.toList;
            if (!(pA.LT.isDividedBy(newPoly.LT) && pA.ReduceBy(newPoly) != pA)))
            newPassive.add(pA)

          newPassive.add(newPoly)



          var newUnprocessed = restPoly
          for (p <- activeReduced ++ passiveReduced)
          {
            if (!p.ReduceBy(newPoly).isZero)
              newUnprocessed.add(p.ReduceBy(newPoly))
          }

          return Buchberger_improved_aux(newActive, newPassive, newUnprocessed)
        }
        else if (!passive.isEmpty)
        {
          val newPoly = passive.get()
          val newPassive = passive.copy()

          val newUnprocessed = unprocessed

          for (p <- active.toList)
            if (newPoly.LT.hasCommonVariables(p.LT))
            {
              val spol = newPoly.SPOL(p)
              if (!spol.isZero)
                newUnprocessed.add(newPoly.SPOL(p))
            }

          val newActive = active.copy()
          newActive.add(newPoly)

          return Buchberger_improved_aux(newActive, newPassive, newUnprocessed)
        }
        else
        {
          return active
        }
      }

      def Buchberger_improved(basis : Basis) : Basis =
      {
        implicit val _ = basis.ordering
        Buchberger_improved_aux(new Basis, new Basis, basis)
      }



      def polynomialToAtom(p : Polynomial) : Conjunction =
      {
        def termToLc(t : Term) : LinearCombination =
        {
          if (t.m.pairs == Nil)
            t.c
          else
            l(t.c) * t.m.pairs.head._1
        }

        val lcs =
          for (t <- p.terms;
            if (!t.isZero))
          yield
            termToLc(t)

        val a = (lcs.tail).foldLeft(lcs.head) ((t1,t2) => t1 + t2)
        conj(a === 0)
      }

      // Create a list ordering
      var orderList = List() : List[ConstantTerm]
      var definedList = Set() : Set[ConstantTerm]

      val predicates = goal.facts.predConj.positiveLitsWithPred(_mul)

      if (predicates.isEmpty)
        return List()

      // Add all elements from LHS
      for (a <- predicates)
      {
        for (aa <- a(0) ++ a(1))
          aa._2 match
          {
            case (OneTerm) => ()
            case (x : ConstantTerm) => definedList += x
          }
      }

      // Remove all elements that occurs on RHS
      for (a <- predicates)
      {
        for (aa <- a(2))
          aa._2 match
          {
            case (x : ConstantTerm) => if (x.toString != "x" && x.toString != "y" && x.toString != "a" && x.toString != "b" && x.toString != "c" && x.toString != "d") definedList -= x
            case (OneTerm) => ()
          }
      }

      // Fix-point computation
      def genDefsymbols(predicates : List[Atom], defined : Set[ConstantTerm], undefined : List[ConstantTerm]) : List[ConstantTerm] =
      {
        if (predicates == Nil)
          undefined

        for (a <- predicates)
        {
          var allDefined = true
          for (aa <- a(0) ++ a(1))
          {
            aa._2 match
            {
              case (OneTerm) => ()
              case (x : ConstantTerm) => if (!defined.exists(xx => xx == x)) allDefined = false
            }
          }

          if (allDefined)
            a(2)(0)._2 match
            {
              case (OneTerm) =>
                return genDefsymbols(predicates diff List(a), defined, undefined)
              case (x : ConstantTerm) =>
                return genDefsymbols(predicates diff List(a), defined + x, x :: undefined)
            }

        }
        undefined.reverse
      }

      orderList = genDefsymbols(predicates.toList,definedList, List())

      implicit val monOrder = new PartitionOrdering(orderList, new GrevlexOrdering(new ListOrdering(orderList)))
      // implicit val monOrder = new GrevlexOrdering(new StringOrdering)

      val basis = new Basis()

      var factsToRemove = List() : List[ap.terfor.preds.Atom]

      for (a <- predicates)
      {
        val p = atomToPolynomial(a)
        if (p.isZero)
          factsToRemove = a :: factsToRemove
        else if (p.isConstant)
        {
          return List(Plugin.AddFormula(Conjunction.TRUE))
        }
        else
          basis.add(p)
      }

      val removeFactsAction = Plugin.RemoveFacts(conj(factsToRemove))

      val gb = 
        if (oldGBSrc.isEmpty || oldGBSrc.toSet != basis.toSet)
        {

          oldGBSrc = Some(basis)

          val gb =  Buchberger_improved(basis)

          val simplified = gb.Simplify()

          oldGBRes = Some(simplified)

          // Translate this to a linear system

          def makeMap(polylist : List[Polynomial]) : List[Monomial] =
          {
            var newmap = List() : List[Monomial]

            for (p <- polylist)
              for (t <- p.terms)
                if (!(newmap exists (x => x.toString == (t.m.toString))))
                {
                  if (t.m.linear)
                    newmap = t.m :: newmap
                  else
                    newmap = newmap ++ List(t.m)
                }
            newmap
          }

          def polyToRow(poly : Polynomial, map : List[Monomial]) : List[IdealInt] =
          {
            for (m <- map)
            yield
            {
              val termOpt = poly.terms find (x => x.m.toString == m.toString)
              termOpt match
              {
                case Some(term) => term.c
                case None => 0 : IdealInt
              }
            }
          }

          def makeMatrix(polylist : List[Polynomial]) : Array[Array[IdealInt]] =
          {
            var maxLength = 0
            var monomialMap = makeMap(polylist)
            val list =
              (for (p <- polylist)
              yield
              {
                polyToRow(p, monomialMap)
              }).toList

            val array = Array.ofDim[IdealInt](list.length, monomialMap.length)

            for (i <- 0 until list.length)
              for (j <- 0 until list(i).length)
                array(i)(j) = list(i)(j)

            array
          }

          def rowToPolynomial(map : List[Monomial], row : Array[IdealInt])(implicit ordering : monomialOrdering) =
          {
            var retPoly = new Polynomial(List())
            for (i <- 0 until row.length)
            {
              if (row(i) != 0)
                retPoly += new Term(row(i), map(i))
            }
            retPoly
          }

          val linearEq = simplified.toList

          if (!linearEq.isEmpty)
          {
            val map = makeMap(linearEq)
            val m = makeMatrix(linearEq)
            val gaussian = new Gaussian(m)

            val linearConj =
              conj(for (r <- gaussian.getRows();
                poly = rowToPolynomial(map, r);
                if (poly.linear))
              yield
                polynomialToAtom(poly))

            if (!linearConj.isTrue)
            {
              val allAxioms = Conjunction.conj(List(linearConj, Conjunction.TRUE),
                goal.order).negate
              return List(removeFactsAction, Plugin.AddFormula(allAxioms))
            }
          }
          gb
        }
        else
        {
          oldGBRes.get
        }

      // If gröbner basis calculation does nothing
      // Lets try to do some interval propagation

      val preds = (predicates.map(atomToPolynomial).toSet ++ gb.toSet).toList
      val ineqs = goal.facts.arithConj.inEqs
      val negeqs = goal.facts.arithConj.negativeEqs
      val intervalSet = new IntervalSet(
        preds,
        ineqs.map(lcToPolynomial).toList,
        negeqs.map(lcToPolynomial).toList)

      if (intervalSet.propagate())
      {
        throw new Exception("Interval propagation error, abort!")
      }

      val intervals = intervalSet.getIntervals();


      var intervalAtoms = List() : List[ap.terfor.inequalities.InEqConj]
      for ((ct, i, (ul, uu, gu)) <- intervals)
      {
        // Generate inequalities according to intervals
        if (ul)
        {
          i.lower match
          {
            case IntervalNegInf =>
            case IntervalPosInf => intervalAtoms = (ct > 0) :: (ct < 0) :: intervalAtoms
            case IntervalVal(v) => intervalAtoms = (ct >= v) :: intervalAtoms
          }
        }

        if (uu)
        {
          i.upper match
          {
            case IntervalNegInf => intervalAtoms = (ct > 0) :: (ct < 0) :: intervalAtoms
            case IntervalVal(v) => intervalAtoms = (ct <= v) :: intervalAtoms
            case IntervalPosInf =>
          }
        }
      }


      val allFormulas = goal reduceWithFacts conj(intervalAtoms).negate
      if (!allFormulas.isFalse)
      {
        return List(removeFactsAction, Plugin.AddFormula(allFormulas))
      }

      // If in final mode

      // At the moment, schedule a new task even when in final state
      // The only reason for this is to make sure that we don't give up,
      // and then conclude that a goal is satisfiable

/*      if (goal.tasks.finalEagerTask)
      {
        // Split directly!
        removeFactsAction :: (Splitter.handleGoal(goal)).toList
      }
      else */
      {
        // Skriva ut goal.tasks
        val scheduleAction = Plugin.ScheduleTask(Splitter, 0)
        List(removeFactsAction, scheduleAction)
      }

    }
  })

  TheoryRegistry register this

  override def toString = "GroebnerMultiplication"
}

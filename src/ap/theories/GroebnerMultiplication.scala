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
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{Term, TerForConvenience, TermOrder, ConstantTerm}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import ap.terfor.OneTerm


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
  val functionPredicateMapping = List(mul -> _mul)


  // Enable turning off and on debug printouts
    val DEBUG_MODE = false
    def printd(str : Any) = if (DEBUG_MODE) print(str)
    def printlnd(str : Any) = if (DEBUG_MODE) println(str)


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
      import TerForConvenience._

      // println("\n\n\t\t\tDesperate times requires desperate measures\n\n\n")


      // Find the "best" split
      def findSplit(intervalSet : IntervalSet) : List[(ap.terfor.Formula, ap.terfor.Formula, String)] =
      {
        var alternatives = List() : List[(ap.terfor.Formula, ap.terfor.Formula, String)]

        val allIntervals = intervalSet.getAllIntervals()
        for ((c, i) <- intervalSet.getAllIntervals())
        {
          (i.lower, i.upper) match
          {
            // if x = [-, +], split at zero
            case (IntervalNegInf(), IntervalPosInf()) =>
              {
                val opt1 = (c < 0)
                val opt2 = (c >= 0)
                val msg = "[-Inf, +Inf] split: " + opt1 + ", " + opt2
                alternatives = (opt1.negate, opt2.negate, msg) :: alternatives
              }
            case _ =>
          }
        }

        for (x <- intervalSet.symbols)
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

      // Extract all predicates
      val predicates = goal.facts.predConj.positiveLitsWithPred(_mul)
      val preds = predicates.map(atomToPolynomial).toList
      val ineqs = goal.facts.arithConj.inEqs
      val negeqs = goal.facts.arithConj.negativeEqs
      val intervalSet = new IntervalSet(
        preds,
        ineqs.map(lcToPolynomial).toList,
        negeqs.map(lcToPolynomial).toList)

      intervalSet.propagate()


      val split = findSplit(intervalSet)

      if (!split.isEmpty)
      {
        // Let's try to find a decent splitting target
        for ((opt1, opt2, msg) <- split)
        {
          val allFormulas = goal reduceWithFacts conj(List(opt1, opt2)).negate
          if (!allFormulas.isFalse)
          {
            printlnd(msg)
            val opt1act = Conjunction.conj(List(opt1, Conjunction.TRUE), goal.order)
            val opt2act = Conjunction.conj(List(opt2, Conjunction.TRUE), goal.order)
            val splitgoal = Plugin.SplitGoal(List(List(Plugin.AddFormula(opt1act)), List(Plugin.AddFormula(opt2act))))
            return List(splitgoal)
          }
        }
      }

      List()
    }
  }










  //////////////////////////////////////////////////////////////////////////////

  val plugin = Some(new Plugin {

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

      printlnd("\n\nGroebnerMultiplication")
      printlnd("\nGoal.facts: " + goal.facts)
      printlnd("\tTrying to calculate Groebner Basis")

      val basis = new Basis()

      var factsToRemove = List() : List[ap.terfor.preds.Atom]

      for (a <- predicates)
      {
        val p = atomToPolynomial(a)
        if (!p.isZero)
          basis.add(p)
        else
          factsToRemove = a :: factsToRemove
      }

      val removeFactsAction = Plugin.RemoveFacts(conj(factsToRemove))

      val gb =  Buchberger_improved(basis)

      val simplified = gb.Simplify()


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
            val poly = rowToPolynomial(map, r);
            if (poly.linear))
          yield
            polynomialToAtom(poly))

        if (!linearConj.isTrue)
        {
          val allAxioms = Conjunction.conj(List(linearConj, Conjunction.TRUE),
            goal.order).negate
          printlnd("\tFound linear formulas!")
          printlnd("\t\t" + allAxioms)
          return List(removeFactsAction, Plugin.AddFormula(allAxioms))
        }
      }

      // If gröbner basis calculation does nothing
      // Lets try to do some interval propagation

      printlnd("\tGroebner failed, trying interval propagation")

      val preds = (predicates.map(atomToPolynomial).toSet ++ gb.toSet).toList
      val ineqs = goal.facts.arithConj.inEqs
      val negeqs = goal.facts.arithConj.negativeEqs
      val intervalSet = new IntervalSet(
        preds,
        ineqs.map(lcToPolynomial).toList,
        negeqs.map(lcToPolynomial).toList)

      intervalSet.propagate()


      val intervals = intervalSet.getIntervals();

      if (!intervals.isEmpty)
        printlnd("\tPropagation result: ")

      var intervalAtoms = List() : List[ap.terfor.inequalities.InEqConj]
      for ((ct, i, (ul, uu, gu)) <- intervals)
      {
        printd("\t\t" + ct + ": (")

        if (ul)
          printd(">")
        printd(i.lower)
        if (ul)
          printd("<")
        printd(", ")
        if (uu)
          printd(">")
        printd(i.upper)
        if (uu)
          printd("<")
        printd(") ")
        printd("gap: " + i.gap)
        printd("\n")

        // Generate inequalities according to intervals
        if (ul)
        {
          i.lower match
          {
            case IntervalNegInf() =>
            case IntervalPosInf() => intervalAtoms = (ct > 0) :: (ct < 0) :: intervalAtoms
            case IntervalVal(v) => intervalAtoms = (ct >= v) :: intervalAtoms
          }
        }

        if (uu)
        {
          i.upper match
          {
            case IntervalNegInf() => intervalAtoms = (ct > 0) :: (ct < 0) :: intervalAtoms
            case IntervalVal(v) => intervalAtoms = (ct <= v) :: intervalAtoms
            case IntervalPosInf() =>
          }
        }
      }


      val allFormulas = goal reduceWithFacts conj(intervalAtoms).negate
      if (!allFormulas.isFalse)
      {
        printlnd("\tReturning axioms: " + allFormulas.negate)
        return List(removeFactsAction, Plugin.AddFormula(allFormulas))
      }

      // Do splitting
      printlnd("\tInterval propagation failed, splitting")
      if (!negeqs.isEmpty)
        printlnd("\t\tNegeq split: ")
      for (eq <- negeqs)
        printlnd("\t\t\t" + eq)

      // Lets try FIFO!
      if (!negeqs.isEmpty)
      {
        val negeq = negeqs.head
        printlnd("\t\tnegeq (" + negeq.getClass + "): " + negeq)
        val opt1 = (negeq > 0)
        val opt2 = (negeq < 0)
        printlnd("\t\t\topt1: " + opt1)
        printlnd("\t\t\topt2: " + opt2)
        val opt1act  = Conjunction.conj(List(opt1.negate, Conjunction.TRUE), goal.order)
        val opt2act  = Conjunction.conj(List(opt2.negate, Conjunction.TRUE), goal.order)
        val actionList = List(List(Plugin.AddFormula(opt1act)), List(Plugin.AddFormula(opt2act)))
        val splitgoal = Plugin.SplitGoal(actionList)
        printlnd("\tReturning: " + splitgoal)
        return List(removeFactsAction, Plugin.SplitGoal(actionList))
      }

      val gaps = intervalSet.getGaps()

      if (!gaps.isEmpty)
      {
        printlnd("\tGap split:")
        for ((ct, i) <- gaps)
        {
          printd("\t\t" + ct + ": (")
          printd(i.lower)
          printd(", ")
          printd(i.upper)
          printd(") gap (" + i.gap + ")\n")
        }

        val (term, interval) = gaps.head
        val opt1 = (term < interval.gap.get._1)
        val opt2 = (term > interval.gap.get._2)

        printlnd("\t\t\topt1: " + opt1)
        printlnd("\t\t\topt2: " + opt2)
        val opt1act  = Conjunction.conj(List(opt1.negate, Conjunction.TRUE), goal.order)
        val opt2act  = Conjunction.conj(List(opt2.negate, Conjunction.TRUE), goal.order)
        val actionList = List(List(Plugin.AddFormula(opt1act)), List(Plugin.AddFormula(opt2act)))
        val splitgoal = Plugin.SplitGoal(actionList)
        printlnd("\tReturning: " + splitgoal)
        return List(Plugin.SplitGoal(actionList))
      }




      printlnd("\tRemoving facts: " + removeFactsAction)
      val scheduleAction = Plugin.ScheduleTask(Splitter, 0)
      List(removeFactsAction, scheduleAction)

    }
  })

  TheoryRegistry register this
}

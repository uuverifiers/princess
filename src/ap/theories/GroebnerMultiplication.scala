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
import ap.proof.theoryPlugins.Plugin
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{Term, TerForConvenience, TermOrder, ConstantTerm}

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


  //////////////////////////////////////////////////////////////////////////////

  val plugin = Some(new Plugin {

   def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = 
   {
     None
   }

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
    {
      import TerForConvenience._
      import ap.terfor.linearcombination.LinearCombination
      import ap.terfor.preds.Atom

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

      import ap.terfor.OneTerm

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

      for (a <- predicates)
      {
        val p = atomToPolynomial(a)
        if (!p.isZero)
          basis.add(p)
      }


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
          return List(Plugin.AddFormula(allAxioms))
        }
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

      intervalSet.propagate()

      val intervals = intervalSet.getIntervals();

      var intervalAtoms = List() : List[ap.terfor.inequalities.InEqConj]
      for ((ct, i, (ul, uu, gu)) <- intervals)
      {
        // Generate inequalities according to intervals
        if (ul)
          intervalAtoms = (ct >= i.lower.get) :: intervalAtoms

        if (uu)
          intervalAtoms = (ct <= i.upper.get) :: intervalAtoms
      }


      val intervalAxioms = goal.reduceWithFacts(conj(intervalAtoms))

      if (!intervalAxioms.isTrue)
      {
        val allAxioms = Conjunction.conj(List(intervalAxioms, Conjunction.TRUE),
          goal.order).negate
        return List(Plugin.AddFormula(allAxioms))
      }

      // Do splitting
      // Lets try FIFO!
      if (!negeqs.isEmpty)
      {
        val negeq = negeqs.head
        val opt1 = (negeq > 0).negate
        val opt2 = (negeq < 0).negate

        val opt1act  = Conjunction.conj(List(opt1, Conjunction.TRUE), goal.order)
        val opt2act  = Conjunction.conj(List(opt2, Conjunction.TRUE), goal.order)
        val actionList = List(List(Plugin.AddFormula(opt1act)), List(Plugin.AddFormula(opt2act)))
        val splitgoal = Plugin.SplitGoal(actionList)
        return List(Plugin.SplitGoal(actionList))
      }

      val gaps = intervalSet.getGaps()

      if (!gaps.isEmpty)
      {
        val (term, interval) = gaps.head
        val opt1 = (term < interval.gap.get._1).negate
        val opt2 = (term > interval.gap.get._2).negate


        val opt1act  = Conjunction.conj(List(opt1, Conjunction.TRUE), goal.order)
        val opt2act  = Conjunction.conj(List(opt2, Conjunction.TRUE), goal.order)
        val actionList = List(List(Plugin.AddFormula(opt1act)), List(Plugin.AddFormula(opt2act)))
        val splitgoal = Plugin.SplitGoal(actionList)
        return List(Plugin.SplitGoal(actionList))
      }


      def findSplit : List[ap.proof.theoryPlugins.Plugin.SplitGoal] = 
      {
        val allIntervals = intervalSet.getAllIntervals()
        for ((c, i) <- allIntervals)
        {
          (i.lower, i.upper) match
          {
            // if x = [-, +], split at zero
            case (IntervalNegInf(), IntervalPosInf()) => 
            {
              val opt1 = (c < 0).negate
              val opt2 = (c >= 0).negate
              val opt1act = Conjunction.conj(List(opt1, Conjunction.TRUE), goal.order)
              val opt2act = Conjunction.conj(List(opt2, Conjunction.TRUE), goal.order)
              val splitgoal = Plugin.SplitGoal(List(List(Plugin.AddFormula(opt1act)), List(Plugin.AddFormula(opt2act))))
              return List(splitgoal)
            }
            case _ => 
          }
        }

        for (p <- predicates)
        {
          val symbols = p(0) ++ p(1) ++ p(2)

          for (s <- symbols)
          {
            s._2 match
            {
              case (OneTerm) => ()
              case (x : ConstantTerm) => 
                {
                  val i = intervalSet.getTermInterval(x)
                  val (opt1, opt2) =
                    (i.lower, i.upper) match
                    {
                      case (IntervalVal(ll), _) => ((x === ll).negate, (x > ll).negate)
                      case (_, IntervalVal(ul)) => ((x === ul).negate, (x < ul).negate)
                      case _ => throw new Exception("Double-Infitity-Ended intervals should have been split already")
                    }
                  // val opt1 = (x >).negate
                  // val opt2 = (x < 0)
                  val opt1act = Conjunction.conj(List(opt1, Conjunction.TRUE), goal.order)
                  val opt2act = Conjunction.conj(List(opt2, Conjunction.TRUE), goal.order)
                  val splitgoal = Plugin.SplitGoal(List(List(Plugin.AddFormula(opt1act)), List(Plugin.AddFormula(opt2act))))
                  return List(splitgoal)
                }
            }
          }
        }

        return List()
      }

      val s = findSplit
      s
    }
  })

  TheoryRegistry register this
}

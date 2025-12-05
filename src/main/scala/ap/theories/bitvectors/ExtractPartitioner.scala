/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2025 Philipp Ruemmer <ph_r@gmx.net>
 *               2019      Peter Backeman <peter@backeman.se>
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

package ap.theories.bitvectors

import ap.theories._

import ap.basetypes.IdealInt
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.terfor.{Term, Formula, TermOrder, ConstantTerm, TerForConvenience,
                  VariableTerm}
import ap.terfor.linearcombination.{LinearCombination, LinearCombination0}
import ap.terfor.preds.Atom
import ap.terfor.conjunctions.Conjunction
import ap.util.{Debug, Seqs}

import scala.collection.mutable.{ArrayBuffer, Map => MMap}

/**
 * Partition extract-atoms for given terms to eliminate overlapping extracts.
 */
object ExtractPartitioner extends TheoryProcedure {
  import ModuloArithmetic._
  import LinearCombination.SingleTerm
  import TerForConvenience._

  def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
    implicit val order = goal.order
    val predConj = goal.facts.predConj
    val extracts = predConj.positiveLitsWithPred(_bv_extract)

    //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
    Debug.assertInt(AC,
      extracts.forall{ ex =>
        ex(0).asInstanceOf[LinearCombination0].constant.signum >= 0 &&
        ex(1).asInstanceOf[LinearCombination0].constant.signum >= 0 })
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    val extractedConsts =
      (for (Seq(_, _, SingleTerm(c : ConstantTerm), _) <- extracts.iterator)
       yield c).toSet

    // TODO: also handle bvand here!

    val diseqs = for (lc <- goal.facts.arithConj.negativeEqs;
                      if !Seqs.disjoint(lc.constants, extractedConsts))
                 yield lc
    val partitions = computeCutPoints(extracts, diseqs)

    //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
    if (debug && !partitions.isEmpty) {
      println("<<Partitions>>")
      for ((k, v) <- partitions){
        println("\t" + k + " --> " + v)
      }
    }
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    splitExtractActions(extracts, partitions, goal)   elseDo
    splitDisequalityActions(diseqs, partitions, goal)
  }

  private def splitExtractActions(extracts : Seq[Atom],
                                  partitions : Map[Term, List[Int]],
                                  goal : Goal)
                                 (implicit order : TermOrder)
                                : Seq[Plugin.Action] = {
    val res =
    for (ex <- extracts;
         action <- ex(2) match {
           case SingleTerm(c : ConstantTerm) =>
             splitExtract(ex, partitions(c))
           case _ =>
             List()
         }) 
    yield action

    //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
    if (!res.isEmpty && debug) {
      println("Splitting extracts")
      for (t <- res)
        println("\t" + t)
    }
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    res
  }

  /**
   * Splitting of disequalities x != N or x != y
   */
  private def splitDisequalityActions(disequalities : Seq[LinearCombination],
                                      partitions : Map[Term, List[Int]],
                                      goal : Goal)
                                     (implicit order : TermOrder)
                                    : Seq[Plugin.Action] = {
    val res =
    for (diseq <- disequalities;
         lhs = diseq(0)._2;
         parts <- (partitions get lhs).toSeq;
         action <- splitDiseq(diseq, parts, goal))
    yield action

    //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
    if (!res.isEmpty && debug) {
      println("Splitting disequalities actions:")
      for (t <- res)
        println("\t" + t)
    }
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    res
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  //   |EXTRACT| PROPAGATION
  //
  // Extract uses SMT-lib semantics
  // If we have extract(7,3)....
  // What are cut-points.
  // They should represent points in between which we have intervas
  // We should let the first arugment be exclusive
  // e.g., extract(7,3) is cut-point 8 and 3
  // Thus, when looping we get (7,3) and (2,0) in SMT-lib semantics

  private def getExtracts(goal : Goal) : Seq[Atom] = {
    // first check if congruence closure has been fully applied

    val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)

    var lastAtom : Atom = null
    val atomIt = extracts.iterator
    while (atomIt.hasNext) {
      val a = atomIt.next()
      
      if (a(2).isConstant)
        // extract can be evaluated, delay all operations on extracts
        return List()
        
      if (lastAtom != null &&
          lastAtom(0) == a(0) && lastAtom(1) == a(1) && lastAtom(2) == a(2))
        // a case where functionality axiom can be applied;
        // in this case, delay all operations of the extracts
        return List()
        
      lastAtom = a
    }

    extracts
  }

  // This propagates all cut-points from lhs <-> rhs in extract

  private def propagateExtract(extract : (Int, Int, ConstantTerm, ConstantTerm),
                               cutPoints : MMap[Term, Set[Int]]) : Boolean = {
    val (ub, lb, t1, t2) = extract

    var changed = false

    val cut1 = cutPoints.getOrElse(t1, Set())
    val cut2 = cutPoints.getOrElse(t2, Set())

    /// T1 ===> T2
    val t1transformed =
      cut1.map(_ - lb).filter(c => c > 0 && c <= ub - lb + 1)

    if (!(t1transformed subsetOf cut2)) {
      cutPoints += t2 -> (cut2 ++ t1transformed)
      changed = true
    }

    // propagate FROM t2 TO t1
    val t2transformed = cut2.map(_ + lb).filter(c => c <= ub)

    if (!(t2transformed subsetOf cut1)) {
      cutPoints += t1 -> (cut1 ++ t2transformed)
      changed = true
    }

    //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
    Debug.assertInt(AC, cutPoints.values.flatten.forall(_ >= 0))
    //-END-ASSERTION-/////////////////////////////////////////////////////////

    changed
  }

  private def propagateDisequality(disequality : (ConstantTerm, ConstantTerm),
                                   cutPoints : MMap[Term, Set[Int]])
                                 : Boolean = {
    val (t1, t2) = disequality
    var changed = false

    val t1cuts = cutPoints.getOrElse(t1, Set())
    val t2cuts = cutPoints.getOrElse(t2, Set())
        
    if (!(t1cuts subsetOf t2cuts)) {
      cutPoints += t2 -> (t2cuts ++ t1cuts)
      changed = true
    }

    if (!(t2cuts subsetOf t1cuts)) {
      cutPoints += t1 -> (t1cuts ++ t2cuts)
      changed = true
    }

    changed
  }

  private def computeCutPoints(extracts : Seq[Atom],
                               disequalities : Seq[LinearCombination])
                             : Map[Term, List[Int]] = {
    val cutPoints = MMap() : MMap[Term, Set[Int]]
    val extractTuples = new ArrayBuffer[(Int, Int, ConstantTerm, ConstantTerm)]
    val diseqTuples = new ArrayBuffer[(ConstantTerm, ConstantTerm)]

    for (Seq(LinearCombination.Constant(IdealInt(ub)),
             LinearCombination.Constant(IdealInt(lb)),
             SingleTerm(t : ConstantTerm),
             res) <- extracts) {
      cutPoints += t -> (Set(lb, ub+1) ++ (cutPoints.getOrElse(t, Set())))
      res match {
        case SingleTerm(s : ConstantTerm) =>
          extractTuples += ((ub, lb, t, s))
        case _ =>
          // nothing
      }
    }

    for (lc <- disequalities)
      if (lc.size == 2 &&
          lc.getCoeff(0) == IdealInt.ONE &&
          lc.getCoeff(1) == IdealInt.MINUS_ONE &&
          lc.constants.size == 2)
        diseqTuples += ((lc.getTerm(0).asInstanceOf[ConstantTerm],
                         lc.getTerm(1).asInstanceOf[ConstantTerm]))

    var changed = true
    while (changed) {
      changed = false
      for (t <- extractTuples) {
        if (propagateExtract(t, cutPoints))
          changed = true
      }

      for (diseq <- diseqTuples) {
        if (propagateDisequality(diseq, cutPoints))
          changed = true
      }
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(AC, cutPoints.values.flatten.forall(_ >= 0))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    cutPoints.map{case (k, v) => k -> v.toList.sorted.reverse}.toMap
  }


  ///////////////////////////
  //
  // EXTRACT (and Diseq) SPLIT FUNCTIONS
  //
  //
  //
  // PRE-CONDITION: parts must have been created using extract (i.e., we can't have
  // extract(1,3) and parts being (0,2) ^ (2,4), but parts should be (0,1) ^ (1,2) ^ (2,3) ^ (3,4)
  private def splitExtract(extract : Atom, cutPoints : List[Int])
                          (implicit order : TermOrder) : List[Plugin.Action] = {
    import TerForConvenience._

    val Seq(LinearCombination.Constant(IdealInt(upper)),
            LinearCombination.Constant(IdealInt(lower)),
            t1, t2) = extract

    var filterCutPoints = cutPoints.filter(x => x >= lower && x <= upper)

    if (filterCutPoints.length < 2) {
      List()
    } else {
      var curPoint = upper
      var newExtracts = List() : List[Conjunction]

      while (!filterCutPoints.isEmpty) {
        val (ub, lb) = (curPoint, filterCutPoints.head)
        filterCutPoints = filterCutPoints.tail
        curPoint = lb - 1

        val bv1 =
          Atom(_bv_extract,
               List(l(ub),       l(lb),       l(t1), l(v(0))), order)
        val bv2 =
          Atom(_bv_extract,
               List(l(ub-lower), l(lb-lower), l(t2), l(v(0))), order)
        val domain = List(l(v(0)) >= 0, l(v(0)) < pow2(ub-lb+1))
        newExtracts = forall(!conj(bv1 :: bv2 :: domain)) :: newExtracts
      }
      Plugin.RemoveFacts(extract) ::
      (for (c <- newExtracts)
       yield Plugin.AddAxiom(List(extract), !c, ModuloArithmetic))
    }
  }

  private def splitDiseq(disequality : LinearCombination,
                         cutPoints : List[Int], goal : Goal)
                        (implicit order : TermOrder) : List[Plugin.Action] = {
    import TerForConvenience._

    // Make sure c1 != c2 according to cutPoints
    def split(c1 : Term, c2 : Term) : List[Plugin.Action] = {
      val upperBounds : List[IdealInt] = (List(c1,c2).map{
        x => {
          val lc = LinearCombination(IdealInt.MINUS_ONE, x, order)
          goal.facts.arithConj.inEqs.findLowerBound(lc) match {
            case Some(b) => -b
            case None => IdealInt(0)
          }
        }})

      // TODO: Can equality between bit-vectors of diff size be equal?
      val upper = upperBounds.max

      if (upper.signum <= 0)
        return List()

      val bits = upper.getHighestSetBit + 1
      val remCutPoints = for (p <- cutPoints; if 0 < p && p < bits) yield p
      val allPoints = bits :: remCutPoints ::: List(0)

      // We store with upper bound non-exclusive
      var curPoint = allPoints.head - 1
      var iterPoints = allPoints.tail
      var newExtracts = List() : List[Formula]
      var variables = List() : List[(VariableTerm, Int)]

      if (iterPoints.length == 1)
        return List()

      while (!iterPoints.isEmpty) {
        val ub = curPoint
        val lb = iterPoints.head
        iterPoints = iterPoints.tail

        val bitLength = ub - lb + 1
        curPoint = lb - 1

        val (v1, v2) = (v(variables.length), v(variables.length+1))
        variables = (v2, bitLength) :: (v1, bitLength) :: variables
        val (tmp1, tmp2) = (l(v1), l(v2))

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, ub >= 0)
        Debug.assertInt(AC, lb >= 0)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        val bv1 = Atom(_bv_extract, List(l(ub), l(lb), l(c1), tmp1), order)
        val bv2 = Atom(_bv_extract, List(l(ub), l(lb), l(c2), tmp2), order)

        val upper = pow2MinusOne(bitLength)
        newExtracts =
          (tmp1 >= 0) :: (tmp1 <= upper) ::
          (tmp2 >= 0) :: (tmp2 <= upper) :: bv1 :: bv2 :: newExtracts
      }

      val diseqs =
        (for (List((v1, bl1), (v2, bl2)) <- variables.sliding(2,2)) yield {
          // TODO: Remove this if domains are not relevant
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, bl1 == bl2)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          v1 === v2
          // conj(v1 >= 0, v1 < pow2(bl1), v2 >= 0, v2 < pow2(bl2), v1 === v2)
        })

      val subFormula = conj(newExtracts) & !conj(diseqs)
      val finalConj = exists(variables.length, subFormula)
      (Plugin.RemoveFacts(disequality =/= 0)) ::
       List(Plugin.AddAxiom(List(disequality =/= 0),
                            finalConj,
                            ModuloArithmetic))
    }

    if (cutPoints.isEmpty) {
      List()
    } else if (disequality.constants.size == 1) {
      // -Constant and Integer
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, disequality.leadingCoeff.isOne)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      split(disequality.leadingTerm, l(-disequality.constant))
    } else if (disequality.constants.size == 2 &&
               disequality.constant.isZero &&
               disequality.getCoeff(0).isOne &&
               disequality.getCoeff(1).isMinusOne) {
      split(disequality.getTerm(0), disequality.getTerm(1))
    } else {
      //println("WARNING: cannot split " + disequality)
      List()
    }
  }

}

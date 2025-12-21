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
import ap.parameters.Param
import ap.proof.theoryPlugins.{Plugin, TheoryProcedure}
import ap.proof.goal.Goal
import ap.terfor.{Term, Formula, TermOrder, ConstantTerm, TerForConvenience,
                  VariableTerm}
import ap.terfor.linearcombination.{LinearCombination, LinearCombination0}
import ap.terfor.preds.Atom
import ap.terfor.conjunctions.Conjunction
import ap.util.{Debug, Seqs}

import scala.collection.mutable.{ArrayBuffer, Map => MMap, HashSet => MHashSet,
                                 HashMap => MHashMap}

/**
 * Partition extract-atoms for given terms to eliminate overlapping extracts.
 */
object ExtractPartitioner extends TheoryProcedure {
  import ModuloArithmetic._
  import LinearCombination.SingleTerm
  import TerForConvenience._

  def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
    extractFunctionality(goal)  elseDo
 //   compressExtractChains(extracts, goal) elseDo
    splitActions(goal)
  }

  private def extractFunctionality(goal : Goal) : Seq[Plugin.Action] =
    if (Param.PROOF_CONSTRUCTION(goal.settings)) {
      // If proofs are enabled, we have to apply the functional consistency
      // axiom manually
      implicit val order = goal.order
      val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)

      (for (Seq(a, b) <- extracts.sliding(2); if Atom.sameFunctionApp(a, b))
       yield {
         //-BEGIN-ASSERTION-////////////////////////////////////////////////////
         if (debug) {
           println(s"Extract functional consistency $a, $b")
         }
         //-END-ASSERTION-//////////////////////////////////////////////////////
         List(Plugin.RemoveFacts(b),
              Plugin.AddAxiom(List(a, b), a.last === b.last, ModuloArithmetic))
       }).toVector.flatten
    } else {
      List()
    }

  /**
   * Rewrite nested extracts to refer to the original bitvector, replacing the
   * intermediate result with an arithmetic expression of the final extracted
   * bitvectors.
   */
  private def compressExtractChains(extracts : Seq[Atom], goal : Goal)
                                   (implicit order : TermOrder)
                                 : Seq[Plugin.Action] = {
    val sources = extracts.groupBy(_(2))

    val toRemove = new MHashSet[Atom]
    val actions = new ArrayBuffer[Plugin.Action]

    for (leg1 <- extracts) {
      val LinearCombination.Constant(upper) = leg1(0)
      val LinearCombination.Constant(lower) = leg1(1)
      val bv1 = leg1(2)
      val bv2 = leg1(3)

      if (!toRemove.contains(leg1) && sources.contains(bv2)) {
        val leg2s = sources(bv2)

        var curUpper = upper - lower
        val leg2ToRewrite = new ArrayBuffer[Atom]
        for (leg2 <- leg2s) {
          val LinearCombination.Constant(locUpper) = leg2(0)
          if (locUpper == curUpper && !toRemove.contains(leg2)) {
            val LinearCombination.Constant(locLower) = leg2(1)
            curUpper = locLower - 1
            leg2ToRewrite += leg2
          }
        }

        if (curUpper.isMinusOne) {
          // we can go ahead and compress this chain
          toRemove += leg1
          toRemove ++= leg2ToRewrite

          val newAtoms = new ArrayBuffer[Atom]
          val bv2Def = new ArrayBuffer[(IdealInt, LinearCombination)]

          bv2Def += ((IdealInt.MINUS_ONE, bv2))

          for (leg2 <- leg2ToRewrite) {
            val bv3 = leg2(3)
            val LinearCombination.Constant(locUpper) = leg2(0)
            val LinearCombination.Constant(locLower) = leg2(1)
            newAtoms +=
              Atom(_bv_extract,
                   List(l(locUpper + lower), l(locLower + lower), bv1, bv3),
                   order)
            bv2Def += ((pow2(locLower), bv3))
          }

          val oldAtoms = leg2ToRewrite.toSeq :+ leg1
          val forToAdd = conj(newAtoms.toSeq :+ (sum(bv2Def) === 0))

          actions += Plugin.AddAxiom(oldAtoms, forToAdd, ModuloArithmetic)

          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          if (debug) {
            println("Compressing extracts")
            for (t <- oldAtoms)
            println("\t" + t)
          }
          //-END-ASSERTION-/////////////////////////////////////////////////////

        }
      }
    }

    if (!toRemove.isEmpty)
      actions += Plugin.RemoveFacts(conj(toRemove))

    actions.toSeq
  }

  /**
   * Partition bv_extract and binary bitwise operator application to eliminate
   * overlapping ranges.
   */
  def splitActions(goal           : Goal,
                   extraCutPoints : Seq[(Term, Seq[Int])] = List())
                                  : Seq[Plugin.Action] = {
    implicit val order = goal.order
    val extracts = goal.facts.predConj.positiveLitsWithPred(_bv_extract)

    val binOps = goal.facts.predConj.positiveLitsWithPred(_bv_and) ++
                 goal.facts.predConj.positiveLitsWithPred(_bv_xor)
    val partitions = computeCutPoints(extracts, binOps, extraCutPoints)

    //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
    if (debug && !partitions.isEmpty) {
      println("<<Partitions>>")
      for ((k, v) <- partitions){
        println("\t" + k + " --> " + v)
      }
    }
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    splitExtractActions(extracts, partitions, goal) ++
    splitBinOpActions(binOps, partitions, goal)
  }

  private def splitExtractActions(extracts   : Seq[Atom],
                                  partitions : Map[Term, Seq[Int]],
                                  goal       : Goal)
                                 (implicit order : TermOrder)
                                : Seq[Plugin.Action] = {
    val res =
      for (ex <- extracts; action <- splitExtract(ex, partitions(ex(2))))
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

  private def splitBinOpActions(binOps     : Seq[Atom],
                                partitions : Map[Term, Seq[Int]],
                                goal       : Goal)
                               (implicit order : TermOrder)
                              : Seq[Plugin.Action] = {
    val res =
      for (op <- binOps;
           action <- splitBinOp(op, partitions.getOrElse(op(1), List())))
      yield action

    //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
    if (!res.isEmpty && debug) {
      println("Splitting binary operator")
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

  // This propagates all cut-points from lhs <-> rhs in extract

  def computeCutPoints(extracts       : Seq[Atom],
                       binOps         : Seq[Atom],
                       extraCutPoints : Seq[(Term, Seq[Int])])
                                      : Map[Term, Seq[Int]] = {
    val prop = new CutPropagator
    extracts.foreach(prop.setupExtract)
    binOps.foreach(prop.setupBinOp)

    for ((t, cuts) <- extraCutPoints)
      prop.addCutPoints(t, cuts)

    prop.runToFixpoint {
      extracts.foreach(prop.propagateExtract)
      binOps.foreach(prop.propagateBinOp)
    }

    prop.sortedCutPoints
  }

  class CutPropagator {
    private val cutPoints = new MHashMap[Term, Set[Int]]

    def getCutPoints(t : Term) : Set[Int] =
      cutPoints.getOrElse(t, Set())

    def sortedCutPoints : Map[Term, Seq[Int]] =
      cutPoints.toMap.transform { case (k, v) => v.toVector.sortBy(-_) }

    private var changedFlag = false

    def runToFixpoint(comp : => Unit) : Unit = {
      var cont = true
      while (cont) {
        changedFlag = false
        comp
        cont = changedFlag
      }
    }

    def addCutPoints(t : Term, points : Iterable[Int]) : Unit = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, points.forall(_ >= 0))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      t match {
        case LinearCombination.Constant(_) => // ignore constants
        case t => {
          val oldPoints = getCutPoints(t)
          val newPoints = oldPoints ++ points
          if (oldPoints.size != newPoints.size) {
            changedFlag = true
            cutPoints.put(t, newPoints)
          }
        }
      }
    }

    def setupExtract(extract : Atom) : Unit = {
      val Seq(LinearCombination.Constant(IdealInt(ub)),
              LinearCombination.Constant(IdealInt(lb)),
              arg, res) = extract
      addCutPoints(arg, List(lb, ub+1))
    }

    def setupBinOp(op : Atom) : Unit = {
      val Seq(LinearCombination.Constant(IdealInt(bits)), arg1, arg2, res) = op
      addCutPoints(arg1, List(0, bits))
    }

    def propagateNot(width : Int, t : Term) : Unit =
      t match {
        case t : LinearCombination => {
          val negT = t.scaleAndAdd(IdealInt.MINUS_ONE, pow2MinusOne(width))
          val cut1 = getCutPoints(t)
          val cut2 = getCutPoints(negT)
          addCutPoints(t, cut2)
          addCutPoints(negT, cut1)
        }
      }

    def propagateExtract(extract : Atom) : Unit = {
      val Seq(LinearCombination.Constant(IdealInt(ub)),
              LinearCombination.Constant(IdealInt(lb)),
              t1, t2) = extract

      val cut1 = getCutPoints(t1)
      val cut2 = getCutPoints(t2)

      /// T1 ===> T2
      addCutPoints(t2, cut1.map(_ - lb).filter(c => c >= 0 && c <= ub - lb + 1))

      // propagate FROM t2 TO t1
      addCutPoints(t1, cut2.map(_ + lb).filter(c => c <= ub))

//      propagateNot(ub - lb + 1, t2)
    }

    /**
     * Propagation for operators such as bv_and and bv_xor.
     */
    def propagateBinOp(op : Atom) : Unit = {
      val Seq(LinearCombination.Constant(IdealInt(bits)), arg1, arg2, res) = op

      val cut1 = getCutPoints(arg1)
      val cut2 = getCutPoints(arg2)
      val cut3 = getCutPoints(res)

      val cut1transformed = cut1.filter(c => c <= bits)
      val cut2transformed = cut2.filter(c => c <= bits)
      val cut3transformed = cut3.filter(c => c <= bits)
    
      addCutPoints(arg1, cut2transformed ++ cut3transformed)
      addCutPoints(arg2, cut1transformed ++ cut3transformed)
      addCutPoints(res,  cut1transformed ++ cut2transformed)

//      propagateNot(bits, arg1)
//      propagateNot(bits, arg2)
//      propagateNot(bits, res)
    }

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

  ///////////////////////////
  //
  // EXTRACT (and Diseq) SPLIT FUNCTIONS
  //
  //
  //
  // PRE-CONDITION: parts must have been created using extract (i.e., we can't have
  // extract(1,3) and parts being (0,2) ^ (2,4), but parts should be (0,1) ^ (1,2) ^ (2,3) ^ (3,4)
  private def splitExtract(extract : Atom, cutPoints : Seq[Int])
                          (implicit order : TermOrder) : Seq[Plugin.Action] = {
    import TerForConvenience._

    val Seq(LinearCombination.Constant(IdealInt(upper)),
            LinearCombination.Constant(IdealInt(lower)),
            t1, t2) = extract

    var filterCutPoints = cutPoints.filter(x => x >= lower && x <= upper)

    if (filterCutPoints.length < 2) {
      List()
    } else {
      var curPoint = upper
      var newExtracts = new ArrayBuffer[Conjunction]

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
        newExtracts += forall(!conj(bv1 :: bv2 :: domain))
      }
      Plugin.RemoveFacts(extract) +:
      (for (c <- newExtracts.toSeq)
       yield Plugin.AddAxiom(List(extract), !c, ModuloArithmetic))
    }
  }

  private def splitBinOp(op : Atom, cutPoints : Seq[Int])
                        (implicit order : TermOrder) : Seq[Plugin.Action] = {
    import TerForConvenience._

    val Seq(LinearCombination.Constant(IdealInt(bits)), arg1, arg2, res) = op

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, bits > 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val actions = new ArrayBuffer[Plugin.Action]
    for (Seq(ub, lb) <- cutPoints.filter(x => x <= bits).sliding(2))
      if (ub != bits || lb != 0) {
        val bv1 = Atom(_bv_extract, List(l(ub-1), l(lb), arg1, l(v(0))), order)
        val bv2 = Atom(_bv_extract, List(l(ub-1), l(lb), arg2, l(v(1))), order)
        val bv3 = Atom(_bv_extract, List(l(ub-1), l(lb), res,  l(v(2))), order)
        val nop = BitwiseOpSplitter.doBVOp(op.pred, ub - lb, l(v(0)), l(v(1)), l(v(2)))
        val domBound = pow2MinusOne(ub - lb)
        val domain = List(l(v(0)) >= 0, l(v(0)) <= domBound,
                          l(v(1)) >= 0, l(v(1)) <= domBound,
                          l(v(2)) >= 0, l(v(2)) <= domBound)
        val f = exists(exists(exists(conj(bv1 :: bv2 :: bv3 :: nop :: domain))))
        actions += Plugin.AddAxiom(List(op), f, ModuloArithmetic)
      }

    if (!actions.isEmpty)
      actions += Plugin.RemoveFacts(op)
    actions.toSeq
  }

  private def splitDiseq(disequality : LinearCombination,
                         cutPoints : List[Int], goal : Goal)
                        (implicit order : TermOrder) : Seq[Plugin.Action] = {
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

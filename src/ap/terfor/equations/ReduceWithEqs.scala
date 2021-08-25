/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2013 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.equations;

import ap.terfor._
import ap.terfor.linearcombination.{LinearCombination,
                                    LinearCombination0, LinearCombination1,
                                    LinearCombination2, LCBlender}
import ap.terfor.inequalities.InEqConj
import ap.terfor.arithconj.ArithConj
import ap.terfor.preds.{Atom, PredConj}
import ap.terfor.substitutions.VariableShiftSubst
import ap.basetypes.IdealInt
import ap.util.{Debug, Logic, Seqs, UnionMap, LazyMappedMap}

import scala.collection.mutable.{Buffer, ArrayBuffer}

/**
 * Reduce a term (currently: a linear combination) by rewriting with equations.
 * The equations have to be given in form of a mapping from atomic terms
 * (constants or variables) to linear combinations
 */
object ReduceWithEqs {

  private val AC = Debug.AC_PROPAGATION

  def apply(eqs : scala.collection.Map[Term, LinearCombination], order : TermOrder)
                                                  : ReduceWithEqs =
    new ReduceWithEqs (eqs, order)

  def apply(eqs : EquationConj, order : TermOrder) : ReduceWithEqs = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, eqs isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    new ReduceWithEqs(eqs.toMap, order)
  }
}

/**
 * Reduce a term (currently: a linear combination) by rewriting with equations.
 * The equations have to be given in form of a mapping from atomic terms
 * (constants or variables) to linear combinations
 */
class ReduceWithEqs private (equations : scala.collection.Map[Term, LinearCombination],
                             order : TermOrder) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(ReduceWithEqs.AC,
                   Logic.forall(for (t <- equations.keysIterator)
                                yield (t.isInstanceOf[ConstantTerm] ||
                                       t.isInstanceOf[VariableTerm])))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def isEmpty : Boolean = equations.isEmpty
  
  private lazy val containsVariables =
    equations exists { case (_, lc) => !lc.variables.isEmpty }

  def addEquations(furtherEqs : scala.collection.Map[Term, LinearCombination])
                                     : ReduceWithEqs = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithEqs.AC,
                    Seqs.disjoint(equations.keySet, furtherEqs.keySet))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (furtherEqs.isEmpty)
      this
    else
      new ReduceWithEqs(UnionMap(equations, furtherEqs), order)
  }

  /**
   * Create a <code>ReduceWithEqs</code> that can be used underneath
   * <code>num</code> binders. The conversion of de Brujin-variables is done on
   * the fly, which should give a good performance when the resulting
   * <code>ReduceWithEqs</code> is not applied too often (TODO: caching)
   */
  def passQuantifiers(num : Int) : ReduceWithEqs =
    if (containsVariables && num > 0)
      new ReduceWithEqs(
            new LazyMappedMap(
                 equations,
                 VariableShiftSubst.upShifter[Term](num, order),
                 VariableShiftSubst.downShifter[Term](num, order),
                 VariableShiftSubst.upShifter[LinearCombination](num, order)),
            order)
    else
      this

  def apply(lc : LinearCombination) : LinearCombination = apply(lc, null)

  //////////////////////////////////////////////////////////////////////////////
  
  def apply(lc : LinearCombination, terms : Buffer[(IdealInt, LinearCombination)])
           : LinearCombination = {
    val res = lc match {
      case _ : LinearCombination0 =>
        lc
        
      case lc : LinearCombination1 => (equations get lc.leadingTerm) match {
        case None =>
          lc
        case Some(eq) if (eq.leadingCoeff.isOne) =>
          reduceWithEq(lc, lc.leadingCoeff, eq, terms)
        case _ =>
          generalApply(lc, terms)
      }
      
      case lc : LinearCombination2 => (equations get lc.leadingTerm) match {
        case None => (equations get (lc getTerm 1)) match {
          case None =>
            lc
          case Some(eq) if (eq.leadingCoeff.isOne) =>
            reduceWithEq(lc, lc getCoeff 1, eq, terms)
          case _ =>
            generalApply(lc, terms)
        }
        case Some(eq) if (eq.leadingCoeff.isOne) =>
          reduceWithEq(lc, lc.leadingCoeff, eq, terms)
        case _ =>
          generalApply(lc, terms)
      }
      
      case _ => generalApply(lc, terms)
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithEqs.AC, (res eq lc) || res != lc)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  private def reduceWithEq(lc : LinearCombination, lcCoeff : IdealInt,
                           eq : LinearCombination,
                           terms : Buffer[(IdealInt, LinearCombination)]) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithEqs.AC, eq.leadingCoeff.isOne)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val eqCoeff = -lcCoeff
    if (terms != null)
      terms += (eqCoeff -> eq)
    apply(LinearCombination.sum(IdealInt.ONE, lc, eqCoeff, eq, order), terms)
  }

  private def generalApply(lc : LinearCombination,
                           terms : Buffer[(IdealInt, LinearCombination)]) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithEqs.AC, lc isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val blender = new LCBlender (order)
    blender += (IdealInt.ONE, lc)
    val changed = runBlender(blender, terms)
    
    if (changed) blender.result else lc
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Run the <code>blender</code> and add linear combinations from
   * <code>eqs</code> whenever it is possible to reduce monomials.
   * <code>true</code> is returned in case any reduction was performed. If the
   * argument <code>terms</code> is given a non-null value, then all terms and
   * coefficients given to the blender will be logged
   */
  private def runBlender(blender : LCBlender,
                         terms : Buffer[(IdealInt, LinearCombination)]) : Boolean = {
    var changed : Boolean = false
    while (blender.hasNext) {
      val (nextCoeff, nextTerm) = blender.peekNext

      (equations get nextTerm) match {
      case Some(eq) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(ReduceWithEqs.AC,
                        eq.leadingTerm == nextTerm && (eq isSortedBy order))
        //-END-ASSERTION-///////////////////////////////////////////////////////
                       
        val (quot, rem) = (nextCoeff reduceAbs eq.leadingCoeff)
        if (!quot.isZero) {
          blender += (-quot, eq)
          if (terms != null)
            terms += (-quot -> eq)
          changed = true
        }
                   
        if (blender.hasNext && (blender.peekNext _2) == nextTerm) blender.next
      }

      case None => blender.next
      }
    }
    
    changed
  }

  /**
   * Run the <code>blender</code> and add linear combinations from
   * <code>eqs</code> whenever it is possible to reduce monomials.
   * <code>true</code> is returned in case any reduction was performed.
   */
  private def runBlender(blender : LCBlender) : Boolean = runBlender(blender, null)

  /**
   * Same as <code>apply(lc:LinearCombination)</code>, but also multiply
   * <cocde>lc</code> with integers in case this allows to eliminate the leading
   * term (pseudo-division). It is ensured that the resulting
   * <code>LinearCombination</code> has a positive leading coefficient
   */
  def pseudoReduce(lc : LinearCombination) : LinearCombination = {
    var curLC = apply(lc)
    
    while (!curLC.isZero && (equations contains curLC.leadingTerm)) {
      val eq = equations(curLC.leadingTerm)
      val curLCCoeff = curLC.leadingCoeff
      val eqCoeff = eq.leadingCoeff
      
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(ReduceWithEqs.AC,
                      eq.leadingTerm == curLC.leadingTerm &&
                      !(eqCoeff divides curLCCoeff))
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val lcGcd = curLCCoeff gcd eqCoeff
      
      val blender = new LCBlender (order)
      blender ++= Array((eqCoeff / lcGcd, curLC), (-curLCCoeff / lcGcd, eq))
      runBlender(blender)
                        
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(ReduceWithEqs.AC,
                      { val res = blender.result
                        res.isZero ||
                          order.compare(res.leadingTerm, curLC.leadingTerm) < 0 })
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      curLC = blender.result
    }

    val res =    
      if (curLC.isZero) {
        LinearCombination.ZERO
      } else if (curLC.leadingCoeff.signum < 0) {
        // when the leading coefficient of the <code>LinearCombination</code> is
        // made positive, it might be possible to apply further reductions
        val blender = new LCBlender (order)
        blender += (IdealInt.MINUS_ONE, curLC)
        runBlender(blender)
        blender.result
      } else {
        curLC
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithEqs.AC, (res eq lc) || res != lc)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
  
    res
  }

  /**
   * Reduce the given linear combination and ensure that the leading coefficient
   * is non-negative. All terms added to <code>lc</code> are added to the buffer
   * <code>terms</code> (with respect to the positive, non-negated
   * <code>lc</code>).
   */
  private def reduceAndMakePositive(lc : LinearCombination,
                                    terms : Buffer[(IdealInt, LinearCombination)])
              : LinearCombination = {
    val curLC = apply(lc, terms)
    
    val res =
      if (curLC.isZero) {
        LinearCombination.ZERO
      } else if (curLC.leadingCoeff.signum < 0) {
        // when the leading coefficient of the <code>LinearCombination</code> is
        // made positive, it might be possible to apply further reductions
        val negTerms = if (terms == null)
                         null
                       else
                         new ArrayBuffer[(IdealInt, LinearCombination)]
  
        val blender = new LCBlender (order)
        blender += (IdealInt.MINUS_ONE, curLC)
        runBlender(blender, negTerms)
        
        if (terms != null)
          terms ++= (for ((c, t) <- negTerms.iterator) yield (-c, t))
        blender.result
      } else {
        curLC
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithEqs.AC, (res eq lc) || (res != lc))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }
  
  private lazy val keySet = equations.keySet
  
  private def reductionPossible(t : TerFor) : Boolean = {
    val keys = keySet
    !Seqs.disjoint(t.constants.asInstanceOf[Set[Term]], keys) ||
    !Seqs.disjoint(t.variables.asInstanceOf[Set[Term]], keys)
  }
  
  def apply(conj : EquationConj) : EquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val res = if (this.isEmpty || conj.isTrue || conj.isFalse ||
                  !reductionPossible(conj))
                conj
              else
                conj.pseudoReduce(this, order)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithEqs.AC,
                     isCompletelyReduced(res) &&
                     ((res eq conj) || (res != conj)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  //////////////////////////////////////////////////////////////////////////////
  // Some helper functions for the computation logging
  
  private def createTermBuffer(logger : ComputationLogger)
                              : ArrayBuffer[(IdealInt, LinearCombination)] =
    if (logger.isLogging)
      new ArrayBuffer[(IdealInt, LinearCombination)]
    else
      null
    
  //////////////////////////////////////////////////////////////////////////////

  def apply(conj : NegEquationConj) : NegEquationConj =
    apply(conj, ComputationLogger.NonLogger)

  def apply(conj : NegEquationConj, logger : ComputationLogger) : NegEquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val res =
      if (conj.isTrue || conj.isFalse || this.isEmpty ||
          !reductionPossible(conj)) {
        conj
      } else {
        var changed = false
        val terms = createTermBuffer(logger)
        val reducedLCs = for (lc <- conj) yield {
                           val newLC = reduceAndMakePositive(lc, terms)
                           if (!(newLC eq lc))
                             changed = true
                           if (terms != null && !terms.isEmpty) {
                             if (!newLC.isNonZero)
                               logger.reduceNegEquation(terms, lc, order)
                             terms.clear
                           }
                           newLC
                         }
        if (changed)
          NegEquationConj(reducedLCs, order)
        else
          conj
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithEqs.AC,
                     isCompletelyReduced(res) &&
                     ((res eq conj) || (res != conj)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  def apply(conj : InEqConj) : InEqConj = apply(conj, ComputationLogger.NonLogger)

  def apply(conj : InEqConj, logger : ComputationLogger) : InEqConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val res =
      if (conj.isTrue || conj.isFalse || this.isEmpty ||
          !reductionPossible(conj)) {
        conj
      } else {
        var changed = false
        val terms = createTermBuffer(logger)
        val reducedLCs = for (lc <- conj) yield {
                           val newLC = apply(lc, terms)
                           if (!(newLC eq lc))
                             changed = true
                           if (terms != null && !terms.isEmpty) {
                             if (!(newLC.isConstant &&
                                   newLC.constant.signum >= 0))
                               logger.reduceInequality(terms, lc, order)
                             terms.clear
                           }
                           newLC
                         }
        if (changed)
          InEqConj(reducedLCs.iterator, logger, order)
        else
          conj
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithEqs.AC,
                     isCompletelyReduced(res) &&
                     ((res eq conj) || (res != conj)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  private def apply(a : Atom, positive : Boolean,
                    logger : ComputationLogger) : Atom = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithEqs.AC, a isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val res =
      if (a.isEmpty || (a.constants.isEmpty && a.variables.isEmpty)) {
        // no arguments that could be reduced
        a
        
      } else if (logger.isLogging) {
        
        val argModifiers = new ArrayBuffer[Seq[(IdealInt, LinearCombination)]]
        val terms = createTermBuffer(logger)
        var changed = false

        val newArgs = for (lc <- a) yield {
          val newArg = apply(lc, terms)
          
          argModifiers += terms.toArray[(IdealInt, LinearCombination)]
          if (!terms.isEmpty)
            changed = true
          terms.clear
          
          newArg
        }
        
        if (changed) {
          val newAtom = Atom(a.pred, newArgs, order)
          logger.reducePredFormula(argModifiers, a, !positive, newAtom, order)
          newAtom
        } else {
          a
        }
        
      } else {

        var changed = false
        val newArgs = for (lc <- a) yield {
          val newArg = apply(lc)
          if (!(newArg eq lc))
            changed = true
          newArg
        }

        if (changed)
          Atom(a.pred, newArgs, order)
        else
          a

      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithEqs.AC,
                     isCompletelyReduced(res) && ((res eq a) || (res != a)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  def apply(conj : PredConj) : PredConj = apply(conj, ComputationLogger.NonLogger)

  def apply(conj : PredConj, logger : ComputationLogger) : PredConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val res =
      if (conj.isTrue || conj.isFalse || this.isEmpty ||
          !reductionPossible(conj)) {
        conj
      } else {

        var changed = false
        val newPosLits = for (a <- conj.positiveLits) yield {
          val newA = apply(a, true, logger)
          if (!(newA eq a))
            changed = true
          newA
        }
        val newNegLits = for (a <- conj.negativeLits) yield {
          val newA = apply(a, false, logger)
          if (!(newA eq a))
            changed = true
          newA
        }

        if (changed)
          PredConj(newPosLits.iterator, newNegLits.iterator, logger, order)
        else
          conj
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithEqs.AC, ((res eq conj) || (res != conj)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  //////////////////////////////////////////////////////////////////////////////
  private def isCompletelyReduced(lcs : Iterable[LinearCombination]) : Boolean =
    Logic.forall(for (lc <- lcs.iterator) yield
                 Logic.forall(for ((c, t) <- lc.pairIterator) yield (
                                equations.get(t) match {
                                case Some(eq) => c isAbsMinMod eq.leadingCoeff
                                case None => true
                                })))
  //////////////////////////////////////////////////////////////////////////////
    
  // pseudo-reduction on conjunctions of inequations
  // (disabled for the time being, it is not clear whether this
  // is a good idea)
  private def applyXX(conj : NegEquationConj) : NegEquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithEqs.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    val res = NegEquationConj(for (lc <- conj.iterator)
                              yield pseudoReduce(lc), order)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithEqs.AC,
      res.isFalse ||
      Logic.forall(for (lc <- res.iterator) yield
                   (!(equations contains lc.leadingTerm) &&
                    Logic.forall(for ((c, t) <- lc.pairIterator) yield (
                                   equations.get(t) match {
                                   case Some(eq) => c isAbsMinMod eq.leadingCoeff
                                   case None => true
                                   })))))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }
  
}

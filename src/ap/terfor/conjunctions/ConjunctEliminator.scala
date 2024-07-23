/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.conjunctions;

import scala.collection.{Set => GSet}

import ap.terfor._
import ap.basetypes.IdealInt
import ap.terfor.{TerFor, Term, Formula, ConstantTerm, TermOrder}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.arithconj.{ArithConj, ModelElement,
                            EqModelElement, InNegEqModelElement}
import ap.terfor.preds.Predicate
import ap.terfor.inequalities.InEqConj
import ap.terfor.substitutions.{Substitution, ConstantSubst, VariableShiftSubst}
import ap.util.{Logic, Debug, Seqs, FilterIt}
import ap.terfor.arithconj.InNegEqModelElement

import scala.collection.immutable.VectorBuilder
import scala.collection.mutable.{HashSet => MHashSet,
                                 LinkedHashSet, HashMap => MHashMap}

object ConjunctEliminator {
  
  val AC = Debug.AC_ELIM_CONJUNCTS
  
  /**
   * When eliminating symbols through Fourier-Motzkin, accept at most this
   * many additional inequalities
   */
  private val FM_ELIM_MAX_GROWTH = 50

}

/**
 * Class for removing irrelevant conjuncts from a conjunction
 * (like equations that have been applied to all other formulas)
 */
abstract class ConjunctEliminator(oriConj : Conjunction,
                                  // symbols that are universally quantified on
                                  // the innermost level
                                  universalSymbols : Set[Term],
                                  // predicates encoding functions that can
                                  // be eliminated from the e-graph if they are
                                  // not referred to from anywhere else
                                  eliminableFunctionPreds : Set[Predicate],
                                  order : TermOrder) {
  
  private var conj = oriConj

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  // we only know how to eliminate constants and variables
  Debug.assertCtor(ConjunctEliminator.AC,
                   Logic.forall(for (t <- universalSymbols.iterator)
                                yield (t match {
                                  case _ : ConstantTerm => true
                                  case _ : VariableTerm => true
                                  case _ => false
                                })))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  private def occursIn(f : TerFor, c : Term) = c match {
    case c : ConstantTerm => f.constants contains c
    case v : VariableTerm => f.variables contains v
  }

  private def someTermOccursIn(f : TerFor, cs : GSet[Term]) =
    (f.constants exists cs) || (f.variables exists cs)

  private def occursInPositiveEqs(c : Term) =
    occursIn(conj.arithConj.positiveEqs, c)

  private def onlyOccursInPositiveEqs(c : Term) =
    !occursInNegativeEqs(c) && !occursInInEqs(c) && !occursInPreds(c)

  private def onlyOccursInNegativeEqs(c : Term) =
    !occursInPositiveEqs(c) && !occursInInEqs(c) && !occursInPreds(c)

  private def occursInNegativeEqs(c : Term) =
    occursIn(conj.arithConj.negativeEqs, c)

  private def occursInInEqs(c : Term) =
    occursIn(conj.arithConj.inEqs, c)

  private def occursInPreds(c : Term) =
    occursIn(conj.predConj, c)

  private def containsEliminatedSymbols(f : TerFor) =
    !Seqs.disjointSeq(universalSymbols, f.constants) ||
    !Seqs.disjointSeq(universalSymbols, f.variables)
  
  /**
   * Called when a formula was eliminated that does not contain universal
   * symbols
   */
  protected def nonUniversalElimination(f : Conjunction)      
  
  /**
   * Called when formulas were eliminated that contain universal symbols
   * (which so far can only be a constants).
   * A method is provided for
   * constructing an assignment for the eliminated symbols that satifies
   * all eliminated formulas, given any partial assignment of values to other
   * symbols (this is the justification why the formulas can be eliminated).
   */
  protected def universalElimination(model : ModelElement) : Unit

  /**
   * Called when a new divisibility judgement (not containing any
   * eliminated/universal symbols) is introduced
   */
  protected def addDivisibility(f : Conjunction)
  
  ////////////////////////////////////////////////////////////////////////////
  // Positive equations
    
  private def eliminablePositiveEqs(c : Term) : Boolean = {
    var occurred : Boolean = false
    val lcIt = conj.arithConj.positiveEqs.iterator
    while (lcIt.hasNext) {
      val lc = lcIt.next()
      if (occursIn(lc, c)) {
        // the constant must occur in at most one equation
        if (occurred) return false
        occurred = true

        // and the coefficient must be at most one
        if (!(lc get c).isUnit) return false
      }
    }
    
    true
  }

  private def eliminablePositiveEqsNonU(c : Term) : Boolean = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConjunctEliminator.AC, !(universalSymbols contains c))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    // we do not remove the equation if c is not an eliminated constant, but
    // the equation contains other eliminated constants;
    // there are chances that we can remove the equation completely later
    !(conj.arithConj.positiveEqs exists {
      lc => occursIn(lc, c) && containsEliminatedSymbols(lc)
    })
  }

  private def elimPositiveEqs(c : Term) : Unit = {
    val oriEqs = conj.arithConj.positiveEqs
    val remainingEqs = new VectorBuilder[LinearCombination]
   
    for (lc <- oriEqs)
      if (occursIn(lc, c))
        elimPositiveEquationHelp(lc, c)
      else
        remainingEqs += lc

    conj = conj.updatePositiveEqs(
                  oriEqs.updateEqsSubset(remainingEqs.result)(order))(order)
  }

  private def elimPositiveEquationHelp(lc : LinearCombination, c : Term) : Unit =
    if (universalSymbols contains c)
      elimPositiveUniEquationHelp(lc, c)
    else
      // the equation can directly be moved to the constraint
      nonUniversalElimination(Conjunction.conj(NegEquationConj(lc, order), order))

  private def elimPositiveUniEquationHelp(lc : LinearCombination,
                                          c : Term) : Unit = c match {
    case c : ConstantTerm => {
      // then we can just ignore the equation; we describe how to compute
      // a witness for the eliminated constant c
      universalElimination(EqModelElement(EquationConj(lc, order), Set(c)))
    }
    case _ : VariableTerm => // nothing
  }

  private def elimAllPositiveUniversalEqs : Unit = {
    val oriEqs = conj.arithConj.positiveEqs
    
    // first determine all constants that can be eliminated based on occurrence
    // in equations
    
    val elimCandidates, nonCandidates = new MHashSet[Term]
    
    {
      val lcIt = oriEqs.iterator
      while (lcIt.hasNext) {
        val lc = lcIt.next()
        val N = lc.size
      
        var i = 0
        while (i < N) {
          val c = lc getTerm i
          if (!(nonCandidates contains c)) {
            if (elimCandidates contains c) {
              // if c is already an element of the set, we have seen it twice,
              // and then it cannot be eliminated
              nonCandidates += c
            } else if ((lc getCoeff i).isUnit &&
                       isEliminationCandidate(c) &&
                       (universalSymbols contains c) &&
                       onlyOccursInPositiveEqs(c))
              elimCandidates += c
            else
              nonCandidates += c
          }
          i = i + 1
        }
      }
    
      elimCandidates --= nonCandidates
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConjunctEliminator.AC, !elimCandidates.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    // now eliminate equations
    
    val remainingEqs, eliminatedEqs = new VectorBuilder[LinearCombination]
    val eliminatedConsts = new MHashSet[ConstantTerm]
    
    {
      val lcIt = oriEqs.iterator
      while (lcIt.hasNext) {
        val lc = lcIt.next()
        val N = lc.size
      
        var i = 0
        var elim = false
        while (i < N && !elim) {
          val c = lc getTerm i
          if (elimCandidates contains c) {
            elim = true
            c match {
              case c : ConstantTerm => {
                // only eliminated constants are recorded
                eliminatedEqs += lc
                eliminatedConsts += c
              }
              case _ =>
                // nothing
            }
          }
          i = i + 1
        }
        
        if (!elim)
          remainingEqs += lc
      }
    }
    
    universalElimination(
      EqModelElement(oriEqs.updateEqsSubset(eliminatedEqs.result)(order),
                    eliminatedConsts))
    
    conj = conj.updatePositiveEqs(
             oriEqs.updateEqsSubset(remainingEqs.result)(order))(order)
  }

  //////////////////////////////////////////////////////////////////////////////
  // Eliminated constants that occur in negative equations. The result are the
  // eliminated equations
    
  private def elimNegativeEqsU(c : Term) : NegEquationConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConjunctEliminator.AC, universalSymbols contains c)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val eqs = conj.arithConj.negativeEqs
    
    val (eliminatedEqs, remainingEqs) =
      eqs partition (occursIn(_ : LinearCombination, c))
    conj = conj.updateNegativeEqs(eqs.updateEqsSubset(remainingEqs)(order))(order)

    // we give back the eliminated equations
    eqs.updateEqsSubset(eliminatedEqs)(order)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Eliminated constants that occur in inequalities

  private def onesidedInEqsU(c : Term) : Boolean = {
    // the coefficient of the constant must have the same sign in all inequalities
    
    var signum : Int = 0
    val lcIt = conj.arithConj.inEqs.iterator
    while (lcIt.hasNext) {
      val lc = lcIt.next()
      val newSignum = (lc get c).signum
      if (newSignum != 0) {
        if (signum * newSignum == -1) return false
        signum = newSignum
      }
    }
    
    true
  }

  private def elimOnesidedInEqsU(c : Term, logger : ComputationLogger) : InEqConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConjunctEliminator.AC, universalSymbols contains c)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val inEqs = conj.arithConj.inEqs
    
    val (eliminatedInEqs, remainingInEqs) =
      inEqs partition (occursIn(_ : LinearCombination, c))
    conj = conj.updateInEqs(inEqs.updateGeqZeroSubset(remainingInEqs, logger)
                                                     (order))(order)

    // we give back the eliminated inequalities
    InEqConj(eliminatedInEqs, order)
  }

  private def elimAllOnesidedInEqsU(logger : ComputationLogger) : Unit = {
    val oriInEqs  = conj.arithConj.inEqs
    val oriNegEqs = conj.arithConj.negativeEqs
    
    // first determine all constants that can be eliminated based on occurrence
    // in inequalities or negative equalities

    val elimSyms = new MHashSet[Term]

    {
      val lowerBound, upperBound = new MHashSet[Term]

      // first scan the inequality symbols
      val lcIt = oriInEqs.iterator
      while (lcIt.hasNext) {
        val lc = lcIt.next()
        val N = lc.size
      
        var i = 0
        while (i < N) {
          val c = lc getTerm i
          if (universalSymbols contains c)
            (lc getCoeff i).signum match {
              case -1 => upperBound += c
              case 1  => lowerBound += c
            }
          i = i + 1
        }
      }

      for (c <- lowerBound)
        if (!(upperBound contains c) &&
            isEliminationCandidate(c) &&
            !occursInPositiveEqs(c) &&
            !occursInPreds(c))
          elimSyms += c
      for (c <- upperBound)
        if (!(lowerBound contains c) &&
            isEliminationCandidate(c) &&
            !occursInPositiveEqs(c) &&
            !occursInPreds(c))
          elimSyms += c

      // then add symbols only occurring in negative equations
      val lcIt2 = oriNegEqs.iterator
      while (lcIt2.hasNext) {
        val lc = lcIt2.next()
        val N = lc.size
      
        var i = 0
        while (i < N) {
          val c = lc getTerm i
          if (!(elimSyms contains c) &&
              (universalSymbols contains c) &&
              isEliminationCandidate(c) &&
              onlyOccursInNegativeEqs(c))
            elimSyms += c
          i = i + 1
        }
      }
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConjunctEliminator.AC, !elimSyms.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    // now eliminate

    val (eliminatedInEqs, remainingInEqs) =
      oriInEqs partition (someTermOccursIn(_ : LinearCombination, elimSyms))
    val (eliminatedNegEqs, remainingNegEqs) =
      oriNegEqs partition (someTermOccursIn(_ : LinearCombination, elimSyms))

    val newInEqs =
      oriInEqs.updateGeqZeroSubset(remainingInEqs, logger)(order)
    val newNegEqs =
      oriNegEqs.updateEqsSubset(remainingNegEqs)(order)
    val newArithConj =
      ArithConj(conj.arithConj.positiveEqs, newNegEqs, newInEqs, order)

    conj = conj.updateArithConj(newArithConj)(order)

    val elimInEqs =
      oriInEqs.updateGeqZeroSubset(eliminatedInEqs)(order)
    val elimNegEqs =
      oriNegEqs.updateEqsSubset(eliminatedNegEqs)(order)
    val elimArithConj =
      ArithConj(EquationConj.TRUE, elimNegEqs, elimInEqs, order)

    // only constants are needed for model construction
    val elimConsts = new MHashSet[ConstantTerm]
    for (c <- elimSyms) c match {
      case c : ConstantTerm => elimConsts += c
      case _                => // nothing
    }

    if (!elimConsts.isEmpty)
      universalElimination(InNegEqModelElement(elimArithConj, elimConsts))
  }

  //////////////////////////////////////////////////////////////////////////////
  // Non-eliminated constants that occur in negative equations

  private def eliminableNegativeEqs(c : Term) : Boolean =
    // we only move equations to the constraints if no eliminated
    // constants occur in any of them
    Logic.forall(for (lc <- conj.arithConj.negativeEqs.iterator)
                 yield (!occursIn(lc, c) || !containsEliminatedSymbols(lc)))

  private def elimNegativeEqs(c : Term) : Unit = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConjunctEliminator.AC, !(universalSymbols contains c))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val (constraintEqs, remainingEqs) =
      conj.arithConj.negativeEqs partition (occursIn(_ : LinearCombination, c))
      
    nonUniversalElimination(Conjunction.disjFor(for (lc <- constraintEqs.iterator)
                                                yield EquationConj(lc, order),
                  order))
    conj = conj.updateNegativeEqs(NegEquationConj(remainingEqs, order))(order)
  }  

  //////////////////////////////////////////////////////////////////////////////
  // Eliminable symbols that only occur in the "congruence graph", i.e.,
  // only in predicates of the form <code>f(t, c)</code>, for some predicate
  // <code>f/<code> encoding a function
  
  private def eliminableFunctionValue(c : Term) : Boolean = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConjunctEliminator.AC, universalSymbols contains c)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (eliminableFunctionPreds.isEmpty) return false
    
    // check in how many predicates the symbol occurs
    var occurred : Boolean = false
    val atomIt = conj.predConj.positiveLits.iterator
    while (atomIt.hasNext) {
      val a = atomIt.next()
      if (occursIn(a, c)) {
        if (!(eliminableFunctionPreds contains a.pred)) return false
        // we currently only eliminate predicates that only contain
        // universal symbols. this could be relaxed ... however, one has to be
        // careful not to destroy completeness, since one could potentially
        // eliminate predicates that have just been introduced by the
        // totality axioms
        if (!(a.constants.asInstanceOf[scala.collection.Set[Term]] subsetOf
                                      universalSymbols)) return false
        if (!(a.variables.asInstanceOf[scala.collection.Set[Term]] subsetOf
                                      universalSymbols)) return false
        
        // the symbol must occur in at most one literal
        if (occurred) return false
        occurred = true
        
        // the constant must only occur in the last argument of the atom
        var i = 0
        while (i < a.length - 1) {
          if (occursIn(a(i), c)) return false
          i = i + 1
        }
        
        // and the coefficient of the symbol in the last argument must be a unit
        if (!(a.last get c).isUnit) return false
      }
    }
  
    // the symbol must not occur in any negated literals
    conj.predConj.negativeLits forall (!occursIn(_, c))
  }

  private def elimFunctionValue(c : Term) : Unit = {
    val (eliminated, remainingPredConj) = conj.predConj partition (occursIn(_, c))
    conj = conj.updatePredConj(remainingPredConj)(order)
  }

  //////////////////////////////////////////////////////////////////////////////
  // Check whether <code>c</code> only occurs in inequalities
  // <code>n*c + t >= a & n*c + t < b</code> such that
  // <code>b - a >= n - maxDivJudgements<code>. In this case,
  // the two inequalities can be replaced with a conjunction
  // <code>!EX (n*_0 + t = b) & !EX (n*_0 + t = b+1) & ...</code>
  
  private def eliminableDivInEqs(c : Term) : Option[(IdealInt, Boolean)] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConjunctEliminator.AC, universalSymbols contains c)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    var firstLC : LinearCombination = null
    var negFirstLC : LinearCombination = null
    var diffBound : IdealInt = null
    var res : IdealInt = null
    var otherUniSyms : Boolean = false
    
    val lcIt = conj.arithConj.inEqs.iterator
    while (lcIt.hasNext) {
      val lc = lcIt.next()
      
      if (occursIn(lc, c)) {
        if (firstLC == null) {
            
          firstLC = lc
          negFirstLC = -lc
          diffBound = (lc get c).abs - 1
          
          // check whether the inequality contains other eliminated symbols
          otherUniSyms = firstLC.termIterator exists {
            case s => s != c && (universalSymbols contains s)
          }
          
        } else if (res != null) {
          
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          // then we have to be in a case where nothing can be eliminated
          Debug.assertInt(ConjunctEliminator.AC,
                          !(firstLC sameNonConstantTerms lc) &&
                          !(negFirstLC sameNonConstantTerms lc))
          //-END-ASSERTION-/////////////////////////////////////////////////////
          return None
          
        } else {
          
          (lc constantDiff negFirstLC) match {
            case None =>
              return None
            case Some(d) => {
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              Debug.assertInt(ConjunctEliminator.AC, d.signum > 0)
              //-END-ASSERTION-/////////////////////////////////////////////////
              res = (diffBound - d) max IdealInt.ZERO
            }
          }
          
        }
      }
    }
    
    if (res == null) None else Some(res, otherUniSyms)
  }
  
  private def elimDivInEqs(c : Term, numDivs : Int,
                           logger : ComputationLogger) : Unit = {
    val elimInEqs = elimOnesidedInEqsU(c, logger)
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConjunctEliminator.AC,
                    elimInEqs.size == 2)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (numDivs > 0) {
      val varLC = c match {
        case c : ConstantTerm =>
          ConstantSubst(c, VariableTerm._0, order)(
          VariableShiftSubst(0, 1, order)(elimInEqs(0)))
        case v@VariableTerm(ind) => {
          val shifter = Array.fill(ind + 1)(1)
          shifter(ind) = -ind
          VariableShiftSubst(shifter, 1, order)(elimInEqs(0))
        }
      }
      for (i <- 1 to numDivs)
        addDivisibility(Conjunction.quantify(List(Quantifier.EX),
                                             EquationConj(varLC + i, order),
                                             order))
    }
                    
    val eliminatedFor = ArithConj.conj(elimInEqs, order)
    c match {
      case c : ConstantTerm =>
        universalElimination(InNegEqModelElement(eliminatedFor, c))
      case _ : VariableTerm => // nothing
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Determine best possible Fourier-Motzkin application
  
  private def bestExactShadow(inEqs : Seq[LinearCombination]) : Option[Term] = {
    val candidates = new LinkedHashSet[Term]

    val candIt = eliminationCandidates(conj)
    while (candIt.hasNext) {
      val c = candIt.next()
      if ((universalSymbols contains c) &&
          !occursInPreds(c) &&
          !occursInPositiveEqs(c) &&
          !occursInNegativeEqs(c))
        candidates += c
    }

    if (candidates.isEmpty)
      return None

    val lowerBounds, upperBounds =
      new MHashMap[Term, Int] { override def default(t:Term) = 0 }
    val lowerNonUnits, upperNonUnits =
      new MHashSet[Term]

    for (lc <- inEqs) {
      var i = 0
      val N = lc.lcSize
      while (i < N) {
        val t = lc getTerm i
        if (candidates contains t) {
          val coeff = lc getCoeff i
          coeff.signum match {
            case 0 => // nothing
            case 1 => {
              lowerBounds.put(t, lowerBounds(t) + 1)
              if (!coeff.isOne) {
                if (upperNonUnits contains t)
                  candidates -= t
                else
                  lowerNonUnits += t
              }
            }
            case -1 => {
              upperBounds.put(t, upperBounds(t) + 1)
              if (!coeff.isMinusOne) {
                if (lowerNonUnits contains t)
                  candidates -= t
                else
                  upperNonUnits += t
              }
            }
          }
        }
        i = i + 1
      }
    }

    Seqs.minOption(candidates.iterator,
                   (c:Term) => {
                     val l = lowerBounds(c)
                     val u = upperBounds(c)
                     if (l == 0 && u == 0) {
                       None
                     } else {
                       val growth = l*u - l - u
                       if (growth <= ConjunctEliminator.FM_ELIM_MAX_GROWTH)
                         Some(growth)
                       else
                         None
                     }
                   })
  }

  //////////////////////////////////////////////////////////////////////////////
  // The main loop

  protected def eliminationCandidates(conj : Conjunction) : Iterator[Term]
  
  protected def isEliminationCandidate(t : Term) : Boolean
  
  def eliminate(logger : ComputationLogger) : Conjunction = {
  var oldconj = conj
  do {
    oldconj = conj

    val elimCandidates = eliminationCandidates(conj)
    if (!elimCandidates.hasNext)
      return conj

    for (c <- elimCandidates) {
      (occursInPositiveEqs(c),
       occursInNegativeEqs(c),
       occursInInEqs(c),
       occursInPreds(c),
       universalSymbols contains c) match {

      case (false, false, false, true, true)
        if (eliminableFunctionValue(c))
        => elimFunctionValue(c)
      
      case (false, false, false, _, _) => // nothing
      
      case (true, false, false, false, true)
        if (eliminablePositiveEqs(c))
        => //elimPositiveEqs(c)
           elimAllPositiveUniversalEqs
   
      case (true, false, false, false, false)
        if (eliminablePositiveEqsNonU(c) && eliminablePositiveEqs(c))
        => elimPositiveEqs(c)
 
      case (false, true, false, false, false)
        if (eliminableNegativeEqs(c))
        => elimNegativeEqs(c)

      case (false, _, _, false, true)
        if (onesidedInEqsU(c))
        => elimAllOnesidedInEqsU(logger)
    
      case (false, false, true, false, true)
        if (conj.arithConj.inEqs.equalityInfs.isEmpty)
        => eliminableDivInEqs(c) match {
          case Some((d, otherUniSyms))
            if (d.isZero || (!otherUniSyms && !logger.isLogging && d <= 1)) =>
              elimDivInEqs(c, d.intValueSafe, logger)
          case _ => // nothing
        }
    
      case _ => // nothing
        
      }
    }
    
    if (oldconj eq conj) {
      // check for possible Fourier-Motzkin eliminations
      
      def exactShadow(inEqs : Seq[LinearCombination]) : Seq[LinearCombination] =
        bestExactShadow(inEqs) match {
          case None => inEqs
          case Some(c) => {
            val (eliminated, remaining) =
              InEqConj.exactShadow(c, inEqs, logger, order)
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(ConjunctEliminator.AC,
                            remaining forall (!occursIn(_, c)))
            //-END-ASSERTION-///////////////////////////////////////////////////
            c match {
              case c : ConstantTerm => {
                val eliminatedFor =
                  ArithConj.conj(InEqConj(eliminated.iterator, order), order)
                if (eliminatedFor.isFalse) {
                  // In this case, the full set of inequalities is unsat,
                  // but this was not detected earlier due to incompleteness
                  // of the checks in InEqConj. It is enough to keep the
                  // eliminated constants
                  eliminated
                } else {
                  universalElimination(InNegEqModelElement(eliminatedFor, c))
                  exactShadow(remaining)
                }
              }
              case _ : VariableTerm =>
                exactShadow(remaining)
            }
          }
        }

      try {
        val rawInEqs = exactShadow(conj.arithConj.inEqs)
        val newInEqs =
          if (rawInEqs eq conj.arithConj.inEqs)
            conj.arithConj.inEqs
          else
            InEqConj(rawInEqs.iterator, logger, order)
        conj = conj.updateInEqs(newInEqs)(order)
      } catch {
        case InEqConj.UNSATISFIABLE_INEQ_EXCEPTION =>
          conj = Conjunction.FALSE
      }
    }
    
  } while (!(oldconj eq conj))

  conj
  }
    
}

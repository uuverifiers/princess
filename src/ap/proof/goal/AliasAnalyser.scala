/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.goal

import ap.proof._
import ap.basetypes.IdealInt
import ap.terfor.{TermOrder, AliasStatus, AliasChecker, ConstantTerm}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj, ReduceWithNegEqs}
import ap.terfor.conjunctions.ReduceWithConjunction
import ap.terfor.preds.{Atom, Predicate, PredConj}
import ap.util.{Debug, LRUCache, Seqs}

import scala.collection.immutable.VectorBuilder

object AliasAnalyser {
  
  private val AC = Debug.AC_ALIAS_ANALYSER

}

/**
 * Class to approximate whether two terms have to be considered as potential
 * aliases, i.e., may have the same value. Two criteria are taken into account
 * for this: arithmetic facts that are available in a proof goal, and constant
 * freedom. The class does caching to speed up queries.
 */
class AliasAnalyser (reducer : ReduceWithConjunction,
                     cf : ConstantFreedom, bc : BindingContext,
                     order : TermOrder)
      extends AliasChecker {

  import AliasAnalyser._

  private val cache, cacheFD =
    new LRUCache[(LinearCombination, LinearCombination),
                 AliasStatus.Value] (10000)
  
  private def cacheKey(a : LinearCombination, b : LinearCombination) = {
    val aHash = a.hashCode
    val bHash = b.hashCode
    if (aHash < bHash || (aHash == bHash && order.compare(a, b) < 0))
      (a, b)
    else
      (b, a)
  }
  
  /**
   * Check whether two terms have to be considered as potential
   * aliases, i.e., may have the same value.
   */
  def apply(a : LinearCombination, b : LinearCombination,
            includeCannotDueToFreedom : Boolean) : AliasStatus.Value = {
    if (includeCannotDueToFreedom) {
      checkAliasFD(a, b)
    } else {
      val res = checkAlias(a, b)
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
//      Debug.assertPost(AC, res == (checkAliasFD(a, b) match {
//                                     case AliasStatus.CannotDueToFreedom =>
//                                       AliasStatus.Cannot
//                                     case s => s
//                                   }))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      res
    }
  }

  /**
   * Check whether the given terms can be aliased.
   */
  private def checkAlias(a : LinearCombination,
                         b : LinearCombination) : AliasStatus.Value =
    if (a == b) {
      AliasStatus.Must
    } else cache(cacheKey(a, b)) {
      if (cf.diffIsShieldingLC(a, b, bc)) {
        AliasStatus.Cannot
      } else {
        implicit val o = order
        val reduced = reducer(EquationConj(a - b, order))
        
        if (reduced.isTrue)
          AliasStatus.Must
        else if (reduced.isFalse)
          AliasStatus.Cannot
        else
          AliasStatus.May
      }
    }

  /**
   * Check whether the given terms can be aliased, and also produce
   * the result <code>AliasStatus.CannotDueToFreedom</code>
   */
  private def checkAliasFD(a : LinearCombination,
                           b : LinearCombination) : AliasStatus.Value =
    if (a == b)
      AliasStatus.Must
    else cacheFD(cacheKey(a, b)) {
      implicit val o = order
      val reduced = reducer(EquationConj(a - b, order))
      
      if (reduced.isTrue)
        AliasStatus.Must
      else if (reduced.isFalse)
        AliasStatus.Cannot
      else if (cf.diffIsShieldingLC(a, b, bc))
        AliasStatus.CannotDueToFreedom
      else
        AliasStatus.May
    }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Find atoms within the sequence <code>atoms</code> that may
   * alias with atoms with the given <code>arguments</code>
   * as the first arguments.
   */
  def findMayAliases(atoms : Seq[Atom],
                     pred : Predicate,
                     arguments : Seq[LinearCombination],
                     includeCannotDueToFreedom : Boolean)
                   : Map[AliasStatus.Value, Seq[Atom]] = {
    if (atoms.isEmpty)
      Map()
    else if (includeCannotDueToFreedom || atoms.size <= 5)
      findMayAliasesNaive(atoms, pred, arguments, includeCannotDueToFreedom)
    else
      findMayAliasesBin(atoms, pred, arguments, false)
  }

  /**
   * Find atoms within the sequence <code>atoms</code> that may
   * alias with atoms with the given <code>arguments</code>
   * as the first arguments.
   *
   * Implementation using binary search.
   */
  private def findMayAliasesBin(_atoms : Seq[Atom],
                                pred : Predicate,
                                _arguments : Seq[LinearCombination],
                                includeCannotDueToFreedom : Boolean)
                              : Map[AliasStatus.Value, Seq[Atom]] = {
//    println("--")

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, !_arguments.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    import AliasStatus.{Must, May, Cannot}

//println(_atoms)
//println(_arguments)

    val atoms = _atoms.toIndexedSeq
    
    val (predLeft, predRight) = PredConj.findAtomsWithPred(atoms, pred, order)

    if (predLeft >= predRight)
      return Map()

    val arguments =    _arguments.toIndexedSeq
    val argumentSize = arguments.size
    val arity =        pred.arity
    val lcOrdering =   order.lcOrdering
    val termOrdering = order.termOrdering

    import lcOrdering.{lt => lcLT, lteq => lcLTeq}
    import termOrdering.{lt => teLT}

    val mayResult = new VectorBuilder[Atom]

    def selectAtoms(left : Int, right : Int, aInd : Int) : Unit = {
      if (left >= right) {
        // nothing
      } else if (aInd == argumentSize) {
        for (ind <- left until right)
          mayResult += atoms(ind)
      } else if (left + 1 == right) {

        val a = atoms(left)
        var res = May
        var n = aInd
      
        while (n < argumentSize && res != Cannot) {
          apply(a(n), arguments(n), false) match {
            case Must | May => // nothing
            case s          => res = s
          }
          n = n + 1
        }

        if (res != Cannot)
          mayResult += a
        
      } else {
      
        val argument = arguments(aInd)
        if (argument.isConstant) {
          // we search for an argument with constant value; consider
          // atoms with either a matching constant argument, or with an
          // aliasing symbolic term
          
          val constsStart =
            one2oneSelection(left, right, aInd, argument, _.isConstant)
          val constsLeft =
            Seqs.risingEdgeFwdFull(atoms,
                                   (a:Atom) => lcLTeq(a(aInd), argument),
                                   constsStart, right)
          val constsRight =
            Seqs.risingEdgeFwdFull(atoms,
                                   (a:Atom) => lcLT(a(aInd), argument),
                                   constsLeft, right)

//          println(" [" + constsLeft + ", " + constsRight + ")")
          selectAtoms(constsLeft, constsRight, aInd + 1)
          
        } else {
        
          val lt = argument.leadingTerm.asInstanceOf[ConstantTerm]
          if (cf.isBottomWRT(lt)) {
            one2oneSelection(left, right, aInd, argument, (_) => false)
          } else {
            // we search for a term that starts with a shielding constant;
            // we can therefore ignore terms with a smaller leading term

            val ind =
            one2oneSelection(left, right, aInd, argument,
              lc => lc.isConstant || teLT(lc.leadingTerm, lt))
//if (ind != right)
//  println("" + right + " -> " + ind)
          }
        }
      }
    }

    def one2oneSelection(left : Int, right : Int,
                         aInd : Int, argument : LinearCombination,
                         stopCond : LinearCombination => Boolean) : Int = {
      var ind = left
      if (aInd == argumentSize - 1) {
        while (ind < right && !stopCond(atoms(ind)(aInd))) {
          if (apply(atoms(ind)(aInd), argument, false) != Cannot)
            mayResult += atoms(ind)
          ind = ind + 1
        }
      } else {
        while (ind < right && !stopCond(atoms(ind)(aInd))) {
          val nextInd =
            Seqs.risingEdgeFwdFull(atoms,
                                   (a:Atom) => lcLT(a(aInd), atoms(ind)(aInd)),
                                   ind + 1, right)
          if (apply(atoms(ind)(aInd), argument, false) != Cannot)
            selectAtoms(ind, nextInd, aInd + 1)
          ind = nextInd
        }
      }

      ind
    }

    selectAtoms(predLeft, predRight, 0)

    Map(May -> mayResult.result)
  }

  /**
   * Find atoms within the sequence <code>atoms</code> that may
   * alias with atoms with the given <code>arguments</code>
   * as the first arguments.
   *
   * Implementation that just linearly scans the given atoms.
   */
  private def findMayAliasesNaive(atoms : Seq[Atom],
                                  pred : Predicate,
                                  arguments : Seq[LinearCombination],
                                  includeCannotDueToFreedom : Boolean)
                                : Map[AliasStatus.Value, Seq[Atom]] = {

    val N = arguments.size
    atoms groupBy { a =>
      var res = if (a.pred == pred) AliasStatus.May else AliasStatus.Cannot
      var n = 0
      
      while (n < N && res != AliasStatus.Cannot) {
        apply(a(n), arguments(n),
              includeCannotDueToFreedom &&
              res != AliasStatus.CannotDueToFreedom) match {
          case AliasStatus.Must | AliasStatus.May =>
            // nothing
          case s =>
            res = s
        }
        n = n + 1
      }

      res
    }
  }

}

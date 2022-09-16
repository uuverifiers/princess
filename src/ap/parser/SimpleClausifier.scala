/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.terfor.conjunctions.Quantifier
import ap.util.{Debug, Seqs, PlainRange, Timeout}

import IBinJunctor._
import IExpression._
import Quantifier._

object SimpleClausifier {

  private val AC = Debug.AC_INPUT_ABSY

  protected[parser] object Literal {
    def unapply(t : IExpression) : Option[IFormula] = t match {
      case LeafFormula(t) => Some(t)
      case t@INot(sub) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        // we assume that the formula is in negation normal form
        Debug.assertPre(AC, LeafFormula.unapply(sub) != None)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        Some(t)
      }
      case _ => None
    }
  }
  
}

////////////////////////////////////////////////////////////////////////////////
  
class SimpleClausifier {

  import SimpleClausifier._
  
  def apply(f : IFormula) : IFormula = {
    val f1 = Transform2NNF(f)
    val f2 = PushDownAllQuantifiers(f1)
    val f3 = CompactifyQuantifiers(f2)
    val f4 = ExBodiesToDNF(f3)
    val f5 = CompactifyExBodies(f4)
    f5
  }

  private var opNum = 0
  
  private def incOpNum = {
    opNum = opNum + 1
    if (opNum % 100 == 0)
      Timeout.check
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Push down all quantifiers but the outermost ALL quantifiers down as far
   * as possible
   */
  private object PushDownAllQuantifiers
                 extends CollectingVisitor[Boolean, IFormula] {
    def apply(f : IFormula) : IFormula = this.visit(f, false)
    
    override def preVisit(t : IExpression,
                          underneathEx : Boolean) : PreVisitResult =
      t match {
        case Literal(t) =>
          // do not look into atoms
          ShortCutResult(t)
        case IQuantified(EX, _) =>
          UniSubArgs(true)
        case _ : ITrigger =>
          throw new Preprocessing.PreprocessingException(
            "Did not expect any triggers to be left at this point")
        case _ =>
          KeepArg
      }
  
    def postVisit(t : IExpression, underneathEx : Boolean,
                  subres : Seq[IFormula]) : IFormula =
      t match {
        case t@IQuantified(EX, _) if underneathEx =>
          PushDownQuantifier(t update subres)
        case t : IFormula =>
          t update subres
      }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Pull up all quantifiers to the innermost enclosing quantifier of the same
   * kind. Outermost universal quantifiers are completely pulled out
   */
  private object CompactifyQuantifiers
                 extends CollectingVisitor[(Quantifier, IBinJunctor.Value),
                                           IFormula] {
    def apply(f : IFormula) : IFormula = this.visit(f, (Quantifier.ALL, null))
    
    override def preVisit(t : IExpression,
                          lastOps : (Quantifier, IBinJunctor.Value))
                        : PreVisitResult =
      t match {
        case Literal(t) =>
          // do not look into atoms
          ShortCutResult(t)
        case IQuantified(q, _) =>
          UniSubArgs((q, null))
        case IBinFormula(j, _, _) =>
          UniSubArgs((lastOps._1, j))
        case _ =>
          KeepArg
      }
  
    def postVisit(t : IExpression,
                  lastOps : (Quantifier, IBinJunctor.Value),
                  subres : Seq[IFormula]) : IFormula =
      t match {
        case t@IBinFormula(j, _, _) if (j != lastOps._2) => {
          val lastQuan = lastOps._1
          val newT = t update subres
          val parts = LineariseVisitor(newT, j)

          // are there any quantifiers to pull out?
          if (parts exists {
                case IQuantified(`lastQuan`, _) => true
                case _ => false
               }) {
            undistributeQuantifier(lastQuan, j, parts)
          } else {
            newT
          }
        }
        case t : IFormula =>
          t update subres
      }
  }

  /**
   * Pull up the outermost quantifiers <code>quan</code> in the
   * <code>parts</code> formulas to the top.
   */
  private def undistributeQuantifier(quan : Quantifier,
                                     junctor : IBinJunctor.Value,
                                     parts : Seq[IFormula]) : IFormula = {
    // determine the sorts of quantifiers
    val bodyQuans = parts map (quanSorts(_, quan, List()))
    val uniSort   = uniformSorts(bodyQuans)

    if ((junctor == And && quan == ALL || junctor == Or && quan == EX) &&
          uniSort.isDefined) {
      // find maximum number of quantifiers in any component

      val maxQuans = (bodyQuans map (_._2)) maxBy (_.size)
      val maxQuansSize = maxQuans.size
      val shiftedBodies =
        for ((body, quans) <- bodyQuans)
        yield shiftVars(body, maxQuansSize - quans.size)
      quanWithSorts(quan, maxQuans, connect(shiftedBodies, junctor))

    } else {
      // find total number of required quantifiers

      // TODO: will this list the sorts in the right order in all cases?
      val allQuans = for ((_, qs) <- bodyQuans; q <- qs) yield q
      val allQuansSize = allQuans.size
      var offset = 0
      val shiftedBodies = for ((body, quans) <- bodyQuans) yield {
        val quansSize = quans.size
        val newBody =
          VariablePermVisitor(body,
                              IVarShift(List.fill(quansSize)(offset),
                                        allQuansSize - quansSize))
        offset = offset + quansSize
        newBody
      }

      quanWithSorts(quan, allQuans, connect(shiftedBodies, junctor))
    }
  }

  private def sepQuan(f : IFormula,
                      q : Quantifier,
                      quans : List[Quantifier])
                     : (IFormula, List[Quantifier]) = f match {
    case IQuantified(`q`, subF) =>
      sepQuan(subF, q, q :: quans)
    case f =>
      (f, quans)
  }

  private def quanSorts(f : IFormula,
                        q : Quantifier,
                        sorts : List[Sort])
                     : (IFormula, List[Sort]) = f match {
    case ISortedQuantified(`q`, sort, subF) =>
      quanSorts(subF, q, sort :: sorts)
    case f =>
      (f, sorts)
  }

  private def uniformSorts(sortsFors : Seq[(IFormula, List[Sort])])
                         : Option[Sort] = {
    val sorts = for ((_, ss) <- sortsFors.iterator; s <- ss.iterator) yield s
    val sort = sorts.next
    if (sorts forall (_ == sort))
      Some(sort)
    else
      None
  }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Turn the bodies of existential quantifiers into DNF and distribute the
   * quantifiers
   */
  private object ExBodiesToDNF extends CollectingVisitor[Quantifier, IFormula] {
    def apply(f : IFormula) : IFormula = this.visit(f, null)
    
    override def preVisit(t : IExpression,
                          lastQuan : Quantifier) : PreVisitResult =
      t match {
        case Literal(t) =>
          // do not look into atoms
          ShortCutResult(t)
        case IQuantified(q, _) =>
          UniSubArgs(q)
        case _ =>
          KeepArg
      }
  
    def postVisit(t : IExpression, lastQuan : Quantifier,
                  subres : Seq[IFormula]) : IFormula = {
      incOpNum
      t match {
        case t@IBinFormula(And, _, _) if (lastQuan == EX) =>
          Conj2DNF(t update subres)
        case t@IQuantified(EX, _) =>
          DistributeEx(t update subres)
        case t : IFormula =>
          t update subres
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Turn a conjunction of two formulae in DNF into a formula in DNF
   * (i.e., one level of multiplying out)
   */
  private object Conj2DNF extends CollectingVisitor[Unit, IFormula] {
    def apply(f : IFormula) : IFormula = this.visit(f, ())
    
    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult =
      t match {
        case IBinFormula(And, IBinFormula(Or, f1, f2), f3) => {
          incOpNum
          TryAgain((f1 & f3) | (f2 & f3), ())
        }
        case IBinFormula(And, f3, IBinFormula(Or, f1, f2)) => {
          incOpNum
          TryAgain((f3 & f1) | (f3 & f2), ())
        }
        case IBinFormula(Or, _, _) =>
          KeepArg
        case t : IFormula =>
          ShortCutResult(t)
      }
  
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IFormula]) : IFormula =
      t.asInstanceOf[IFormula] update subres
  }
  
  ////////////////////////////////////////////////////////////////////////////////
  
  /**
   * Push down one quantifier as far as possible
   */
  private object PushDownQuantifier
                 extends CollectingVisitor[Boolean, IFormula] {
    def apply(f : IFormula) : IFormula = this.visit(f, false)
    
    override def preVisit(t : IExpression,
                          // used to propagate whether we already have looked
                          // at this node and pushed down a quantifier (then we
                          // can directly descend)
                          pushed : Boolean) : PreVisitResult =
      if (pushed) {
        UniSubArgs(false)
      } else t match {
        case ISortedQuantified(ALL, sort, IBinFormula(And, f1, f2)) =>
          TryAgain(sort.all(f1) & sort.all(f2), true)
        case ISortedQuantified(EX, sort, IBinFormula(Or, f1, f2)) =>
          TryAgain(sort.ex(f1) | sort.ex(f2), true)
        
        case ISortedQuantified(ALL, sort, IBinFormula(Or, f1, f2))
          if (!ContainsVariable(f1, 0)) =>
            TryAgain(shiftVars(f1, 1, -1) | sort.all(f2), true)
        case ISortedQuantified(ALL, sort, IBinFormula(Or, f1, f2))
          if (!ContainsVariable(f2, 0)) =>
            TryAgain(sort.all(f1) | shiftVars(f2, 1, -1), true)
        
        case ISortedQuantified(EX, sort, IBinFormula(And, f1, f2))
          if (!ContainsVariable(f1, 0)) =>
            TryAgain(shiftVars(f1, 1, -1) & sort.ex(f2), true)
        case ISortedQuantified(EX, sort, IBinFormula(And, f1, f2))
          if (!ContainsVariable(f2, 0)) =>
            TryAgain(sort.ex(f1) & shiftVars(f2, 1, -1), true)
      
        case IQuantified(_, t)
          if (!ContainsVariable(t, 0)) =>
            ShortCutResult(shiftVars(t, 1, -1))
          
        case t : IFormula =>
          ShortCutResult(t)
      }
  
    def postVisit(t : IExpression, pushed : Boolean,
                  subres : Seq[IFormula]) : IFormula =
      t.asInstanceOf[IFormula] update subres
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private object DistributeEx extends CollectingVisitor[Unit, IFormula] {
    def apply(f : IFormula) : IFormula = this.visit(f, ())
  
    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult =
      t match {
        case IBinFormula(Or, _, _) =>
          KeepArg
        case ISortedQuantified(EX, sort, IBinFormula(Or, f1, f2)) =>
          TryAgain(sort.ex(f1) | sort.ex(f2), ())
        case t@IQuantified(_, sub) => {
          incOpNum
          if (ContainsVariable(sub, 0))
            ShortCutResult(t)
          else
            ShortCutResult(shiftVars(sub, 1, -1))
        }
      }
    
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IFormula]) : IFormula =
      t.asInstanceOf[IFormula] update subres
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Simplify the bodies of existential quantifiers by turning
   * <code>ALL ... & ALL ...</code> into <code>ALL (... & ...)</code>
   */
  private object CompactifyExBodies
                 extends CollectingVisitor[Boolean, IFormula] {
    def apply(f : IFormula) : IFormula = this.visit(f, false)
    
    override def preVisit(t : IExpression, underEx : Boolean) : PreVisitResult =
      t match {
        case Literal(t) =>
          ShortCutResult(t)
        case IQuantified(EX, IQuantified(EX, _)) => {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, !underEx)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          KeepArg
        }
        case IQuantified(EX, _) => {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, !underEx)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          UniSubArgs(true)
        }
        case _ : IFormula =>
          UniSubArgs(false)
      }

    def postVisit(t : IExpression, underEx : Boolean,
                  subres : Seq[IFormula]) : IFormula = t match {
      case t@IBinFormula(And, _, _) if (underEx) => {
        val newT = t update subres

        val (withQuans, withoutQuans) =
          LineariseVisitor(newT, IBinJunctor.And) partition {
            case IQuantified(ALL, _) => true
            case _ => false
          }

        if (withQuans.size <= 1) {
          newT
        } else {
          and(withoutQuans) &&&
          undistributeQuantifier(ALL, IBinJunctor.And, withQuans)
        }
      }

      case t : IFormula =>
        t update subres
    }
  }

}

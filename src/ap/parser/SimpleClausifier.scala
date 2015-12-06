/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2014 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.terfor.conjunctions.Quantifier
import ap.util.{Debug, Seqs, PlainRange}

import IBinJunctor._
import IExpression._
import Quantifier._

object SimpleClausifier {

  private val AC = Debug.AC_INPUT_ABSY
  
  def apply(f : IFormula) : IFormula = {
    val f1 = Transform2NNF(f)
    val f2 = PushDownAllQuantifiers(f1)
    val f3 = CompactifyQuantifiers(f2)
    val f4 = ExBodiesToDNF(f3)
    val f5 = CompactifyExBodies(f4)
    f5
  }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Push down all quantifiers but the outermost ALL quantifiers down as far
   * as possible
   */
  private object PushDownAllQuantifiers
                 extends CollectingVisitor[Boolean, IFormula] {
    def apply(f : IFormula) : IFormula = this.visit(f, false)
    
    override def preVisit(t : IExpression, underneathEx : Boolean) : PreVisitResult =
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
        case t@IQuantified(q, _) if (underneathEx || q == EX) =>
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
                          lastOps : (Quantifier, IBinJunctor.Value)) : PreVisitResult =
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
  
    def postVisit(t : IExpression, lastOps : (Quantifier, IBinJunctor.Value),
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

            val bodyQuans = parts map (sepQuan(_, lastQuan, List()))

            if (j == And && lastQuan == ALL || j == Or && lastQuan == EX) {
              // find maximum number of quantifiers in any component

              val maxQuans = (bodyQuans map (_._2)) maxBy (_.size)
              val maxQuansSize = maxQuans.size
              val shiftedBodies =
                for ((body, quans) <- bodyQuans)
                yield VariableShiftVisitor(body, 0, maxQuansSize - quans.size)
              quan(maxQuans, connect(shiftedBodies, j))

            } else {
              // find total number of required quantifiers

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

              quan(allQuans, connect(shiftedBodies, j))
            }

          } else {
            newT
          }
        }
        case t : IFormula =>
          t update subres
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

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Turn the bodies of existential quantifiers into DNF and distribute the
   * quantifiers
   */
  private object ExBodiesToDNF extends CollectingVisitor[Quantifier, IFormula] {
    def apply(f : IFormula) : IFormula = this.visit(f, null)
    
    override def preVisit(t : IExpression, lastQuan : Quantifier) : PreVisitResult =
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
                  subres : Seq[IFormula]) : IFormula =
      t match {
        case t@IBinFormula(And, _, _) if (lastQuan == EX) =>
          Conj2DNF(t update subres)
        case t@IQuantified(EX, _) =>
          DistributeEx(t update subres)
        case t : IFormula =>
          t update subres
      }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Pull up all quantifiers of the kind <code>quanToPullUp</code> one step
   * over a binary propositional connective. This transforms, e.g.,
   * <code> (ALL ALL ... ) | (ALL ALL ...)</code> into
   * <code> ALL ALL ALL ALL .... (... | ...)</code>
   */
  private object PullUpQuantifier extends CollectingVisitor[Quantifier, IFormula] {
    def apply(f : IFormula, quanToPullUp : Quantifier) : IFormula =
      this.visit(f, quanToPullUp)
    
    override def preVisit(t : IExpression, quanToPullUp : Quantifier) : PreVisitResult =
      t match {
        case IBinFormula(j,
                         IQuantified(`quanToPullUp`, f1),
                         IQuantified(`quanToPullUp`, f2))
          if (j == And && quanToPullUp == ALL || j == Or && quanToPullUp == EX) =>
            TryAgain(IQuantified(quanToPullUp, IBinFormula(j, f1, f2)),
                     quanToPullUp)
        case IBinFormula(j, IQuantified(`quanToPullUp`, f1), f2) =>
          TryAgain(IQuantified(quanToPullUp,
                               IBinFormula(j, f1, VariableShiftVisitor(f2, 0, 1))),
                   quanToPullUp)
        case IBinFormula(j, f1, IQuantified(`quanToPullUp`, f2)) =>
          TryAgain(IQuantified(quanToPullUp,
                               IBinFormula(j, VariableShiftVisitor(f1, 0, 1), f2)),
                   quanToPullUp)
        case IQuantified(`quanToPullUp`, _) =>
          KeepArg
        case t : IFormula =>
          ShortCutResult(t)
      }
  
    def postVisit(t : IExpression, quanToPullUp : Quantifier,
                  subres : Seq[IFormula]) : IFormula =
      t.asInstanceOf[IFormula] update subres
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
        case IBinFormula(And, IBinFormula(Or, f1, f2), f3) =>
          TryAgain((f1 & f3) | (f2 & f3), ())
        case IBinFormula(And, f3, IBinFormula(Or, f1, f2)) =>
          TryAgain((f3 & f1) | (f3 & f2), ())
        case IBinFormula(Or, _, _) =>
          KeepArg
        case t : IFormula =>
          ShortCutResult(t)
      }
  
    def postVisit(t : IExpression, arg : Unit, subres : Seq[IFormula]) : IFormula =
      t.asInstanceOf[IFormula] update subres
  }
  
  ////////////////////////////////////////////////////////////////////////////////
  
  /**
   * Push down one quantifier as far as possible
   */
  private object PushDownQuantifier extends CollectingVisitor[Boolean, IFormula] {
    def apply(f : IFormula) : IFormula = this.visit(f, false)
    
    override def preVisit(t : IExpression,
                          // used to propagate whether we already have looked
                          // at this node and pushed down a quantifier (then we
                          // can directly descend)
                          pushed : Boolean) : PreVisitResult =
      if (pushed) {
        UniSubArgs(false)
      } else t match {
        case IQuantified(ALL, IBinFormula(And, f1, f2)) =>
          TryAgain(all(f1) & all(f2), true)
        case IQuantified(EX, IBinFormula(Or, f1, f2)) =>
          TryAgain(ex(f1) | ex(f2), true)
        
        case IQuantified(ALL, IBinFormula(Or, f1, f2))
          if (!ContainsSymbol(f1, IVariable(0))) =>
            TryAgain(VariableShiftVisitor(f1, 1, -1) | all(f2), true)
        case IQuantified(ALL, IBinFormula(Or, f1, f2))
          if (!ContainsSymbol(f2, IVariable(0))) =>
            TryAgain(all(f1) | VariableShiftVisitor(f2, 1, -1), true)
        
        case IQuantified(EX, IBinFormula(And, f1, f2))
          if (!ContainsSymbol(f1, IVariable(0))) =>
            TryAgain(VariableShiftVisitor(f1, 1, -1) & ex(f2), true)
        case IQuantified(EX, IBinFormula(And, f1, f2))
          if (!ContainsSymbol(f2, IVariable(0))) =>
            TryAgain(ex(f1) & VariableShiftVisitor(f2, 1, -1), true)
      
        case IQuantified(_, t)
          if (!ContainsSymbol(t, IVariable(0))) =>
            ShortCutResult(VariableShiftVisitor(t, 1, -1))
          
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
        case IQuantified(EX, IBinFormula(Or, f1, f2)) =>
          TryAgain(ex(f1) | ex(f2), ())
        case t@IQuantified(_, sub) =>
          if (ContainsSymbol(sub, IVariable(0)))
            ShortCutResult(t)
          else
            ShortCutResult(VariableShiftVisitor(sub, 1, -1))
      }
    
    def postVisit(t : IExpression, arg : Unit, subres : Seq[IFormula]) : IFormula =
      t.asInstanceOf[IFormula] update subres
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
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
          val bodyQuans = withQuans map (sepQuan(_, ALL, List()))
          val maxQuans = (bodyQuans map (_._2)) maxBy (_.size)
          val maxQuansSize = maxQuans.size
          val shiftedBodies =
            for ((body, quans) <- bodyQuans)
            yield VariableShiftVisitor(body, 0, maxQuansSize - quans.size)
          and(withoutQuans) &&& quan(maxQuans, and(shiftedBodies))
        }
      }

      case t : IFormula =>
        t update subres
    }
  }

}

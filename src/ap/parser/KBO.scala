/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.terfor.ConstantTerm
import ap.util.Seqs

/**
 * Implementation of the Knuth-Bendix term order
 * 
 * The used weights are:
 *    IFunction, IConstant => as given by the weight functions
 *    IIntLit              => 1
 *    IVariable            => 1
 *    ITimes, IPlus        => 0
 *    
 * The used basic ordering is:
 *    functions > + > * > constants > Variables > literals 
 *    
 */
class KBO(funWeights : IFunction => Int, constWeights : ConstantTerm => Int,
          funOrder : Ordering[IFunction], constOrder : Ordering[ConstantTerm])
      extends Ordering[ITerm] {

  private def weight(t : ITerm) : Int = t match {
    case IConstant(c) =>
      constWeights(c)
    case IFunApp(f, args) =>
      funWeights(f) + (for (a <- args.iterator) yield weight(a)).sum
    case IPlus(t1, t2) =>
      weight(t1) + weight(t2)
    case ITimes(_, t) =>
      weight(t)
    case _ : IIntLit | _ : IVariable =>
      1
  }

  private val headSymComparator = new Ordering[ITerm] {
    def compare(t1 : ITerm, t2 : ITerm) : Int =
      Seqs.lexCombineInts(headSymKind(t1) - headSymKind(t2), (t1, t2) match {
        case (IFunApp(f1, _), IFunApp(f2, _)) => funOrder.compare(f1, f2)
        case (IConstant(c1), IConstant(c2))   => constOrder.compare(c1, c2)
        case (IVariable(i1), IVariable(i2))   => i1 - i2
        case (IIntLit(v1), IIntLit(v2))       => v1 compare v2
      })
      
    private def headSymKind(t : ITerm) : Int = t match {
      case _ : IFunApp   => 6
      case _ : IPlus     => 5
      case _ : ITimes    => 4
      case _ : IConstant => 3
      case _ : IVariable => 2
      case _ : IIntLit   => 1
    }
  }
  
  private implicit val exprOrdering = new Ordering[IExpression] {
    def compare(e1 : IExpression, e2 : IExpression) : Int =
      KBO.this.compare(e1.asInstanceOf[ITerm], e2.asInstanceOf[ITerm])
  }
  
  def compare(t1 : ITerm, t2 : ITerm) : Int =
    Seqs.lexCombineInts(weight(t1) - weight(t2),
                        headSymComparator.compare(t1, t2),
                        Seqs.lexCompareOrdering(t1.iterator, t2.iterator))
}
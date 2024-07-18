/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011-2024 Philipp Ruemmer <ph_r@gmx.net>
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
        case _                                => 0
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
  
  private implicit val exprOrdering : Ordering[IExpression] =
    new Ordering[IExpression] {
      def compare(e1 : IExpression, e2 : IExpression) : Int =
        KBO.this.compare(e1.asInstanceOf[ITerm], e2.asInstanceOf[ITerm])
    }
  
  def compare(t1 : ITerm, t2 : ITerm) : Int =
    Seqs.lexCombineInts(weight(t1) - weight(t2),
                        headSymComparator.compare(t1, t2),
                        Seqs.lexCompareOrdering(t1.iterator, t2.iterator))
}

/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013 Philipp Ruemmer <ph_r@gmx.net>
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

import ap._
import IExpression.Predicate

import scala.collection.mutable.{HashMap => MHashMap, LinkedHashMap,
                                  ArrayBuffer}

/**
 * Class to compress chains of implications, for faster constraint
 * propagation
 */
object ImplicationCompressor {

  private type SignedPredicate = (Predicate, Boolean)

  def apply(f : IFormula) : IFormula = {

    val implications = new LinkedHashMap[SignedPredicate, List[SignedPredicate]]

    def addImp(p : SignedPredicate, q : SignedPredicate) =
      if (p != q)
        implications.put(p, q :: implications.getOrElse(p, List()))
    
    // Extract an implication graph from the input formulae
    // Recognised patterns include:
    // !a | b                (succedent:  a & !b)
    // (a & b) | (!a & !b)   (succedent:  (!a | !b) & (a | b))

    for (p <- LineariseVisitor(Transform2NNF(f), IBinJunctor.Or)) {println(p); p match {
      case IBinFormula(IBinJunctor.And, left, right) => {
        val leftFors = LineariseVisitor(left, IBinJunctor.Or) filter isPred
        
        if (!leftFors.isEmpty) {
          val rightFors = LineariseVisitor(right, IBinJunctor.Or) filter isPred
          for (p <- rightFors) {
            val (posP, negP) = toSignedPreds(p)
            for (q <- leftFors) {
              val (posQ, negQ) = toSignedPreds(q)
              addImp(posP, negQ)
              addImp(posQ, negP)
            }
          }
        }
      }
      case _ => // nothing
    }}

    println(implications)
    
    null
  }

  private val isPred : Function[IFormula, Boolean] = {
    case IAtom(_, Seq()) => true
    case INot(IAtom(_, Seq())) => true
    case _ => false
  }

  private def toSignedPreds(f : IFormula) = f match {
    case IAtom(p, _)       => ((p, true), (p, false))
    case INot(IAtom(p, _)) => ((p, false), (p, true))
  }
  
}

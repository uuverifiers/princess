/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

import ap._
import IExpression.Predicate

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 LinkedHashMap, LinkedHashSet,
                                 ArrayBuffer, ArrayStack}

/**
 * Class to compress chains of implications, for faster constraint
 * propagation
 */
object ImplicationCompressor {

  import IExpression._
    
  def apply(f : IFormula) : IFormula = {

    val nnfF = Transform2NNF(f)

    val implications = new MHashMap[IFormula, List[IFormula]]
    val allPreds = new LinkedHashSet[IFormula]
    
    def addImp(p : IFormula, q : IFormula) = if (p != q) {
      allPreds += p
      allPreds += q
      implications.put(p, q :: implications.getOrElse(p, List()))
    }
    
    // Extract an implication graph from the input formulae
    // Recognised patterns include:
    // !a | b                (succedent:  a & !b)
    // (a & b) | (!a & !b)   (succedent:  (!a | !b) & (a | b))

    for (p <- LineariseVisitor(nnfF, IBinJunctor.Or)) p match {
      case IBinFormula(IBinJunctor.And, left, right) => {
        val leftFors = LineariseVisitor(left, IBinJunctor.Or) filter isPred
        
        if (!leftFors.isEmpty) {
          val rightFors = LineariseVisitor(right, IBinJunctor.Or) filter isPred
          for (p <- rightFors; q <- leftFors) {
            addImp(~p, q)
            addImp(~q, p)
          }
        }
      }
      case _ => // nothing
    }

//    println(implications)

    def impliedPreds(p : IFormula) : Option[Seq[IFormula]] = {
      val todo = new ArrayStack[IFormula]
      val res = new LinkedHashSet[IFormula]
      
      todo push p
      
      while (!todo.isEmpty) {
        val next = todo.pop
        if (!(res contains next)) {
          if (res contains ~next)
            return None
          res += next
          todo ++= implications.getOrElse(next, List())
        }
      }
      
      Some(res.toSeq)
    }

    val replacements = (for (p <- allPreds.iterator) yield impliedPreds(p) match {
      case None => (p -> p)
      case Some(preds) => (p -> or(preds))
    }).toMap

    PredReplacer.visit(nnfF, replacements)
    
    /*
    // Compute strongly connected components, Tarjan's algorithm
    
    val rootPointer = new MHashMap[IFormula, IFormula]
    val roots = new LinkedHashSet[IFormula]
    
    {
      var index = 0
      val stack = new LinkedHashSet[IFormula]
      val predIndex = new MHashMap[IFormula, Int]
      val predLowIndex = new MHashMap[IFormula, Int]
      
      def connect(p : IFormula) : Unit = {
        predIndex.put(p, index)
        predLowIndex.put(p, index)
        index = index + 1
        stack += p
        
        for (q <- implications.getOrElse(p, List())) {
          if (!(predIndex contains q)) {
            connect(q)
            predLowIndex.put(p, predLowIndex(p) min predLowIndex(q))
          } else if (stack contains q) {
            predLowIndex.put(p, predLowIndex(p) min predIndex(q))
          }
        }
        
        if (predIndex(p) == predLowIndex(p)) {
          // found a component
          roots += p
          var cont = true
          while (cont) {
            val q = stack.last
            stack remove q
            rootPointer.put(q, p)
            if (q == p)
              cont = false
          }
        }
      }
      
      for (p <- allPreds)
        if (!(predIndex contains p))
          connect(p)
    }

    // Build lemmas shortening implication chains
    import IExpression._
    
    def impliedPreds(p : IFormula) : Option[Seq[IFormula]] = {
      val todo = new ArrayStack[IFormula]
      val res = new LinkedHashSet[IFormula]
      
      todo push p
      
      while (!todo.isEmpty) {
        val next = todo.pop
        if (!(res contains next)) {
          if (res contains ~next)
            return None
          res += next
          todo ++= implications.getOrElse(next, List())
        }
      }
      
      Some(res.toSeq)
    }
    
    val componentsDone = new MHashSet[IFormula]
    val lemmas = new ArrayBuffer[IFormula]
    
    for (p <- roots) if (!(componentsDone contains p)) {
      (impliedPreds(p), impliedPreds(~p)) match {
        case (None, None) =>
          lemmas += false
        case (Some(preds), None) =>
          lemmas += and(preds)
        case (None, Some(preds)) =>
          lemmas += and(preds)
        case (Some(preds1), Some(preds2))
          if (preds1.size > 2 || preds2.size > 2) =>
          lemmas += and(preds1) | and(preds2)
        case _ => // nothing
      }
      
      componentsDone += p
      componentsDone += rootPointer(~p)
    }
    
//    println(lemmas)
    
    for (p <- allPreds)
      println("" + p + " -> " + impliedPreds(p))
    
    !and(lemmas)
   */
  }

  private val isPred : Function[IFormula, Boolean] = {
    case IAtom(_, Seq()) => true
    case INot(IAtom(_, Seq())) => true
    case _ => false
  }

  private object PredReplacer
    extends CollectingVisitor[Map[IFormula, IFormula], IFormula] {
      
    override def preVisit(t : IExpression,
                            replacements : Map[IFormula, IFormula]) : PreVisitResult =
      t match {
      case p@(INot(IAtom(_, Seq())) | IAtom(_, Seq())) =>
        (replacements get p.asInstanceOf[IFormula]) match {
          case Some(repl) => ShortCutResult(repl)
          case None       => ShortCutResult(p.asInstanceOf[IFormula])
        }
      case _ : IBinFormula => KeepArg
      case f : IFormula => ShortCutResult(f)
    }

    def postVisit(t : IExpression,
                  replacements : Map[IFormula, IFormula],
                  subres : Seq[IFormula]) : IFormula =
      (t update subres).asInstanceOf[IFormula]
  }
    
}

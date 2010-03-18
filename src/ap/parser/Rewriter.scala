/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.util.Debug

import scala.collection.mutable.Stack

/**
 * Simple rewriting engine on the input AST datastructures
 */
object Rewriter {

  private val AC = Debug.AC_INPUT_ABSY
  
  /**
   * Exhaustively apply the given rewriting rule to the expression
   * (and to all of its subexpressions). The rewriting rule should signal
   * that it is not applicable by returning the unmodified (identical) argument
   */
  def rewrite(expr : IExpression,
              rewritingRule : IExpression => IExpression) : IExpression = {

    // apply the rule until we have reached a fixed-point
    def fixRewriting(e : IExpression) : IExpression = {
      var expr = e
      var oldExpr : IExpression = null
      while (!(expr eq oldExpr)) {
        oldExpr = expr
        expr = rewritingRule(expr)
      }
      expr
    }
    
    val toVisit = new Stack[IExpression]
    val results = new Stack[IExpression]
    
    def pushSubExpr(expr : IExpression) : Unit = {
      toVisit push PostVisit(expr)
      for (i <- (expr.length - 1) to 0 by -1) toVisit push expr(i)
    }
    
    toVisit push expr
    
    while (!toVisit.isEmpty) toVisit.pop match {
      case PostVisit(oldExpr) => {
        var subRes : List[IExpression] = List()
        for (_ <- 0 until oldExpr.length) subRes = results.pop :: subRes
        
        val newExpr = oldExpr update subRes

        if (newExpr eq oldExpr) {
          // if no changes have been made, the expression is irreducible
          results push oldExpr
        } else {
          val rewrittenExpr = fixRewriting(newExpr)
          if (rewrittenExpr eq newExpr)
            // the expression is irreducible
            results push newExpr
          else
            // otherwise we have to continue rewriting
            pushSubExpr(rewrittenExpr)
        }
      }
      
      case e => pushSubExpr(fixRewriting(e))
    }
    
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertInt(AC, results.size == 1)
    ////////////////////////////////////////////////////////////////////////////
    
    results.pop
  }
  
  private case class PostVisit(expr : IExpression) extends IExpression

  /**
   * Combine the given rewriting rules to a rule that always applies the first
   * applicable rewriting rule
   */
  def combineRewritings(rewritings : Seq[IExpression => IExpression])
                       : (IExpression => IExpression) = (e) => {
    var expr = e

    var i : Int = 0
    while (i < rewritings.size && (expr eq e)) {
      expr = rewritings(i)(e)
      i = i + 1
    }
    
    expr
  }
  
}

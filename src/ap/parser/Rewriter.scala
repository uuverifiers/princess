/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.util.Debug

import scala.collection.mutable.{ArrayStack => Stack}

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
    
    while (!toVisit.isEmpty) toVisit.pop() match {
      case PostVisit(oldExpr) => {
        var subRes : List[IExpression] = List()
        for (_ <- 0 until oldExpr.length) subRes = results.pop() :: subRes
        
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
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(AC, results.size == 1)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    results.pop()
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

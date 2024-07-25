/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2021 Philipp Ruemmer <ph_r@gmx.net>
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

/**
 * Class to turn <-> into conjunction and disjunctions, eliminate
 * if-then-else expressions and epsilon terms, and move universal quantifiers
 * outwards (to make later Skolemisation more efficient; currently disabled)
 */
object EquivExpander extends ContextAwareVisitor[Unit, IExpression] {

  import IExpression._
  
  def apply(f : IFormula) : IFormula =
    this.visit(f, Context(())).asInstanceOf[IFormula]
  
  override def preVisit(t : IExpression, c : Context[Unit]) : PreVisitResult =
    t match {
    
      case LeafFormula(t) => {
        // check whether there are any ite terms that we have to expand

        val iteSearcher = new ITESearcher
        iteSearcher.visit(t, true) match {
          case Some(p) =>
            expandITE(iteSearcher.iteCond,
                      p._1.asInstanceOf[IFormula], p._2.asInstanceOf[IFormula],
                      c)
          
          case None => {
            // check whether there are any epsilon terms that we have to expand

            val epsSearcher =
              new EPSSearcher2
            val epsLessFor =
              epsSearcher.visit(t,Context(())).asInstanceOf[IFormula]
        
            if (epsSearcher.foundEPS == null) {
              ShortCutResult(t)
            } else {
              val sort = epsSearcher.foundEPS.sort

              // replace the eps constant with a fresh variable, shift all other
              // variables upwards
              val shiftedBody = new VariableShiftVisitor(0, 1) {
                override def postVisit(t : IExpression, quantifierNum : Int,
                                       subres : Seq[IExpression]) : IExpression=
                  t match {
                    case IConstant(c) if (c == epsSearcher.epsConst) =>
                      v(quantifierNum, sort)
                    case t =>
                      super.postVisit(t, quantifierNum, subres)
                  }
              }.visit(epsLessFor, 0).asInstanceOf[IFormula]
        
              TryAgain(if (c.polarity > 0)
                         sort.all(epsSearcher.foundEPS.cond ==> shiftedBody)
                       else
                         sort.ex(epsSearcher.foundEPS.cond & shiftedBody),
                       c)
            }
          }
        }
      }
      
      case IFormulaITE(cond, left, right) =>
        expandITE(cond, left, right, c)
      
      case IBinFormula(IBinJunctor.Eqv, f1, f2) =>
        if ((c.binders contains Context.EX) ^ (c.polarity < 0))
          TryAgain((f1 &&& f2) ||| (~f1 &&& ~f2), c)
        else
          TryAgain((f1 ===> f2) &&& (f2 ===> f1), c)
          
      case _ =>
        super.preVisit(t, c)
    }

  private def expandITE(cond : IFormula,
                        left : IFormula, right : IFormula,
                        c : Context[Unit]) = 
    if (// (c.binders contains Context.EX) ^ 
        (c.polarity < 0))
      TryAgain((cond &&& left) ||| (~cond &&& right), c)
    else
      TryAgain((cond ===> left) &&& (~cond ===> right), c)
  
  def postVisit(t : IExpression, c : Context[Unit],
                subres : Seq[IExpression]) : IExpression = t match {
    // Pull up existential quantifiers, if there are any. E.g.,
    // EX f1 & EX f2  ~~>   EX EX (f1 & f2)
    // This speeds up solving of formulas with many eps-expressions, which
    // otherwise lead to many quantifiers distributed throughout the formula

/*
 Disabled, since it breaks some test cases; needs more work

    case IBinFormula(IBinJunctor.And | IBinJunctor.Or, _, _) => {
      val q = Quantifier(c.polarity > 0)
      val (leftQuans,  leftF)  = extrQuans(subres(0).asInstanceOf[IFormula], q)
      val (rightQuans, rightF) = extrQuans(subres(1).asInstanceOf[IFormula], q)
      val shiftedLeft  = VariableShiftVisitor(leftF,  0,          rightQuans)
      val shiftedRight = VariableShiftVisitor(rightF, rightQuans, leftQuans)
      quan(for (_ <- 0 until (leftQuans + rightQuans)) yield q,
           updateAndSimplifyLazily(t,
             List(shiftedLeft, shiftedRight)).asInstanceOf[IFormula])
    }

    case _ : INot => {
      val q = Quantifier(c.polarity > 0)
      val dualQ = q.dual
      val (quans, subfor) = extrQuans(subres(0).asInstanceOf[IFormula], q)
      quan(for (_ <- 0 until quans) yield dualQ, ~subfor)
    }
 */
    case t =>
      updateAndSimplifyLazily(t, subres)
  }

  /**
   * Strip a formula of leading quantifiers
   */
  private def extrQuans(f : IFormula, q : Quantifier) : (Int, IFormula) = {
    var quanNum = 0
    var resF = f

    while (resF.isInstanceOf[IQuantified] &&
           resF.asInstanceOf[IQuantified].quan == q) {
      quanNum = quanNum + 1
      resF = resF.asInstanceOf[IQuantified].subformula
    }

    resF match {
      case _ : ITrigger =>
        // we need to keep the quantifiers in place in this case, otherwise
        // we get dangling triggers
        (0, f)
      case _ =>
        (quanNum, resF)
    }
  }

}

/**
 * Search for occurrences of EPS in the given formula. The first found
 * occurrence is stored in the field <code>foundEPS</code> and replaced with a
 * fresh constant <code>epsConst</code>
 */
private class EPSSearcher extends CollectingVisitor[Boolean, IExpression] {
  
  import IExpression._
  
  var foundEPS : IEpsilon = _
  var epsConst : ConstantTerm = _
  
  override def preVisit(t : IExpression,
                        descendIntoFors : Boolean) : PreVisitResult =
    t match {
      case t : IEpsilon if (foundEPS == null) => {
        foundEPS = t
        epsConst = t.sort newConstant "eps"
        ShortCutResult(epsConst)
      }
      case t : IEpsilon if (foundEPS == t) =>
        ShortCutResult(epsConst)
      case t : IEpsilon if (foundEPS != null) =>
        ShortCutResult(t)
      case t : ITerm =>
        UniSubArgs(false)
      case t : IFormula =>
        // only descend into the first level of formulae
        if (descendIntoFors) KeepArg else ShortCutResult(t)
    }
  
  def postVisit(t : IExpression,
                descendIntoFors : Boolean,
                subres : Seq[IExpression]) : IExpression =
    t update subres
  
}

/**
 * Search for occurrences of EPS in the given formula. The first found
 * occurrence is stored in the field <code>foundEPS</code> and replaced with a
 * fresh constant <code>epsConst</code>. This version of the visitor
 * works inside-out.
 * 
 * TODO: replace multiple epsilons simultaneously
 */
private class EPSSearcher2 extends ContextAwareVisitor[Unit, IExpression] {
  
  import IExpression._
  
  var foundEPS : IEpsilon = _
  var epsConst : ConstantTerm = _
  
  def postVisit(t : IExpression,
                ctxt : Context[Unit],
                subres : Seq[IExpression]) : IExpression =
    (t update subres) match {
      case t : IEpsilon => {
        val N = ctxt.binders.size
        if (ContainsSymbol.allVariablesAtLeast(t, N)) {
          val shiftedT = VariableShiftVisitor(t, N, -N).asInstanceOf[IEpsilon]
          if (foundEPS == null) {
            foundEPS = shiftedT
            epsConst = t.sort newConstant "eps"
            epsConst
          } else if (shiftedT == foundEPS) {
            epsConst
          } else {
            t
          }
        } else {
          t
        }
      }
      case t =>
        t
    }
  
}

/**
 * Search for occurrences of ITE in the given formula. For the first found
 * occurrence, the condition is stored in the field <code>iteCond</code>,
 * and two versions of the sub-expressions are generated (one for the then-,
 * one for the else-branch)
 */
private class ITESearcher
              extends CollectingVisitor[Boolean,
                                        Option[(IExpression, IExpression)]] {
  
  import IExpression._
  
  var iteCond  : IFormula = _
  
  override def preVisit(t : IExpression,
                        descendIntoFors : Boolean) : PreVisitResult =
    t match {
      case ITermITE(cond, left, right) if (iteCond == null) => {
        iteCond = cond
        ShortCutResult(Some(left, right))
      }
      case ITermITE(cond, left, right) if (iteCond == cond) =>
        ShortCutResult(Some(left, right))
      case t : ITerm =>
        UniSubArgs(false)
      case t : IFormula =>
        // only descend into the first level of formulae
        if (descendIntoFors) KeepArg else ShortCutResult(None)
    }
  
  def postVisit(t : IExpression,
                descendIntoFors : Boolean,
                subres : Seq[Option[(IExpression, IExpression)]])
               : Option[(IExpression, IExpression)] =
    if (iteCond == null) {
      None
    } else {
      val (leftSubres, rightSubres) =
        (for ((n, old) <- subres zip t.subExpressions)
           yield (n getOrElse (old, old))).unzip
      Some((updateAndSimplifyLazily(t, leftSubres),
            updateAndSimplifyLazily(t, rightSubres)))
    }

}

/**
 * Visitor for replacing if-then-else expressions with epsilon terms
 */
/*
private object TermITETranslator extends CollectingVisitor[Unit, IExpression] {
  import IExpression._
  
  def postVisit(t : IExpression,
                arg : Unit,
                subres : Seq[IExpression]) : IExpression = t match {
    case _ : ITermITE => {
      val cond = VariableShiftVisitor(subres(0), 0, 1).asInstanceOf[IFormula]
      val left = VariableShiftVisitor(subres(1), 0, 1).asInstanceOf[ITerm]
      val right = VariableShiftVisitor(subres(2), 0, 1).asInstanceOf[ITerm]
      eps((!cond | (v(0) === left)) & (cond | (v(0) === right)))
    }
    case t =>
      t update subres
  }
}
*/

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
          case Some((thenFor : IFormula, elseFor : IFormula)) =>
            expandITE(iteSearcher.iteCond, thenFor, elseFor, c)
          
          case None => {
            // check whether there are any epsilon terms that we have to expand

            val epsSearcher = new EPSSearcher
            val epsLessFor = epsSearcher.visit(t, true).asInstanceOf[IFormula]
        
            if (epsSearcher.foundEPS == null) {
              ShortCutResult(t)
            } else {
              val sort = epsSearcher.foundEPS.sort

              // replace the eps constant with a fresh variable, shift all other
              // variables upwards
              val shiftedBody = new VariableShiftVisitor(0, 1) {
                override def postVisit(t : IExpression, quantifierNum : Int,
                                       subres : Seq[IExpression]) : IExpression =
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
      case t if (foundEPS != null) =>
        ShortCutResult(t)
      case t : IEpsilon if (foundEPS == null) => {
        foundEPS = t
        epsConst = t.sort newConstant "eps"
        ShortCutResult(epsConst)
      }
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
 * Search for occurrences of ITE in the given formula. For the first found
 * occurrence, the condition is stored in the field <code>iteCond</code>,
 * and two versions of the sub-expressions are generated (one for the then-,
 * one for the else-branch)
 */
private class ITESearcher
              extends CollectingVisitor[Boolean, Option[(IExpression, IExpression)]] {
  
  import IExpression._
  
  var iteCond : IFormula = _
  
  override def preVisit(t : IExpression,
                        descendIntoFors : Boolean) : PreVisitResult =
    t match {
      case t if (iteCond != null) =>
        ShortCutResult(None)
      case ITermITE(cond, left, right) if (iteCond == null) => {
        iteCond = cond
        ShortCutResult(Some(left, right))
      }
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

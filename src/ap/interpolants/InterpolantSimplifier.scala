/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010-2022 Philipp Ruemmer <ph_r@gmx.net>
 *                         Angelo Brillout <bangelo@inf.ethz.ch>
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

package ap.interpolants

import ap._
import ap.basetypes.IdealInt
import ap.parser._
import ap.theories.{SimpleArray, ExtArray}


/**
 * Extended version of the InputAbsy simplifier that also rewrites certain
 * array expressions:
 *    \exists int a; x = store(a, b, c)
 * is replaced with
 *    select(x, b) = c 
 */
class InterpolantSimplifier(select : IFunction, store : IFunction)
      extends ap.parser.Simplifier {
  import IBinJunctor._
  import IIntRelation._
  import IExpression._
  import Quantifier._

  private class StoreRewriter(depth : Int) {
    var foundProblem : Boolean = false
    var storeArgs : Option[(ITerm, ITerm)] = None

    def rewrite(t : ITerm) : ITerm = t match {
      case IPlus(t1, t2) => rewrite(t1) +++ rewrite(t2)
      case IFunApp(`store`, Seq(IVariable(`depth`), t1, t2)) => {
        if (storeArgs != None)
          foundProblem = true
        storeArgs = Some(shiftVariables(t1), shiftVariables(t2))
        0
      }
      case _ => shiftVariables(t)
    }
    
    private def shiftVariables(t : ITerm) : ITerm = {
      if ((SymbolCollector variables t) contains IVariable(depth))
        foundProblem = true
      VariableShiftVisitor(t, depth + 1, -1)
    }
  }
  
  private def rewriteEquation(t : ITerm, depth : Int) : Option[IFormula] = {
    val rewriter = new StoreRewriter(depth)
    val newT = rewriter rewrite t

    rewriter.storeArgs match {
      case Some((t1, t2)) if (!rewriter.foundProblem) =>
        Some(select(-newT, t1) === t2)
      case _ =>
        None
    }
  }
  
  private def translate(f : IFormula,
                        negated : Boolean,
                        depth : Int) : Option[IFormula] = f match {
      
    case ISortedQuantified(q, sort, subF) if (q == Quantifier(negated)) =>
      for (res <- translate(subF, negated, depth + 1))
      yield ISortedQuantified(q, sort, res)
        
    case IIntFormula(EqZero, t) if (!negated) =>
      rewriteEquation(t, depth)
    
    case INot(IIntFormula(EqZero, t)) if (negated) =>
      for (f <- rewriteEquation(t, depth)) yield !f
        
    case _ => None
  }
  
  private def elimStore(expr : IExpression) : IExpression = expr match {
    case IQuantified(EX, f) =>  translate(f, false, 0) getOrElse expr
    case IQuantified(ALL, f) => translate(f, true, 0) getOrElse expr
    case _ => expr
  }

  protected override def furtherSimplifications(expr : IExpression) =
    elimStore(expr)
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Even more extended version of the InputAbsy simplifier that also
 * rewrites certain array expression.
 */
class ArraySimplifier extends ap.parser.Simplifier {
  import IBinJunctor._
  import IIntRelation._
  import IExpression._
  import Quantifier._

  /**
   *    \exists int a; (x = store(a, b, c) & phi)
   * is replaced with
   *    \exists int d, a; (select(x, b) = c & a = store(x, b, d) & phi)
   */
  private def elimStore(expr : IExpression) : IExpression = expr match {
    case IFunApp(SimpleArray.Select(),
                 Seq(IFunApp(SimpleArray.Store(),
                             Seq(ar, storeArgs @ _*)),
                     selectArgs @ _*))
        if (storeArgs.size == selectArgs.size + 1) =>
      ite(selectArgs === storeArgs.init,
          storeArgs.last,
          IFunApp(SimpleArray(selectArgs.size).select, List(ar) ++ selectArgs))

    case IQuantified(EX, f) =>
      (for (res <- translateStore(f, false, 0))
       yield IQuantified(EX, IQuantified(EX, res))) getOrElse expr
    case IQuantified(ALL, f) =>
      (for (res <- translateStore(f, true, 0))
       yield IQuantified(ALL, IQuantified(ALL, res))) getOrElse expr
    case _ => expr
  }

  private def translateStore(f : IFormula,
                             negated : Boolean,
                             depth : Int) : Option[IFormula] = {

    def shiftTerm(t : ITerm) : ITerm       =
      VariableShiftVisitor(t, depth + 1, 1)
    def shiftFor (f : IFormula) : IFormula =
      VariableShiftVisitor(f, depth + 1, 1)

    f match {
      case ISortedQuantified(q, sort, subF) if (q == Quantifier(negated)) =>
        for (res <- translateStore(subF, negated, depth + 1))
        yield ISortedQuantified(q, sort, res)
  
      case IBinFormula(j, left, right)
          if (j == (if (negated) IBinJunctor.Or else IBinJunctor.And)) =>
        (for (newLeft <- translateStore(left, negated, depth))
         yield IBinFormula(j, newLeft, shiftFor(right))) orElse
        (for (newRight <- translateStore(right, negated, depth))
         yield IBinFormula(j, shiftFor(left), newRight))
  
      case INot(f) =>
        for (res <- translateStore(f, !negated, depth)) yield INot(res)

      case Eq(IFunApp(SimpleArray.Store(),
                      Seq(w@IVariable(`depth`), args @ _*)), ar)
          if (!negated && !ContainsSymbol(ar, w) &&
              (args forall { t => !ContainsSymbol(t, w) })) => {
        val theory = SimpleArray(args.size - 1)
        val shiftedAr = shiftTerm(ar)
        val shiftedArgs = for (t <- args) yield shiftTerm(t)
        Some((IFunApp(theory.select, List(shiftedAr) ++ shiftedArgs.init) ===
                shiftedArgs.last) &
             (IFunApp(theory.store,
                      List(shiftedAr) ++ shiftedArgs.init ++
                      List(v(depth + 1))) === w))
      }
  
      case Eq(ar, IFunApp(SimpleArray.Store(),
                          Seq(w@IVariable(`depth`), args @ _*)))
          if (!negated && !ContainsSymbol(ar, w) &&
              (args forall { t => !ContainsSymbol(t, w) })) => {
        val theory = SimpleArray(args.size - 1)
        val shiftedAr = shiftTerm(ar)
        val shiftedArgs = for (t <- args) yield shiftTerm(t)
        Some((IFunApp(theory.select, List(shiftedAr) ++ shiftedArgs.init) ===
                shiftedArgs.last) &
             (IFunApp(theory.store,
                      List(shiftedAr) ++ shiftedArgs.init ++
                      List(v(depth + 1))) === w))
      }
  
      case _ => None
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   *    \forall int a; phi[select(a, x)]
   * is replaced with
   *    \forall int y; phi[y]
   *
   * Similarly for \exists.
   */
  private def elimQuantifiedSelect(t : IExpression) : IExpression = t match {
    case ISortedQuantified(q, sort, subF) if (SelectFromVarDetector(subF)) =>
      ISortedQuantified(q, sort, SelectReplaceVisitor(subF))
    case t => t
  }

  private object SelectFromVarDetector
          extends ContextAwareVisitor[Unit, Unit] {
    def apply(t : IFormula) : Boolean =
      try {
        uniqueArgs = null
        visitWithoutResult(t, Context(()))
        true
      } catch {
        case FoundBadVarOccurrence => false
      }

    private var uniqueArgs : Seq[ITerm] = null

    private object FoundBadVarOccurrence extends Exception

    override def preVisit(t : IExpression,
                          ctxt : Context[Unit]) : PreVisitResult = t match {
      case IFunApp(SimpleArray.Select(),
                   Seq(IVariable(depth), selectArgs @ _*))
        if (depth == ctxt.binders.size) => {

        val badSymbol = (t : IExpression) => t match {
          case IVariable(ind) if (ind <= depth) => true
          case _ => false
        }

        if (selectArgs exists (ContainsSymbol(_, badSymbol)))
          throw FoundBadVarOccurrence

        val shiftedArgs =
          (for (a <- selectArgs.iterator)
           yield VariableShiftVisitor(a, depth, -depth)).toList

        if (uniqueArgs == null)
          uniqueArgs = shiftedArgs
        else if (uniqueArgs != shiftedArgs)
          throw FoundBadVarOccurrence

        ShortCutResult(())
      }

      case IVariable(depth) if (depth == ctxt.binders.size) =>
        throw FoundBadVarOccurrence

      case _ =>
        super.preVisit(t, ctxt)
    }

    def postVisit(t : IExpression, context : Context[Unit],
                  subres : Seq[Unit]) : Unit = ()
  }

  private object SelectReplaceVisitor
          extends ContextAwareVisitor[Unit, IExpression] {

    def apply(t : IFormula) : IFormula =
      visit(t, Context(())).asInstanceOf[IFormula]

    override def preVisit(t : IExpression,
                          ctxt : Context[Unit]) : PreVisitResult = t match {
      case IFunApp(SimpleArray.Select(), Seq(v@IVariable(depth), _*))
        if (depth == ctxt.binders.size) =>
          ShortCutResult(v)

      case IVariable(depth) if (depth == ctxt.binders.size) =>
        throw new Exception

      case _ =>
        super.preVisit(t, ctxt)
    }

    def postVisit(t : IExpression, context : Context[Unit],
                  subres : Seq[IExpression]) : IExpression =
      t update subres
  }

  //////////////////////////////////////////////////////////////////////////////

  val rewritings =
    Vector(elimStore _ , elimQuantifiedSelect _)

  private val rewritingFun =
    Rewriter.combineRewritings(rewritings)
  
  protected override def furtherSimplifications(expr : IExpression) =
    rewritingFun(expr)
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Even more extended version of the InputAbsy simplifier that also
 * rewrites certain array expression.
 */
class ExtArraySimplifier extends ap.parser.Simplifier {
  import IBinJunctor._
  import IIntRelation._
  import IExpression._
  import Quantifier._

  /**
   *    store(a, b, c) = a
   * is replace with
   *    select(a, b) = c
   */
  private def rewriteStoreEq(expr : IExpression) : IExpression = expr match {
    case Eq(IFunApp(ExtArray.Store(theory),
                    Seq(ar, storeArgs @ _*)),
            ar2)                                if ar == ar2 =>
      IFunApp(theory.select, List(ar) ++ storeArgs.init) === storeArgs.last
    case Eq(ar2,
            IFunApp(ExtArray.Store(theory),
                    Seq(ar, storeArgs @ _*)))   if ar == ar2 =>
      IFunApp(theory.select, List(ar) ++ storeArgs.init) === storeArgs.last
    case _ => expr
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   *    \exists a; (x = store(a, b, c) & phi)
   * is replaced with
   *    \exists d, a; (select(x, b) = c & a = store(x, b, d) & phi)
   */
  private def elimStore(expr : IExpression) : IExpression = expr match {
    case IFunApp(ExtArray.Select(theory1),
                 Seq(IFunApp(ExtArray.Store(theory2),
                             Seq(ar, storeArgs @ _*)),
                     selectArgs @ _*))
        if theory1 == theory2 =>
      ite(selectArgs === storeArgs.init,
          storeArgs.last,
          IFunApp(theory1.select, List(ar) ++ selectArgs))

    case ISortedQuantified(EX,  ExtArray.ArraySort(theory), f) =>
      (for (res <- translateStore(f, false, 0))
       yield theory.objSort.ex(theory.sort.ex(res))) getOrElse expr
    case ISortedQuantified(ALL, ExtArray.ArraySort(theory), f) =>
      (for (res <- translateStore(f, true, 0))
       yield theory.objSort.all(theory.sort.all(res))) getOrElse expr
    case _ => expr
  }

  private def translateStore(f : IFormula,
                             negated : Boolean,
                             depth : Int) : Option[IFormula] = {

    def shiftTerm(t : ITerm) : ITerm       =
      VariableShiftVisitor(t, depth + 1, 1)
    def shiftFor (f : IFormula) : IFormula =
      VariableShiftVisitor(f, depth + 1, 1)

    f match {
      case ISortedQuantified(q, sort, subF) if (q == Quantifier(negated)) =>
        for (res <- translateStore(subF, negated, depth + 1))
        yield ISortedQuantified(q, sort, res)
  
      case IBinFormula(j, left, right)
          if (j == (if (negated) IBinJunctor.Or else IBinJunctor.And)) =>
        (for (newLeft <- translateStore(left, negated, depth))
         yield IBinFormula(j, newLeft, shiftFor(right))) orElse
        (for (newRight <- translateStore(right, negated, depth))
         yield IBinFormula(j, shiftFor(left), newRight))
  
      case INot(f) =>
        for (res <- translateStore(f, !negated, depth)) yield INot(res)

      case Eq(IFunApp(ExtArray.Store(theory),
                      Seq(w@IVariable(`depth`), args @ _*)), ar)
          if (!negated && !ContainsSymbol(ar, w) &&
              (args forall { t => !ContainsSymbol(t, w) })) => {
        val shiftedAr = shiftTerm(ar)
        val shiftedArgs = for (t <- args) yield shiftTerm(t)
        Some((IFunApp(theory.select, List(shiftedAr) ++ shiftedArgs.init) ===
                shiftedArgs.last) &
             (IFunApp(theory.store,
                      List(shiftedAr) ++ shiftedArgs.init ++
                      List(v(depth + 1, theory.objSort))) === w))
      }
  
      case Eq(ar, IFunApp(ExtArray.Store(theory),
                          Seq(w@IVariable(`depth`), args @ _*)))
          if (!negated && !ContainsSymbol(ar, w) &&
              (args forall { t => !ContainsSymbol(t, w) })) => {
        val shiftedAr = shiftTerm(ar)
        val shiftedArgs = for (t <- args) yield shiftTerm(t)
        Some((IFunApp(theory.select, List(shiftedAr) ++ shiftedArgs.init) ===
                shiftedArgs.last) &
             (IFunApp(theory.store,
                      List(shiftedAr) ++ shiftedArgs.init ++
                      List(v(depth + 1, theory.objSort))) === w))
      }
  
      case _ => None
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   *    \forall int a; phi[select(a, x)]
   * is replaced with
   *    \forall int y; phi[y]
   *
   * Similarly for \exists.
   */
  private def elimQuantifiedSelect(t : IExpression) : IExpression = t match {
    case ISortedQuantified(q, ExtArray.ArraySort(theory), subF)
           if SelectFromVarDetector(subF) =>
      ISortedQuantified(q, theory.objSort, SelectReplaceVisitor(subF, theory))
    case t => t
  }

  private object SelectFromVarDetector
          extends ContextAwareVisitor[Unit, Unit] {
    def apply(t : IFormula) : Boolean =
      try {
        uniqueArgs = null
        visitWithoutResult(t, Context(()))
        true
      } catch {
        case FoundBadVarOccurrence => false
      }

    private var uniqueArgs : Seq[ITerm] = null

    private object FoundBadVarOccurrence extends Exception

    override def preVisit(t : IExpression,
                          ctxt : Context[Unit]) : PreVisitResult = t match {
      case IFunApp(ExtArray.Select(_),
                   Seq(IVariable(depth), selectArgs @ _*))
        if (depth == ctxt.binders.size) => {

        val badSymbol = (t : IExpression) => t match {
          case IVariable(ind) if (ind <= depth) => true
          case _ => false
        }

        if (selectArgs exists (ContainsSymbol(_, badSymbol)))
          throw FoundBadVarOccurrence

        val shiftedArgs =
          (for (a <- selectArgs.iterator)
           yield VariableShiftVisitor(a, depth, -depth)).toList

        if (uniqueArgs == null)
          uniqueArgs = shiftedArgs
        else if (uniqueArgs != shiftedArgs)
          throw FoundBadVarOccurrence

        ShortCutResult(())
      }

      case IVariable(depth) if (depth == ctxt.binders.size) =>
        throw FoundBadVarOccurrence

      case _ =>
        super.preVisit(t, ctxt)
    }

    def postVisit(t : IExpression, context : Context[Unit],
                  subres : Seq[Unit]) : Unit = ()
  }

  private object SelectReplaceVisitor
          extends ContextAwareVisitor[ExtArray, IExpression] {

    def apply(t : IFormula, theory : ExtArray) : IFormula =
      visit(t, Context(theory)).asInstanceOf[IFormula]

    override def preVisit(t : IExpression,
                          ctxt : Context[ExtArray]) : PreVisitResult = t match {
      case IFunApp(ExtArray.Select(_), Seq(IVariable(depth), _*))
        if depth == ctxt.binders.size =>
          ShortCutResult(v(depth, ctxt.a.objSort))

      case IVariable(depth) if depth == ctxt.binders.size =>
        throw new Exception

      case _ =>
        super.preVisit(t, ctxt)
    }

    def postVisit(t : IExpression, context : Context[ExtArray],
                  subres : Seq[IExpression]) : IExpression =
      t update subres
  }

  //////////////////////////////////////////////////////////////////////////////

  val rewritings =
    Vector(rewriteStoreEq _, elimStore _ , elimQuantifiedSelect _)

  private val rewritingFun =
    Rewriter.combineRewritings(rewritings)
  
  protected override def furtherSimplifications(expr : IExpression) =
    rewritingFun(expr)
}

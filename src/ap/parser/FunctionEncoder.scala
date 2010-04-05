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

import ap.terfor.TermOrder
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Quantifier
import ap.util.{Debug, Seqs}

object FunctionEncoder {
  
  private val AC = Debug.AC_INPUT_ABSY
  
  import IExpression._

  //////////////////////////////////////////////////////////////////////////////
  
  private abstract class EncodingContext(val frame : AbstractionFrame)
  private case class NormalContext(_frame : AbstractionFrame)
                     extends EncodingContext(_frame)
  private case class AddDefinitions(_frame : AbstractionFrame,
                                    triggers : List[Seq[ITerm]])
                     extends EncodingContext(_frame)

  //////////////////////////////////////////////////////////////////////////////

  private def withMinimalScope(t : IFormula, f : (IFormula) => IFormula,
                               criticalVars : Iterable[IVariable]) : IFormula =
    t match {
      case IBinFormula(op, _, _) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(FunctionEncoder.AC,
                        op == IBinJunctor.And || op == IBinJunctor.Or)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        val parts = LineariseVisitor(t, op)
        val (outside, inside) =
          parts partition (x => Seqs.disjointSeq(SymbolCollector variables x,
                                                 criticalVars))
        val outsideFor = connect(outside, op)
        val insideFor = if (inside.size == 1)
          withMinimalScope(inside(0), f, criticalVars)
        else
          f(connect(inside, op))
        IBinFormula(op, outsideFor, insideFor)
      }
      case _ => f(t)
    }
                     
  //////////////////////////////////////////////////////////////////////////////

  private class TriggerVisitor(frame : AbstractionFrame)
                extends CollectingVisitor[ITerm, ITerm] {
    
    val occurringApps = new scala.collection.mutable.HashSet[IFunApp]

    def postVisit(t : IExpression, trigger : ITerm, subres : Seq[ITerm]) : ITerm =
      t match {
        case t : IFunApp => {
          val updatedT = t update subres
          val (shiftedT, definingFrame) = selectFrameFor(updatedT, frame)
          if (frame eq definingFrame) occurringApps += updatedT
          val abstractionNums = definingFrame.abstractions.getOrElse( shiftedT,
            throw new Preprocessing.PreprocessingException(
              "Trigger has to occur in body of quantified formula: " + trigger))
          if (abstractionNums.size > 1)
            throw new Preprocessing.PreprocessingException(
              "Ambiguous trigger for relational function: " + trigger)
          val abstractionNum = abstractionNums.elements.next
          v(abstractionNum + definingFrame.depth - frame.depth)
        }
        case t : ITerm => t update subres
        case _ => 
          throw new Preprocessing.PreprocessingException(
            "Unexpected expression in trigger: " + t)
      }
  }
                     
  //////////////////////////////////////////////////////////////////////////////

  // Abstraction frames are pushed immediately underneath each level of
  // quantifiers are collect all function definitions that should be
  // inserted at this point in the <code>postVisit</code> phase
  private class AbstractionFrame(val prevFrame : AbstractionFrame,
                                 // the number of quantifiers immediately above
                                 // this frame
                                 val quantifierNum : Int) {
    // Function notation can also be used for relations ("relational functions"")
    // in this case, we have to introduce distinct abstraction variables even
    // for different occurrences of the same function application.
    // e.g.  f(c) = f(c) has to be invalid if "f" is not functional
    // Therefore, the value of the abstractions map is a set
    var abstractions : Map[IFunApp, Set[Int]] = Map()
    // the number of all quantifiers above this point
    val depth : Int =
      (if (prevFrame == null) 0 else prevFrame.depth) + quantifierNum
  }

  /**
   * Select the frame in which <code>t</code> should be inserted and return it,
   * together with the shifted version of </code>t</code> that belongs to this
   * quantifier level
   */
  private def selectFrameFor(t : IFunApp, topFrame : AbstractionFrame)
                                     : (IFunApp, AbstractionFrame) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(FunctionEncoder.AC,
                    t forall (s => !s.isInstanceOf[IFunApp]))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    var curFrame = topFrame
    var tVars =
      Set() ++ (for (v <- (SymbolCollector variables t).elements) yield v.index)
    
    // We insert the definition of the new bound variable at the outermost
    // possible point, which is determined by the variables occurring in
    // <code>t</code>
    while (curFrame.prevFrame != null &&
           Seqs.disjointSeq(tVars, 0 until curFrame.quantifierNum) &&
           Seqs.disjointSeq(tVars, curFrame.abstractions.values flatMap (_.elements))) {
      tVars = for (i <- tVars) yield (i - curFrame.quantifierNum)
      curFrame = curFrame.prevFrame
    }
    
    val skippedLevels = topFrame.depth - curFrame.depth
    val shiftedT =
      VariableShiftVisitor(t, skippedLevels, -skippedLevels).asInstanceOf[IFunApp]

    (shiftedT, curFrame)
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class to generate a relational encoding of functions. This means that
 * an (n+1)-ary predicate is introduced for each n-ary function, together
 * with axioms for totality and functionality, and that all applications of the
 * function are replaced referring to the predicate. The state of the class
 * consists of the mapping from functions to relations (so far), as well as
 * the axioms that have been introduced for the relational encoding.
 */
class FunctionEncoder {
  
  import FunctionEncoder._
  import IExpression._
  
  def apply(f : IFormula, order : TermOrder) : (IFormula, TermOrder) = {
    val nnfF = Transform2NNF(f)
    
    val freeVars = SymbolCollector variables nnfF
    val firstFreeVariableIndex =
      Seqs.max(for (IVariable(i) <- freeVars.elements) yield i) + 1
    val visitor =
      new EncoderVisitor(firstFreeVariableIndex, order)
    val context : Context[EncodingContext] =
      Context(AddDefinitions(new AbstractionFrame (null, 0), List()))
    
    val newF = visitor.visit(nnfF, context).asInstanceOf[IFormula]
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // no dangling variables in the result
    Debug.assertInt(FunctionEncoder.AC,
                    Set() ++ (SymbolCollector variables newF) == Set() ++ freeVars)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    (newF, visitor.order)
  }

  // axioms for totality and functionality of the predicates
  def axioms = axiomsVar
  def clearAxioms = {
    axiomsVar = true
  }
  
  private var axiomsVar : IFormula = true
  
  //////////////////////////////////////////////////////////////////////////////

  // map with all predicates that are used to encode functions
  private val relations =
    new scala.collection.mutable.HashMap[IFunction, Predicate]
  
  val predTranslation = new scala.collection.mutable.HashMap[Predicate, IFunction]
  
  private def totality(pred : Predicate) : IFormula = {
    val args = (for (i <- 1 until pred.arity) yield v(i)) ++ List(v(0))
    val atom = IAtom(pred, args)
    quan(List.make(pred.arity - 1, Quantifier.ALL), ex(atom))
  }
  
  private def functionality(pred : Predicate) : IFormula = {
    val baseArgs = for (i <- 0 until (pred.arity - 1)) yield v(i)
    val atom1 = IAtom(pred, baseArgs ++ List(v(pred.arity - 1)))
    val atom2 = IAtom(pred, baseArgs ++ List(v(pred.arity)))
    val matrix = atom1 ==> (atom2 ==> (v(pred.arity - 1) === v(pred.arity)))
    quan(List.make(pred.arity + 1, Quantifier.ALL), matrix)
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private class EncoderVisitor(var nextAbstractionNum : Int, var order : TermOrder)
                extends ContextAwareVisitor[EncodingContext, IExpression] {
  
    private def toRelation(fun : IFunction) : Predicate = 
      relations.getOrElseUpdate(fun, {
        val pred = new Predicate(fun.name, fun.arity + 1)
        order = order extend pred
        if (!fun.relational)
          axiomsVar = axiomsVar &&& functionality(pred)
        if (!fun.partial)
          axiomsVar = axiomsVar &&& totality(pred)
        predTranslation += (pred -> fun)
        pred
      })
  
    /**
     * Replace a function invocation with a bound variable and insert the
     * definition of this variable into <code>frame</code>. If this particular
     * invocation has already been abstracted at an earlier point, the old
     * variable is returned.
     */
    def abstractFunApp(t : IFunApp, frame : AbstractionFrame) : IVariable = {
      val (shiftedT, definingFrame) = selectFrameFor(t, frame)    
    
      def allocNewAbstraction = {
        val localIndex = nextAbstractionNum + definingFrame.depth
        nextAbstractionNum = nextAbstractionNum + 1
        definingFrame.abstractions =
          definingFrame.abstractions +
          (shiftedT -> (definingFrame.abstractions.getOrElse(shiftedT, Set()) + localIndex))
        localIndex
      }
      
      val localVarIndex =
        if (t.fun.relational)
          // We use a new definition for each occurrence of a relational
          // function
          allocNewAbstraction
        else
          // Check whether a definition for this function application already
          // exists
          (definingFrame.abstractions get shiftedT) match {
            case Some(s) => {
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              Debug.assertInt(FunctionEncoder.AC, s.size == 1)
              //-END-ASSERTION-/////////////////////////////////////////////////
              s.elements.next
            }
            case None => allocNewAbstraction
          }
    
      v(localVarIndex + frame.depth - definingFrame.depth)
    }

    ////////////////////////////////////////////////////////////////////////////
  
    /**
     * Add the abstraction definitions given in <code>frame</code> as premisses
     * or conjuncts to <code>f</code>. The resulting formula has the form
     * <code>EX* p1(..) & p2(...) ... & ALL* p'1(...) -> p'2(...) -> f</code>,
     * where <code>p1, p2, ...</code> are the applications given in
     * <code>matchedApps</code>.
     */
    private def addAbstractionDefs(f : IFormula,
                                   matchedApps : scala.collection.Set[IFunApp],
                                   frame : AbstractionFrame,
                                   minimiseScope : Boolean) : IFormula = {
      val abstractions = (for ((t, s) <- frame.abstractions.elements;
                               n <- s.elements) yield (t, n)          ).toList
      val (posAbstractions, negAbstractions) =
        abstractions partition (x => matchedApps contains (x _1))
      
      val unmatched = if (minimiseScope)
          withMinimalScope(f, addAbstractionsHelp(_, true, negAbstractions),
                           for ((_, n) <- negAbstractions) yield IVariable(n))
        else
          addAbstractionsHelp(f, true, negAbstractions)
      addAbstractionsHelp(unmatched, false, posAbstractions)
    }
    
    private def addAbstractionsHelp(f : IFormula,
                                    universal : Boolean,
                                    abstractions : Seq[(IFunApp, Int)]) : IFormula =
      if (abstractions.isEmpty) {
        f
      } else {
        val oldMaxNum = Seqs.max(for ((_, i) <- abstractions.elements) yield i)
    
        // all the previous bound variables have to be shifted upwards to make
        // place for the abstraction variables
        val shiftsAr = Array.make(oldMaxNum + 1, abstractions.length)
        // the abstraction variables are mapped to the indexes
        // 0 .. (abstractions.length-1)
        for (((_, oldNum), newNum) <- abstractions.elements.zipWithIndex)
          shiftsAr(oldNum) = newNum - oldNum
    
        val shifts = IVarShift(shiftsAr.toList, abstractions.length)
        val fWithDefs =
          (VariablePermVisitor(f, shifts) /: abstractions.elements.zipWithIndex) (
            (f, abstraction) => {
              val ((t, oldNum), newNum) = abstraction
              val shiftedT = VariablePermVisitor(t, shifts).asInstanceOf[IFunApp]
              val definedVar = v(newNum)
              val defAtom = IAtom(toRelation(t.fun),
                                  shiftedT.args ++ List(definedVar))
              if (universal) defAtom ==> f else defAtom & f 
            })
      
        val quan = if (universal) Quantifier.ALL else Quantifier.EX
        IExpression.quan(Array.make(abstractions.length, quan), fWithDefs)
      }
    
    ////////////////////////////////////////////////////////////////////////////
    
    override def preVisit(t : IExpression, c : Context[EncodingContext])
                                                    : PreVisitResult = t match {
      case INot(sub) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        // we assume that the formula is in negation normal form
        Debug.assertPre(FunctionEncoder.AC, LeafFormula.unapply(sub) != None)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        super.preVisit(t, toNormal(c))
      }
      case IQuantified(q1, IQuantified(q2, _)) if (q1 == q2) =>
        // do not push an abstraction frame if two quantifiers of the same
        // kind directly follow after each other
        super.preVisit(t, toNormal(c))
      case IQuantified(q, _) => {
        // otherwise, push an abstraction frame and tell the
        // <code>postVisit</code> method to define function abstractions at
        // this point
        val quantifierNum = c.quans.length - c.a.frame.depth + 1
        val newFrame = new AbstractionFrame (c.a.frame, quantifierNum)
        super.preVisit(t, c(AddDefinitions(newFrame, List())))
      }
      case ITrigger(exprs, body) => (c.a, c.quans) match {
        case (AddDefinitions(frame, triggers), Quantifier.EX :: _) =>
          TryAgain(body, c(AddDefinitions(frame, exprs :: triggers)))
        case (AddDefinitions(frame, triggers), Quantifier.ALL :: _) =>
          // ignore triggers underneath universal quantifiers
          TryAgain(body, c(AddDefinitions(frame, triggers)))
        case _ => 
          throw new Preprocessing.PreprocessingException(
                                         "Triggers in illegal position: " + t)
      }
      case _ =>
        super.preVisit(t, toNormal(c))      
    }

    private def toNormal(c : Context[EncodingContext]) = c.a match {
      case _ : NormalContext => c
      case AddDefinitions(frame, _) => c(NormalContext(frame))
    }

    ////////////////////////////////////////////////////////////////////////////

    def postVisit(t : IExpression, c : Context[EncodingContext],
                  subres : Seq[IExpression]) : IExpression = {
      val abstracted = t match {
        case t : IFunApp =>
          abstractFunApp(t update subres, c.a.frame)
        case IQuantified(Quantifier.EX, _) =>
          // ignore existential quantifiers, which are rebuilt by the
          // AddDefinitions context
          subres(0)
        case _ =>
          t update subres
      }

      // check whether definitions for function applications have to be added
      c.a match {
        case AddDefinitions(frame, triggers) => (c.quans, triggers) match {
          case ((Quantifier.ALL :: _) | List(), List()) =>
            addAbstractionDefs(abstracted.asInstanceOf[IFormula], Set(),
                               frame, false)
          
          case (Quantifier.EX :: _, triggers) => {
            val actualTriggers = if (triggers.isEmpty) List(List()) else triggers
            val innerQuans = Array.make(c.a.frame.quantifierNum, Quantifier.EX)
            
            connect(for (exprs <- actualTriggers.elements) yield {
               val triggerVisitor = new TriggerVisitor(c.a.frame)
               for (e <- exprs) triggerVisitor.visit(e, e)
               val withDefs = addAbstractionDefs(abstracted.asInstanceOf[IFormula],
                                                 triggerVisitor.occurringApps,
                                                 frame, true)
               quan(innerQuans, withDefs)
            }, IBinJunctor.Or)
          }
        }
        
        case _ : NormalContext =>
          abstracted
      }
    }
  }

}

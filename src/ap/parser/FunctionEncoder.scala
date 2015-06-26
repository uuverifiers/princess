/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2013 Philipp Ruemmer <ph_r@gmx.net>
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

import scala.collection.mutable.{ArrayBuilder, HashSet => MHashSet, PriorityQueue}

import ap.terfor.TermOrder
//import ap.terfor.preds.Predicate
//import ap.terfor.conjunctions.Quantifier
import ap.util.{Debug, Seqs}
import ap.theories.Theory

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
                               criticalVars : Set[IVariable]) : IFormula =
    t match {
      case IBinFormula(op, _, _) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(FunctionEncoder.AC,
                        op == IBinJunctor.And || op == IBinJunctor.Or)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        val parts = LineariseVisitor(t, op)
        val (outside, inside) =
          parts partition (x => ContainsSymbol.freeFrom(x, criticalVars))
        if (outside.isEmpty) {
          f(t)
        } else if (inside.isEmpty) {
          t
        } else {
          val outsideFor = connect(outside, op)
          val insideFor = if (inside.size == 1)
            withMinimalScope(inside(0), f, criticalVars)
          else
            f(connect(inside, op))
          IBinFormula(op, outsideFor, insideFor)
        }
      }
      case _ => f(t)
    }

  //////////////////////////////////////////////////////////////////////////////

  private class TriggerVisitor(frame : AbstractionFrame,
                               var localAbstractionIndex : Int)
                extends CollectingVisitor[ITerm, ITerm] {
    
    val occurringApps = new scala.collection.mutable.HashSet[IFunApp]
    
    // we potentially introduce local abstractions when scanning triggers
    // containing terms that are not part of the matrix of the quantified
    // formula
    val localAbstractions = new AbstractionFrame(null, frame.depth)
    
    def postVisit(t : IExpression, trigger : ITerm, subres : Seq[ITerm]) : ITerm =
      t match {
        case t : IFunApp => {
          val updatedT = t update subres
          val (shiftedT, definingFrame) = selectFrameFor(updatedT, frame)
          if (frame eq definingFrame) occurringApps += updatedT
          
          (definingFrame.abstractions get shiftedT) match {
            case Some(abstractionNums) => {
              if (abstractionNums.size > 1)
                throw new Preprocessing.PreprocessingException(
                  "Ambiguous trigger for relational function: " + trigger)
              v(abstractionNums.head + frame.depth - definingFrame.depth)
            }
            case None =>
              // otherwise we have to introduce a local abstraction
              v(localAbstractions.getAbstraction(updatedT, {
                val res = localAbstractionIndex
                localAbstractionIndex = localAbstractionIndex + 1
                res
              }))
          }
        }
        case t : ITerm => t update subres
        case _ => 
          throw new Preprocessing.PreprocessingException(
            "Unexpected expression in trigger: " + t)
      }
  }
                     
  //////////////////////////////////////////////////////////////////////////////

  // Abstraction frames are pushed immediately underneath each level of
  // quantifiers and collect all function definitions that should be
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
    var abstractionList : List[(IFunApp, Int)] = List()
    // the number of all quantifiers above this point
    val depth : Int =
      (if (prevFrame == null) 0 else prevFrame.depth) + quantifierNum
  
    def getAbstraction(t : IFunApp, newGlobalAbstractionIndex : => Int) : Int = {
      def allocNewAbstraction = {
        val localIndex = newGlobalAbstractionIndex + depth
        abstractions =
          abstractions + (t -> (abstractions.getOrElse(t, Set()) + localIndex))
        abstractionList =
          (t, localIndex) :: abstractionList
        localIndex
      }
      
      if (t.fun.relational)
        // We use a new definition for each occurrence of a relational
        // function
        allocNewAbstraction
      else
        // Check whether a definition for this function application already
        // exists
        (abstractions get t) match {
          case Some(s) => {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(FunctionEncoder.AC, s.size == 1)
            //-END-ASSERTION-///////////////////////////////////////////////////
            s.head
          }
          case None => allocNewAbstraction
        }
    }
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
                    t.subExpressions forall (s => !s.isInstanceOf[IFunApp]))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    var curFrame = topFrame
    var tVars =
      (for (v <- (SymbolCollector variables t).iterator) yield v.index).toSet
    
    // We insert the definition of the new bound variable at the outermost
    // possible point, which is determined by the variables occurring in
    // <code>t</code>
    while (curFrame.prevFrame != null &&
           Seqs.disjointSeq(tVars, 0 until curFrame.quantifierNum) &&
           Seqs.disjointSeq(tVars, curFrame.abstractionList.iterator map (_._2))) {
      tVars = for (i <- tVars) yield (i - curFrame.quantifierNum)
      curFrame = curFrame.prevFrame
    }
    
    val skippedLevels = topFrame.depth - curFrame.depth
    val shiftedT =
      VariableShiftVisitor(t, skippedLevels, -skippedLevels).asInstanceOf[IFunApp]

    (shiftedT, curFrame)
  }

  /**
   * Determine all abstractions that are used in the given formula.
   * This depends on the fact that the list <code>abstractions</code> is ordered
   * topologically, starting with the outermost function applications;
   * this order will be preserved by the function
   */
  private def findRelevantAbstractions
    (p : IFormula, abstractions : IndexedSeq[(IFunApp, Int, IAtom)])
    : IndexedSeq[(IFunApp, Int, IAtom)] = {

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // Abstractions should be sorted
    Debug.assertPre(FunctionEncoder.AC, (abstractions sliding 2) forall {
                      case Seq((_, x, _), (_, y, _)) => x < y
                      case _ => true
                    })
    //-END-ASSERTION-/////////////////////////////////////////////////////////// 

    val vars = new PriorityQueue[Int] ()(intReverseOrdering)
    val addToVars : Int => Unit = (vars enqueue _)
    val defs = ArrayBuilder.make[(IFunApp, Int, IAtom)]

    val varsIterator = new Iterator[Int] {
      var nextVar = -1
      var nextReady = false

      def hasNext : Boolean = {
        while (!nextReady && !vars.isEmpty) {
          val n = vars.dequeue
          if (n > nextVar) {
            nextVar = n
            nextReady = true
          }
        }
        nextReady
      }

      def next : Int = {
        if (!nextReady)
          hasNext
        nextReady = false
        nextVar
      }
    }

    VariableIndexCollector(p, addToVars)

    for ((_, newApp@(funApp, newVarNum, atom)) <-
           Seqs.binIntersect(varsIterator, abstractions,
                             intAbstractionCompare)) {
      VariableIndexCollector(funApp, addToVars)
      defs += newApp
    }

    val res = defs.result
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // Check that we have actually found all definitions relevant for this
    // sub-formula 
    Debug.assertPost(FunctionEncoder.AC, {
                       val allVars = new MHashSet[Int]
                       VariableIndexCollector(p, (allVars += _))
                       for ((funApp, _, _) <- res)
                         VariableIndexCollector(funApp, (allVars += _))
                       
                       abstractions forall {
                         case app@(_, num, _) =>
                           !(allVars contains num) || (res contains app)
                       }
                     })
    //-END-ASSERTION-/////////////////////////////////////////////////////////// 
    res
  }

  //////////////////////////////////////////////////////////////////////////////

  private val intAbstractionCompare =
    (x : Int, a : (IFunApp, Int, IAtom)) => x - a._2

  private val intReverseOrdering = Ordering.fromLessThan[Int](_ > _)

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
class FunctionEncoder (tightFunctionScopes : Boolean,
                       genTotalityAxioms : Boolean) extends Cloneable {
  
  import FunctionEncoder._
  import IExpression._
  
  override def clone : FunctionEncoder = {
    val res = new FunctionEncoder(tightFunctionScopes, genTotalityAxioms)
    
    res.axiomsVar = this.axiomsVar
    res.relations ++= this.relations
    res.predTranslation ++= this.predTranslation
    
    res
  }
  
  def apply(f : IFormula, order : TermOrder) : (IFormula, TermOrder) = {
    val nnfF = Transform2NNF(f)

    val freeVars = SymbolCollector variables nnfF
    val firstFreeVariableIndex =
      Seqs.max(for (IVariable(i) <- freeVars.iterator) yield i) + 1
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
  protected[ap] val relations =
    new scala.collection.mutable.HashMap[IFunction, Predicate]
  
  val predTranslation =
    new scala.collection.mutable.HashMap[Predicate, IFunction]
  
  private def totality(pred : Predicate) : IFormula = {
    val args = (for (i <- 1 until pred.arity) yield v(i)) ++ List(v(0))
    val atom = IAtom(pred, args)
    quan(List.fill(pred.arity - 1){Quantifier.ALL}, ex(atom))
  }
  
  private def functionality(pred : Predicate) : IFormula = {
    val baseArgs = for (i <- 0 until (pred.arity - 1)) yield v(i)
    val atom1 = IAtom(pred, baseArgs ++ List(v(pred.arity - 1)))
    val atom2 = IAtom(pred, baseArgs ++ List(v(pred.arity)))
    val matrix = atom1 ==> (atom2 ==> (v(pred.arity - 1) === v(pred.arity)))
    quan(List.fill(pred.arity + 1){Quantifier.ALL}, matrix)
  }

  def addFunction(fun : IFunction) : Predicate = 
    relations.getOrElseUpdate(fun, {
      val pred = new Predicate(fun.name, fun.arity + 1)
      if (!fun.relational)
        axiomsVar = axiomsVar &&& functionality(pred)
      if (!fun.partial && genTotalityAxioms)
        axiomsVar = axiomsVar &&& totality(pred)
      predTranslation += (pred -> fun)
      pred
    })

  //////////////////////////////////////////////////////////////////////////////

  def addTheory(t : Theory) : Unit =
    for (pair@(f, p) <- t.functionPredicateMapping) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(FunctionEncoder.AC, p.arity == f.arity + 1)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      relations += pair
      predTranslation += (p -> f)
    }

  //////////////////////////////////////////////////////////////////////////////
  
  private class EncoderVisitor(var nextAbstractionNum : Int, var order : TermOrder)
                extends ContextAwareVisitor[EncodingContext, IExpression] {
  
    private def toRelation(fun : IFunction) : Predicate =
      relations.getOrElse(fun, {
        val pred = addFunction(fun)
        order = order extendPred pred
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
    
      val localVarIndex = definingFrame.getAbstraction(shiftedT, {
        val res = nextAbstractionNum
        nextAbstractionNum = nextAbstractionNum + 1
        res
      })
      
      v(localVarIndex + frame.depth - definingFrame.depth)
    }

    ////////////////////////////////////////////////////////////////////////////
  
    /**
     * Add the given abstraction definitions as premises
     * or conjuncts to <code>f</code>. The resulting formula has the form
     * <code>EX* p1(..) & p2(...) ... & ALL* p'1(...) -> p'2(...) -> f</code>,
     * where <code>p1, p2, ...</code> are the applications given in
     * <code>matchedApps</code>.
     */
    private def addAbstractionDefs(f : IFormula,
                                   matchedApps : scala.collection.Set[IFunApp],
                                   abstractions : Seq[(IFunApp, Int)],
                                   minimiseScope : Boolean)
                                  : IFormula =
      if (abstractions.isEmpty) {
        f
      } else {
        val (posAbstractions, negAbstractions) =
          abstractions partition (x => matchedApps contains (x _1))
      
        def addNegAbstractions(subFor : IFormula) = {
          // reserve variables for the universal quantifiers
          val (shiftedF, negAbstractionRels) = funsToRelations(subFor, negAbstractions)
      
          // add the negative definitions and universal quantifiers
          IExpression.quan(Array.fill(negAbstractions.length){Quantifier.ALL},
                           distributeUniDefinitions(shiftedF, negAbstractionRels))
        }
        
        val unmatched = if (minimiseScope)
          withMinimalScope(f, addNegAbstractions _,
                           (for ((_, n) <- negAbstractions.iterator)
                              yield IVariable(n)).toSet)
        else
          addNegAbstractions(f)
      
        // reserve variables for the existential quantifiers
        val (shiftedUnmatched, posAbstractionRels) =
          funsToRelations(unmatched, posAbstractions)

        // add the positive definitions and existential quantifiers
        IExpression.quan(Array.fill(posAbstractions.length){Quantifier.EX},
                         addDefPredicates(shiftedUnmatched, false,
                                          posAbstractionRels.iterator))
      }
    
    /**
     * Add the given abstraction definitions as premises to the formula
     * <code>f</code>. This function will try to distribute the definitions
     * to the sub-formulae as far as possible.
     */
    private def distributeUniDefinitions
       (f : IFormula, abstractions : Seq[(IFunApp, Int, IAtom)]) : IFormula =
      if (abstractions.isEmpty)
        f
      else f match {
        case IBinFormula(op, _, _) => {
          val parts = LineariseVisitor(f, op)
          val indexedAbstractions = abstractions.toIndexedSeq
          val relevantDefs =
            for (p <- parts) 
            yield findRelevantAbstractions(p, indexedAbstractions)
        
          val toplevelDefs = op match {
            case _ if (!tightFunctionScopes) =>
              abstractions.toSet
            case IBinJunctor.And =>
              // distribute all definitions
              Set[(IFunApp, Int, IAtom)]()
            case IBinJunctor.Or =>
              // we include those definitions on the top level that occur in
              // an atom
              Set() ++ (for ((defs, p) <- relevantDefs.iterator zip parts.iterator;
                             if (!p.isInstanceOf[IBinFormula]);
                             d <- defs.iterator) yield d)
          } 

          val subres = connect(
            for ((p, defs) <- parts.iterator zip relevantDefs.iterator) yield {
              distributeUniDefinitions(p, defs filterNot (toplevelDefs contains _))
            }, op)

          addDefPredicates(subres, true,
                           abstractions.iterator filter (toplevelDefs contains _))
        }
        case _ =>
          addDefPredicates(f, true, abstractions.iterator)
      }
    
    /**
     * Reserve variables in the correct range for the function abstractions,
     * shift everything to the right place, and create relational atoms
     * representing the function applications
     */
    private def funsToRelations(f : IFormula,
                                abstractions : Seq[(IFunApp, Int)])
                               : (IFormula, Seq[(IFunApp, Int, IAtom)]) = {
      // all the previous bound variables have to be shifted upwards to make
      // place for the abstraction variables;
      // the abstraction variables are mapped to the indexes
      // 0 .. (abstractions.length-1)
      val mapping =
        (for (((_, oldNum), newNum) <- abstractions.iterator.zipWithIndex)
         yield (oldNum -> (newNum - oldNum))).toMap
      val shifts = IVarShift(mapping, abstractions.length)
      
      (VariablePermVisitor(f, shifts),
       for (((t, oldNum), newNum) <- abstractions.zipWithIndex) yield {
         val shiftedT = VariablePermVisitor(t, shifts).asInstanceOf[IFunApp]
         val definedVar = v(newNum)
         val defAtom = IAtom(toRelation(t.fun), shiftedT.args ++ List(definedVar))
         (shiftedT, newNum, defAtom)
       })
    }
    
    private def addDefPredicates(f : IFormula,
                                 universal : Boolean,
                                 abstractions : Iterator[(IFunApp, Int, IAtom)]) =
      (f /: abstractions) {
        case (f, (_, _, defAtom)) =>
          if (universal) defAtom ==> f else defAtom & f 
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
        val quantifierNum = c.binders.length - c.a.frame.depth + 1
        val newFrame = new AbstractionFrame (c.a.frame, quantifierNum)
        super.preVisit(t, c(AddDefinitions(newFrame, List())))
      }
      case ITrigger(exprs, body) => (c.a, c.binders) match {
        case (AddDefinitions(frame, triggers), Context.EX :: _) =>
          TryAgain(body, c(AddDefinitions(frame, exprs :: triggers)))
        case (AddDefinitions(frame, triggers), Context.ALL :: _) =>
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
        case AddDefinitions(frame, triggers) => (c.binders, triggers) match {
          case ((Context.ALL :: _) | List(), List()) =>
            addAbstractionDefs(abstracted.asInstanceOf[IFormula], Set(),
                               frame.abstractionList, false)
          
          case (Context.EX :: _, triggers) => {
            // we might have to add also triggers following existential
            // quantifiers. in the presence of multiple sets of triggers, the
            // quantified formula will be duplicated
            val actualTriggers = if (triggers.isEmpty) List(List()) else triggers
            val innerQuans = Array.fill(c.a.frame.quantifierNum){Quantifier.EX}
            
            connect(for (exprs <- actualTriggers.iterator) yield {
               val triggerVisitor = new TriggerVisitor(c.a.frame, nextAbstractionNum)
               for (e <- exprs) triggerVisitor.visit(e, e)
               val withDefs =
                 addAbstractionDefs(abstracted.asInstanceOf[IFormula],
                                    triggerVisitor.occurringApps,
                                    frame.abstractionList :::
                                      triggerVisitor.localAbstractions.abstractionList,
                                    true)
               quan(innerQuans, withDefs)
            }, IBinJunctor.Or)
          }
          case _ => {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            // this should not happen
            Debug.assertInt(FunctionEncoder.AC, false)
            //-END-ASSERTION-///////////////////////////////////////////////////
            null
          }
        }
        
        case _ : NormalContext =>
          abstracted
      }
    }
  }

}

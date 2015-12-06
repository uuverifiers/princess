/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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

import ap._
import ap.basetypes.IdealInt
import ap.theories._
import ap.terfor.preds.Predicate
import ap.terfor.{ConstantTerm, TermOrder}
import ap.parser.IExpression.Quantifier
import ap.util.Seqs

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

import java.io.PrintStream

/**
 * Class for printing <code>IFormula</code>s in the SMT-LIB 2 format
 */
object SMTLineariser {

  private val SaneId =
    """[+-/*=%?!.$_~&^<>@a-zA-Z][+-/*=%?!.$_~&^<>@a-zA-Z0-9]*""".r
  
  def quoteIdentifier(str : String) = str match {
    case SaneId() => str
    case _        => "|" + str.replace("|", "\\|") + "|"
  }

  //////////////////////////////////////////////////////////////////////////////

  def toSMTExpr(value : IdealInt) : String =
    if (value.signum < 0)
      "(- " + value.abs.toString + ")"
    else
      value.toString
  
  //////////////////////////////////////////////////////////////////////////////

  private val emptyConstantType :
       ConstantTerm => Option[SMTParser2InputAbsy.SMTType] = (_) => None
  private val emptyFunctionType :
       IFunction => Option[SMTParser2InputAbsy.SMTFunctionType] = (_) => None

  private val trueConstant  = IConstant(new ConstantTerm("true"))
  private val falseConstant = IConstant(new ConstantTerm("false"))
  private val eqPredicate   = new Predicate ("=", 2)

  //////////////////////////////////////////////////////////////////////////////

  def apply(formula : IFormula) : Unit =
    apply(formula, emptyConstantType, emptyFunctionType)

  def asString(formula : IFormula) : String =
    ap.DialogUtil.asString { apply(formula) }

  def asString(t : ITerm) : String =
    ap.DialogUtil.asString { apply(t) }

  def asString(t : IExpression) : String = t match {
    case t : IFormula => asString(t)
    case t : ITerm => asString(t)
  }

  def apply(formula : IFormula,
            constantType :
              ConstantTerm => Option[SMTParser2InputAbsy.SMTType],
            functionType :
              IFunction => Option[SMTParser2InputAbsy.SMTFunctionType]) : Unit =
    formula match {
      case IBoolLit(value) => print(value)
      case _ => {
        val lineariser = new SMTLineariser("", "", "", List(), List(), "", "", "",
                                           constantType, functionType)
        lineariser printFormula formula
      }
    }

  def apply(term : ITerm) : Unit = {
    val lineariser = new SMTLineariser("", "", "", List(), List(), "", "", "",
                                       emptyConstantType, emptyFunctionType)
    lineariser printTerm term
  }

  //////////////////////////////////////////////////////////////////////////////

  def apply(formulas : Seq[IFormula], signature : Signature,
            benchmarkName : String) : Unit =
    apply(formulas, signature, "AUFLIA", "unknown", benchmarkName)

  def apply(formulas : Seq[IFormula], signature : Signature,
            logic : String, status : String,
            benchmarkName : String) : Unit = {
    val order = signature.order
    
    val (finalFormulas, constsToDeclare) : (Seq[IFormula], Set[ConstantTerm]) =
      if (Seqs.disjoint(order.orderedConstants, signature.existentialConstants)) {
        // if all constants are universal, we do not have to add explicit quantifiers
        (for (f <- formulas) yield ~f,
         signature.universalConstants ++ signature.nullaryFunctions)
      } else {
        val formula = IExpression.connect(formulas, IBinJunctor.Or)
        // add the nullary functions
        val withFunctions =
          IExpression.quanConsts(Quantifier.ALL, signature.nullaryFunctions, formula)
        // ... and the existentially quantified constants
        val withExConstants =
          IExpression.quanConsts(Quantifier.EX,
                                 signature.existentialConstants,
                                 withFunctions)
        // add the universally quantified constants
        val withUniConstants =
          IExpression.quanConsts(Quantifier.ALL,
                                 signature.universalConstants,
                                 withFunctions)
        
        (List(~withUniConstants), Set())
      }
    
    val lineariser = new SMTLineariser(benchmarkName,
                                       logic, status,
                                       constsToDeclare.toList,
                                       order.orderedPredicates.toList,
                                       "fun", "pred", "const",
                                       emptyConstantType, emptyFunctionType)
   
    lineariser.open
    for (f <- finalFormulas)
      lineariser.printFormula("assert", f)
    lineariser.close
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for printing <code>IFormula</code>s in the SMT-Lib format
 */
class SMTLineariser(benchmarkName : String,
                    logic : String,
                    status : String,
                    constsToDeclare : Seq[ConstantTerm],
                    predsToDeclare : Seq[Predicate],
                    funPrefix : String, predPrefix : String, constPrefix : String,
                    constantType :
                           ConstantTerm => Option[SMTParser2InputAbsy.SMTType],
                    functionType :
                           IFunction => Option[SMTParser2InputAbsy.SMTFunctionType]) {

  import SMTLineariser.{quoteIdentifier, toSMTExpr,
                        trueConstant, falseConstant, eqPredicate}

  private def fun2Identifier(fun : IFunction) =
    (TheoryRegistry lookupSymbol fun) match {
      case Some(t : SimpleArray) => fun match {
        case t.select => "select"
        case t.store => "store"
      }
      case Some(t : MulTheory) => fun match {
        case t.mul => "*"
      }
      case _ =>
        quoteIdentifier(funPrefix + fun.name)
    }

  private def pred2Identifier(pred : Predicate) =
    quoteIdentifier(predPrefix + pred.name)
  private def const2Identifier(const : ConstantTerm) =
    quoteIdentifier(constPrefix + const.name)
  
  //////////////////////////////////////////////////////////////////////////////

  def open {
    println("(set-logic " + logic + ")")
    println("(set-info :source |")
    println("    Benchmark: " + benchmarkName)
    println("    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)")
    println("|)")
  
    println("(set-info :status " + status + ")")

    // declare the required predicates
    for (pred <- predsToDeclare) {
      print("(declare-fun " + pred2Identifier(pred) + " (")
      print((for (_ <- 1 to pred.arity) yield "Int") mkString " ")
      println(") Bool)")
    }
    
    // declare universal constants
    for (const <- constsToDeclare)
      println("(declare-fun " + const2Identifier(const) + " () Int)")
  }
  
  def printFormula(clauseName : String, formula : IFormula) {
    print("(" + clauseName + " ")
    printFormula(formula)
    println(")")
  }
  
  def printFormula(formula : IFormula) = {
    // first derive types of variables
    var typedFormula = formula
    var oldTypedFormula : IFormula = null
    while (!(typedFormula eq oldTypedFormula)) {
      oldTypedFormula = typedFormula
      typedFormula =
        VariableTypeInferenceVisitor.visit(typedFormula, ())
                                    .asInstanceOf[IFormula]
    }
    AbsyPrinter.visit(typedFormula, PrintContext(List(), None))
  }
  
  def printTerm(term : ITerm) =
    AbsyPrinter.visit(term, PrintContext(List(), None))
  
  def close {
    println("(check-sat)")
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  import SMTParser2InputAbsy.{SMTType, SMTArray, SMTBool, SMTInteger,
                              SMTFunctionType}

  private def getTermType(t : ITerm)
                         (implicit variableType : Int => Option[SMTType])
                         : Option[SMTType] = t match {
    case IFunApp(SimpleArray.Select(), args) =>
      for (SMTArray(_, res) <- getTermType(args.head)) yield res
    case IFunApp(SimpleArray.Store(), args) =>
      getTermType(args.head)
    case IFunApp(f, _) =>
      for (SMTFunctionType(_, res) <- functionType(f)) yield res
    case IConstant(c) =>
      constantType(c)
    case IVariable(ind) =>
      variableType(ind)
    case _ => None
  }

  private def getArgTypes(t : IFunApp)
                         (implicit variableType : Int => Option[SMTType])
                         : Option[Seq[SMTType]] = {
    val IFunApp(fun, args) = t
    fun match {
      case SimpleArray.Select() =>
        for (s@SMTArray(argTypes, _) <- getTermType(args.head))
        yield (s :: argTypes)
      case SimpleArray.Store() =>
        for (s@SMTArray(argTypes, resType) <- getTermType(args.head))
        yield (s :: argTypes ::: List(resType))
      case fun =>
        for (SMTFunctionType(argTypes, _) <- functionType(fun)) yield argTypes
    }
  }

  private object BooleanTerm {
    def unapply(t : IExpression)
               (implicit variableType : Int => Option[SMTType])
               : Option[ITerm] = t match {
      case t@IFunApp(f, _)
        if (functionType(f) match {
              case Some(SMTFunctionType(_, SMTBool)) => true
              case _ => false
            }) =>
        Some(t)
      case t : ITerm if (getTermType(t) == Some(SMTBool)) =>
        Some(t)
      case _ =>
        None
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private val type2Predicate = new MHashMap[SMTType, Predicate]
  private val predicate2Type = new MHashMap[Predicate, SMTType]

  private def getTypePredicate(t : SMTType) : Predicate =
    type2Predicate.getOrElseUpdate(t, {
      val p = new Predicate("type_" + t, 1)
      predicate2Type.put(p, t)
      p
    })

  object TypePredicate {
    def unapply(t : IExpression) : Option[(ITerm, SMTType)] = t match {
      case IAtom(p, Seq(v)) => for (s <- predicate2Type get p) yield (v, s)
      case _                => None
    }
  }

  object TypedTerm {
    def unapply(t : ITerm)
               (implicit variableType : Int => Option[SMTType])
              : Option[(ITerm, Option[SMTType])] =
      Some((t, getTermType(t)))
  }

  object TypedTermSeq {
    def unapplySeq(ts : Seq[ITerm])
                  (implicit variableType : Int => Option[SMTType])
                 : Option[Seq[(ITerm, Option[SMTType])]] =
      Some(for (t <- ts) yield (t, getTermType(t)))
  }

  private object VariableTypeInferenceVisitor
                 extends CollectingVisitor[Unit, IExpression] {

    private val variableTypes = new ArrayBuffer[SMTType]

    private def setVariableType(variableIndex : Int, t : SMTType) : Unit = {
      val pos = variableTypes.size - variableIndex - 1
      val oldType = variableTypes(pos)
      if (oldType != null && oldType != t)
        Console.err.println("Warning: type clash during inference: " +
                            oldType + " vs " + t)
      variableTypes(pos) = t
    }

    private def equalTypes(t1 : ITerm, t2 : ITerm) : Unit = (t1, t2) match {
      case (IVariable(ind1), IVariable(ind2)) =>
        (getVariableType(ind1), getVariableType(ind2)) match {
          case (Some(t), None) => setVariableType(ind2, t)
          case (None, Some(t)) => setVariableType(ind1, t)
          case _ => // nothing
        }
      case (IVariable(ind), t) =>
        for (s <- getTermType(t)) setVariableType(ind, s)
      case (t, IVariable(ind)) =>
        for (s <- getTermType(t)) setVariableType(ind, s)
      case _ =>
        // nothing
    }

    implicit val getVariableType : Int => Option[SMTType] = (ind:Int) => {
      val pos = variableTypes.size - ind - 1
      variableTypes(pos) match {
        case null => None
        case t => Some(t)
      }
    }

    override def preVisit(t : IExpression,
                          arg : Unit) : PreVisitResult = {
      t match {
        case t : IQuantified =>
          variableTypes += null
        case TypePredicate(IVariable(ind), s) =>
          setVariableType(ind, s)
        case IExpression.Eq(IFunApp(SimpleArray.Select(),
                            TypedTermSeq((IVariable(ind), None), indexes @ _*)),
                            TypedTerm((_, Some(resT))))
          if (indexes forall { case (_, s) => s.isDefined }) =>
            setVariableType(ind,
              SMTArray(indexes.toList map {
                         case (_, Some(t)) => t
                         case _ => null // cannot happen
                       }, resT))
        case IExpression.Eq(TypedTerm((_, Some(resT))),
                            IFunApp(SimpleArray.Select(),
                            TypedTermSeq((IVariable(ind), None), indexes @ _*)))
          if (indexes forall { case (_, s) => s.isDefined }) =>
            setVariableType(ind,
              SMTArray(indexes.toList map {
                         case (_, Some(t)) => t
                         case _ => null // cannot happen
                       }, resT))
        case IExpression.Eq(s, t) =>
          equalTypes(s, t)
        case ITermITE(_, s, t) =>
          equalTypes(s, t)
        case t@IFunApp(_, args) =>
          for (argTypes <- getArgTypes(t)) {
            for ((IVariable(ind), s) <- args.iterator zip argTypes.iterator)
              setVariableType(ind, s)
          }
        case _ =>
          // nothing
      }

      KeepArg
    }

    def postVisit(t : IExpression,
                  arg : Unit, subres : Seq[IExpression]) : IExpression = t match {
      case IQuantified(Quantifier.ALL,
                       IBinFormula(IBinJunctor.Or,
                                   INot(TypePredicate(IVariable(0), _)),
                                   _)) |
           IQuantified(Quantifier.EX,
                       IBinFormula(IBinJunctor.And,
                                   TypePredicate(IVariable(0), _),
                                   _)) => {
        variableTypes reduceToSize (variableTypes.size - 1)
        t update subres
      }
      case _ : IQuantified => {
        val f@IQuantified(q, subF) = t update subres
        import IExpression._
        val res = getVariableType(0) match {
          case Some(t) => q match {
            case Quantifier.ALL =>
              all(getTypePredicate(t)(v(0)) ==> subF)
            case Quantifier.EX =>
              ex(getTypePredicate(t)(v(0)) & subF)
          }
          case None => f
        }
        variableTypes reduceToSize (variableTypes.size - 1)
        res
      }
      case _ => t update subres
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def printSMTType(t : SMTType) : Unit = t match {
    case SMTInteger => print("Int")
    case SMTBool    => print("Bool")
    case SMTArray(args, res) => {
      print("(Array")
      for (s <- args) {
        print(" ")
        printSMTType(s)
      }
      print(" ")
      printSMTType(res)
      print(")")
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private case class PrintContext(vars : List[(String, Option[SMTType])],
                                  pendingType : Option[SMTType]) {
    def pushVar(name : String) =
      PrintContext((name, pendingType) :: vars, None)
    def addPendingType(t : SMTType) =
      PrintContext(vars, Some(t))
    implicit val variableType : Int => Option[SMTType] = (ind) => vars(ind)._2
  }

  private object AbsyPrinter extends CollectingVisitor[PrintContext, Unit] {

    override def preVisit(t : IExpression,
                          ctxt : PrintContext) : PreVisitResult = {
    import ctxt.variableType
    t match {
      // Terms with Boolean type, which were encoded as integer terms
      case IIntFormula(IIntRelation.EqZero, BooleanTerm(t)) =>
        // strip off the integer encoding
        TryAgain(t, ctxt)

      case IIntFormula(IIntRelation.EqZero,
                       IPlus(BooleanTerm(t), IIntLit(v))) if (!v.isZero) =>
        // strip off the integer encoding
        TryAgain(!IExpression.eqZero(t), ctxt)
      case IIntFormula(IIntRelation.EqZero,
                       IPlus(IIntLit(v), BooleanTerm(t))) if (!v.isZero) =>
        // strip off the integer encoding
        TryAgain(!IExpression.eqZero(t), ctxt)

      // Terms
      case IConstant(c) => {
        print(const2Identifier(c) + " ")
        ShortCutResult(())
      }
      case IIntLit(value) => {
        print(toSMTExpr(value) + " ")
        ShortCutResult(())
      }
      case IPlus(_, _) => {
        print("(+ ")
        KeepArg
      }
      case ITimes(coeff, _) => {
        print("(* " + toSMTExpr(coeff) + " ")
        KeepArg
      }
      case IVariable(index) => {
        print(ctxt.vars(index)._1 + " ")
        ShortCutResult(())
      }
      case t@IFunApp(fun, args) => {
        // check if any Boolean arguments have to be decoded
        var changed = false
        val newArgs = getArgTypes(t) match {
          case Some(argTypes) =>
            (for (p <- args.iterator zip argTypes.iterator) yield p match {
               case (IIntLit(IdealInt.ZERO), SMTBool) => {
                 changed = true
                 trueConstant
               }                
               case (IIntLit(v), SMTBool) if (!v.isZero) => {
                 changed = true
                 falseConstant
               }
               case (t, _) => t
             }).toList
          case _ => args
        }

        if (changed) {
          TryAgain(IFunApp(fun, newArgs), ctxt)
        } else {
          print((if (args.isEmpty) "" else "(") + fun2Identifier(fun) + " ")
          KeepArg
        }
      }

      case _ : ITermITE | _ : IFormulaITE => {
        print("(ite ")
        KeepArg
      }

      // Formulae
      case IAtom(pred, args) => {
        print((if (args.isEmpty) "" else "(") + pred2Identifier(pred) + " ")
        KeepArg
      }
      case IBinFormula(junctor, _, _) => {
        print("(")
        print(junctor match {
          case IBinJunctor.And => "and"
          case IBinJunctor.Or => "or"
          case IBinJunctor.Eqv => "="
        })
        print(" ")
        KeepArg
      }
      case IBoolLit(value) => {
        print(value + " ")
        ShortCutResult(())
      }
      case IExpression.Eq(s, t) =>
        // rewrite to a proper equation
        TryAgain(IAtom(eqPredicate, List(s, t)), ctxt)
      case IIntFormula(rel, _) => {
        print("(")
        print(rel match {
          case IIntRelation.EqZero => "="
          case IIntRelation.GeqZero => "<="
        })
        print(" 0 ")
        KeepArg
      }
      case INot(_) => {
        print("(not ")
        KeepArg
      }
      case IQuantified(Quantifier.ALL,
                       IBinFormula(IBinJunctor.Or,
                                   INot(TypePredicate(IVariable(0), t)),
                                   subF)) =>
        TryAgain(IExpression.all(subF), ctxt addPendingType t)
      case IQuantified(Quantifier.EX,
                       IBinFormula(IBinJunctor.And,
                                   TypePredicate(IVariable(0), t),
                                   subF)) =>
        TryAgain(IExpression.ex(subF), ctxt addPendingType t)
      case IQuantified(quan, _) => {
        val varName = "var" + ctxt.vars.size
        print("(")
        print(quan match {
          case Quantifier.ALL => "forall"
          case Quantifier.EX => "exists"
        })
        print(" ((" + varName + " ")
        printSMTType(ctxt.pendingType.getOrElse(SMTInteger))
        print(")) ")
        UniSubArgs(ctxt pushVar varName)
      }
      case ITrigger(trigs, body) => {
        // we have to handle this case recursively, since the
        // order of the parameters has to be changed
        
        print("(! ")
        visit(body, ctxt)
        print(" :pattern (")
        for (t <- trigs)
          visit(t, ctxt)
        print(")) ")
        
        ShortCutResult(())
      }
    }
    }
    
    def postVisit(t : IExpression,
                  arg : PrintContext, subres : Seq[Unit]) : Unit = t match {
      case IPlus(_, _) | ITimes(_, _) | IAtom(_, Seq(_, _*)) | IFunApp(_, Seq(_, _*)) |
           IBinFormula(_, _, _) | IIntFormula(_, _) | INot(_) |
           IQuantified(_, _) | ITermITE(_, _, _) | IFormulaITE(_, _, _) =>
        print(") ")
      case IAtom(_, _) | IFunApp(_, _) =>
        // nothing
    }
  
  }
  
}

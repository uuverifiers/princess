/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011-2014 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser;

import ap._
import ap.parameters.{ParserSettings, Param}
import ap.terfor.OneTerm
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.preds.Atom
import ap.util.{Debug, Logic, PlainRange}
import ap.theories.SimpleArray
import ap.basetypes.IdealInt
import smtlib._
import smtlib.Absyn._

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

object SMTParser2InputAbsy {

  private val AC = Debug.AC_PARSER
  
  import Parser2InputAbsy._

  abstract class SMTType
  case object SMTBool extends SMTType
  case object SMTInteger extends SMTType
  case class  SMTArray(arguments : List[SMTType],
                       result : SMTType) extends SMTType
  
  sealed abstract class VariableType
  case class BoundVariable(varType : SMTType)              extends VariableType
  case class SubstExpression(e : IExpression, t : SMTType) extends VariableType
  
  private type Env = Environment[SMTType, VariableType, Unit, SMTType]
  
  def apply(settings : ParserSettings) =
    new SMTParser2InputAbsy (new Env, settings)
  
  /**
   * Parse starting at an arbitrarily specified entry point
   */
  private def parseWithEntry[T](input : java.io.Reader,
                                env : Env,
                                entry : (parser) => T) : T = {
    val l = new Yylex(new CRRemover2 (input))
    val p = new parser(l)
    
    try { entry(p) } catch {
      case e : Exception =>
        throw new ParseException(
             "At line " + String.valueOf(l.line_num()) +
             ", near \"" + l.buff() + "\" :" +
             "     " + e.getMessage())
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private val badStringChar = """[^a-zA-Z_0-9']""".r
  
  private def sanitise(s : String) : String =
    badStringChar.replaceAllIn(s, (m : scala.util.matching.Regex.Match) =>
                                       ('a' + (m.toString()(0) % 26)).toChar.toString)

  //////////////////////////////////////////////////////////////////////////////

  /** Implicit conversion so that we can get a Scala-like iterator from a
   * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  def asString(s : SymbolRef) : String = s match {
    case s : IdentifierRef     => asString(s.identifier_)
    case s : CastIdentifierRef => asString(s.identifier_)
  }
  
  def asString(id : Identifier) : String = id match {
    case id : SymbolIdent =>
      asString(id.symbol_)
    case id : IndexIdent =>
      asString(id.symbol_) + "_" +
      ((id.listindexc_ map (_.asInstanceOf[Index].numeral_)) mkString "_")
  }
  
  def asString(s : Symbol) : String = s match {
    case s : NormalSymbol =>
      sanitise(s.normalsymbolt_)
    case s : QuotedSymbol =>
      sanitise(s.quotedsymbolt_.substring(1, s.quotedsymbolt_.length - 1))
  }
  
  object PlainSymbol {
    def unapply(s : SymbolRef) : scala.Option[String] = s match {
      case s : IdentifierRef => s.identifier_ match {
        case id : SymbolIdent => id.symbol_ match {
          case s : NormalSymbol => Some(s.normalsymbolt_)
          case _ => None
        }
        case _ => None
      }
      case _ => None
    }
  }
  
  object IndexedSymbol {
    def unapplySeq(s : SymbolRef) : scala.Option[Seq[String]] = s match {
      case s : IdentifierRef => s.identifier_ match {
        case id : IndexIdent => id.symbol_ match {
          case s : NormalSymbol =>
            Some(List(s.normalsymbolt_) ++
                 (id.listindexc_ map (_.asInstanceOf[Index].numeral_)))
          case _ => None
        }
        case _ => None
      }
      case _ => None
    }
  }

  object CastSymbol {
    def unapply(s : SymbolRef) : scala.Option[(String, Sort)] = s match {
      case s : CastIdentifierRef => s.identifier_ match {
        case id : SymbolIdent => id.symbol_ match {
          case ns : NormalSymbol => Some((ns.normalsymbolt_, s.sort_))
          case _ => None
        }
        case _ => None
      }
      case _ => None
    }
  }  

  //////////////////////////////////////////////////////////////////////////////
  
  private object LetInlineVisitor
          extends CollectingVisitor[(List[IExpression], Int), IExpression] {

    override def preVisit(t : IExpression,
                          substShift : (List[IExpression], Int)) : PreVisitResult = {
      val (subst, shift) = substShift
      t match {
        case IVariable(index)
          if (index < subst.size && subst(index).isInstanceOf[ITerm]) =>
          ShortCutResult(subst(index))

        case IVariable(index)
          if (index >= subst.size) =>
          ShortCutResult(IVariable(index + shift))

        case IIntFormula(IIntRelation.EqZero, IVariable(index))
          if (index < subst.size && subst(index).isInstanceOf[IFormula]) =>
          ShortCutResult(subst(index))
          
        case IQuantified(_, _) | IEpsilon(_) => {
          val (subst, shift) = substShift
          val newSubst = for (t <- subst) yield VariableShiftVisitor(t, 0, 1)
          UniSubArgs((IVariable(0) :: newSubst, shift))
        }
        case _ => KeepArg
      }
    }

    def postVisit(t : IExpression,
                  substShift : (List[IExpression], Int),
                  subres : Seq[IExpression]) : IExpression = t update subres
  }

}


class SMTParser2InputAbsy (_env : Environment[SMTParser2InputAbsy.SMTType,
                                              SMTParser2InputAbsy.VariableType,
                                              Unit,
                                              SMTParser2InputAbsy.SMTType],
                           settings : ParserSettings)
      extends Parser2InputAbsy(_env) {
  
  import IExpression._
  import Parser2InputAbsy._
  import SMTParser2InputAbsy._
  
  /** Implicit conversion so that we can get a Scala-like iterator from a
    * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  type GrammarExpression = Term

  //////////////////////////////////////////////////////////////////////////////

  def apply(input : java.io.Reader)
           : (IFormula, List[IInterpolantSpec], Signature) = {
    def entry(parser : smtlib.parser) = {
      val parseTree = parser.pScriptC
      parseTree match {
        case parseTree : Script => parseTree
        case _ => throw new ParseException("Input is not an SMT-LIB 2 file")
      }
    }
    
    apply(parseWithEntry(input, env, entry _))
    
    val (assumptionFormula, interpolantSpecs) =
      if (genInterpolants) {
        val namedParts = (for ((a, i) <- assumptions.iterator.zipWithIndex)
                          yield INamedPart(new PartName ("p" + i), a)).toList
        val names = for(part <- namedParts) yield part.name
        val interSpecs = (for(i <- 1 until names.length)
                          yield new IInterpolantSpec(names take i, names drop i)).toList
        val namedAxioms = INamedPart(PartName.NO_NAME, getAxioms)
        (connect(namedParts, IBinJunctor.And) &&& namedAxioms,
         interSpecs)
      } else {
        (connect(assumptions, IBinJunctor.And) &&& getAxioms, List())
      }

    val completeFor = !assumptionFormula
    (completeFor, interpolantSpecs, genSignature(completeFor))
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Parse an SMT-LIB script of the form
   * <code>(ignore expression)</code>.
   */
  def parseIgnoreCommand(input : java.io.Reader) : IExpression = {
    def entry(parser : smtlib.parser) = {
      val parseTree = parser.pScriptC
      parseTree match {
        case script : Script
          if (script.listcommand_.size == 1) =>
            script.listcommand_.head match {
              case cmd : IgnoreCommand => cmd.term_
              case _ =>
                throw new ParseException(
                    "Input is not of the form (ignore expression)")
            }
        case _ => throw new ParseException(
                    "Input is not of the form (ignore expression)")
      }
    }
    val expr = parseWithEntry(input, env, entry _)
    translateTerm(expr, -1) match {
      case p@(_, SMTBool)    => asFormula(p)
      case p@(_, SMTInteger) => asTerm(p)
    }
  }

  def parseExpression(str : String) : IExpression =
    parseIgnoreCommand(
      new java.io.BufferedReader (
        new java.io.StringReader("(ignore " + str + ")")))
  
  //////////////////////////////////////////////////////////////////////////////

  protected def defaultFunctionType(f : IFunction) : SMTType = SMTInteger

  /**
   * Translate boolean-valued functions as predicates or as functions? 
   */
  private var booleanFunctionsAsPredicates =
    Param.BOOLEAN_FUNCTIONS_AS_PREDICATES(settings)
  /**
   * Inline all let-expressions?
   */
  private var inlineLetExpressions = true
  /**
   * Inline functions introduced using define-fun?
   */
  private var inlineDefinedFuns = true
  /**
   * Totality axioms?
   */
  private var totalityAxiom = true
  /**
   * Functionality axioms?
   */
  private var functionalityAxiom = true
  /**
   * Set up things for interpolant generation?
   */
  private var genInterpolants = false
  
  //////////////////////////////////////////////////////////////////////////////

  private val printer = new PrettyPrinterNonStatic
  
  //////////////////////////////////////////////////////////////////////////////
  
  private object BooleanParameter {
    def unapply(param : AttrParam) : scala.Option[Boolean] = param match {
      case param : SomeAttrParam => param.sexpr_ match {
        case expr : SymbolSExpr =>
          asString(expr.symbol_) match {
            case "true" => Some(true)
            case "false" => Some(false)
            case _ => None
          }
        case _ => None
      }
      case _ : NoAttrParam => None
    }
  }

  private val assumptions = new ArrayBuffer[IFormula]

  private val functionDefs = new MHashMap[IFunction, (IExpression, SMTType)]

  private val sortDefs = new MHashMap[String, SMTType]

  private var declareConstWarning = false
  
  private def apply(script : Script) = for (cmd <- script.listcommand_) cmd match {
//      case cmd : SetLogicCommand =>
//      case cmd : SetInfoCommand =>
//      case cmd : SortDeclCommand =>
//      case cmd : PushCommand =>
//      case cmd : PopCommand =>
//      case cmd : CheckSatCommand =>
//      case cmd : ExitCommand =>

      //////////////////////////////////////////////////////////////////////////

      case cmd : SortDefCommand => {
        if (!cmd.listsymbol_.isEmpty)        
          throw new Parser2InputAbsy.TranslationException(
              "Currently only define-sort with arity 0 is supported")
        sortDefs.put(asString(cmd.symbol_), translateSort(cmd.sort_))
      }

      //////////////////////////////////////////////////////////////////////////
      
      case cmd : SetOptionCommand => {
        def noBooleanParam(option : String) =
          throw new Parser2InputAbsy.TranslationException(
              "Expected a boolean parameter after option " + option)
        
        val annot = cmd.optionc_.asInstanceOf[Option]
                                .annotation_.asInstanceOf[AttrAnnotation]
        annot.annotattribute_ match {
          case ":boolean-functions-as-predicates" => annot.attrparam_ match {
            case BooleanParameter(value) =>
              booleanFunctionsAsPredicates = value
            case _ =>
              noBooleanParam(":boolean-functions-as-predicates")
          }
          
          case ":inline-let" => annot.attrparam_ match {
            case BooleanParameter(value) =>
              inlineLetExpressions = value
            case _ =>
               noBooleanParam(":inline-let")
          }
          
          case ":inline-definitions" => annot.attrparam_ match {
            case BooleanParameter(value) =>
              inlineDefinedFuns = value
            case _ =>
               noBooleanParam(":inline-definitions")
          }
          
          case ":totality-axiom" => annot.attrparam_ match {
            case BooleanParameter(value) =>
              totalityAxiom = value
            case _ =>
               noBooleanParam(":totality-axiom")
          }
          
          case ":functionality-axiom" => annot.attrparam_ match {
            case BooleanParameter(value) =>
              functionalityAxiom = value
            case _ =>
               noBooleanParam(":functionality-axiom")
          }
          
          case ":produce-interpolants" => annot.attrparam_ match {
            case BooleanParameter(value) =>
              genInterpolants = value
            case _ =>
               noBooleanParam(":produce-interpolants")
          }
          
          case opt =>
            warn("ignoring option " + opt)
        }
      }

      //////////////////////////////////////////////////////////////////////////
      
      case cmd : FunctionDeclCommand => {
        // Functions are always declared to have integer inputs and outputs
        val name = asString(cmd.symbol_)
        val args : Seq[SMTType] = cmd.mesorts_ match {
          case sorts : SomeSorts =>
            for (s <- sorts.listsort_) yield translateSort(s)
          case _ : NoSorts =>
            List()
        }
        val res = translateSort(cmd.sort_)
        if (args.length > 0) {
          if (!booleanFunctionsAsPredicates || res != SMTBool)
            // use a real function
            env.addFunction(new IFunction(name, args.length,
                                          !totalityAxiom, !functionalityAxiom),
                            res)
          else
            // use a predicate
            env.addPredicate(new Predicate(name, args.length), ())
        } else if (res != SMTBool)
          // use a constant
          env.addConstant(new ConstantTerm(name), Environment.NullaryFunction, res)
        else
          // use a nullary predicate (propositional variable)
          env.addPredicate(new Predicate(name, 0), ())
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : ConstDeclCommand => {
        if (!declareConstWarning) {
          warn("accepting command declare-const, which is not SMT-LIB 2")
          declareConstWarning = true
        }

        val name = asString(cmd.symbol_)
        val res = translateSort(cmd.sort_)
        if (res != SMTBool)
          // use a constant
          env.addConstant(new ConstantTerm(name), Environment.NullaryFunction, res)
        else
          // use a nullary predicate (propositional variable)
          env.addPredicate(new Predicate(name, 0), ())
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : FunctionDefCommand => {
        // Functions are always declared to have integer inputs and outputs
        val name = asString(cmd.symbol_)
        val argNum = pushVariables(cmd.listesortedvarc_)
        val resType = translateSort(cmd.sort_)
        
        // parse the definition of the function
        val body@(_, bodyType) = translateTerm(cmd.term_, 0)

        if (bodyType != resType)
          throw new Parser2InputAbsy.TranslationException(
              "Body of function definition has wrong type")

        // pop the variables from the environment
        for (_ <- PlainRange(argNum)) env.popVar

        // use a real function
        val f = new IFunction(name, argNum, true, true)
        env.addFunction(f, resType)
  
        if (inlineDefinedFuns) {
          functionDefs += (f -> body) 
        } else {
          // set up a defining equation and formula
          val lhs = IFunApp(f, for (i <- 1 to argNum) yield v(argNum - i))
          val matrix = ITrigger(List(lhs), lhs === asTerm(body))
          addAxiom(quan(Array.fill(argNum){Quantifier.ALL}, matrix))
        }
      }

      //////////////////////////////////////////////////////////////////////////
      
      case cmd : AssertCommand => {
        val f = asFormula(translateTerm(cmd.term_, -1))
        assumptions += f
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : GetInterpolantsCommand =>
        genInterpolants = true
      
      //////////////////////////////////////////////////////////////////////////
      
      case _ =>
        warn("ignoring " + (printer print cmd))
  }

  //////////////////////////////////////////////////////////////////////////////

  protected def translateSort(s : Sort) : SMTType = s match {
    case s : IdentSort => asString(s.identifier_) match {
      case "Int" => SMTInteger
      case "Bool" => SMTBool
      case id if (sortDefs contains id) => sortDefs(id)
      case id => {
        warn("treating sort " + (printer print s) + " as Int")
        SMTInteger
      }
    }
    case s : CompositeSort => asString(s.identifier_) match {
      case "Array" => {
        val args =
          for (t <- s.listsort_.toList) yield translateSort(t)
        if (args.size < 2)
          throw new Parser2InputAbsy.TranslationException(
            "Expected at least two sort arguments in " + (printer print s))
        SMTArray(args.init, args.last)
      }
      case id => {
        warn("treating sort " + (printer print s) + " as Int")
        SMTInteger
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  protected def translateTerm(t : Term, polarity : Int)
                             : (IExpression, SMTType) = t match {
    case t : smtlib.Absyn.ConstantTerm =>
      translateSpecConstant(t.specconstant_)
      
    case t : NullaryTerm =>
      symApp(t.symbolref_, List(), polarity)
    case t : FunctionTerm =>
      symApp(t.symbolref_, t.listterm_, polarity)

    case t : QuantifierTerm =>
      translateQuantifier(t, polarity)
    
    case t : AnnotationTerm => {
      val triggers = for (annot <- t.listannotation_;
                          a = annot.asInstanceOf[AttrAnnotation];
                          if (a.annotattribute_ == ":pattern")) yield {
        a.attrparam_ match {
          case p : SomeAttrParam => p.sexpr_ match {
            case e : ParenSExpr => 
              for (expr <- e.listsexpr_.toList;
                   transTriggers = {
                     try { List(translateTrigger(expr)) }
                     catch { case _ : TranslationException |
                                  _ : Environment.EnvironmentException => {
                       warn("could not parse trigger " +
                            (printer print expr) +
                            ", ignoring")
                       List()
                     } }
                   };
                   t <- transTriggers) yield t
            case _ =>
              throw new Parser2InputAbsy.TranslationException(
                 "Expected list of patterns after \":pattern\"")
          }
          case _ : NoAttrParam =>
            throw new Parser2InputAbsy.TranslationException(
               "Expected trigger patterns after \":pattern\"")
        }
      }
      
      if (triggers.isEmpty)
        translateTerm(t.term_, polarity)
      else
        ((asFormula(translateTerm(t.term_, polarity)) /: triggers) {
           case (res, trigger) => ITrigger(ITrigger.extractTerms(trigger), res)
         }, SMTBool)
    }
    
    case t : LetTerm =>
      translateLet(t, polarity)
  }

  //////////////////////////////////////////////////////////////////////////////

  // add bound variables to the environment and record their number
  private def pushVariables(vars : smtlib.Absyn.ListSortedVariableC) : Int = {
    var quantNum : Int = 0
    
    for (binder <- vars) binder match {
      case binder : SortedVariable => {
        pushVar(binder.sort_, binder.symbol_)
        quantNum = quantNum + 1
      }
    }
    
    quantNum
  }

  private def pushVariables(vars : smtlib.Absyn.ListESortedVarC) : Int = {
    var quantNum : Int = 0
    
    for (binder <- vars) binder match {
      case binder : ESortedVar => {
        pushVar(binder.sort_, binder.symbol_)
        quantNum = quantNum + 1
      }
    }
    
    quantNum
  }

  private def pushVar(bsort : Sort, bsym : Symbol) : Unit =
    env.pushVar(asString(bsym), BoundVariable(translateSort(bsort)))
  
  private def translateQuantifier(t : QuantifierTerm, polarity : Int)
                                 : (IExpression, SMTType) = {
    val quant : Quantifier = t.quantifier_ match {
      case _ : AllQuantifier => Quantifier.ALL
      case _ : ExQuantifier => Quantifier.EX
    }

    val quantNum = pushVariables(t.listsortedvariablec_)
    
    val body = asFormula(translateTerm(t.term_, polarity))

    // we might need guards 0 <= x <= 1 for quantifiers ranging over booleans
    val guard = connect(
        for (binderC <- t.listsortedvariablec_.iterator;
             binder = binderC.asInstanceOf[SortedVariable];
             if (translateSort(binder.sort_) == SMTBool)) yield {
          (env lookupSym asString(binder.symbol_)) match {
            case Environment.Variable(ind, _) => (v(ind) >= 0) & (v(ind) <= 1)
            case _ => { // just prevent a compiler warning
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              Debug.assertInt(SMTParser2InputAbsy.AC, false)
              //-END-ASSERTION-/////////////////////////////////////////////////
              null
            }
          }
        },
        IBinJunctor.And)
      
    val matrix = guard match {
      case IBoolLit(true) =>
        body
      case _ => {
        // we need to insert the guard underneath possible triggers
        def insertGuard(f : IFormula) : IFormula = f match {
          case ITrigger(pats, subF) =>
            ITrigger(pats, insertGuard(subF))
          case _ => quant match {
            case Quantifier.ALL => guard ===> f
            case Quantifier.EX => guard &&& f
          }
        }
        
        insertGuard(body)
      }
    }
      
    val res = quan(Array.fill(quantNum){quant}, matrix)

    // pop the variables from the environment
    for (_ <- PlainRange(quantNum)) env.popVar
    
    (res, SMTBool)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private var letVarCounter = 0
  
  private def letVarName(base : String) = {
    val res = base + "_" + letVarCounter
    letVarCounter = letVarCounter + 1
    res
  }
  
  /**
   * If t is an integer term, let expression in positive position:
   *   (let ((v t)) s)
   *   ->
   *   \forall int v; (v=t -> s)
   * 
   * If t is a formula, let expression in positive position:
   *   (let ((v t)) s)
   *   ->
   *   \forall int v; ((t <-> v=0) -> s)
   *   
   * TODO: possible optimisation: use implications instead of <->, depending
   * on the polarity of occurrences of v
   */
  private def translateLet(t : LetTerm, polarity : Int)
                          : (IExpression, SMTType) = {
    val bindings = for (b <- t.listbindingc_) yield {
      val binding = b.asInstanceOf[Binding]
      val (boundTerm, boundType) = translateTerm(binding.term_, 0)
      (asString(binding.symbol_), boundType, boundTerm)
    }

    if (env existsVar (_.isInstanceOf[BoundVariable])) {
      // we are underneath a real quantifier, so have to introduce quantifiers
      // for this let expression, or directly substitute
      
      for ((v, t, _) <- bindings) env.pushVar(v, BoundVariable(t))

      val wholeBody@(body, bodyType) = translateTerm(t.term_, polarity)
      
      for (_ <- bindings) env.popVar

      //////////////////////////////////////////////////////////////////////////
      
      if (inlineLetExpressions) {
        // then we directly inline the bound formulae and terms
        
        val subst = for ((_, t, s) <- bindings.toList.reverse) yield asTerm((s, t))
        (LetInlineVisitor.visit(body, (subst, -bindings.size)), bodyType)
      } else {
        val definingEqs =
          connect(for (((_, t, s), num) <- bindings.iterator.zipWithIndex) yield {
            val shiftedS = VariableShiftVisitor(s, 0, bindings.size)
            val bv = v(bindings.length - num - 1)
            t match {        
              case SMTBool    =>
                IFormulaITE(asFormula((shiftedS, t)),
                            IIntFormula(IIntRelation.EqZero, bv),
                            IIntFormula(IIntRelation.EqZero, bv + i(-1)))
              case _ =>
                asTerm((shiftedS, t)) === bv
            }}, IBinJunctor.And)
      
        bodyType match {
          case SMTBool =>
            (if (polarity > 0)
              quan(Array.fill(bindings.length){Quantifier.ALL},
                   definingEqs ==> asFormula(wholeBody))
             else
               quan(Array.fill(bindings.length){Quantifier.EX},
                    definingEqs &&& asFormula(wholeBody)),
             SMTBool)
        }
      }
      
    } else {
      // we introduce a boolean or integer variables to encode this let expression

      for ((name, t, s) <- bindings)
        // directly substitute small expressions, unless the user
        // has chosen otherwise
        if (inlineLetExpressions && SizeVisitor(s) <= 1000) {
          env.pushVar(name, SubstExpression(s, t))
        } else addAxiom(t match {
          case SMTBool => {
            val f = new IFunction(letVarName(name), 1, true, false)
            env.addFunction(f, SMTInteger)
            env.pushVar(name, SubstExpression(all((v(0) === 0) ==> (f(v(0)) === 0)),
                                              SMTBool))
            all(ITrigger(List(f(v(0))),
                         (v(0) === 0) ==>
                         (((f(v(0)) === 0) & asFormula((s, t))) |
                             ((f(v(0)) === 1) & !asFormula((s, t))))))
//            assumptions += all(ITrigger(List(f(v(0))),
//                               ((v(0) === 0) ==> ((f(v(0)) === 0) | (f(v(0)) === 1)))))
          }
          case exprType => {
            val c = new ConstantTerm(letVarName(name))
            env.addConstant(c, Environment.NullaryFunction, exprType)
            env.pushVar(name, SubstExpression(c, exprType))
            c === asTerm((s, t))
          }
        })
      
      /*
      val definingEqs = connect(
        for ((v, t, s) <- bindings.iterator) yield
             if (SizeVisitor(s) <= 20) {
               env.pushVar(v, SubstExpression(s, t))
               i(true)
             } else t match {
               case SMTBool => {
                 val p = new Predicate(letVarName(v), 0)
                 env.addPredicate(p, ())
                 env.pushVar(v, SubstExpression(p(), SMTBool))
                 asFormula((s, t)) <=> p()
               }
               case SMTInteger => {
                 val c = new ConstantTerm(letVarName(v))
                 env.addConstant(c, Environment.NullaryFunction, ())
                 env.pushVar(v, SubstExpression(c, SMTInteger))
                 asTerm((s, t)) === c
               }
             }, IBinJunctor.And)
      */
      
      val wholeBody = translateTerm(t.term_, polarity)
      
/*      val definingEqs =
        connect(for ((v, t, s) <- bindings.reverseIterator) yield {
          (env lookupSym v) match {
            case Environment.Variable(_, IntConstant(c)) =>
              asTerm((s, t)) === c
            case Environment.Variable(_, BooleanConstant(p)) =>
              asFormula((s, t)) <=> p()
          }}, IBinJunctor.And) */
      
      for (_ <- bindings) env.popVar

      wholeBody
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private var tildeWarning = false
  
  protected def symApp(sym : SymbolRef, args : Seq[Term], polarity : Int)
                      : (IExpression, SMTType) = sym match {
    ////////////////////////////////////////////////////////////////////////////
    // Hardcoded connectives of formulae
    
    case PlainSymbol("true") => {
      checkArgNum("true", 0, args)
      (i(true), SMTBool)
    }
    case PlainSymbol("false") => {
      checkArgNum("false", 0, args)
      (i(false), SMTBool)
    }

    case PlainSymbol("not") => {
      checkArgNum("not", 1, args)
      (!asFormula(translateTerm(args.head, -polarity)), SMTBool)
    }
    
    case PlainSymbol("and") =>
      (connect(for (s <- flatten("and", args))
                 yield asFormula(translateTerm(s, polarity)),
               IBinJunctor.And),
       SMTBool)
    
    case PlainSymbol("or") =>
      (connect(for (s <- flatten("or", args))
                 yield asFormula(translateTerm(s, polarity)),
               IBinJunctor.Or),
       SMTBool)
    
    case PlainSymbol("=>") => {
      if (args.size == 0)
        throw new Parser2InputAbsy.TranslationException(
          "Operator \"=>\" has to be applied to at least one argument")

      (connect((for (a <- args.init) yield
                 !asFormula(translateTerm(a, -polarity))) ++
               List(asFormula(translateTerm(args.last, polarity))),
               IBinJunctor.Or),
       SMTBool)
    }
    
    case PlainSymbol("xor") => {
      if (args.size == 0)
        throw new Parser2InputAbsy.TranslationException(
          "Operator \"xor\" has to be applied to at least one argument")

      (connect(List(asFormula(translateTerm(args.head, polarity))) ++
               (for (a <- args.tail) yield
                 !asFormula(translateTerm(a, -polarity))),
               IBinJunctor.Eqv),
       SMTBool)
    }
    
    case PlainSymbol("ite") => {
      checkArgNum("ite", 3, args)
      val transArgs = for (a <- args) yield translateTerm(a, 0)
      (transArgs map (_._2)) match {
        case Seq(SMTBool, SMTBool, SMTBool) =>
          (IFormulaITE(asFormula(transArgs(0)),
                       asFormula(transArgs(1)), asFormula(transArgs(2))),
           SMTBool)
        case Seq(SMTBool, t1, t2) =>
          (ITermITE(asFormula(transArgs(0)),
                    asTerm(transArgs(1)), asTerm(transArgs(2))),
           t1)
      }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    // Hardcoded predicates (which might also operate on booleans)
    
    case PlainSymbol("=") => {
      val transArgs = for (a <- args) yield translateTerm(a, 0)
      (if (transArgs forall (_._2 == SMTBool)) {
         connect(for (Seq(a, b) <- (transArgs map (asFormula(_))) sliding 2)
                   yield (a <=> b),
                 IBinJunctor.And)
       } else {
         val types = (transArgs map (_._2)).toSet
         if (types.size > 1)
           throw new Parser2InputAbsy.TranslationException(
             "Can only compare terms of same type using =")
         connect(for (Seq(a, b) <- (transArgs map (asTerm(_))) sliding 2)
                   yield (a === b),
                 IBinJunctor.And)
       },
       SMTBool)
    }
    
    case PlainSymbol("distinct") => {
      val transArgs = for (a <- args) yield translateTerm(a, 0)
      (if (transArgs forall (_._2 == SMTBool)) transArgs.length match {
         case 0 | 1 => true
         case 2 => asTerm(transArgs(0)) =/= asTerm(transArgs(1))
         case _ => false
       } else {
         val types = (transArgs map (_._2)).toSet
         if (types.size > 1)
           throw new Parser2InputAbsy.TranslationException(
             "Can only compare terms of same type using distinct")
         connect(for (firstIndex <- 1 until transArgs.length;
                      firstTerm = asTerm(transArgs(firstIndex));
                      secondIndex <- 0 until firstIndex) yield {
           firstTerm =/= asTerm(transArgs(secondIndex))
         }, IBinJunctor.And)
       }, SMTBool)
    }
    
    case PlainSymbol("<=") =>
      (translateChainablePred(args, _ <= _), SMTBool)
    case PlainSymbol("<") =>
      (translateChainablePred(args, _ < _), SMTBool)
    case PlainSymbol(">=") =>
      (translateChainablePred(args, _ >= _), SMTBool)
    case PlainSymbol(">") =>
      (translateChainablePred(args, _ > _), SMTBool)
    
    case IndexedSymbol("divisible", denomStr) => {
      checkArgNum("divisible", 1, args)
      val denom = i(IdealInt(denomStr))
      val num = VariableShiftVisitor(asTerm(translateTerm(args.head, 0)), 0, 1)
      (ex(num === v(0) * denom), SMTBool)
    }
      
    ////////////////////////////////////////////////////////////////////////////
    // Hardcoded integer operations

    case PlainSymbol("+") =>
      (sum(for (s <- flatten("+", args))
             yield asTerm(translateTerm(s, 0), SMTInteger)),
       SMTInteger)

    case PlainSymbol("-") if (args.length == 1) =>
      (-asTerm(translateTerm(args.head, 0), SMTInteger), SMTInteger)

    case PlainSymbol("~") if (args.length == 1) => {
      if (!tildeWarning) {
        warn("interpreting \"~\" as unary minus, like in SMT-LIB 1")
        tildeWarning = true
      }
      (-asTerm(translateTerm(args.head, 0), SMTInteger), SMTInteger)
    }

    case PlainSymbol("-") => {
      (asTerm(translateTerm(args.head, 0), SMTInteger) -
          sum(for (a <- args.tail)
                yield asTerm(translateTerm(a, 0), SMTInteger)),
       SMTInteger)
    }

    case PlainSymbol("*") =>
      ((for (s <- flatten("*", args))
          yield asTerm(translateTerm(s, 0), SMTInteger))
          reduceLeft (mult _),
       SMTInteger)

    case PlainSymbol("div") => {
      checkArgNum("div", 2, args)
      val Seq(num, denom) =
        for (a <- args) yield VariableShiftVisitor(asTerm(translateTerm(a, 0)), 0, 1)
      val v0Denom = mult(v(0), denom)
      (eps((v0Denom <= num) & (denom match {
             case Const(denomVal) => v0Denom > num - denomVal.abs
             case denom => (num < v0Denom + denom) | (num < v0Denom - denom)
           })),
       SMTInteger)
    }
       
    case PlainSymbol("mod") => {
      checkArgNum("mod", 2, args)
      val Seq(num, denom) =
        for (a <- args) yield VariableShiftVisitor(asTerm(translateTerm(a, 0)), 0, 1)
      (eps((v(0) >= 0) & (denom match {
             case Const(denomVal) => v(0) < denomVal.abs
             case denom => (v(0) < denom) | (v(0) < -denom)
           }) &
           ex(VariableShiftVisitor(num, 0, 1) ===
              mult(v(0), VariableShiftVisitor(denom, 0, 1)) + v(1))),
       SMTInteger)
    }

    case PlainSymbol("abs") => {
      checkArgNum("abs", 1, args)
      val arg = VariableShiftVisitor(asTerm(translateTerm(args.head, 0)), 0, 1)
      (eps((v(0) === arg | v(0) === -arg) & (v(0) >= 0)), SMTInteger)
    }
      
    ////////////////////////////////////////////////////////////////////////////
    // Array operations
    
    case PlainSymbol("select") => {
      val transArgs = for (a <- args) yield translateTerm(a, 0)
      transArgs.head._2 match {
        case SMTArray(_, resultType) =>
          (IFunApp(SimpleArray(args.size - 1).select,
                   for (a <- transArgs) yield asTerm(a)),
           resultType)
        case s =>
          throw new Parser2InputAbsy.TranslationException(
            "select has to be applied to an array expression, not " + s)
      }
    }

    case PlainSymbol("store") => {
      val transArgs = for (a <- args) yield translateTerm(a, 0)
      transArgs.head._2 match {
        case s : SMTArray =>
          (IFunApp(SimpleArray(args.size - 2).store,
                   for (a <- transArgs) yield asTerm(a)),
           s)
        case s =>
          throw new Parser2InputAbsy.TranslationException(
            "store has to be applied to an array expression, not " + s)
      }
    }

/*
    case PlainSymbol("select") if (args.size == 2) => {
      genArrayAxioms(!totalityAxiom, 1)
      unintFunApp("select", sym, args, polarity)
    }

    case PlainSymbol("store") if (args.size == 3) => {
      genArrayAxioms(!totalityAxiom, 1)
      unintFunApp("store", sym, args, polarity)
    }

    case PlainSymbol("select") if (args.size != 2) => {
      genArrayAxioms(!totalityAxiom, args.size - 1)
      unintFunApp("_select_" + (args.size - 1), sym, args, polarity)
    }
    
    case PlainSymbol("store") if (args.size != 3) => {
      genArrayAxioms(!totalityAxiom, args.size - 2)
      unintFunApp("_store_" + (args.size - 2), sym, args, polarity)
    }
*/    
    ////////////////////////////////////////////////////////////////////////////
    // Declared symbols from the environment
    case id => unintFunApp(asString(id), sym, args, polarity)
  }
  
  private def unintFunApp(id : String,
                          sym : SymbolRef, args : Seq[Term], polarity : Int)
                         : (IExpression, SMTType) =
    (env lookupSym id) match {
      case Environment.Predicate(pred, _, _) => {
        checkArgNumLazy(printer print sym, pred.arity, args)
        (IAtom(pred, for (a <- args) yield asTerm(translateTerm(a, 0))),
         SMTBool)
      }
      
      case Environment.Function(fun, resultType) => {
        checkArgNumLazy(printer print sym, fun.arity, args)
        (functionDefs get fun) match {
          case Some((body, t)) => {
            var translatedArgs = List[ITerm]()
            for (a <- args)
              translatedArgs = asTerm(translateTerm(a, 0)) :: translatedArgs
            (VariableSubstVisitor(body, (translatedArgs, 0)), t)
          }
          case None =>
            (IFunApp(fun, for (a <- args) yield asTerm(translateTerm(a, 0))),
             resultType)
        }
      }

      case Environment.Constant(c, _, t) =>
        (c, t)
      
      case Environment.Variable(i, BoundVariable(t)) =>
        (v(i), t)
        
      case Environment.Variable(i, SubstExpression(e, t)) =>
        (e, t)
    }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private def translateTrigger(expr : SExpr) : IExpression = expr match {
    
    case expr : ConstantSExpr => translateSpecConstant(expr.specconstant_)._1
    
    case expr : SymbolSExpr => (env lookupSym asString(expr.symbol_)) match {
      case Environment.Function(fun, _) => {
        checkArgNumSExpr(printer print expr.symbol_,
                         fun.arity, List[SExpr]())
        IFunApp(fun, List())
      }
      case Environment.Predicate(pred, _, _) => {
        checkArgNumSExpr(printer print expr.symbol_,
                         pred.arity, List[SExpr]())
        IAtom(pred, List())
      }
      case Environment.Constant(c, _, _) => c
      case Environment.Variable(i, BoundVariable(t)) if (t != SMTBool) => v(i)
      case _ =>
        throw new Parser2InputAbsy.TranslationException(
          "Unexpected symbol in a trigger: " +
          (printer print expr.symbol_))
    }
    
    case expr : ParenSExpr => {
      if (expr.listsexpr_.isEmpty)
        throw new Parser2InputAbsy.TranslationException(
          "Expected a function application, not " + (printer print expr))
      
      expr.listsexpr_.head match {
        case funExpr : SymbolSExpr => asString(funExpr.symbol_) match {
          case "select" =>
            IFunApp(SimpleArray(expr.listsexpr_.size - 2).select,
                    translateSExprTail(expr.listsexpr_))
          case "store" =>
            IFunApp(SimpleArray(expr.listsexpr_.size - 3).store,
                    translateSExprTail(expr.listsexpr_))

          case funName => (env lookupSym funName) match {
            case Environment.Function(fun, _) => {
              checkArgNumSExpr(printer print funExpr.symbol_, fun.arity,
                               expr.listsexpr_.tail)
              IFunApp(fun, translateSExprTail(expr.listsexpr_))
            }
            case Environment.Predicate(pred, _, _) => {
              checkArgNumSExpr(printer print funExpr.symbol_, pred.arity,
                               expr.listsexpr_.tail)
              IAtom(pred, translateSExprTail(expr.listsexpr_))
            }
            case Environment.Constant(c, _, _) => {
              checkArgNumSExpr(printer print funExpr.symbol_,
                               0, expr.listsexpr_.tail)
              c
            }
            case Environment.Variable(i, BoundVariable(t)) if (t != SMTBool) => {
              checkArgNumSExpr(printer print funExpr.symbol_,
                               0, expr.listsexpr_.tail)
              v(i)
            }
            case _ =>
              throw new Parser2InputAbsy.TranslationException(
                "Unexpected symbol in a trigger: " +
                (printer print funExpr.symbol_))
          }
        }
      }
    }
  }
  
  private def translateSExprTail(exprs : ListSExpr) : Seq[ITerm] = {
    val args = exprs.tail.toList
    for (e <- args) yield translateTrigger(e) match {
      case ta : ITerm => ta
      case ta : IFormula => ITermITE(ta, i(0), i(1))
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  protected def translateSpecConstant(c : SpecConstant)
                                     : (ITerm, SMTType) = c match {
    case c : NumConstant =>
      (i(IdealInt(c.numeral_)), SMTInteger)
    case c : HexConstant =>
      (i(IdealInt(c.hexadecimal_ substring 2, 16)), SMTInteger)
    case c : BinConstant =>
      (i(IdealInt(c.binary_ substring 2, 2)), SMTInteger)
  }
  
  private def translateChainablePred(args : Seq[Term],
                                     op : (ITerm, ITerm) => IFormula) : IFormula = {
    val transArgs = for (a <- args) yield asTerm(translateTerm(a, 0))
    connect(for (Seq(a, b) <- transArgs sliding 2) yield op(a, b), IBinJunctor.And)
  }
  
  private def flatten(op : String, args : Seq[Term]) : Seq[Term] =
    for (a <- args;
         b <- collectSubExpressions(a, (t:Term) => t match {
                case t : NullaryTerm => t.symbolref_ match {
                  case PlainSymbol(`op`) => true
                  case _ => false
                }
                case t : FunctionTerm => t.symbolref_ match {
                  case PlainSymbol(`op`) => true
                  case _ => false
                }
                case _ => false
              }, SMTConnective))
    yield b

  private def checkArgNumLazy(op : => String, expected : Int, args : Seq[Term]) : Unit =
    if (expected != args.size) checkArgNum(op, expected, args)
      
  protected def checkArgNum(op : String, expected : Int, args : Seq[Term]) : Unit =
    if (expected != args.size)
      throw new Parser2InputAbsy.TranslationException(
          "Operator \"" + op +
          "\" is applied to a wrong number of arguments: " +
          ((for (a <- args) yield (printer print a)) mkString ", "))
  
  private def checkArgNumSExpr(op : => String, expected : Int, args : Seq[SExpr]) : Unit =
    if (expected != args.size)
      throw new Parser2InputAbsy.TranslationException(
          "Operator \"" + op +
          "\" is applied to a wrong number of arguments: " +
          ((for (a <- args) yield (printer print a)) mkString ", "))
  
  private object SMTConnective extends ASTConnective {
    def unapplySeq(t : Term) : scala.Option[Seq[Term]] = t match {
      case t : NullaryTerm => Some(List())
      case t : FunctionTerm => Some(t.listterm_.toList)
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  protected def asFormula(expr : (IExpression, SMTType)) : IFormula = expr match {
    case (expr : IFormula, SMTBool) =>
      expr
    case (expr : ITerm, SMTBool) =>
      // then we assume that an integer encoding of boolean values was chosen
      IIntFormula(IIntRelation.EqZero, expr)
    case (expr, _) =>
      throw new Parser2InputAbsy.TranslationException(
                   "Expected a formula, not " + expr)
  }

  protected def asTerm(expr : (IExpression, SMTType)) : ITerm = expr match {
    case (expr : ITerm, _) =>
      expr
    case (expr : IFormula, SMTBool) =>
      ITermITE(expr, i(0), i(1))
    case (expr, _) =>
      throw new Parser2InputAbsy.TranslationException(
                   "Expected a term, not " + expr)
  }

  private def asTerm(expr : (IExpression, SMTType),
                     expectedSort : SMTType) : ITerm = expr match {
    case (expr : ITerm, `expectedSort`) =>
      expr
    case (expr, _) =>
      throw new Parser2InputAbsy.TranslationException(
                   "Expected a term of type " + expectedSort + ", not " + expr)
  }
}
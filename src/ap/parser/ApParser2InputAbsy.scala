/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011-2017 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser;

import ap._
import ap.parameters.ParserSettings
import ap.terfor.OneTerm
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.preds.Atom
import ap.util.{Debug, Logic, PlainRange}
import ap.basetypes.IdealInt
import ap.parser.ApInput._
import ap.parser.ApInput.Absyn._
import ap.theories.ADT
import ap.types.{Sort, MonoSortedIFunction, SortedIFunction,
                 SortedConstantTerm,
                 MonoSortedPredicate, SortedPredicate}

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 ArrayBuffer}

object ApParser2InputAbsy {

  private val AC = Debug.AC_PARSER
  
  import Parser2InputAbsy._

  type Env = Environment[Unit, Sort, Unit, Unit, Sort]
  
  def apply(settings : ParserSettings) =
    new ApParser2InputAbsy(new Env, settings)
  
  def parseExpression(input : java.io.Reader, env : Env) : IExpression = {
    def entry(parser : ApInput.parser) = {
      val parseTree = parser.pEntry
      parseTree match {
        case parseTree : ExprEntry => parseTree.expression_
        case _ => throw new ParseException("Input is not an expression")
      }
    }
    val expr = parseWithEntry(input, env, entry _)
    val t = new ApParser2InputAbsy (env, ParserSettings.DEFAULT)
    (t translateExpression expr)._1
  }
  
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

}

class ApParser2InputAbsy(_env : ApParser2InputAbsy.Env,
                         settings : ParserSettings)
      extends Parser2InputAbsy[Unit, Sort, Unit, Unit, Sort, Unit](_env, settings) {
  
  import IExpression._
  import Parser2InputAbsy._
  import ApParser2InputAbsy._
  
  /** Implicit conversion so that we can get a Scala-like iterator from a
    * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  type GrammarExpression = Expression

  //////////////////////////////////////////////////////////////////////////////

  def apply(input : java.io.Reader)
           : (IFormula, List[IInterpolantSpec], Signature) = {
    def entry(parser : ApInput.parser) = {
      val parseTree = parser.pEntry
      parseTree match {
        case parseTree : APIEntry => parseTree.api_
        case _ => throw new ParseException("Input is not a Princess file")
      }
    }
    
    translateAPI(parseWithEntry(input, env, entry _))
  }

  private def translateAPI(api : API)
              : (IFormula, List[IInterpolantSpec], Signature) = {
    collectSortDeclarations(api)
    collectDeclarations(api)
    collectFunPredDefs(api)
    inlineFunPredDefs

    val formula = translateProblem(api)
    val interSpecs = translateInterpolantSpecs(api)

    val completeFor = getAxioms ===> formula
    (completeFor, interSpecs, genSignature(completeFor))
  }

  //////////////////////////////////////////////////////////////////////////////
  
  protected def translateProblem(api : API) : IFormula = api match {
    case api : BlockList => {
      api.listblock_.filter(_.isInstanceOf[Problem]) match {
        case Seq(problem : Problem) =>
          asFormula(translateExpression(problem.expression_))
        case _ => throw new Parser2InputAbsy.TranslationException(
                             "Found zero or more than one \\problem blocks")
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  protected def translateInterpolantSpecs(api : API)
                                         : List[IInterpolantSpec] = api match {
    case api : BlockList => {
      (for (block <- api.listblock_; if (block.isInstanceOf[Interpolant])) yield {
         val inter = block.asInstanceOf[Interpolant]
         IInterpolantSpec(
           (for (id <- inter.listident_1) yield (env lookupPartName id)).toList,
           (for (id <- inter.listident_2) yield (env lookupPartName id)).toList)
       }).toList
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def collectSortDeclarations(api : API) : Unit = api match {
    case api : BlockList => {

      // first determine all declared ADTs
      val adtNames = new ArrayBuffer[String]

      for (block <- api.listblock_.iterator) block match {
        case block : SortDecls =>
          for (decl <- block.listdeclsortc_.iterator) decl match {
            case decl : DeclADT =>
              adtNames += decl.ident_
          }
        case _ => // nothing
      }

      // then translate ADT constructors
      val ctors = new ArrayBuffer[(String, ADT.CtorSignature)]

      for (block <- api.listblock_.iterator) block match {
        case block : SortDecls =>
          for (decl <- block.listdeclsortc_.iterator) decl match {
            case decl : DeclADT => {
              val adtSort = ADT.ADTSort(adtNames indexOf decl.ident_)

              for (ctorC <- decl.listdeclctorc_.iterator) {
                val ctor = ctorC.asInstanceOf[DeclCtor]

                val ctorName = ctor.ident_

                val arguments = ctor.optformalargs_ match {
                  case _ : NoFormalArgs =>
                    List()
                  case args : WithFormalArgs =>
                    for (arg <- args.formalargsc_.asInstanceOf[FormalArgs]
                                    .listargtypec_) yield arg match {
                      case arg : ArgType =>
                        throw new Parser2InputAbsy.TranslationException(
                          "Construct " + ctorName +
                          " needs to have named arguments")
                      case arg : NamedArgType => {
                        val argSort = arg.type_ match {
                          case ti : TypeIdent
                            if (adtNames contains ti.ident_) =>
                              ADT.ADTSort(adtNames indexOf ti.ident_)
                          case t =>
                            ADT.OtherSort(type2Sort(t))
                        }
                        (arg.ident_, argSort)
                      }
                    }
                }

                ctors += ((ctorName, ADT.CtorSignature(arguments, adtSort)))
              }
            }
          }
        case _ => // nothing
      }

      val adt = new ADT(adtNames.toVector, ctors.toVector)

      for (sort <- adt.sorts)
        env.addSort(sort.name, sort)
      for (f <- adt.constructors)
        env.addFunction(f, ())
      for (sels <- adt.selectors)
        for (sel <- sels)
          env.addFunction(sel, ())
      for (f <- adt.ctorIds)
        env.addFunction(f, ())

      // generate the is_ queries as inlined functions
      for (((name, ADT.CtorSignature(_, ADT.ADTSort(adtNum))), ctorNum) <-
              ctors.iterator.zipWithIndex) {
        val query =
          new MonoSortedPredicate("is_" + name, List(adt sorts adtNum))
        env.addPredicate(query, ())
        val body = adt.hasCtor(v(0), ctorNum)
        predicateDefs.put(query, body)
      }
    }
  }
  

  //////////////////////////////////////////////////////////////////////////////

  protected def collectDeclarations(api : API) : Unit = api match {
    case api : BlockList =>
      for (block <- api.listblock_.iterator) block match {
        case block : FunctionDecls =>
          for (decl <- block.listdeclfunc_.iterator)
            collectDeclFunC(decl,
              (id, sort) => env.addConstant(sort newConstant id,
                                            Environment.NullaryFunction,
                                            ()))
        case block : ExConstants =>
          for (decl <- block.listdeclconstantc_.iterator)
            collectDeclConstantC(decl,
              (id, sort) => env.addConstant(sort newConstant id,
                                            Environment.Existential,
                                            ()))
        case block : UniConstants =>
          for (decl <- block.listdeclconstantc_.iterator)
            collectDeclConstantC(decl,
              (id, sort) => env.addConstant(sort newConstant id,
                                            Environment.Universal,
                                            ()))
        case block : PredDecls =>
          for (decl <- block.listdeclpredc_.iterator) decl match {
            case decl : DeclPred => {
              val name = decl.ident_
              val argSorts : Seq[Sort] = decl.optformalargs_ match {
                case _ : NoFormalArgs =>
                  List()
                case args : WithFormalArgs =>
                  determineSorts(args.formalargsc_)
              }
              val sorted = argSorts exists (_ != Sort.Integer)

              val wrappedOpts = asScalaBuffer(decl.listpredoption_)
              val (negMatchOpts, otherOpts1) =
                wrappedOpts partition (_.isInstanceOf[NegMatch])
              val (noMatchOpts, otherOpts2) =
                otherOpts1 partition (_.isInstanceOf[NoMatch])
        
              val negMatch = !negMatchOpts.isEmpty
              val noMatch = !noMatchOpts.isEmpty
        
              if (!otherOpts2.isEmpty) {
                val strs = for (o <- otherOpts2) yield predOption2String(o)
                throw new Parser2InputAbsy.TranslationException(
                       "Illegal options for predicate: " + (strs mkString " "))
              }

              if (negMatch && noMatch)
                throw new Parser2InputAbsy.TranslationException(
                 "Illegal options for predicate: both \\negMatch and \\noMatch")

              val pred =
                if (sorted)
                  new MonoSortedPredicate(name, argSorts)
                else
                  new Predicate(name, argSorts.size)

              env.addPredicate(pred,
                               if (negMatch)
                                 Signature.PredicateMatchStatus.Negative
                               else if (noMatch)
                                 Signature.PredicateMatchStatus.None
                               else
                                 Signature.PredicateMatchStatus.Positive,
                               ())
            }
          }
        case _ => /* nothing */
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def collectDeclFunC(decl : DeclFunC, addCmd : (String, Sort) => Unit) : Unit =
    decl match {
      case decl : DeclFun => {
        val resSort = type2Sort(decl.type_)
        val argSorts = determineSorts(decl.formalargsc_)
        val sorted = (List(resSort) ++ argSorts) exists (_ != Sort.Integer)

        val wrappedOpts = asScalaBuffer(decl.listfunoption_)
        val (partialOpts, otherOpts1) =
          wrappedOpts partition (_.isInstanceOf[Partial])
        val (relationalOpts, otherOpts2) =
          otherOpts1 partition (_.isInstanceOf[Relational])
        
        val partial = !partialOpts.isEmpty
        val relational = !relationalOpts.isEmpty
        
        if (!otherOpts2.isEmpty) {
          val strs = for (o <- otherOpts2) yield funOption2String(o)
          throw new Parser2InputAbsy.TranslationException(
                       "Illegal options for function: " + (strs mkString " "))
        }

        val fun =
          if (sorted)
            new MonoSortedIFunction(decl.ident_,
                                    argSorts, resSort,
                                    partial, relational)
          else
            new IFunction(decl.ident_, argSorts.size,
                          partial, relational)

        env.addFunction(fun, ())
      }
      case decl : DeclFunConstant => {
        if (!decl.listfunoption_.isEmpty)
          throw new Parser2InputAbsy.TranslationException(
                                        "Constants do not have options")
        collectConstDeclarations(decl.declconstc_, addCmd)
      }
    }

  //////////////////////////////////////////////////////////////////////////////

  private def determineArity(args : FormalArgsC) : Int = args match {
    case args : FormalArgs => {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(ApParser2InputAbsy.AC,
        Logic.forall(for (at <- args.listargtypec_.iterator)
                     yield (at match {
                              case at : ArgType => at.type_.isInstanceOf[TypeInt]
                              case at : NamedArgType => at.type_.isInstanceOf[TypeInt]
                            })))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      args.listargtypec_.size
    }
  }
  
  private def determineSorts(args : FormalArgsC) : Seq[Sort] = args match {
    case args : FormalArgs =>
      for (at <- args.listargtypec_) yield at match {
        case at : ArgType      => type2Sort(at.type_)
        case at : NamedArgType => type2Sort(at.type_)
      }
  }
  
  private def funOption2String(option : FunOption) : String = option match {
    case _ : Partial => "\\partial"
    case _ : Relational => "\\relational"
  }
  
  private def predOption2String(option : PredOption) : String = option match {
    case _ : NegMatch => "\\negMatch"
    case _ : NoMatch => "\\noMatch"
  }
  
  private def collectDeclConstantC(decl : DeclConstantC,
                                   addCmd : (String, Sort) => Unit) : Unit =
    collectConstDeclarations(decl.asInstanceOf[DeclConstant].declconstc_, addCmd)

  private def collectDeclBinder(decl : DeclBinder,
                                addCmd : (String, Sort) => Unit) : Unit = decl match {
    case decl : DeclBinder1 =>
      collectVarDeclarations(decl.declvarc_, addCmd)
    case decl : DeclBinderM =>
      for (decl <- decl.listdeclvarc_.iterator) 
                                 collectVarDeclarations(decl, addCmd)
  }
  
  private def collectVarDeclarations(decl : DeclVarC,
                                     addCmd : (String, Sort) => Unit) : Unit = decl match {
    case decl : DeclVar => {
      val sort = type2Sort(decl.type_)
      for (id <- decl.listident_.iterator) addCmd(id, sort)
    }
  }

  private def collectConstDeclarations(decl : DeclConstC,
                                       addCmd : (String, Sort) => Unit) : Unit =
    decl match {
      case decl : DeclConst => {
        val sort = type2Sort(decl.type_)
        for (id <- decl.listident_.iterator) addCmd(id, sort)
      }
    }

  private def type2Sort(t : Type) : Sort = t match {
    case _ : TypeInt => Sort.Integer
    case _ : TypeNat => Sort.Nat
    case _ : TypeBool => Sort.Bool
    case t : TypeInterval => {
      val lb = t.intervallower_ match {
        case _ : InfLower =>      None
        case iv : NumLower =>     Some(IdealInt(iv.intlit_))
        case iv : NegNumLower =>  Some(-IdealInt(iv.intlit_))
      }
      val ub = t.intervalupper_ match {
        case _ : InfUpper =>     None
        case iv : NumUpper =>    Some(IdealInt(iv.intlit_))
        case iv : NegNumUpper => Some(-IdealInt(iv.intlit_))
      }

      for (l <- lb; u <- ub)
        if (l > u)
          throw new Parser2InputAbsy.TranslationException(
            "Interval types have to be non-empty")
          
      Sort.Interval(lb, ub)
    }
    case t : TypeIdent =>
      env lookupSort t.ident_
  }

  private def collectSingleVarDecl(decl : DeclSingleVarC) : Unit = decl match {
    case decl : DeclSingleVar =>
      env.pushVar(decl.ident_, type2Sort(decl.type_))
  }

  //////////////////////////////////////////////////////////////////////////////

  private val predicateDefs = new MHashMap[Predicate, IFormula]
  private val functionDefs  = new MHashMap[IFunction, ITerm]

  private def collectFunPredDefs(api : API) : Unit = api match {
    case api : BlockList =>
      for (block <- api.listblock_.iterator) block match {
        case block : FunctionDecls =>
          for (decl <- block.listdeclfunc_.iterator) decl match {
            case decl : DeclFun if (decl.optbody_.isInstanceOf[SomeBody]) => {
              val Environment.Function(fun, _) = env.lookupSym(decl.ident_)
              
              // declare arguments
              for (arg <- decl.formalargsc_.asInstanceOf[FormalArgs]
                              .listargtypec_.reverse)
                arg match {
                  case arg : NamedArgType =>
                    env.pushVar(arg.ident_, type2Sort(arg.type_))
                  case _ : ArgType =>
                    throw new Parser2InputAbsy.TranslationException(
                      "Argument name missing in definition of function " +
                      decl.ident_)
                }

              val body = decl.optbody_.asInstanceOf[SomeBody].expression_
              functionDefs.put(fun, asTerm(translateExpression(body)))

              for (_ <- 0 until fun.arity) env.popVar
            }
            case _ => // nothing
          }

        case block : PredDecls =>
          for (decl <- block.listdeclpredc_.iterator) decl match {
            case decl : DeclPred if (decl.optbody_.isInstanceOf[SomeBody]) => {
              val Environment.Predicate(pred, _, _) = env.lookupSym(decl.ident_)

              // declare arguments
              decl.optformalargs_ match {
                case _ : NoFormalArgs =>
                  // nothing
                case args : WithFormalArgs =>
                  for (arg <- args.formalargsc_.asInstanceOf[FormalArgs]
                                  .listargtypec_.reverse)
                    arg match {
                      case arg : NamedArgType =>
                        env.pushVar(arg.ident_, type2Sort(arg.type_))
                      case _ : ArgType =>
                        throw new Parser2InputAbsy.TranslationException(
                          "Argument name missing in definition of predicate " +
                          decl.ident_)
                    }
              }

              val body = decl.optbody_.asInstanceOf[SomeBody].expression_
              predicateDefs.put(pred, asFormula(translateExpression(body)))

              for (_ <- 0 until pred.arity) env.popVar
            }
            case _ => /* nothing */
          }
        case _ => /* nothing */
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Make sure that defined functions and predicates are closed under
   * inlining definitions.
   */
  private def inlineFunPredDefs : Unit = {
    val closedPreds = new MHashSet[Predicate]
    val closedFuns  = new MHashSet[IFunction]

    val isDefinedFun = (expr : IExpression) => expr match {
      case IAtom(pred, _) =>
        predicateDefs contains pred
      case IFunApp(fun, _) =>
        functionDefs contains fun
      case _ =>
        false
    }

    ////////////////////////////////////////////////////////////////////////////

    var openPreds = List[Predicate]()
    var openFuns  = List[IFunction]()

    for ((pred, body) <- predicateDefs)
      if (ContainsSymbol(body, isDefinedFun))
        openPreds = pred :: openPreds
      else
        closedPreds += pred

    for ((fun, body) <- functionDefs)
      if (ContainsSymbol(body, isDefinedFun))
        openFuns = fun :: openFuns
      else
        closedFuns += fun

    if (openPreds.isEmpty && openFuns.isEmpty)
      return

    ////////////////////////////////////////////////////////////////////////////

    val cannotBeInlined = (expr : IExpression) => expr match {
      case IAtom(pred, _) =>
        (predicateDefs contains pred) && !(closedPreds contains pred)
      case IFunApp(fun, _) =>
        (functionDefs contains fun) && !(closedFuns contains fun)
      case _ =>
        false
    }

    object Inliner extends CollectingVisitor[Unit, IExpression] {
      def postVisit(t : IExpression, arg : Unit,
                    subres : Seq[IExpression]) : IExpression = t match {
        case IAtom(pred, _) if (closedPreds contains pred) =>
          VariableSubstVisitor(
            predicateDefs(pred),
            (subres.toList.map(_.asInstanceOf[ITerm]), 0))
        case IFunApp(fun, _) if (closedFuns contains fun) =>
          VariableSubstVisitor(
            functionDefs(fun),
            (subres.toList.map(_.asInstanceOf[ITerm]), 0))
        case _ =>
          t update subres
      }
    }

    var changed = true
    while (changed) {
      changed = false

      openPreds =
        for (pred <- openPreds;
             if {
               val body = predicateDefs(pred)
               if (ContainsSymbol(body, cannotBeInlined)) {
                 true
               } else {
                 val newBody = Inliner.visit(body, ())
                 predicateDefs.put(pred, newBody.asInstanceOf[IFormula])
                 closedPreds += pred
                 changed = true
                 false
               }
             })
        yield pred

      openFuns =
        for (fun <- openFuns;
             if {
               val body = functionDefs(fun)
               if (ContainsSymbol(body, cannotBeInlined)) {
                 true
               } else {
                 val newBody = Inliner.visit(body, ())
                 functionDefs.put(fun, newBody.asInstanceOf[ITerm])
                 closedFuns += fun
                 changed = true
                 false
               }
             })
        yield fun
    }

    if (!openPreds.isEmpty || !openFuns.isEmpty)
      throw new Parser2InputAbsy.TranslationException(
        "Recursive function or predicate definitions are not supported yet")
  }

  //////////////////////////////////////////////////////////////////////////////

  private def translateExpression(f : Expression) : (IExpression, Sort) = f match {
    ////////////////////////////////////////////////////////////////////////////
    // Formulae
    case f : ExprEqv =>
      translateBinForConnective(f.expression_1, f.expression_2, _ <=> _)
    case f : ExprImp =>
      translateBinForConnective(f.expression_1, f.expression_2, _ ==> _)
    case f : ExprImpInv =>
      translateBinForConnective(f.expression_2, f.expression_1, _ ==> _)
    case f : ExprOr => {
      val subs = collectSubExpressions(f, _.isInstanceOf[ExprOr], ApConnective)
      ((for (f <- subs.iterator)
          yield asFormula(translateExpression(f))) reduceLeft (_ | _),
       Sort.Bool)
    }
    case f : ExprAnd => {
      val subs = collectSubExpressions(f, _.isInstanceOf[ExprAnd], ApConnective)
      ((for (f <- subs.iterator)
          yield asFormula(translateExpression(f))) reduceLeft (_ & _),
       Sort.Bool)
    }
    case f : ExprNot =>
      translateUnForConnective(f.expression_, ! _)
    case f : ExprQuant =>
      (translateQuant(f), Sort.Bool)
    case _ : ExprTrue =>
      (i(true), Sort.Bool)
    case _ : ExprFalse =>
      (i(false), Sort.Bool)
    case f : ExprDistinct =>
      // TODO: check sorts
      (distinct(translateOptArgs(f.optargs_) map (asTerm _)), Sort.Bool)
    case f : ExprIdApp =>
      translateFunctionApp(f.ident_, translateOptArgs(f.optargs_))
    case f : ExprDotAttr =>
      translateFunctionApp(f.ident_,
                           List(translateExpression(f.expression_)))
    case f : ExprRel => f.relsym_ match {
      case _ : RelEq =>
        translateCompBinTerConnective("=", f.expression_1, f.expression_2,
                                      _ === _)
      case _ : RelNEq =>
        translateCompBinTerConnective("!=", f.expression_1, f.expression_2,
                                      _ =/= _)
      case _ : RelLeq =>
        translateNumBinTerConnective("<=", f.expression_1, f.expression_2,
                                     _ <= _)
      case _ : RelGeq =>
        translateNumBinTerConnective(">=", f.expression_1, f.expression_2,
                                     _ >= _)
      case _ : RelLt =>
        translateNumBinTerConnective("<", f.expression_1, f.expression_2,
                                     _ < _)
      case _ : RelGt =>
        translateNumBinTerConnective(">", f.expression_1, f.expression_2,
                                     _ > _)
    }
    case f : ExprTrigger =>
      (translateTrigger(f), Sort.Bool)
    case f : ExprPart =>
      (INamedPart(env lookupPartName f.ident_,
                  asFormula(translateExpression(f.expression_))),
       Sort.Bool)
    ////////////////////////////////////////////////////////////////////////////
    // Terms
    case t : ExprPlus =>
      translateNumBinTerConnective("+", t.expression_1, t.expression_2, _ + _)
    case t : ExprMinus =>
      translateNumBinTerConnective("-", t.expression_1, t.expression_2, _ - _)
    case t : ExprMult =>
      translateNumBinTerConnective("*", t.expression_1, t.expression_2, mult _)
    case t : ExprDiv =>
      translateNumBinTerConnective("/", t.expression_1, t.expression_2, mulTheory.eDiv _)
    case t : ExprMod =>
      translateNumBinTerConnective("%", t.expression_1, t.expression_2, mulTheory.eMod _)
    case t : ExprUnPlus =>
      translateUnTerConnective("+", t.expression_, (lc) => lc)
    case t : ExprUnMinus =>
      translateUnTerConnective("-", t.expression_, - _)
    case t : ExprExp =>
      translateNumBinTerConnective("^", t.expression_1, t.expression_2, mulTheory.pow _)
    case t : ExprLit =>
      (IIntLit(IdealInt(t.intlit_)), Sort.Integer)
    case t : ExprEpsilon => {
      collectSingleVarDecl(t.declsinglevarc_)
      val cond = asFormula(translateExpression(t.expression_))
      val sort = env.popVar
      (sort eps cond, sort)
    }
    case t : ExprAbs =>
      translateUnTerConnective("\\abs", t.expression_, abs _)
    case t : ExprMax => {
      val args = translateNumOptArgs("\\max", t.optargs_)
      if (args.isEmpty)
        throw new Parser2InputAbsy.TranslationException(
            "Function max needs to receive at least one argument")
      (max(args), Sort.Integer)
    }
    case t : ExprMin => {
      val args = translateNumOptArgs("\\min", t.optargs_)
      if (args.isEmpty)
        throw new Parser2InputAbsy.TranslationException(
            "Function min needs to receive at least one argument")
      (min(args), Sort.Integer)
    }
    ////////////////////////////////////////////////////////////////////////////
    // If-then-else (can be formula or term)
    case t : ExprIfThenElse => {
      val cond = asFormula(translateExpression(t.expression_1))
      (translateExpression(t.expression_2),
       translateExpression(t.expression_3)) match {
        case ((left : ITerm, sortL), (right : ITerm, sortR)) => {
          val resSort = unifySorts(sortL, sortR) match {
            case Some(s) =>
              s
            case None =>
              throw new Parser2InputAbsy.TranslationException(
                "\\if ... \\then ... \\else cannot be applied with branches " +
                sortL + ", " + sortR)
          }
          (ITermITE(cond, left, right), resSort)
        }
        case (left, right) =>
          (IFormulaITE(cond, asFormula(left), asFormula(right)), Sort.Bool)
      }
    }
  }
  
  private object ApConnective extends ASTConnective {
    def unapplySeq(f : Expression) : Option[Seq[Expression]] = f match {
      case f : ExprAnd => Some(List(f.expression_1, f.expression_2))
      case f : ExprOr => Some(List(f.expression_1, f.expression_2))
    }
  }
  
  private def asFormula(expr : (IExpression, Sort)) : IFormula = expr match {
    case (expr : IFormula, _) =>
      expr
    case (t : ITerm, Sort.Bool) =>
      eqZero(t)
    case (expr, sort) => 
      throw new Parser2InputAbsy.TranslationException(
                   "Expected a formula, not " + expr + " of sort " + sort)
  }
  
  private def asTerm(expr : (IExpression, Sort)) : ITerm = expr match {
    case (expr : ITerm, _) =>
      expr
    case (IBoolLit(true), _) =>
      i(0)
    case (IBoolLit(false), _) =>
      i(1)
    case (f : IFormula, _) =>
      ite(f, i(0), i(1))
    case _ => 
      throw new Parser2InputAbsy.TranslationException(
                   "Expected a term, not " + expr)
  }

  private def asNumTerm(opName : String,
                        expr : (IExpression, Sort)) : ITerm = expr match {
    case (expr : ITerm, Sort.Numeric(_)) =>
      expr
    case (_, s) => 
      throw new Parser2InputAbsy.TranslationException(
              opName + " expects a numeric term, not sort " + s)
  }
  //////////////////////////////////////////////////////////////////////////////

  private def translateUnForConnective(f : Expression,
                                       con : (IFormula) => IFormula)
              : (IExpression, Sort) =
    (con(asFormula(translateExpression(f))), Sort.Bool)
  
  private def translateUnTerConnective(opName : String,
                                       f : Expression,
                                       con : (ITerm) => IExpression)
              : (IExpression, Sort) =
    (con(asNumTerm(opName, translateExpression(f))), Sort.Integer)

  private def translateBinForConnective(f1 : Expression, f2 : Expression,
                                        con : (IFormula, IFormula) => IFormula)
              : (IExpression, Sort) =
    (con(asFormula(translateExpression(f1)),
         asFormula(translateExpression(f2))),
     Sort.Bool)
  
  private def translateNumBinTerConnective(opName : String,
                                           f1 : Expression, f2 : Expression,
                                           con : (ITerm, ITerm) => IExpression)
                                          : (IExpression, Sort) =
    translateBinTerConnective(opName, f1, f2, con,
      (s1, s2) => (s1, s2) match {
                    case (Sort.Numeric(_), Sort.Numeric(_)) =>
                      Some(Sort.Integer)
                    case _ =>
                      None
                  })

  private def translateCompBinTerConnective(opName : String,
                                            f1 : Expression, f2 : Expression,
                                            con : (ITerm, ITerm) => IExpression)
                                           : (IExpression, Sort) =
    translateBinTerConnective(opName, f1, f2, con, comparableSorts _)

  private def comparableSorts(s1 : Sort, s2 : Sort) : Option[Sort] =
    for (s <- unifySorts(s1, s2)) yield Sort.Bool

  private def unifySorts(s1 : Sort, s2 : Sort) : Option[Sort] =
    (s1, s2) match {
      case (Sort.Numeric(_), Sort.Numeric(_)) =>
        Some(Sort.Integer)
      case (s1, s2) if s1 == s2 =>
        Some(s1)
      case _ =>
        None
    }

  private def unifySorts(args : Seq[(IExpression, Sort)],
                         sorts : Seq[Sort]) : Boolean =
    (args.iterator zip sorts.iterator) forall {
      case ((_, s), fs) => unifySorts(s, fs).isDefined
    }

  private def translateBinTerConnective(opName : String,
                                        f1 : Expression, f2 : Expression,
                                        con : (ITerm, ITerm) => IExpression,
                                        coercer : (Sort, Sort) => Option[Sort])
                                       : (IExpression, Sort) = {
    val left  = translateExpression(f1)
    val right = translateExpression(f2)
    val resSort = coercer(left._2, right._2) match {
      case Some(s) =>
        s
      case None =>
      println(left)
      println(right)
        throw new Parser2InputAbsy.TranslationException(
            "Operator " + opName + " cannot be applied to arguments of sort " +
            left._2 + ", " + right._2)
    }
    (con(asTerm(left), asTerm(right)), resSort)
  }
  
  private def translateQuant(f : ExprQuant) : IFormula = {
    // add the bound variables to the environment and record their number
    var quantNum : Int = 0
    collectDeclBinder(f.declbinder_,
                      (id, sort) => { quantNum = quantNum + 1; env.pushVar(id, sort) })

    def body(matrix : IFormula) = {
      val sorts = for (_ <- 0 until quantNum) yield env.popVar
      f.quant_ match {
        case _ : QuantAll => all(sorts, matrix)
        case _ : QuantEx  => ex(sorts, matrix)
      }
    }
    
    asFormula(translateUnForConnective(f.expression_, body _))
  }

  //////////////////////////////////////////////////////////////////////////////
  
  // TODO: check argument sorts
  private def translateFunctionApp(name : String,
                                   args : Seq[(IExpression, Sort)])
                                  : (IExpression, Sort) =
    env.lookupSym(name) match {
      case Environment.Predicate(pred, _, _) => {
        if (pred.arity != args.size)
          throw new Parser2InputAbsy.TranslationException(
              "Predicate " + pred +
              " is applied to a wrong number of arguments: " +
              (args mkString ", "))

        val argTerms = args map (asTerm _)
        pred match {
          case pred : SortedPredicate => {
            val formalSorts = pred iArgumentTypes argTerms
            if (!unifySorts(args, formalSorts))
              throw new Parser2InputAbsy.TranslationException(
                "Predicate " + pred.name +
                " cannot be applied to arguments of sort " +
                (args map (_._2) mkString ", "))
          }
          case _ => // nothing
        }

        ((predicateDefs get pred) match {
           case Some(body) =>
             VariableSubstVisitor(body, (argTerms.toList, 0))
           case None => 
             IAtom(pred, argTerms)
         },
         Sort.Bool)
      }
      
      case Environment.Function(fun, _) => {
        if (fun.arity != args.size)
          throw new Parser2InputAbsy.TranslationException(
              "Function " + fun +
              " is applied to a wrong number of arguments: " +
              (args mkString ", "))

        val argTerms = args map (asTerm _)
        val resSort = fun match {
          case fun : SortedIFunction => {
            val (formalSorts, resSort) = fun iFunctionType argTerms
            if (!unifySorts(args, formalSorts))
              throw new Parser2InputAbsy.TranslationException(
                "Function " + fun.name +
                " cannot be applied to arguments of sort " +
                (args map (_._2) mkString ", "))
            resSort
          }
          case _ =>
            Sort.Integer
        }

        ((functionDefs get fun) match {
           case Some(body) =>
             VariableSubstVisitor(body, (argTerms.toList, 0))
           case None => 
             IFunApp(fun, argTerms)
         },
         resSort)
      }
      
      case Environment.Constant(c, _, _) => {
        if (!args.isEmpty)
            throw new Parser2InputAbsy.TranslationException(
                               "Constant " + c + " does not have arguments")
        (c, getSort(c))
      }
      
      case Environment.Variable(i, sort) => {
        if (!args.isEmpty)
            throw new Parser2InputAbsy.TranslationException(
                               "Variable " + name + " does not have arguments")
        (v(i), sort)
      }
    }

  private def getSort(c : ConstantTerm) : Sort = c match {
    case c : SortedConstantTerm => c.sort
    case _ => Sort.Integer
  }

  private def translateTrigger(trigger : ExprTrigger) : IFormula = {
    val patterns = translateExprArgs(trigger.listargc_)
    val body = asFormula(translateExpression(trigger.expression_))
    ITrigger(ITrigger.extractTerms(patterns), body)
  }
  
  private def translateOptArgs(args : OptArgs)
                              : Seq[(IExpression, Sort)] = args match {
    case args : Args => translateArgs(args.listargc_)
    case _ : NoArgs => List()
  }
  
  private def translateArgs(args : ListArgC) =
    for (arg <- args) yield arg match {
      case arg : Arg => translateExpression(arg.expression_)
    }

  private def translateNumOptArgs(opName : String,
                                  args : OptArgs) : Seq[ITerm] = args match {
    case args : Args => translateNumArgs(opName, args.listargc_)
    case _ : NoArgs => List()
  }
  
  private def translateNumArgs(opName : String, args : ListArgC) =
    for (arg <- args) yield arg match {
      case arg : Arg => asNumTerm(opName, translateExpression(arg.expression_))
    }

  private def translateExprArgs(args : ListArgC) =
    for (arg <- args) yield arg match {
      case arg : Arg => translateExpression(arg.expression_)._1
    }

}

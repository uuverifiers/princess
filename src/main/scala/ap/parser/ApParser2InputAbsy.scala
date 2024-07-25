/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011-2021 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.basetypes.IdealInt
import ap.parser.ApInput._
import ap.parser.ApInput.Absyn._
import ap.theories.{ADT, ModuloArithmetic}
import IExpression.Sort
import ap.types.{MonoSortedIFunction, SortedIFunction,
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
    val p = new parser(l) {
      override def report_error(message : String, info : Object) : Unit = {
        Console.err.println(message)
      }
    }
    
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
  import scala.collection.JavaConverters.asScala

  implicit def impToScalaList[A](l : java.util.List[A]) : Seq[A] =
    asScala(l).toSeq

  implicit def impToScalaIterator[A](l : java.util.Iterator[A]) : Iterator[A] =
    asScala(l)

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
      (for (block <- api.listblock_;
            if block.isInstanceOf[Interpolant];
            inter = block.asInstanceOf[Interpolant];
            intBlocks = inter.listinterpblockc_;
            n <- 1 until intBlocks.size) yield {
         val left = intBlocks take n
         val right = intBlocks drop n
         IInterpolantSpec(
           (for (ids <- left; id <- ids.asInstanceOf[InterpBlock].listident_)
              yield (env lookupPartName id)).toList,
           (for (ids <- right; id <- ids.asInstanceOf[InterpBlock].listident_)
              yield (env lookupPartName id)).toList)
       }).toList
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def collectSortDeclarations(api : API) : Unit = api match {
    case api : BlockList => {

      // declare uninterpreted sorts
      for (block <- api.listblock_.iterator) block match {
        case block : SortDecls =>
          for (decl <- block.listdeclsortc_.iterator) decl match {
            case decl : DeclUnintSort => {
              val name = decl.ident_
              val sort = Sort.createUninterpretedSort(name)
              addTheory(sort.theory)
              env.addSort(name, sort)
            }
            case decl : DeclInfUnintSort => {
              val name = decl.ident_
              env.addSort(name, Sort.createInfUninterpretedSort(name))
            }
            case _ => // nothing
          }
        case _ => // nothing
      }

      // determine all declared ADTs
      val adtNames = new ArrayBuffer[String]

      for (block <- api.listblock_.iterator) block match {
        case block : SortDecls =>
          for (decl <- block.listdeclsortc_.iterator) decl match {
            case decl : DeclADT =>
              adtNames += decl.ident_
            case _ => // nothing
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
            case _ => // nothing
          }
        case _ => // nothing
      }

      val adt = new ADT(adtNames.toVector, ctors.toVector,
                        Param.ADT_MEASURE(settings))

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
        val query = MonoSortedPredicate("is_" + name, List(adt sorts adtNum))
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
              (id, sort) => env.addConstant(toMVBool(sort) newConstant id,
                                            Environment.NullaryFunction,
                                            ()))
        case block : ExConstants =>
          for (decl <- block.listdeclconstantc_.iterator)
            collectDeclConstantC(decl,
              (id, sort) => env.addConstant(toMVBool(sort) newConstant id,
                                            Environment.Existential,
                                            ()))
        case block : UniConstants =>
          for (decl <- block.listdeclconstantc_.iterator)
            collectDeclConstantC(decl,
              (id, sort) => env.addConstant(toMVBool(sort) newConstant id,
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

              val wrappedOpts = decl.listpredoption_
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

              val pred = MonoSortedPredicate(name, argSorts)

              env.addPredicate(pred,
                               (),
                               if (negMatch)
                                 Signature.PredicateMatchStatus.Negative
                               else if (noMatch)
                                 Signature.PredicateMatchStatus.None
                               else
                                 Signature.PredicateMatchStatus.Positive)
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

        val wrappedOpts = decl.listfunoption_
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

        val fun = MonoSortedIFunction(decl.ident_, argSorts, toMVBool(resSort),
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
      val (lb, ub) = translateBounds(t.intervallower_, t.intervalupper_)
      Sort.Interval(lb, ub)
    }
    case t : TypeMod => {
      val (lb, ub) = translateBounds(t.intervallower_, t.intervalupper_)
      if (lb.isEmpty || ub.isEmpty)
        throw new Parser2InputAbsy.TranslationException(
          "Modulo sorts have to be finite")
      ModuloArithmetic.ModSort(lb.get, ub.get)
    }
    case t : TypeBV =>
      ModuloArithmetic.UnsignedBVSort(translateIntLit2Int(t.intlit_))
    case t : TypeSignedBV =>
      ModuloArithmetic.SignedBVSort(translateIntLit2Int(t.intlit_))
    case t : TypeIdent =>
      env lookupSort t.ident_
  }

  private def translateBounds(lower : IntervalLower,
                              upper : IntervalUpper)
                           : (Option[IdealInt], Option[IdealInt]) = {
    val lb = bound2IdealInt(lower)
    val ub = bound2IdealInt(upper)
    for (l <- lb; u <- ub)
      if (l > u)
        throw new Parser2InputAbsy.TranslationException(
          "Interval types have to be non-empty")
    (lb, ub)
  }

  private def bound2IdealInt(b : IntervalLower) : Option[IdealInt] = b match {
    case _ : InfLower =>      None
    case iv : NumLower =>     Some(translateIntLit(iv.intlit_))
    case iv : NegNumLower =>  Some(-translateIntLit(iv.intlit_))
  }

  private def bound2IdealInt(b : IntervalUpper) : Option[IdealInt] = b match {
    case _ : InfUpper =>      None
    case iv : NumUpper =>     Some(translateIntLit(iv.intlit_))
    case iv : NegNumUpper =>  Some(-translateIntLit(iv.intlit_))
  }

  private def toMVBool(s : Sort) : Sort = s match {
    case Sort.Bool => Sort.MultipleValueBool
    case s => s
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
    case f : ExprOr =>
      translateBoolBinConnectiveOp("|", f, _.isInstanceOf[ExprOr], _ | _,
                                   ModuloArithmetic.bv_or)
    case f : ExprOrOr =>
      translateBoolBinConnective("||", f, _.isInstanceOf[ExprOrOr],_ | _,
                                 (bits : Int, t1 : ITerm, t2 : ITerm) =>
                                 throw new TranslationException(
                                   "|| can only be applied to formulas"))
    case f : ExprAnd =>
      translateBoolBinConnectiveOp("&", f, _.isInstanceOf[ExprAnd],_ & _,
                                   ModuloArithmetic.bv_and)
    case f : ExprAndAnd =>
      translateBoolBinConnective("&&", f, _.isInstanceOf[ExprAndAnd], _ & _,
                                 (bits : Int, t1 : ITerm, t2 : ITerm) =>
                                 throw new TranslationException(
                                   "&& can only be applied to formulas"))
    case f : ExprNot =>
      translateUnForConnective(f.expression_, ! _)
    case f : ExprTilde => translateExpression(f.expression_) match {
      case p@(_, s@ModuloArithmetic.UnsignedBVSort(bits)) =>
        (IFunApp(ModuloArithmetic.bv_not, List(bits, asTerm(p))), s)
      case (t, s) =>
        throw new TranslationException(
          "~ can only be applied to bit-vectors, not to " + t)
    }
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
        translateNumCompBinTerConnective("<=", f.expression_1, f.expression_2,
                                         _ <= _)
      case _ : RelGeq =>
        translateNumCompBinTerConnective(">=", f.expression_1, f.expression_2,
                                         _ >= _)
      case _ : RelLt =>
        translateNumCompBinTerConnective("<", f.expression_1, f.expression_2,
                                         _ < _)
      case _ : RelGt =>
        translateNumCompBinTerConnective(">", f.expression_1, f.expression_2,
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
    case t : ExprShiftL =>
      (translateExpression(t.expression_1),
       translateExpression(t.expression_2)) match {
        case ((left : ITerm, Sort.Numeric(_)), (IIntLit(bits), Sort.Numeric(_)))
          if bits.signum >= 0 =>
            (left * (IdealInt(2) pow bits.intValueSafe), Sort.Integer)
        case ((left : ITerm,
                 sort@ModuloArithmetic.ModSort(lower, upper)),
              (right : ITerm,
                 Sort.Numeric(_) | _ : ModuloArithmetic.ModSort)) =>
            (ModuloArithmetic.shiftLeft(sort, left, right), sort)
        case ((left, _), (right, _)) =>
          throw new Parser2InputAbsy.TranslationException(
            "Cannot shift " + left + " to the left by " + right + " bits")
      }
    case t : ExprShiftR =>
      (translateExpression(t.expression_1),
       translateExpression(t.expression_2)) match {
        case ((left : ITerm, Sort.Numeric(_)), (IIntLit(bits), Sort.Numeric(_)))
          if bits.signum >= 0 =>
            (mulTheory.eDiv(left, (IdealInt(2) pow bits.intValueSafe)),
             Sort.Integer)
        case ((left : ITerm,
                 sort@ModuloArithmetic.ModSort(lower, upper)),
              (right : ITerm,
                 Sort.Numeric(_) | _ : ModuloArithmetic.ModSort)) =>
            (ModuloArithmetic.shiftRight(sort, left, right), sort)
        case ((left, _), (right, _)) =>
          throw new Parser2InputAbsy.TranslationException(
            "Cannot shift " + left + " to the right by " + right + " bits")
      }
    case t : ExprPlus =>
      translateNumBinTerConnective("+", t.expression_1, t.expression_2, _ + _)
    case t : ExprMinus =>
      translateNumBinTerConnective("-", t.expression_1, t.expression_2, _ - _)
    case t : ExprMult =>
      translateNumBinTerConnective("*", t.expression_1, t.expression_2, mult _)
    case t : ExprDiv =>
      translateNumBinTerConnective("/", t.expression_1, t.expression_2,
                                   mulTheory.eDiv _)
    case t : ExprMod =>
      translateNumBinTerConnective("%", t.expression_1, t.expression_2,
                                   mulTheory.eMod _)
    case t : ExprUnPlus =>
      translateNumUnTerConnective("+", t.expression_, (lc) => lc)
    case t : ExprUnMinus =>
      translateNumUnTerConnective("-", t.expression_, - _)
    case t : ExprConcat =>
      (translateExpression(t.expression_1),
       translateExpression(t.expression_2)) match {
        case ((left : ITerm,
                 ModuloArithmetic.UnsignedBVSort(leftBits)),
              (right : ITerm,
                 ModuloArithmetic.UnsignedBVSort(rightBits))) =>
            (ModuloArithmetic.bv_concat(leftBits, rightBits, left, right),
             ModuloArithmetic.UnsignedBVSort(leftBits + rightBits))
        case _ =>
          throw new Parser2InputAbsy.TranslationException(
            "Concatenation ++ can only be applied to unsigned bit-vector " +
            "expressions")
      }
    case t : ExprExp =>
      wrapResult(translateBinTerConnective("^", t.expression_1, t.expression_2,
                                           mulTheory.pow _, powSortCoercion _))
    case t : ExprLit =>
      (IIntLit(translateIntLit(t.intlit_)), Sort.Integer)
    case t : ExprEpsilon => {
      collectSingleVarDecl(t.declsinglevarc_)
      val cond = asFormula(translateExpression(t.expression_))
      val sort = env.popVar
      (sort eps cond, sort)
    }
    case t : ExprAbs =>
      translateNumUnTerConnective("\\abs", t.expression_, abs _)
    case t : ExprDotAbs =>
      translateNumUnTerConnective("\\abs", t.expression_, abs _)
    case t : ExprMax => {
      val (args, sort) = translateNumOptArgs("\\max", t.optargs_)
      if (args.isEmpty)
        throw new Parser2InputAbsy.TranslationException(
            "Function \\max needs to receive at least one argument")
      (max(args), sort)
    }
    case t : ExprMin => {
      val (args, sort) = translateNumOptArgs("\\min", t.optargs_)
      if (args.isEmpty)
        throw new Parser2InputAbsy.TranslationException(
            "Function \\min needs to receive at least one argument")
      (min(args), sort)
    }
    case t : ExprCast =>
      translateCast(t.expression_, t.type_)
    case t : ExprDotCast =>
      translateCast(t.expression_, t.type_)
    case t : ExprSize =>
      translateSize(t.expression_)
    case t : ExprDotSize =>
      translateSize(t.expression_)
    case t : ExprBracket =>
      (translateExpression(t.expression_1),
       translateExpression(t.expression_2)) match {
        case ((left : ITerm, _ : ModuloArithmetic.ModSort | Sort.Numeric(_)),
              (IIntLit(IdealInt(bit)), _)) if bit >= 0 =>
            (1 - ModuloArithmetic.extract(bit, bit, left),
             Sort.MultipleValueBool)
        case ((left, _), (right, _)) =>
          throw new Parser2InputAbsy.TranslationException(
            "Cannot extract bit " + right + " of " + left)
      }
    case t : ExprBitRange =>
      translateExpression(t.expression_) match {
        case (left : ITerm, _ : ModuloArithmetic.ModSort | Sort.Numeric(_)) => {
          val begin = translateIntLit2Int(t.intlit_1)
          val end   = translateIntLit2Int(t.intlit_2)
          if (!(begin >= end && end >= 0))
            throw new Parser2InputAbsy.TranslationException(
              "Cannot extracts bits " + begin + ":" + end + " of " + left)
          (ModuloArithmetic.extract(begin, end, left),
           ModuloArithmetic.UnsignedBVSort(begin - end + 1))
        }
        case (left, _) =>
          throw new Parser2InputAbsy.TranslationException(
            "Cannot extracts any bits from " + left)
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
      case f : ExprAndAnd => Some(List(f.expression_1, f.expression_2))
      case f : ExprOrOr => Some(List(f.expression_1, f.expression_2))
    }
  }
  
  private def asFormula(expr : (IExpression, Sort)) : IFormula = expr match {
    case (expr : IFormula, _) =>
      expr
    case (IIntLit(IdealInt.ZERO), Sort.Bool | Sort.MultipleValueBool) =>
      i(true)
    case (IIntLit(_), Sort.Bool | Sort.MultipleValueBool) =>
      i(false)
    case (t : ITerm, Sort.Bool | Sort.MultipleValueBool) =>
      eqZero(t)
    case (expr, sort) => 
      throw new Parser2InputAbsy.TranslationException(
                   "Expected a formula, not " + expr + " of sort " + sort)
  }
  
  private def asTerm(expr : (IExpression, Sort)) : ITerm = expr match {
    case (expr : ITerm, Sort.MultipleValueBool) =>
      ite(eqZero(expr), i(0), i(1))
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

  private def assertNumSort(opName : String, sort : Sort) : Unit = sort match {
    case Sort.Numeric(_) =>
      // ok
    case ModuloArithmetic.ModSort(_, _) =>
      // ok
    case sort =>
      throw new Parser2InputAbsy.TranslationException(
              opName + " expects a numeric term, not sort " + sort)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def translateCast(t : Expression, ty : Type) : (IExpression, Sort) = {
      val p@(arg, oldSort) = translateExpression(t)
      type2Sort(ty) match {
        case `oldSort` =>
          (arg, oldSort)
        case Sort.Integer =>
          (arg, Sort.Integer)
        case sort : ModuloArithmetic.ModSort =>
          (ModuloArithmetic.cast2Sort(sort, asTerm(p)), sort)
        case sort =>
          throw new Parser2InputAbsy.TranslationException(
            "Cannot cast to sort " + sort)
      }
  }

  private def translateSize(t : Expression) : (IExpression, Sort) = {
      val (arg, sort) = translateExpression(t)
      sort match {
        case sort : ADT.ADTProxySort => {
          if (sort.adtTheory.termSize == null)
            throw new Parser2InputAbsy.TranslationException(
                "Function \\size can only be used in combination with option " +
                "-adtMeasure=size")
          (IFunApp(sort.adtTheory.termSize(sort.sortNum),
                   List(arg.asInstanceOf[ITerm])),
           Sort.Integer)
        }
        case sort =>
          throw new Parser2InputAbsy.TranslationException(
              "Function \\size needs to receive an ADT term as argument")
      }
  }

  private def translateUnForConnective(f : Expression,
                                       con : (IFormula) => IFormula)
              : (IExpression, Sort) =
    (con(asFormula(translateExpression(f))), Sort.Bool)
  
  private def translateNumUnTerConnective(opName : String,
                                          f : Expression,
                                          con : (ITerm) => IExpression)
                                       : (IExpression, Sort) = {
    val (expr, sort) = translateExpression(f)
    val resSort = sort match {
      case Sort.Numeric(_) => Sort.Integer
      case sort : ModuloArithmetic.ModSort => sort
      case sort =>
        throw new Parser2InputAbsy.TranslationException(
                opName + " expects a numeric term, not sort " + sort)
    }
    wrapResult((con(asTerm((expr, sort))), resSort))
  }

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
    wrapResult(translateBinTerConnective(opName, f1, f2, con,
                                         numSortCoercion _))

  private def translateNumCompBinTerConnective(
                                           opName : String,
                                           f1 : Expression, f2 : Expression,
                                           con : (ITerm, ITerm) => IExpression)
                                          : (IExpression, Sort) = {
    (translateBinTerConnective(opName, f1, f2, con, numSortCoercion _)._1,
     Sort.Bool)
  }

  private def wrapResult(res : (IExpression, Sort)) : (IExpression, Sort) =
    res._2 match {
      case s : ModuloArithmetic.ModSort =>
        (ModuloArithmetic.cast2Sort(s, res._1.asInstanceOf[ITerm]), s)
      case _ =>
        res
    }

  private def numSortCoercion(s1 : Sort, s2 : Sort) : Option[Sort] =
    (s1, s2) match {
      case (Sort.Numeric(_), Sort.Numeric(_)) =>
        Some(Sort.Integer)
      case (s1 : ModuloArithmetic.ModSort,
            s2 : ModuloArithmetic.ModSort) if (s1 == s2) =>
        Some(s1)
      case (s : ModuloArithmetic.ModSort, Sort.Numeric(_)) =>
        Some(s)
      case (Sort.Numeric(_), s : ModuloArithmetic.ModSort) =>
        Some(s)
      case _ =>
        None
    }

  private def powSortCoercion(s1 : Sort, s2 : Sort) : Option[Sort] =
    (s1, s2) match {
      case (Sort.Numeric(_), Sort.Integer) =>
        Some(Sort.Integer)
      case (s : ModuloArithmetic.ModSort, Sort.Integer) =>
        Some(s)
      case _ =>
        None
    }

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
      case (Sort.Numeric(_), _ : ModuloArithmetic.ModSort) =>
        Some(Sort.Integer)
      case (_ : ModuloArithmetic.ModSort, Sort.Numeric(_)) =>
        Some(Sort.Integer)
      case (Sort.Bool, Sort.MultipleValueBool) |
           (Sort.MultipleValueBool, Sort.Bool) =>
        Some(Sort.MultipleValueBool)
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
        throw new Parser2InputAbsy.TranslationException(
            "Operator " + opName + " cannot be applied to arguments of sort " +
            left._2 + ", " + right._2)
    }
    (con(asTerm(left), asTerm(right)), resSort)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def translateBoolBinConnectiveOp(
                 opName : String,
                 f : Expression,
                 cont : GrammarExpression => Boolean,
                 forCon : (IFormula, IFormula) => IFormula,
                 bvOp : IFunction) : (IExpression, Sort) =
    translateBoolBinConnective(opName, f, cont, forCon,
                               (bits : Int, t1 : ITerm, t2 : ITerm) =>
                                  IFunApp(bvOp, List(bits, t1, t2)))

  private def translateBoolBinConnective(
                 opName : String,
                 f : Expression,
                 cont : GrammarExpression => Boolean,
                 forCon : (IFormula, IFormula) => IFormula,
                 bvCon : (Int, ITerm, ITerm) => ITerm) : (IExpression, Sort) = {
    val subs = collectSubExpressions(f, cont, ApConnective)
    val transSubst = subs map (translateExpression _)

    transSubst.head._2 match {
      case Sort.Bool | Sort.MultipleValueBool =>
        ((for (p <- transSubst.iterator) yield asFormula(p)) reduceLeft forCon,
         Sort.Bool)
      case s@ModuloArithmetic.UnsignedBVSort(bits) => {
        if (transSubst exists (_._2 != s))
          throw new TranslationException(
            opName + " can only be applied to operands with consistent sorts")
        ((for (p <- transSubst.iterator) yield asTerm(p)) reduceLeft {
           (t1, t2) => bvCon(bits, t1, t2)
         }, s)
      }
      case s =>
        throw new TranslationException(
          opName + " cannot be applied to operands of sort " + s)
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private def translateQuant(f : ExprQuant) : IFormula = {
    // add the bound variables to the environment and record their number
    var quantNum : Int = 0
    collectDeclBinder(f.declbinder_,
                      (id, sort) => {
                        quantNum = quantNum + 1
                        env.pushVar(id, toMVBool(sort))
                      })

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
            val formalSorts = pred iArgumentSorts argTerms
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
        (c, SortedConstantTerm sortOf c)
      }
      
      case Environment.Variable(i, sort) => {
        if (!args.isEmpty)
            throw new Parser2InputAbsy.TranslationException(
                               "Variable " + name + " does not have arguments")
        (v(i, sort), sort)
      }

      case Environment.OverloadedSym(_) =>
        throw new Parser2InputAbsy.TranslationException(
          "Did not expect overloaded symbol " + name)
    }

  private def translateTrigger(trigger : ExprTrigger) : IFormula = {
    val patterns = translateExprArgs(trigger.listargc_) map (_._1)
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

  private def translateNumOptArgs(opName : String, args : OptArgs)
                                 : (Seq[ITerm], Sort) = args match {
    case args : Args => {
      val transArgs = translateExprArgs(args.listargc_)
      val sort = transArgs.head._2
      assertNumSort(opName, sort)
      if (transArgs exists { case (_, s) => s != sort })
        throw new Parser2InputAbsy.TranslationException(
               opName + " has to be applied to terms of the same numeric sort")
      (transArgs map (_._1.asInstanceOf[ITerm]), sort)
    }
    case _ : NoArgs =>
      (List(), Sort.Integer)
  }
  
  private def translateExprArgs(args : ListArgC) =
    (for (arg <- args.iterator) yield arg match {
       case arg : Arg => translateExpression(arg.expression_)
     }).toSeq

  private def translateIntLit(l : IntLit) : IdealInt = l match {
    case l : DIntLit => IdealInt(l.decintlit_)
    case l : HIntLit => IdealInt(l.hexintlit_ substring 2, 16)
  }

  private def translateIntLit2Int(l : IntLit) : Int =
    translateIntLit(l).intValueSafe

}

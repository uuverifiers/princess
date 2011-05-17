/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser;

import ap._
import ap.terfor.{ConstantTerm, OneTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.preds.{Predicate, Atom}
import ap.util.{Debug, Logic, PlainRange}
import ap.basetypes.IdealInt
import ApInput._
import ApInput.Absyn._

import scala.collection.mutable.{Stack, ArrayBuffer}

object ApParser2InputAbsy {

  private val AC = Debug.AC_PARSER
  
  import Parser2InputAbsy._
  
  def parseExpression(input : java.io.Reader, env : Environment) : IExpression = {
    def entry(parser : ApInput.parser) = {
      val parseTree = parser.pEntry
      parseTree match {
        case parseTree : ExprEntry => parseTree.expression_
        case _ => throw new ParseException("Input is not an expression")
      }
    }
    val expr = parseWithEntry(input, env, entry _)
    val t = new ApParser2InputAbsy (env)
    t translateExpression expr
  }
  
  /**
   * Parse starting at an arbitrarily specified entry point
   */
  private def parseWithEntry[T](input : java.io.Reader,
                                env : Environment,
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

class ApParser2InputAbsy (_env : Environment) extends Parser2InputAbsy(_env) {
  
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
    collectDeclarations(api)
    val formula = translateProblem(api)
    val interSpecs = translateInterpolantSpecs(api)
    (formula, interSpecs, env.toSignature)
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

  protected def collectDeclarations(api : API) : Unit = api match {
    case api : BlockList =>
      for (block <- api.listblock_.iterator) block match {
        case block : FunctionDecls =>
          for (decl <- block.listdeclfunc_.iterator)
            collectDeclFunC(decl,
                            (id) => env.addConstant(new ConstantTerm(id),
                                                    Environment.NullaryFunction))
        case block : ExConstants =>
          for (decl <- block.listdeclconstantc_.iterator)
            collectDeclConstantC(decl,
                                 (id) => env.addConstant(new ConstantTerm(id),
                                                         Environment.Existential))
        case block : UniConstants =>
          for (decl <- block.listdeclconstantc_.iterator)
            collectDeclConstantC(decl,
                                 (id) => env.addConstant(new ConstantTerm(id),
                                                         Environment.Universal))
        case block : PredDecls =>
          for (decl <- block.listdeclpredc_.iterator) decl match {
            case decl : DeclPred => {
              val name = decl.ident_
              val arity = decl.optformalargs_ match {
                case _ : NoFormalArgs => 0
                case args : WithFormalArgs => determineArity(args.formalargsc_)
              }
              env.addPredicate(new Predicate(name, arity))
            }
          }
        case _ : Problem => /* nothing */
        case _ : Interpolant => /* nothing */
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def collectDeclFunC(decl : DeclFunC, addCmd : String => Unit) : Unit =
    decl match {
      case decl : DeclFun => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(ApParser2InputAbsy.AC, decl.type_.isInstanceOf[TypeInt])
        //-END-ASSERTION-///////////////////////////////////////////////////////
        val wrappedOpts = asScalaBuffer(decl.listfunoption_)
        val (partialOpts, otherOpts1) = wrappedOpts partition (_.isInstanceOf[Partial])
        val (relationalOpts, otherOpts2) = otherOpts1 partition (_.isInstanceOf[Relational])
        
        val partial = !partialOpts.isEmpty
        val relational = !relationalOpts.isEmpty
        
        if (!otherOpts2.isEmpty) {
          val strs = for (o <- otherOpts2) yield funOption2String(o)
          throw new Parser2InputAbsy.TranslationException(
                       "Illegal options for function: " + (strs mkString " "))
        }
        env.addFunction(new IFunction (decl.ident_,
                                       determineArity(decl.formalargsc_),
                                       partial, relational))
      }
      case decl : DeclFunConstant => {
        if (!decl.listfunoption_.isEmpty)
          throw new Parser2InputAbsy.TranslationException(
                                        "Constants do not have options")
        collectDeclarations(decl.declvarconstc_, addCmd)
      }
    }

  //////////////////////////////////////////////////////////////////////////////

  private def determineArity(args : FormalArgsC) : Int = args match {
    case args : FormalArgs => {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(ApParser2InputAbsy.AC,
                      Logic.forall(for (at <- args.listargtypec_.iterator)
                                   yield (at.asInstanceOf[ArgType].type_.isInstanceOf[TypeInt])))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      args.listargtypec_.size
    }
  }
  
  private def funOption2String(option : FunOption) : String = option match {
    case _ : Partial => "\\partial"
    case _ : Relational => "\\relational"
  }
  
  private def collectDeclConstantC(decl : DeclConstantC,
                                   addCmd : String => Unit) : Unit =
    collectDeclarations(decl.asInstanceOf[DeclConstant].declvarconstc_, addCmd)

  private def collectDeclBinder(decl : DeclBinder,
                                addCmd : String => Unit) : Unit = decl match {
    case decl : DeclBinder1 => collectDeclarations(decl.declvarconstc_, addCmd)
    case decl : DeclBinderM => for (decl <- decl.listdeclvarconstc_.iterator) 
                                 collectDeclarations(decl, addCmd)
  }

  private def collectDeclarations(decl : DeclVarConstC,
                                  addCmd : String => Unit) : Unit = decl match {
    case decl : DeclVarConst => { 
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(ApParser2InputAbsy.AC, decl.type_.isInstanceOf[TypeInt])
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      for (id <- decl.listident_.iterator) addCmd(id)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def translateExpression(f : Expression) : IExpression = f match {
    ////////////////////////////////////////////////////////////////////////////
    // Formulae
    case f : ExprEqv =>
      translateBinForConnective(f.expression_1, f.expression_2, _ <=> _)
    case f : ExprImp =>
      translateBinForConnective(f.expression_1, f.expression_2, _ ==> _)
    case f : ExprOr => {
      val subs = collectSubExpressions(f, _.isInstanceOf[ExprOr], ApConnective)
      (for (f <- subs.iterator)
         yield asFormula(translateExpression(f))) reduceLeft (_ | _)
    }
    case f : ExprAnd => {
      val subs = collectSubExpressions(f, _.isInstanceOf[ExprAnd], ApConnective)
      (for (f <- subs.iterator)
         yield asFormula(translateExpression(f))) reduceLeft (_ & _)
    }
    case f : ExprNot =>
      translateUnForConnective(f.expression_, ! _)
    case f : ExprQuant =>
      translateQuant(f)
    case _ : ExprTrue => i(true)
    case _ : ExprFalse => i(false)
    case f : ExprIdApp => translateExprIdApp(f)
    case f : ExprRel =>
      translateBinTerConnective(f.expression_1, f.expression_2,
                                f.relsym_ match {
                                  case _ : RelEq => _ === _
                                  case _ : RelNEq => _ =/= _
                                  case _ : RelLeq => _ <= _
                                  case _ : RelGeq => _ >= _
                                  case _ : RelLt => _ < _
                                  case _ : RelGt => _ > _
                                })
    case f : ExprTrigger => translateTrigger(f)
    case f : ExprPart =>
      INamedPart(env lookupPartName f.ident_,
                 asFormula(translateExpression(f.expression_)))
    ////////////////////////////////////////////////////////////////////////////
    // Terms
    case t : ExprPlus =>
      translateBinTerConnective(t.expression_1, t.expression_2, _ + _)
    case t : ExprMinus =>
      translateBinTerConnective(t.expression_1, t.expression_2, _ - _)
    case t : ExprMult =>
      translateBinTerConnective(t.expression_1, t.expression_2, mult _)
    case t : ExprUnPlus =>
      translateUnTerConnective(t.expression_, (lc) => lc)
    case t : ExprUnMinus =>
      translateUnTerConnective(t.expression_, - _)
    case t : ExprLit =>
      IIntLit(IdealInt(t.intlit_))
  }
  
  private object ApConnective extends ASTConnective {
    def unapplySeq(f : Expression) : Option[Seq[Expression]] = f match {
      case f : ExprAnd => Some(List(f.expression_1, f.expression_2))
      case f : ExprOr => Some(List(f.expression_1, f.expression_2))
    }
  }
  
  private def asFormula(expr : IExpression) : IFormula = expr match {
    case expr : IFormula =>
      expr
    case _ => 
      throw new Parser2InputAbsy.TranslationException(
                   "Expected a formula, not " + expr)
  }
  
  private def asTerm(expr : IExpression) : ITerm = expr match {
    case expr : ITerm =>
      expr
    case _ => 
      throw new Parser2InputAbsy.TranslationException(
                   "Expected a term, not " + expr)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def translateUnForConnective(f : Expression,
                                       con : (IFormula) => IExpression)
              : IExpression =
    con(asFormula(translateExpression(f)))
  
  private def translateUnTerConnective(f : Expression,
                                       con : (ITerm) => IExpression)
              : IExpression =
    con(asTerm(translateExpression(f)))
  
  private def translateBinForConnective(f1 : Expression, f2 : Expression,
                                        con : (IFormula, IFormula) => IExpression)
              : IExpression =
    con(asFormula(translateExpression(f1)), asFormula(translateExpression(f2)))
  
  private def translateBinTerConnective(f1 : Expression, f2 : Expression,
                                        con : (ITerm, ITerm) => IExpression)
              : IExpression =
    con(asTerm(translateExpression(f1)), asTerm(translateExpression(f2)))
  
  private def translateQuant(f : ExprQuant) : IFormula = {
    val quant : Quantifier = f.quant_ match {
      case _ : QuantAll => Quantifier.ALL
      case _ : QuantEx => Quantifier.EX
    }
    
    // add the bound variables to the environment and record their number
    var quantNum : Int = 0
    collectDeclBinder(f.declbinder_,
                      (id) => { quantNum = quantNum + 1; env pushVar id })
    
    val res = translateUnForConnective(f.expression_,
                                       quan(Array.fill(quantNum){quant}, _))

    // pop the variables from the environment
    for (_ <- PlainRange(quantNum)) env.popVar
    
    res.asInstanceOf[IFormula]
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private def translateExprIdApp(f : ExprIdApp) : IExpression =
    env.lookupSym(f.ident_) match {
      case Environment.Predicate(pred) => {
        val args = translateOptArgs(f.optargs_)
        if (pred.arity != args.size)
          throw new Parser2InputAbsy.TranslationException(
              "Predicate " + pred +
              " is applied to a wrong number of arguments: " + (args mkString ", "))
        
        IAtom(pred, args)
      }
      
      case Environment.Function(fun, _) => {
        val args = translateOptArgs(f.optargs_)
        if (fun.arity != args.size)
          throw new Parser2InputAbsy.TranslationException(
              "Function " + fun +
              " is applied to a wrong number of arguments: " + (args mkString ", "))
        
        IFunApp(fun, args)
      }
      
      case Environment.Constant(c, _) => {
        f.optargs_ match {
          case _ : Args =>
            throw new Parser2InputAbsy.TranslationException(
                               "Constant " + c + " does not have arguments")
          case _ : NoArgs => // nothing
        }
        c
      }
      
      case Environment.Variable(i) => {
        f.optargs_ match {
          case _ : Args =>
            throw new Parser2InputAbsy.TranslationException(
                               "Variable " + f.ident_ + " does not have arguments")
          case _ : NoArgs => // nothing
        }
        v(i)
      }
    }
  
  private def translateTrigger(trigger : ExprTrigger) :IFormula = {
    val patterns = translateArgs(trigger.listargc_)
    val body = asFormula(translateExpression(trigger.expression_))
    ITrigger(patterns, body)
  }
  
  private def translateOptArgs(args : OptArgs) : Seq[ITerm] = args match {
    case args : Args => translateArgs(args.listargc_)
    case _ : NoArgs => List()
  }
  
  private def translateArgs(args : ListArgC) =
    for (arg <- args) yield arg match {
      case arg : Arg => asTerm(translateExpression(arg.expression_))
    }

}

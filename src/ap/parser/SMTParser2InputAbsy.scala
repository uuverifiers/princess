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
import ap.parameters.{ParserSettings, Param}
import ap.terfor.OneTerm
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.preds.Atom
import ap.proof.certificates.{Certificate, DagCertificateConverter,
                              CertificatePrettyPrinter, CertFormula}
import ap.theories.{SimpleArray, ADT, ModuloArithmetic}
import ap.types.{MonoSortedIFunction, MonoSortedPredicate}
import ap.basetypes.{IdealInt, IdealRat, Tree}
import ap.parser.smtlib._
import ap.parser.smtlib.Absyn._
import ap.util.{Debug, Logic, PlainRange}

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

object SMTParser2InputAbsy {

  private val AC = Debug.AC_PARSER
  
  import Parser2InputAbsy._
  import IExpression.{Sort => TSort}

  abstract class SMTType {
    def toSort : TSort
  }
  case object SMTBool                              extends SMTType {
    def toSort = TSort.Bool
  }
  case object SMTInteger                           extends SMTType {
    def toSort = TSort.Integer
  }
  case class  SMTArray(arguments : List[SMTType],
                       result : SMTType)           extends SMTType {
    def toSort = TSort.Integer // TODO
  }
  case class SMTBitVec(width : Int)                extends SMTType {
    def toSort = ModuloArithmetic.UnsignedBVSort(width)
    val modulus = IdealInt(2) pow width
  }
  case class SMTADT(adt : ADT, sortNum : Int)      extends SMTType {
    def toSort = adt sorts sortNum
    override def toString = (adt sorts sortNum).name
  }
  case class SMTUnint(sort : TSort)                extends SMTType {
    def toSort = sort
    override def toString = sort.name
  }  

  case class SMTFunctionType(arguments : List[SMTType],
                             result : SMTType)
  
  sealed abstract class VariableType
  case class BoundVariable(varType : SMTType)              extends VariableType
  case class SubstExpression(e : IExpression, t : SMTType) extends VariableType
  
  private type Env =
    Environment[SMTType, VariableType, Unit, SMTFunctionType, SMTType]
  
  def apply(settings : ParserSettings) =
    new SMTParser2InputAbsy (new Env, settings, null)
  
  def apply(settings : ParserSettings, prover : SimpleAPI) =
    new SMTParser2InputAbsy (new Env, settings, prover)
  
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

  private case class IncrementalException(t : Throwable) extends Exception
  
  private object ExitException extends Exception("SMT-LIB interpreter terminated")
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Class for adding parentheses <code>()</code> after each SMT-LIB command;
   * this is necessary in the interactive/incremental mode, because otherwise
   * the parser always waits for the next token to arrive before forwarding
   * a command.
   * This also removes all CR-characters in a stream (necessary because the
   * lexer seems to dislike CRs in comments), and adds an LF in the end,
   * because the lexer does not allow inputs that end with a //-comment line
   * either.
   */
  class SMTCommandTerminator(input : java.io.Reader) extends java.io.Reader {
  
    private val CR : Int         = '\r'
    private val LF : Int         = '\n'
    private val LParen : Int     = '('
    private val RParen : Int     = ')'
    private val Quote : Int      = '"'
    private val Pipe : Int       = '|'
    private val Semicolon : Int  = ';'
    private val Backslash : Int  = '\\'

    private var parenDepth : Int = 0
    private var state : Int = 0
    
    def read(cbuf : Array[Char], off : Int, len : Int) : Int = {
      var read = 0
      var cont = true

      while (read < len && cont) {
        state match {
          case 0 => input.read match {
            case CR => // nothing, read next character
            case LParen => {
              parenDepth = parenDepth + 1
              cbuf(off + read) = LParen.toChar
              read = read + 1
            }
            case RParen if (parenDepth > 1) => {
              parenDepth = parenDepth - 1
              cbuf(off + read) = RParen.toChar
              read = read + 1
            }
            case RParen if (parenDepth == 1) => {
              parenDepth = 0
              cbuf(off + read) = RParen.toChar
              read = read + 1
              state = 5
            }
            case Quote => {
              cbuf(off + read) = Quote.toChar
              read = read + 1
              state = 1
            }
            case Pipe => {
              cbuf(off + read) = Pipe.toChar
              read = read + 1
              state = 3
            }
            case Semicolon => {
              cbuf(off + read) = Semicolon.toChar
              read = read + 1
              state = 4
            }
            case -1 => {
              cbuf(off + read) = LF.toChar
              read = read + 1
              state = 7
            }
            case next => {
              cbuf(off + read) = next.toChar
              read = read + 1
            }
          }

          case 1 => input.read match {
            case Backslash => {
              cbuf(off + read) = Backslash.toChar
              read = read + 1
              state = 2
            }
            case Quote => {
              cbuf(off + read) = Quote.toChar
              read = read + 1
              state = 0
            }
            case CR => // nothing, read next character
            case -1 => {
              cbuf(off + read) = LF.toChar
              read = read + 1
              state = 7
            }
            case next => {
              cbuf(off + read) = next.toChar
              read = read + 1
            }
          }

          case 2 => input.read match {
            case -1 => {
              cbuf(off + read) = LF.toChar
              read = read + 1
              state = 7
            }
            case CR => // nothing, read next character
            case next => {
              cbuf(off + read) = next.toChar
              read = read + 1
              state = 1
            }
          }

          case 3 => input.read match {
            case Pipe => {
              cbuf(off + read) = Pipe.toChar
              read = read + 1
              state = 0
            }
            case CR => // nothing, read next character
            case -1 => {
              cbuf(off + read) = LF.toChar
              read = read + 1
              state = 7
            }
            case next => {
              cbuf(off + read) = next.toChar
              read = read + 1
            }
          }

          case 4 => input.read match {
            case LF => {
              cbuf(off + read) = LF.toChar
              read = read + 1
              state = 0
            }
            case CR => // nothing, read next character
            case -1 => {
              cbuf(off + read) = LF.toChar
              read = read + 1
              state = 7
            }
            case next => {
              cbuf(off + read) = next.toChar
              read = read + 1
            }
          }

          case 5 => {
            cbuf(off + read) = LParen.toChar
            read = read + 1
            state = 6
          }

          case 6 => {
            cbuf(off + read) = RParen.toChar
            read = read + 1
            state = 0
          }

          case 7 => {
            return if (read == 0) -1 else read
          }
        }

        cont = state >= 5 || input.ready
      }

      read
    }
   
    def close : Unit = input.close

    override def ready : Boolean = (state >= 5 || input.ready)
  
  }
  
  //////////////////////////////////////////////////////////////////////////////

/*
  private val badStringChar = """[^a-zA-Z_0-9']""".r
  
  private def sanitise(s : String) : String =
    badStringChar.replaceAllIn(s, (m : scala.util.matching.Regex.Match) =>
                                       ('a' + (m.toString()(0) % 26)).toChar.toString)
 */

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
//      sanitise(s.normalsymbolt_)
      s.normalsymbolt_
    case s : QuotedSymbol =>
//      sanitise(s.quotedsymbolt_.substring(1, s.quotedsymbolt_.length - 1))
      s.quotedsymbolt_.substring(1, s.quotedsymbolt_.length - 1)
  }
  
  object PlainSymbol {
    def unapply(s : SymbolRef) : scala.Option[String] = s match {
      case s : IdentifierRef => PlainIdentifier unapply s.identifier_
      case _ => None
    }
  }

  object PlainIdentifier {
    def unapply(id : Identifier) : scala.Option[String] = id match {
      case id : SymbolIdent => id.symbol_ match {
        case s : NormalSymbol => Some(s.normalsymbolt_)
        case _ => None
      }
      case _ => None
    }
  }
  
  object IndexedSymbol {
    def unapplySeq(s : SymbolRef) : scala.Option[Seq[String]] = s match {
      case s : IdentifierRef => IndexedIdentifier unapplySeq s.identifier_
      case _ => None
    }
  }

  object IndexedIdentifier {
    def unapplySeq(id : Identifier) : scala.Option[Seq[String]] = id match {
      case id : IndexIdent => id.symbol_ match {
        case s : NormalSymbol =>
          Some(List(s.normalsymbolt_) ++
               (id.listindexc_ map (_.asInstanceOf[Index].numeral_)))
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

  val BVDecLiteral = """bv([0-9]+)""".r

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

////////////////////////////////////////////////////////////////////////////////

class SMTParser2InputAbsy (_env : Environment[SMTParser2InputAbsy.SMTType,
                                              SMTParser2InputAbsy.VariableType,
                                              Unit,
                                              SMTParser2InputAbsy.SMTFunctionType,
                                              SMTParser2InputAbsy.SMTType],
                           settings : ParserSettings,
                           prover : SimpleAPI)
      extends Parser2InputAbsy
          [SMTParser2InputAbsy.SMTType,
           SMTParser2InputAbsy.VariableType,
           Unit,
           SMTParser2InputAbsy.SMTFunctionType,
           SMTParser2InputAbsy.SMTType,
           (Map[IFunction, (IExpression, SMTParser2InputAbsy.SMTType)], // functionDefs
            Int,                                                        // nextPartitionNumber
            Map[PartName, Int]                                          // partNameIndexes
            )](_env, settings) {
  
  import IExpression.{Sort => TSort, _}
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

  private var timeoutChecker : () => Boolean = () => false

  def processIncrementally(input : java.io.Reader,
                           timeout : Int, _timeoutPer : Int,
                           userDefStoppingCond : => Boolean) : Unit = {
    val startTime = System.currentTimeMillis
    timeoutChecker = () => {
      (System.currentTimeMillis - startTime > timeout) || userDefStoppingCond
    }

    timeoutPer = timeout min _timeoutPer

    val l = new Yylex(new SMTCommandTerminator (input))
    val p = new parser(l) {
      override def commandHook(cmd : Command) : Boolean = {
        try {
          apply(cmd)
        } catch {
          case ExitException => throw ExitException
          case t : Throwable => throw IncrementalException(t)
        }
        false
      }
    }

    try { p.pScriptC } catch {
      case ExitException => {
        // normal exit
        input.close
      }
      case IncrementalException(t) =>
        throw t
      case e : Exception =>
//        e.printStackTrace
        throw new ParseException(
             "At line " + String.valueOf(l.line_num()) +
             ", near \"" + l.buff() + "\" :" +
             "     " + e.getMessage())
    }
  }

  private var justStoreAssertions = false

  def extractAssertions(input : java.io.Reader) : Seq[IFormula] = {
    try {
      justStoreAssertions = true
      processIncrementally(input, Int.MaxValue, Int.MaxValue, false)
    } finally {
      justStoreAssertions = false
    }
    val res = assumptions.toList
    assumptions.clear
    res
  }

  def functionTypeMap : Map[IFunction, SMTFunctionType] =
    (for (Environment.Function(f, t) <- env.symbols) yield (f -> t)).toMap

  def constantTypeMap : Map[ConstantTerm, SMTType] =
    (for (Environment.Constant(c, _, t) <- env.symbols) yield (c -> t)).toMap

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

  private val incremental = (prover != null)
  
  protected def incrementalityMessage(thing : String, warnOnly : Boolean) =
    thing +
    " is only supported in incremental mode (option +incremental)" +
    (if (warnOnly) ", ignoring it" else "")

  /**
   * Check whether the given expression should never be inlined,
   * e.g., because it is too big. This method is meant to be
   * redefinable in subclasses
   */
  protected def neverInline(expr : IExpression) : Boolean =
    SizeVisitor(expr) > 100

  private def checkIncremental(thing : String) =
    if (!incremental)
      throw new Parser2InputAbsy.TranslationException(
                  incrementalityMessage(thing, false))

  private def checkIncrementalWarn(thing : String) : Boolean =
    if (incremental) {
      true
    } else {
      warn(incrementalityMessage(thing, true))
      false
    }

  private var printSuccess = false

  private def success : Unit = {
    if (incremental && printSuccess)
      println("success")
  }

  private def unsupported : Unit = {
    if (incremental)
      println("unsupported")
  }

  private def error(str : String) : Unit = {
    if (incremental)
      println("(error \"" + str + "\")")
    else
      warn(str)
  }

  private val reusedSymbols : scala.collection.Map[String, AnyRef] =
    if (incremental) prover.getSymbolMap else null

  private def importProverSymbol(name : String,
                                 args : Seq[SMTType],
                                 res : SMTType) : Boolean =
    incremental &&
    ((reusedSymbols get name) match {
       case None =>
         false
       case Some(c : ConstantTerm) if (args.isEmpty) => {
         env.addConstant(c, Environment.NullaryFunction, res)
         true
       }
       case Some(f : IFunction) if (args.size == f.arity) => {
         env.addFunction(f, SMTFunctionType(args.toList, res))
         true
       }
       case Some(p : Predicate) if (args.size == p.arity && res == SMTBool) => {
         env.addPredicate(p, ())
         true
       }
       case Some(_) => {
         warn("inconsistent definition of symbol " + name)
         false
       }
     })

  //////////////////////////////////////////////////////////////////////////////

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
   * Set up proof generation?
   */
  private var genProofs = false
  /**
   * Set up interpolant generation?
   */
  private var genInterpolants = false
  /**
   * Set up unsat-core generation?
   */
  private var genUnsatCores = false
  /**
   * Timeout per query, in incremental mode
   */
  private var timeoutPer = Int.MaxValue
  
  private def needCertificates : Boolean =
    genProofs || genInterpolants || genUnsatCores

  //////////////////////////////////////////////////////////////////////////////

  private val assumptions = new ArrayBuffer[IFormula]

  private var functionDefs = Map[IFunction, (IExpression, SMTType)]()

  // Information about partitions used for interpolation
  private var nextPartitionNumber : Int = 0
  private var partNameIndexes = Map[PartName, Int]()
//  private val interpolantSpecs = new ArrayBuffer[IInterpolantSpec]

  private def getPartNameIndexFor(name : PartName) : Int =
    (partNameIndexes get name) match {
      case Some(ind) => ind
      case None => {
        val ind = nextPartitionNumber
        nextPartitionNumber = nextPartitionNumber + 1
        partNameIndexes = partNameIndexes + (name -> ind)
        ind
      }
    }

  private var realSortWarning = false

  private var lastReasonUnknown = ""

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add a new frame to the settings stack; this in particular affects the
   * <code>Environment</code>.
   */
  protected def push : Unit = {
    checkIncremental("push")
    pushState((functionDefs, nextPartitionNumber, partNameIndexes))
    prover.push
  }

  /**
   * Pop a frame from the settings stack.
   */
  protected def pop : Unit = {
    checkIncremental("pop")
    prover.pop

    val (oldFunctionDefs, oldNextPartitionNumber, oldPartNameIndexes) = popState
    functionDefs = oldFunctionDefs
    nextPartitionNumber = oldNextPartitionNumber
    partNameIndexes = oldPartNameIndexes

    // make sure that the prover generates proofs; this setting
    // is handled via the stack in the prover, but is global
    // in SMT-LIB scripts
    prover.setConstructProofs(needCertificates)
  }

  /**
   * Erase all stored information.
   */
  protected override def reset : Unit = {
    super.reset
    prover.reset

    printSuccess         = false
    booleanFunctionsAsPredicates =
      Param.BOOLEAN_FUNCTIONS_AS_PREDICATES(settings)
    inlineLetExpressions = true
    inlineDefinedFuns    = true
    totalityAxiom        = true
    functionalityAxiom   = true
    genProofs            = false
    genInterpolants      = false
    genUnsatCores        = false
    assumptions.clear
    functionDefs         = Map()
    nextPartitionNumber  = 0
    partNameIndexes      = Map()
  }

  protected override def addAxiom(f : IFormula) : Unit =
    if (incremental) {
      prover setPartitionNumber -1
      prover addAssertion PartNameEliminator(f)
    } else {
      super.addAxiom(f)
    }

  private def addConstant(c : ConstantTerm, cType : SMTType) : Unit = {
    env.addConstant(c, Environment.NullaryFunction, cType)
    if (incremental)
      prover.addConstantRaw(c)
  }

  //////////////////////////////////////////////////////////////////////////////

  private val printer = new PrettyPrinterNonStatic

  private val constantTypeFunction =
    (c : ConstantTerm) => (env lookupSymPartial c.name) match {
       case Some(Environment.Constant(_, _, t)) => Some(t)
       case _ => None
    }

  private val functionTypeFunction =
    (f : IFunction) => (env lookupSymPartial f.name) match {
      case Some(Environment.Function(_, t)) => Some(t)
      case _ => None
    }

  private def smtLinearise(f : IFormula) : Unit =
    SMTLineariser(f, constantTypeFunction, functionTypeFunction)
  
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

  private object NumParameter {
    def unapply(param : AttrParam) : scala.Option[IdealInt] = param match {
      case param : SomeAttrParam => param.sexpr_ match {
        case expr : ConstantSExpr => expr.specconstant_ match {
          case const : NumConstant => Some(IdealInt(const.numeral_))
          case _ => None
        }
        case _ => None
      }
      case _ : NoAttrParam => None
    }
  }

  private def handleBooleanAnnot(option : String, annot : AttrAnnotation)
                                (todo : Boolean => Unit) : Boolean =
    if (annot.annotattribute_ == option) {
      annot.attrparam_ match {
        case BooleanParameter(value) =>
          todo(value)
        case _ =>
          throw new Parser2InputAbsy.TranslationException(
            "Expected a boolean parameter after option " + option)
      }
      true
    } else {
      false
    }

  private def handleNumAnnot(option : String, annot : AttrAnnotation)
                            (todo : IdealInt => Unit) : Boolean =
    if (annot.annotattribute_ == option) {
      annot.attrparam_ match {
        case NumParameter(value) =>
          todo(value)
        case _ =>
          throw new Parser2InputAbsy.TranslationException(
            "Expected a numeric parameter after option " + option)
      }
      true
    } else {
      false
    }

  //////////////////////////////////////////////////////////////////////////////

  private def apply(script : Script) : Unit =
    for (cmd <- script.listcommand_) apply(cmd)

  private def apply(cmd : Command) : Unit = cmd match {

      case cmd : SetLogicCommand => {
        // just ignore for the time being
        success
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : SetOptionCommand => {
        val annot = cmd.optionc_.asInstanceOf[Option]
                                .annotation_.asInstanceOf[AttrAnnotation]

        val handled =
        handleBooleanAnnot(":print-success", annot) {
          value => printSuccess = value
        } ||
        handleBooleanAnnot(":produce-models", annot) {
          value => // nothing
        } ||
        handleBooleanAnnot(":boolean-functions-as-predicates", annot) {
          value => booleanFunctionsAsPredicates = value
        } ||
        handleBooleanAnnot(":inline-let", annot) {
          value => inlineLetExpressions = value
        } ||
        handleBooleanAnnot(":inline-definitions", annot) {
          value => inlineDefinedFuns = value
        } ||
        handleBooleanAnnot(":totality-axiom", annot) {
          value => totalityAxiom = value
        } ||
        handleBooleanAnnot(":functionality-axiom", annot) {
          value => functionalityAxiom = value
        } ||
        handleBooleanAnnot(":produce-proofs", annot) {
          value => {
            genProofs = value
            if (incremental)
              prover.setConstructProofs(needCertificates)
          }
        } ||
        handleBooleanAnnot(":produce-interpolants", annot) {
          value => {
            genInterpolants = value
            if (incremental)
              prover.setConstructProofs(needCertificates)
          }
        } ||
        handleBooleanAnnot(":produce-unsat-cores", annot) {
          value => {
            genUnsatCores = value
            if (incremental)
              prover.setConstructProofs(needCertificates)
          }
        } ||
        handleNumAnnot(":timeout-per", annot) {
          value => timeoutPer = (value min IdealInt(Int.MaxValue)).intValue
        }

        if (handled) {
          success
        } else {
          if (incremental)
            unsupported
          else
            warn("ignoring option " + annot.annotattribute_)
        }
      }

      //////////////////////////////////////////////////////////////////////////
      
      case cmd : SetInfoCommand =>
        success

      //////////////////////////////////////////////////////////////////////////

      case cmd : SortDeclCommand => {
        ensureEnvironmentCopy

        if (cmd.numeral_.toInt != 0)
          throw new Parser2InputAbsy.TranslationException(
            "Polymorphic sorts are not supported yet")

        val name = asString(cmd.symbol_)
        warn("treating sort " + name + " as infinite sort")

        val sort = new TSort.InfUninterpreted(name)

        env.addSort(name, SMTUnint(sort))

        success
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : DataDeclCommand => {
        ensureEnvironmentCopy

        val name = asString(cmd.symbol_)
        val sortNames = List(name)
        val (adtCtors, smtCtorArgs) =
          translateDataCtorList(sortNames, 0, cmd.listconstructordeclc_)

        setupADT(sortNames, List((adtCtors, smtCtorArgs)))

        success
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : DataDeclsCommand => {
        ensureEnvironmentCopy

        val sortNames =
          for (sortc <- cmd.listpolysortc_) yield {
            val sort = sortc.asInstanceOf[PolySort]
            if (sort.numeral_.toInt != 0)
              throw new Parser2InputAbsy.TranslationException(
                "Polymorphic algebraic data-types are not supported yet")
            asString(sort.symbol_)
          }

        val allCtors =
          for ((maybedecl, sortNum) <-
                 cmd.listmaybepardatadecl_.zipWithIndex) yield {
            val decl = maybedecl match {
              case d : MonoDataDecl => d
              case _ : ParDataDecl =>
                throw new Parser2InputAbsy.TranslationException(
                  "Polymorphic algebraic data-types are not supported yet")
            }
            translateDataCtorList(sortNames, sortNum,
                                  decl.listconstructordeclc_)  
          }

        setupADT(sortNames, allCtors)

        success
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : DataDeclsOldCommand => {
        ensureEnvironmentCopy

        if (!cmd.listsymbol_.isEmpty)
          throw new Parser2InputAbsy.TranslationException(
            "Polymorphic algebraic data-types are not supported yet")

        val sortNames =
          for (declc <- cmd.listolddatadeclc_) yield {
            val decl = declc.asInstanceOf[OldDataDecl]
            asString(decl.symbol_)
          }

        val allCtors =
          for ((declc, sortNum) <- cmd.listolddatadeclc_.zipWithIndex) yield {
            val decl = declc.asInstanceOf[OldDataDecl]
            translateDataCtorList(sortNames, sortNum,
                                  decl.listconstructordeclc_)
          }

        setupADT(sortNames, allCtors)

        success
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : SortDefCommand => {
        if (!cmd.listsymbol_.isEmpty)        
          throw new Parser2InputAbsy.TranslationException(
              "Currently only define-sort with arity 0 is supported")
        env.addSort(asString(cmd.symbol_), translateSort(cmd.sort_))
        success
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

        ensureEnvironmentCopy

        if (!importProverSymbol(name, args, res)) {
          if (args.length > 0) {
            if (!booleanFunctionsAsPredicates || res != SMTBool) {
              // use a real function
              val f = MonoSortedIFunction(name,
                                          args map (_.toSort),
                                          res.toSort,
                                          !totalityAxiom, !functionalityAxiom)
              env.addFunction(f, SMTFunctionType(args.toList, res))
              if (incremental)
                prover.addFunction(f,
                                   if (functionalityAxiom)
                                     SimpleAPI.FunctionalityMode.Full
                                   else
                                     SimpleAPI.FunctionalityMode.None)
            } else {
              // use a predicate
              val p = MonoSortedPredicate(name, args map (_.toSort))
              env.addPredicate(p, ())
              if (incremental)
                prover.addRelation(p)
            }
          } else if (res != SMTBool) {
            // use a constant
            addConstant(res.toSort newConstant name, res)
          } else {
            // use a nullary predicate (propositional variable)
            val p = new Predicate(name, 0)
            env.addPredicate(p, ())
            if (incremental)
              prover.addRelation(p)
          }
        }

        success
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : ConstDeclCommand => {
        val name = asString(cmd.symbol_)
        val res = translateSort(cmd.sort_)

        ensureEnvironmentCopy

        if (!importProverSymbol(name, List(), res)) {
          if (res != SMTBool) {
            // use a constant
            addConstant(res.toSort newConstant name, res)
          } else {
            // use a nullary predicate (propositional variable)
            val p = new Predicate(name, 0)
            env.addPredicate(p, ())
            if (incremental)
              prover.addRelation(p)
          }
        }

        success
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : FunctionDefCommand => {
        // Functions are always declared to have integer inputs and outputs
        val name = asString(cmd.symbol_)
        val args : Seq[SMTType] = 
          for (sortedVar <- cmd.listesortedvarc_)
          yield translateSort(sortedVar.asInstanceOf[ESortedVar].sort_)
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
        val f = MonoSortedIFunction(name, args map (_.toSort), resType.toSort,
                                    true, true)
        env.addFunction(f, SMTFunctionType(args.toList, resType))
    
        if (inlineDefinedFuns && !neverInline(body._1)) {
          functionDefs = functionDefs + (f -> body) 
        } else if (incremental && args.isEmpty) {
          // use the SimpleAPI abbreviation feature
          resType match {
            case SMTBool =>
              functionDefs =
                functionDefs + (f -> (prover abbrev asFormula(body), SMTBool))
            case t =>
              functionDefs =
                functionDefs + (f -> (prover abbrev asTerm(body), t))
          }
        } else {
          // set up a defining equation and formula
          if (incremental)
            prover.addFunction(f, SimpleAPI.FunctionalityMode.NoUnification)
          addAxiomEquation(f, body)
        }

        success
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : RecFunctionDefCommand => {
        val name = asString(cmd.symbol_)
        val args : Seq[SMTType] = 
          for (sortedVar <- cmd.listesortedvarc_)
          yield translateSort(sortedVar.asInstanceOf[ESortedVar].sort_)
        val argNum = pushVariables(cmd.listesortedvarc_)
        val resType = translateSort(cmd.sort_)

        // use a real function
        val f = MonoSortedIFunction(name, args map (_.toSort), resType.toSort,
                                    true, true)
        env.addFunction(f, SMTFunctionType(args.toList, resType))

        if (incremental)
          prover.addFunction(f, SimpleAPI.FunctionalityMode.NoUnification)
        
        // parse the definition of the function
        val body@(_, bodyType) = translateTerm(cmd.term_, 0)

        if (bodyType != resType)
          throw new Parser2InputAbsy.TranslationException(
              "Body of function definition has wrong type")

        // pop the variables from the environment
        for (_ <- PlainRange(argNum)) env.popVar

        registerRecFunctions(List((f, body)))
        success
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : RecFunctionDefsCommand => {
        // create functions
        val functions = for (sigc <- cmd.listfunsignaturec_) yield {
          val sig = sigc.asInstanceOf[FunSignature]
          val name = asString(sig.symbol_)
          val args : Seq[SMTType] = 
            for (sortedVar <- sig.listesortedvarc_)
            yield translateSort(sortedVar.asInstanceOf[ESortedVar].sort_)
          val resType = translateSort(sig.sort_)

          // use a real function
          val f = MonoSortedIFunction(name, args map (_.toSort), resType.toSort,
                                      true, true)
          env.addFunction(f, SMTFunctionType(args.toList, resType))

          if (incremental)
            prover.addFunction(f, SimpleAPI.FunctionalityMode.NoUnification)

          f
        }

        // parse bodies
        val funDefs =
          for (((sigc, bodyExpr), f) <-
                 (cmd.listfunsignaturec_ zip cmd.listterm_) zip functions) yield {
            val sig = sigc.asInstanceOf[FunSignature]
            val argNum = pushVariables(sig.listesortedvarc_)
            val resType = translateSort(sig.sort_)

            val body@(_, bodyType) = translateTerm(bodyExpr, 0)
            if (bodyType != resType)
              throw new Parser2InputAbsy.TranslationException(
                "Body of function definition has wrong type")
            
            // pop the variables from the environment
            for (_ <- PlainRange(argNum)) env.popVar

            (f, body)
          }

        registerRecFunctions(funDefs)
        success
      }

      //////////////////////////////////////////////////////////////////////////
      
      case cmd : PushCommand => {
        for (_ <- 0 until cmd.numeral_.toInt)
          push
        success
      }

      case cmd : PopCommand => {
        for (_ <- 0 until cmd.numeral_.toInt)
          pop
        success
      }

      //////////////////////////////////////////////////////////////////////////
      
      case cmd : AssertCommand => {
        val f = asFormula(translateTerm(cmd.term_, -1))
        if (incremental && !justStoreAssertions) {
          if (needCertificates) {
            PartExtractor(f, false) match {
              case List(INamedPart(PartName.NO_NAME, g)) => {
                // generate consecutive partition numbers
                prover setPartitionNumber nextPartitionNumber
                nextPartitionNumber = nextPartitionNumber + 1
                prover addAssertion PartNameEliminator(g)
              }
              case parts =>
                for (INamedPart(name, g) <- parts) {
                  prover setPartitionNumber getPartNameIndexFor(name)
                  prover addAssertion PartNameEliminator(g)
                }
            }
          } else {
            prover addAssertion f
          }
        } else {
          assumptions += f
        }

        success
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : CheckSatCommand => if (incremental) try {
        var res = prover checkSat false
        val startTime = System.currentTimeMillis

        while (res == SimpleAPI.ProverStatus.Running) {
          if (timeoutChecker()) {
            println("unknown")
            lastReasonUnknown = "timeout"
            Console.err.println("Global timeout, stopping solver")
            prover.stop
            throw ExitException
          }
          if ((System.currentTimeMillis - startTime).toInt > timeoutPer)
            prover.stop
          res = prover.getStatus(100)
        }
        
        res match {
          case SimpleAPI.ProverStatus.Sat |
               SimpleAPI.ProverStatus.Invalid =>
            println("sat")
          case SimpleAPI.ProverStatus.Unsat |
               SimpleAPI.ProverStatus.Valid =>
            println("unsat")
          case SimpleAPI.ProverStatus.Unknown => {
            println("unknown")
            lastReasonUnknown = "timeout"
          }
          case SimpleAPI.ProverStatus.Inconclusive => {
            println("unknown")
            lastReasonUnknown = "incomplete"
          }
          case SimpleAPI.ProverStatus.OutOfMemory =>
            error("out of memory or stack overflow")
          case _ =>
            error("unexpected prover result")
        }
      } catch {
        case e : SimpleAPI.SimpleAPIException =>
          error(e.getMessage)
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : GetAssertionsCommand =>
        error("get-assertions not supported")

      //////////////////////////////////////////////////////////////////////////

      // TODO: fix output of arrays

      case cmd : GetValueCommand => if (checkIncrementalWarn("get-value")) {
        prover.getStatus(false) match {
          case SimpleAPI.ProverStatus.Sat |
               SimpleAPI.ProverStatus.Invalid |
               SimpleAPI.ProverStatus.Inconclusive => try {
            val expressions = cmd.listterm_.toList

            val values = prover.withTimeout(timeoutPer) {
              for (expr <- expressions) yield
                translateTerm(expr, 0) match {
                  case (f : IFormula, _) =>
                    (prover eval f).toString
                  case (t : ITerm, _) =>
                    SMTLineariser asString (prover evalToTerm t)
                }
            }
            
            println("(" +
              (for ((e, v) <- expressions.iterator zip values.iterator)
               yield ("(" + (printer print e) + " " + v + ")")).mkString(" ") +
              ")")
          } catch {
            case SimpleAPI.TimeoutException =>
              error("timeout when constructing full model")
            case SimpleAPI.NoModelException =>
              error("no model available")
          }

          case _ =>
            error("no model available")
        }
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : GetProofCommand =>
        if (checkIncrementalWarn("get-proof")) {
          prover.getStatus(false) match {
            case SimpleAPI.ProverStatus.Unsat |
                 SimpleAPI.ProverStatus.Valid
                 if genProofs => {
              println("(proof \"")
              val nameMapping =
                (for ((n, i) <- partNameIndexes.iterator)
                 yield (i, n)).toMap
              println(prover.certificateAsString(nameMapping,
                                                 Param.InputFormat.SMTLIB))
              println("\")")
            }
            case _ =>
              error("no proof available")
          }
        }

      //////////////////////////////////////////////////////////////////////////

      case cmd : GetUnsatCoreCommand =>
        if (checkIncrementalWarn("get-unsat-core")) {
          prover.getStatus(false) match {
            case SimpleAPI.ProverStatus.Unsat |
                 SimpleAPI.ProverStatus.Valid => {
              val core = prover.getUnsatCore
              val names =
                (for ((name, n) <- partNameIndexes.iterator;
                      if (core contains n))
                 yield name.toString).toVector.sorted
              println("(" + (names mkString " ") + ")")
              success
            }
            case _ =>
              error("no unsatisfiable core available")
          }
        }

      //////////////////////////////////////////////////////////////////////////

      case cmd : GetAssignmentCommand =>
        error("get-assignment not supported")

      //////////////////////////////////////////////////////////////////////////

      // TODO: fix output of arrays

      case cmd : GetModelCommand => if (checkIncrementalWarn("get-model")) {
        prover.getStatus(false) match {
          case SimpleAPI.ProverStatus.Sat |
               SimpleAPI.ProverStatus.Invalid |
               SimpleAPI.ProverStatus.Inconclusive => try {
            val model = prover.withTimeout(timeoutPer) {
              prover.partialModelAsFormula
            }

            SMTLineariser printModel model
          } catch {
            case SimpleAPI.TimeoutException =>
              error("timeout when constructing full model")
            case SimpleAPI.NoModelException =>
              error("no model available")
          }

          case _ =>
            error("no model available")
        }
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : GetInterpolantsCommand =>
        if (incremental) {
          if (genInterpolants) prover.getStatus(false) match {
            case SimpleAPI.ProverStatus.Unsat |
                 SimpleAPI.ProverStatus.Valid => {

              try { prover.withTimeout(timeoutPer) {
                if (cmd.listsexpr_.isEmpty) {

                  val interpolantSpecs =
                    for (i <- 0 until nextPartitionNumber) yield Set(i)
                  val interpolants = prover.getInterpolants(interpolantSpecs)

                  print("(")
                  var sep = ""
                  for (interpolant <- prover.getInterpolants(interpolantSpecs)) {
                    print(sep)
                    sep = "\n"
                    smtLinearise(interpolant)
                  }
                  println(")")

                } else translateTreeInterpolantSpec(cmd.listsexpr_) match {

                  case List(tree) => {
                    val allMentionedNames =
                      (for (t <- tree.iterator; n <- t.iterator) yield n).toSet
                    val remainingNames =
                      ((0 until nextPartitionNumber).iterator filterNot
                         allMentionedNames).toList

                    val finalTree =
                      if (!remainingNames.isEmpty) {
                        warn("not all asserted formulas are mentioned in interpolant specification, " +
                             "putting remaining formulas in the last/root partition")
                        Tree(tree.d ++ remainingNames, tree.children)
                      } else {
                        tree
                      }

                    val interpolants =
                      prover.getTreeInterpolant(finalTree,
                                                (timeoutPer / tree.size) min 3000)

                    print("(")
                    var sep = ""
                    for (t <- interpolants.children) t foreachPostOrder { f =>
                      print(sep)
                      sep = "\n"
                      smtLinearise(f)
                    }
                    println(")")
                  }

                  case _ =>
                    error("could not parse interpolant specification")
                }
              } } catch {
                case SimpleAPI.TimeoutException =>
                  error("timeout while computing interpolants")
              }
/*
   Old code that only works for sequence interpolants
                  for (p <- cmd.listsexpr_.toList) yield p match {
                    case p : SymbolSExpr =>
                      Set(partNameIndexes(
                            env.lookupPartName(printer print p.symbol_)))
                    case p : ParenSExpr
                        if (!p.listsexpr_.isEmpty &&
                            (printer print p.listsexpr_.head) == "and") => {
                      val it = p.listsexpr_.iterator
                      it.next
                      (for (s <- it)
                       yield partNameIndexes(
                               env.lookupPartName(printer print s))).toSet
                    }
                    case p =>
                      throw new Parser2InputAbsy.TranslationException(
                        "Could not parse interpolation partition: " +
                        (printer print p))
                  }
 */

            }

            case _ =>
              error("no proof available")
          } else {
            error(":produce-interpolants has to be set before get-interpolants")
          }
        } else {
          genInterpolants = true
        }
      
      //////////////////////////////////////////////////////////////////////////
      
      case cmd : GetInfoCommand => if (checkIncrementalWarn("get-info"))
        cmd.annotattribute_ match {
          case ":authors" => {
            println("(:authors \"")
            CmdlMain.printGreeting
            println("\n\")")
          }
          case ":name" =>
            println("(:name \"Princess\")")
          case ":version" =>
            println("(:version \"" + CmdlMain.version + "\")")
          case ":error-behavior" =>
            println("(:error-behavior \"immediate-exit\")")
          case ":interpolation-method" =>
            println("(:interpolation-method \"tree\")")
          case ":reason-unknown" =>
            println("(:reason-unknown " + lastReasonUnknown + ")")
        }
      
      //////////////////////////////////////////////////////////////////////////
      
      case cmd : GetOptionCommand => if (checkIncrementalWarn("get-option")) {
        unsupported
      }
      
      //////////////////////////////////////////////////////////////////////////
      
      case cmd : EchoCommand => if (checkIncrementalWarn("echo")) {
        println(cmd.smtstring_)
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : ResetCommand => if (checkIncrementalWarn("reset")) {
        reset
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : ExitCommand => if (checkIncrementalWarn("exit")) {
        throw ExitException
      }

      //////////////////////////////////////////////////////////////////////////

      case _ : EmptyCommand =>
        // command to be ignored

      //////////////////////////////////////////////////////////////////////////

      case _ =>
        warn("ignoring " + (printer print cmd))
  }

  //////////////////////////////////////////////////////////////////////////////

  protected def translateSort(s : Sort) : SMTType = s match {
    case s : IdentSort => s.identifier_ match {
      case PlainIdentifier("Int") =>
        SMTInteger
      case PlainIdentifier("Bool") =>
        SMTBool
      case PlainIdentifier("Real") => {
        if (!realSortWarning) {
          warn("treating sort Real as Int")
          realSortWarning = true
        }
        SMTInteger
      }
      case IndexedIdentifier("BitVec", width) =>
        SMTBitVec(width.toInt)
      case PlainIdentifier(id) =>
        env lookupSort id
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

      val baseExpr =
        if (needCertificates) {
          val names = for (annot <- t.listannotation_;
                           a = annot.asInstanceOf[AttrAnnotation];
                           if (a.annotattribute_ == ":named")) yield {
            a.attrparam_ match {
              case p : SomeAttrParam => p.sexpr_ match {
                case e : SymbolSExpr => 
                  printer print e
                case _ =>
                  throw new Parser2InputAbsy.TranslationException(
                     "Expected name after \":named\"")
              }
              case _ : NoAttrParam =>
                throw new Parser2InputAbsy.TranslationException(
                   "Expected name after \":named\"")
            }
          }
          
          translateTerm(t.term_, polarity) match {
            case p@(expr, SMTBool) =>
              ((asFormula(p) /: names) {
                 case (res, name) => INamedPart(env lookupPartName name, res)
               }, SMTBool)
            case p =>
              // currently names for terms are ignored
              p
          }
        } else {
          translateTerm(t.term_, polarity)
        }

      if (triggers.isEmpty)
        baseExpr
      else
        ((asFormula(baseExpr) /: triggers) {
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

  private def pushVar(bsort : Sort, bsym : Symbol) : Unit = {
    ensureEnvironmentCopy
    env.pushVar(asString(bsym), BoundVariable(translateSort(bsort)))
  }
  
  private def translateQuantifier(t : QuantifierTerm, polarity : Int)
                                 : (IExpression, SMTType) = {
    val quantNum = pushVariables(t.listsortedvariablec_)
    val matrix = asFormula(translateTerm(t.term_, polarity))

    // pop the variables from the environment
    val types = for (_ <- 0 until quantNum)
                yield env.popVar.asInstanceOf[BoundVariable].varType

    t.quantifier_ match {
      case _ : AllQuantifier =>
        (all(types map (_.toSort), matrix), SMTBool)
      case _ : ExQuantifier =>
        (ex(types map (_.toSort), matrix), SMTBool)
      case _ : EpsQuantifier => {
        if (t.listsortedvariablec_.size != 1)
          throw new ParseException("_eps has to bind exactly one variable")
        (types.head.toSort eps matrix, types.head)
      }
    }
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

    ensureEnvironmentCopy

    if (env existsVar (_.isInstanceOf[BoundVariable])) {
      // we are underneath a real quantifier, so have to introduce quantifiers
      // for this let expression, or directly substitute
      
      for ((v, t, _) <- bindings) env.pushVar(v, BoundVariable(t))

      val wholeBody@(body, bodyType) = translateTerm(t.term_, polarity)
      
      for (_ <- bindings) env.popVar

      //////////////////////////////////////////////////////////////////////////
      
      if (inlineLetExpressions) {
        // then we directly inline the bound formulae and terms
        
        val subst =
          for ((_, t, s) <- bindings.toList.reverse) yield asTerm((s, t))
        (LetInlineVisitor.visit(body, (subst, -bindings.size)), bodyType)
      } else {
        val definingEqs =
          connect(for (((_, t, s), num) <-
                    bindings.iterator.zipWithIndex) yield {
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
      // we introduce a boolean or integer variables to encode this
      // let expression

      for ((name, t, s) <- bindings)
        // directly substitute small expressions, unless the user
        // has chosen otherwise
        if (inlineLetExpressions && !neverInline(s)) {
          env.pushVar(name, SubstExpression(s, t))
        } else if (incremental) {
          // use the SimpleAPI abbreviation feature
          t match {
            case SMTBool =>
              env.pushVar(name,
                          SubstExpression(prover.abbrev(asFormula((s, t))),
                                          SMTBool))
            case _ =>
              env.pushVar(name,
                          SubstExpression(prover.abbrev(asTerm((s, t))), t))
          }
        } else addAxiom(t match {
          case SMTBool => {
            val f = new MonoSortedIFunction(letVarName(name),
                                            List(TSort.Integer), TSort.Bool,
                                            true, false)
            env.addFunction(f, SMTFunctionType(List(SMTInteger), SMTBool))

            env.pushVar(name, SubstExpression(
                                  containFunctionApplications(eqZero(f(0))),
                                  SMTBool))
            all(ITrigger(List(f(v(0))),
                         eqZero(v(0)) ==>
                         ((eqZero(f(v(0))) & asFormula((s, t))) |
                             ((f(v(0)) === 1) & !asFormula((s, t))))))
          }
          case exprType => {
            val c = t.toSort newConstant letVarName(name)
            addConstant(c, exprType)
            env.pushVar(name, SubstExpression(c, exprType))
            c === asTerm((s, t))
          }
        })
      
      val wholeBody = translateTerm(t.term_, polarity)

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
                   yield (a <===> b),
                 IBinJunctor.And)
       } else {
         val types = (transArgs map (_._2)).toSet
         if (types.size > 1)
           throw new Parser2InputAbsy.TranslationException(
             "Can only compare terms of same type using =")
         connect(for (Seq(a, b) <- (transArgs map (asTerm(_))) sliding 2)
                   yield translateEq(a, b, types.iterator.next, polarity),
                 IBinJunctor.And)
       },
       SMTBool)
    }
    
    case PlainSymbol("distinct") => {
      val transArgs = for (a <- args) yield translateTerm(a, 0)
      (if (transArgs forall (_._2 == SMTBool)) transArgs.length match {
         case 0 | 1 => true
         case 2 => ~(asFormula(transArgs(0)) <===> asFormula(transArgs(1)))
         case _ => false
       } else {
         val types = (transArgs map (_._2)).toSet
         if (types.size > 1)
           throw new Parser2InputAbsy.TranslationException(
             "Can only compare terms of same type using distinct")
         distinct(for (p <- transArgs.iterator) yield asTerm(p))
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
      val Seq(num, denom) = for (a <- args) yield asTerm(translateTerm(a, 0))
      (mulTheory.eDiv(num, denom), SMTInteger)
    }
       
    case PlainSymbol("mod") => {
      checkArgNum("mod", 2, args)
      val Seq(num, denom) = for (a <- args) yield asTerm(translateTerm(a, 0))
      (mulTheory.eMod(num, denom), SMTInteger)
    }

    case PlainSymbol("abs") => {
      checkArgNum("abs", 1, args)
      (abs(asTerm(translateTerm(args.head, 0))), SMTInteger)
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

    ////////////////////////////////////////////////////////////////////////////
    // Bit-vector operations

    case IndexedSymbol(BVDecLiteral(value), width) => {
      val t = SMTBitVec(width.toInt)
      (ModuloArithmetic.cast2Sort(t.toSort, IdealInt(value)), t)
    }

    case PlainSymbol("concat") => {
      checkArgNum("concat", 2, args)
      val a0@(transArg0, type0) = translateTerm(args(0), 0)
      val a1@(transArg1, type1) = translateTerm(args(1), 0)
      val (mod0, width0) = extractBVModulusWidth("concat", type0, args(0))
      val (mod1, width1) = extractBVModulusWidth("concat", type1, args(1))
      (ModuloArithmetic.mod_concat(i(mod0), i(mod1), asTerm(a0), asTerm(a1)),
       SMTBitVec(width0 + width1))
    }

    case IndexedSymbol("extract", beginStr, endStr) => {
      checkArgNum("extract", 1, args)
      val begin = beginStr.toInt
      val end = endStr.toInt
      val a0@(transArg0, type0) = translateTerm(args(0), 0)
      val (_, width0) = extractBVModulusWidth("extract", type0, args(0))
      val resType = SMTBitVec(begin - end + 1)
      (ModuloArithmetic.mod_extract(i(SMTBitVec(width0 - begin - 1).modulus),
                                    i(resType.modulus),
                                    i(SMTBitVec(end).modulus),
                                    asTerm(a0)),
       resType)
    }

    case PlainSymbol("bvnot") =>
      translateBVUnaryOp("bvnot", ModuloArithmetic.mod_not, args)
    case PlainSymbol("bvneg") =>
      translateBVUnaryOp("bvneg", ModuloArithmetic.mod_neg, args)

    case PlainSymbol("bvand") =>
      translateBVBinOp("bvand",  ModuloArithmetic.mod_and, args)
    case PlainSymbol("bvor") =>
      translateBVBinOp("bvor",   ModuloArithmetic.mod_or, args)
    case PlainSymbol("bvadd") =>
      translateBVBinOp("bvadd",  ModuloArithmetic.mod_add, args)
    case PlainSymbol("bvsub") =>
      translateBVBinOp("bvsub",  ModuloArithmetic.mod_sub, args)
    case PlainSymbol("bvmul") =>
      translateBVBinOp("bvmul",  ModuloArithmetic.mod_mul, args)
    case PlainSymbol("bvudiv") =>
      translateBVBinOp("bvudiv", ModuloArithmetic.mod_udiv, args)
    case PlainSymbol("bvsdiv") =>
      translateBVBinOp("bvsdiv", ModuloArithmetic.mod_sdiv, args)
    case PlainSymbol("bvurem") =>
      translateBVBinOp("bvurem", ModuloArithmetic.mod_urem, args)
    case PlainSymbol("bvsrem") =>
      translateBVBinOp("bvsrem", ModuloArithmetic.mod_srem, args)
    case PlainSymbol("bvsmod") =>
      translateBVBinOp("bvsmod", ModuloArithmetic.mod_smod, args)
    case PlainSymbol("bvshl") =>
      translateBVBinOp("bvshl",  ModuloArithmetic.mod_shl, args)
    case PlainSymbol("bvlshr") =>
      translateBVBinOp("bvlshr", ModuloArithmetic.mod_lshr, args)
    case PlainSymbol("bvashr") =>
      translateBVBinOp("bvashr", ModuloArithmetic.mod_ashr, args)
    case PlainSymbol("bvxor") =>
      translateBVBinOp("bvxor",  ModuloArithmetic.mod_xor, args)
    case PlainSymbol("bvxnor") =>
      translateBVBinOp("bvxnor", ModuloArithmetic.mod_xnor, args)

    case PlainSymbol("bvnand") => {
      val (t, tp) = translateBVBinOp("bvnand", ModuloArithmetic.mod_and, args)
      (ModuloArithmetic.mod_not(i(tp.modulus), t), tp)
    }
    case PlainSymbol("bvnor") => {
      val (t, tp) = translateBVBinOp("bvnor", ModuloArithmetic.mod_or, args)
      (ModuloArithmetic.mod_not(i(tp.modulus), t), tp)
    }

    case PlainSymbol("bvcomp") => {
      checkArgNum("bvcomp", 2, args)
      val a0@(transArg0, type0) = translateTerm(args(0), 0)
      val a1@(transArg1, type1) = translateTerm(args(1), 0)
      val modulus = checkArgBVAgreement("bvcomp", args(0), type0, args(1), type1)
      (ModuloArithmetic.mod_comp(i(modulus), asTerm(a0), asTerm(a1)), SMTBitVec(1))
    }

    case PlainSymbol("bvult") =>
      translateBVBinPred("bvult", ModuloArithmetic.mod_ult, args)
    case PlainSymbol("bvule") =>
      translateBVBinPred("bvule", ModuloArithmetic.mod_ule, args)
    case PlainSymbol("bvslt") =>
      translateBVBinPred("bvslt", ModuloArithmetic.mod_slt, args)
    case PlainSymbol("bvsle") =>
      translateBVBinPred("bvsle", ModuloArithmetic.mod_sle, args)

    case PlainSymbol("bvugt") =>
      translateBVBinPredInv("bvugt", ModuloArithmetic.mod_ult, args)
    case PlainSymbol("bvuge") =>
      translateBVBinPredInv("bvuge", ModuloArithmetic.mod_ule, args)
    case PlainSymbol("bvsgt") =>
      translateBVBinPredInv("bvsgt", ModuloArithmetic.mod_slt, args)
    case PlainSymbol("bvsge") =>
      translateBVBinPredInv("bvsge", ModuloArithmetic.mod_sle, args)

    case IndexedSymbol("zero_extend", digitsStr) => {
      checkArgNum("zero_extend", 1, args)
      val digits = digitsStr.toInt
      val (transArg0, type0) = translateTerm(args(0), 0)
      val (_, width) = extractBVModulusWidth("zero_extend", type0, args(0))
      (transArg0, SMTBitVec(width + digits))
    }

    case IndexedSymbol("sign_extend", digitsStr) => {
      checkArgNum("sign_extend", 1, args)
      val digits = digitsStr.toInt
      val a0@(transArg0, type0) = translateTerm(args(0), 0)
      val (_, width) = extractBVModulusWidth("sign_extend", type0, args(0))
      (ModuloArithmetic.cast2UnsignedBV(width + digits,
         ModuloArithmetic.cast2SignedBV(width, asTerm(a0))),
       SMTBitVec(width + digits))
    }

    // Not supported yet: repeat, rotate_left, rotate_right

    ////////////////////////////////////////////////////////////////////////////
    // ADT operations

    case PlainSymbol("_size") => {
      checkArgNum("_size", 1, args)
      val (expr, ty) = translateTerm(args.head, 0)
      ty match {
        case SMTADT(adt, sortNum) => {
          if (adt.termSize == null)
            throw new Parser2InputAbsy.TranslationException(
                "Function _size can only be used in combination with option " +
                "-adtMeasure=size")
          (IFunApp(adt.termSize(sortNum), List(expr.asInstanceOf[ITerm])),
           SMTInteger)
        }
        case _ =>
          throw new Parser2InputAbsy.TranslationException(
              "Function _size needs to receive an ADT term as argument")
      }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Declared symbols from the environment
    case id => unintFunApp(asString(id), sym, args, polarity)
  }

  private def translateEq(a : ITerm, b : ITerm, t : SMTType,
                          polarity : Int) : IFormula =
    t match {
      case SMTArray(argTypes, resType) if (polarity > 0) => {
        val arity = argTypes.size
        val theory = SimpleArray(arity)
        val args = (for (n <- 0 until arity) yield v(n))
        val matrix =
          translateEq(IFunApp(theory.select,
                              List(VariableShiftVisitor(a, 0, arity)) ++ args),
                      IFunApp(theory.select,
                              List(VariableShiftVisitor(b, 0, arity)) ++ args),
                      resType, polarity)

        quan(for (_ <- 0 until arity) yield Quantifier.ALL, matrix)
      }

      case SMTBool =>
        eqZero(a) <=> eqZero(b)
//        all(all(!((VariableShiftVisitor(a, 0, 2) === v(0)) &
//                 (VariableShiftVisitor(b, 0, 2) === v(1)) &
//                 ((eqZero(v(0)) & (v(1) === 1)) | (eqZero(v(1)) & (v(0) === 1))))))
//                 geqZero(v(0)) & geqZero(v(1)) & (v(0) <= 1) & (v(1) <= 1)) ==>
//                (v(0) === v(1))))

      case _ =>
        a === b
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
      
      case Environment.Function(fun, SMTFunctionType(_, resultType)) => {
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

  private def translateBVUnaryOp(name : String, f : IFunction, args : Seq[Term])
                                : (IExpression, SMTType) = {
    checkArgNum(name, 1, args)
    val a0@(transArg0, type0) = translateTerm(args(0), 0)
    (f(i(extractBVModulus(name, type0, args(0))), asTerm(a0)), type0)
  }

  private def extractBVModulus(name : String, t : SMTType,
                               arg : Term) : IdealInt =
    extractBVModulusWidth(name, t, arg)._1

  private def extractBVModulusWidth(name : String, t : SMTType,
                                    arg : Term) : (IdealInt, Int) =
    t match {
      case t@SMTBitVec(w) =>
        (t.modulus, w)
      case _ =>
        throw new Parser2InputAbsy.TranslationException(
          name + " cannot be applied to " + (printer print arg)
        )
    }

  private def translateBVBinOp(name : String, f : IFunction, args : Seq[Term])
                              : (ITerm, SMTBitVec) = {
    checkArgNum(name, 2, args)
    val a0@(transArg0, type0) = translateTerm(args(0), 0)
    val a1@(transArg1, type1) = translateTerm(args(1), 0)
    val modulus = checkArgBVAgreement(name, args(0), type0, args(1), type1)
    (f(i(modulus), asTerm(a0), asTerm(a1)), type0.asInstanceOf[SMTBitVec])
  }

  private def translateBVBinPred(name : String, p : Predicate, args : Seq[Term])
                                : (IExpression, SMTType) = {
    checkArgNum(name, 2, args)
    val a0@(transArg0, type0) = translateTerm(args(0), 0)
    val a1@(transArg1, type1) = translateTerm(args(1), 0)
    val modulus = checkArgBVAgreement(name, args(0), type0, args(1), type1)
    (p(i(modulus), asTerm(a0), asTerm(a1)), SMTBool)
  }

  private def translateBVBinPred(name : String, args : Seq[Term],
                                 op : (Int, ITerm, ITerm) => IFormula)
                                : (IExpression, SMTType) = {
    checkArgNum(name, 2, args)
    val a0@(transArg0, type0) = translateTerm(args(0), 0)
    val a1@(transArg1, type1) = translateTerm(args(1), 0)
    val width = checkArgBVAgreementBits(name, args(0), type0, args(1), type1)
    (op(width, asTerm(a0), asTerm(a1)), SMTBool)
  }

  private def translateBVBinPredInv(name : String, p : Predicate, args : Seq[Term])
                                   : (IExpression, SMTType) = {
    checkArgNum(name, 2, args)
    val a0@(transArg0, type0) = translateTerm(args(0), 0)
    val a1@(transArg1, type1) = translateTerm(args(1), 0)
    val modulus = checkArgBVAgreement(name, args(0), type0, args(1), type1)
    (p(i(modulus), asTerm(a1), asTerm(a0)), SMTBool)
  }

  private def checkArgBVAgreementBits(name : String,
                                      arg0 : Term, type0 : SMTType,
                                      arg1 : Term, type1 : SMTType) : Int =
    (type0, type1) match {
      case (t@SMTBitVec(w1), SMTBitVec(w2)) if (w1 == w2) =>
        w1
      case _ =>
        throw new Parser2InputAbsy.TranslationException(
          name + " cannot be applied to " +
          (printer print arg0) + " and " + (printer print arg1)
        )
    }

  private def checkArgBVAgreement(name : String,
                                  arg0 : Term, type0 : SMTType,
                                  arg1 : Term, type1 : SMTType) : IdealInt =
    IdealInt(2) pow checkArgBVAgreementBits(name, arg0, type0, arg1, type1)

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

  private def translateTreeInterpolantSpec(exprs : ListSExpr)
                                          : List[Tree[Set[Int]]] = {
    var result = List[Tree[Set[Int]]]()

    for (p <- exprs) p match {
      case p : SymbolSExpr =>
        result =
          List(Tree(Set(partNameIndexes(
                          env.lookupPartName(printer print p.symbol_))),
                    result))
      case p : ParenSExpr
        if (!p.listsexpr_.isEmpty &&
            (printer print p.listsexpr_.head) == "and") => {
        val it = p.listsexpr_.iterator
        it.next
        val names = (for (s <- it) yield partNameIndexes(
                       env.lookupPartName(printer print s))).toSet
        result = List(Tree(names, result))
      }
      case p : ParenSExpr =>
        result = result ++ translateTreeInterpolantSpec(p.listsexpr_)
    }

    result    
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

    case c : RatConstant => {
      val v = IdealRat(c.rational_)
      if (v.denom.isOne) {
        warn("mapping rational literal " + c.rational_ + " to an integer literal")
        (i(v.num), SMTInteger)
      } else {
        warn("mapping rational literal " + c.rational_ + " to an integer constant")
        val const = new ConstantTerm("rat_" + c.rational_)
        addConstant(const, SMTInteger)
        (const, SMTInteger)
      }
    }
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

  private def translateDataCtorList(sortNames : Seq[String],
                                    resultSortNum : Int,
                                    constructorDecls : Seq[ConstructorDeclC])
                : (Seq[(String, ADT.CtorSignature)], Seq[Seq[SMTType]]) =
    (for (ctor <- constructorDecls) yield ctor match {
       case ctorDecl : ConstructorDecl => {
         val ctorName = asString(ctorDecl.symbol_)

         val (adtArgs, smtArgs) =
           (for (s <- ctorDecl.listselectordeclc_) yield {
              val selDecl = s.asInstanceOf[SelectorDecl]
              val selName = asString(selDecl.symbol_)

              val (adtSort, smtSort) =
                (sortNames indexOf (printer print selDecl.sort_)) match {
                  case -1 => {
                    val t = translateSort(selDecl.sort_)
                    (ADT.OtherSort(t.toSort), t)
                  }
                  case ind =>
                    // we don't have the actual ADT yet, so just put
                    // null for the moment
                    (ADT.ADTSort(ind), SMTADT(null, ind))
                }

              ((selName, adtSort), smtSort)
            }).unzip

          ((ctorName, ADT.CtorSignature(adtArgs, ADT.ADTSort(resultSortNum))),
           smtArgs)
       }

       case ctorDecl : NullConstructorDecl =>
         ((asString(ctorDecl.symbol_),
           ADT.CtorSignature(List(), ADT.ADTSort(resultSortNum))),
          List())
     }).unzip
  
  private def setupADT(sortNames : Seq[String],
                       allCtors : Seq[(Seq[(String, ADT.CtorSignature)],
                                       Seq[Seq[SMTType]])]) : Unit = {
        val adtCtors = (allCtors map (_._1)).flatten
        val datatype =
          new ADT (sortNames, adtCtors, Param.ADT_MEASURE(settings))

        val smtDataTypes =
          for (n <- 0 until sortNames.size) yield SMTADT(datatype, n)

        // add types to environment
        for (t <- smtDataTypes)
          env.addSort(t.toString, t)

        // add adt symbols to the environment
        val smtCtorFunctionTypes =
          for (((_, args), num) <- allCtors.zipWithIndex;
               args2 <- args.iterator;
               cleanedArgs = for (t <- args2) yield t match {
                 case SMTADT(null, n) => smtDataTypes(n)
                 case t => t
               })
          yield SMTFunctionType(cleanedArgs.toList, smtDataTypes(num))

        for ((f, smtType) <-
             datatype.constructors.iterator zip smtCtorFunctionTypes.iterator)
          env.addFunction(f, smtType)

        for ((sels, smtType) <-
               datatype.selectors.iterator zip smtCtorFunctionTypes.iterator;
             (f, arg) <-
               sels.iterator zip smtType.arguments.iterator) {
          env.addFunction(f, SMTFunctionType(List(smtType.result), arg))
        }

        // generate the is- queries as inlined functions
        for (((ctors, _), adtNum) <- allCtors.iterator.zipWithIndex;
             ctorIdFun = datatype ctorIds adtNum;
             ctorIdTerm = ctorIdFun(v(0));
             ((name, _), ctorNum) <- ctors.iterator.zipWithIndex) {
          val query = new IFunction("is-" + name, 1, true, true)
          env.addFunction(query,
                          SMTFunctionType(List(smtDataTypes(adtNum)), SMTBool))
          val body = ctorIdTerm === ctorNum
          functionDefs = functionDefs + (query -> (body, SMTBool))
        }
  }

  //////////////////////////////////////////////////////////////////////////////

  protected def registerRecFunctions(
                  funs : Seq[(IFunction, (IExpression, SMTType))]) : Unit =
    for ((f, body) <- funs) {
      // set up a defining equation and formula
      warn("assuming that recursive function " + f.name + " is partial")
      addAxiomEquation(f, body)
    }

  private def addAxiomEquation(f : IFunction,
                               body : (IExpression, SMTType)) : Unit = {
    val argNum = f.arity

    val lhs = IFunApp(f, for (i <- 1 to argNum) yield v(argNum - i))
    val axiom =
      if (argNum == 0)
        lhs === asTerm(body)
      else
        quan(Array.fill(argNum + 1){Quantifier.ALL}, 
          ITrigger(List(lhs),
            (lhs === v(argNum)) ==> (asTerm(body) === v(argNum))))

    addAxiom(axiom)
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
    case (IBoolLit(true), _) =>
      i(0)
    case (IBoolLit(false), _) =>
      i(1)
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

/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011-2021 Philipp Ruemmer <ph_r@gmx.net>
 *               2020      Zafer Esen <zafer.esen@gmail.com>
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
import ap.proof.certificates.{Certificate, DagCertificateConverter,
                              CertificatePrettyPrinter, CertFormula}
import ap.theories.{ExtArray, ADT, ModuloArithmetic, Theory, Heap}
import ap.theories.strings.{StringTheory, StringTheoryBuilder}
import ap.theories.rationals.Rationals
import ap.algebra.{PseudoRing, RingWithDivision, RingWithOrder,
                   RingWithIntConversions}
import ap.types.{MonoSortedIFunction, MonoSortedPredicate}
import ap.basetypes.{IdealInt, IdealRat, Tree}
import ap.parser.smtlib._
import ap.parser.smtlib.Absyn._
import ap.util.{Debug, Logic, PlainRange}

import scala.collection.mutable.{ArrayBuffer,
                                 HashMap => MHashMap, HashSet => MHashSet}

object SMTParser2InputAbsy {

  private val AC = Debug.AC_PARSER
  
  import Parser2InputAbsy._
  import IExpression.{Sort => TSort}

  abstract class SMTType {
    def toSort : TSort
  }
  case object SMTBool                              extends SMTType {
    def toSort = TSort.MultipleValueBool
  }
  case object SMTInteger                           extends SMTType {
    def toSort = TSort.Integer
  }
  case class  SMTReal(sort : TSort)                extends SMTType {
    def toSort = sort
  }
  case class  SMTArray(arguments : List[SMTType],
                       result : SMTType)           extends SMTType {
    val theory = ExtArray(arguments map { t => toNormalBool(t.toSort) },
                          toNormalBool(result.toSort))
    def toSort = theory.sort
  }
  case class SMTBitVec(width : Int)                extends SMTType {
    def toSort = ModuloArithmetic.UnsignedBVSort(width)
    val modulus = IdealInt(2) pow width
  }
  case class SMTADT(adt : ADT, sortNum : Int)      extends SMTType {
    def toSort = adt sorts sortNum
    override def toString = (adt sorts sortNum).name
  }
  case class SMTHeap(heap : Heap) extends SMTType {
    def toSort = heap.HeapSort
    override def toString = heap.HeapSort.name
  }
  case class SMTHeapAddress(heap : Heap) extends SMTType {
    def toSort = heap.AddressSort
    override def toString = heap.AddressSort.name
  }
  case class SMTUnint(sort : TSort)                extends SMTType {
    def toSort = sort
    override def toString = sort.name
  }

  case class SMTString(sort : TSort)               extends SMTType {
    def toSort = sort
    override def toString = "String"
  }
  case class SMTChar(sort : TSort)                 extends SMTType {
    def toSort = sort
    override def toString = "Char"
  }
  case class SMTRegLan(sort : TSort)               extends SMTType {
    def toSort = sort
    override def toString = "RegLan"
  }

  private def toNormalBool(s : TSort) : TSort = s match {
    case TSort.MultipleValueBool => TSort.Bool
    case s => s
  }

  case class SMTFunctionType(arguments : List[SMTType],
                             result : SMTType)

  val SMTBoolVariableType = SMTFunctionType(List(), SMTBool)

  sealed abstract class VariableType
  case class BoundVariable(varType : SMTType)              extends VariableType
  case class SubstExpression(e : IExpression, t : SMTType) extends VariableType
  
  private type Env =
    Environment[SMTType, VariableType,
                SMTFunctionType, SMTFunctionType, SMTType]
  
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
    private val SQuote : Int     = '\''
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
            case SQuote => {
              cbuf(off + read) = SQuote.toChar
              read = read + 1
              state = 2
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

          // process a double-quoted string "..."
          case 1 => input.read match {
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

          // process a single-quoted string '...'
          case 2 => input.read match {
            case SQuote => {
              cbuf(off + read) = SQuote.toChar
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

          // parse a quoted identified |...|
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

          // parse a comment ;...
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

          // output (
          case 5 => {
            cbuf(off + read) = LParen.toChar
            read = read + 1
            state = 6
          }

          // output )
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

  def asString(s : Sort) : String = s match {
    case s : IdentSort =>
      asString(s.identifier_)
    case s : CompositeSort =>
      asString(s.identifier_) + "_" +
      (s.listsort_ map (asString(_))).mkString("_")
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
        case s : NormalSymbol =>
          Some(s.normalsymbolt_)
        case s : QuotedSymbol =>
          Some(s.quotedsymbolt_.substring(1, s.quotedsymbolt_.length - 1))
        case _ =>
          None
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

        case t@IVariable(index)
          if (index >= subst.size) =>
          ShortCutResult(t shiftedBy shift)

        case IIntFormula(IIntRelation.EqZero, IVariable(index))
          if (index < subst.size && subst(index).isInstanceOf[IFormula]) =>
          ShortCutResult(subst(index))
          
        case t : IVariableBinder => {
          val (subst, shift) = substShift
          val newSubst = for (t <- subst) yield VariableShiftVisitor(t, 0, 1)
          UniSubArgs((IVariable(0, t.sort) :: newSubst, shift))
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
                                              SMTParser2InputAbsy.SMTFunctionType,
                                              SMTParser2InputAbsy.SMTFunctionType,
                                              SMTParser2InputAbsy.SMTType],
                           settings : ParserSettings,
                           prover : SimpleAPI)
      extends Parser2InputAbsy
          [SMTParser2InputAbsy.SMTType,
           SMTParser2InputAbsy.VariableType,
           SMTParser2InputAbsy.SMTFunctionType,
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
      override def report_error(message : String, info : Object) : Unit = {
        Console.err.println(message)
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

  private def incrementalNoExtract = incremental && !justStoreAssertions
  
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
    SizeVisitor(expr) > inlineSizeLimit

  private def checkIncremental(thing : String) =
    if (!incremental)
      throw new Parser2InputAbsy.TranslationException(
                  incrementalityMessage(thing, false))

  private def checkNotExtracting(thing : String) =
    if (justStoreAssertions)
      throw new Parser2InputAbsy.TranslationException(
                  thing + " cannot be handled when extracting assertions")

  private def checkIncrementalWarn(thing : String) : Boolean =
    if (incremental) {
      !justStoreAssertions
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
         env.addPredicate(p, SMTFunctionType(args.toList, SMTBool))
         true
       }
       case Some(_) => {
         warn("inconsistent definition of symbol " + name)
         false
       }
     })

  private def importProverSymbol(name : String) : Boolean = {
    import ap.types.SortedConstantTerm
    import SMTLineariser.{sort2SMTType, functionTypeFromSort, predTypeFromSort}

    incremental &&
    ((reusedSymbols get name) match {
       case None =>
         false
       case Some(c : ConstantTerm) => {
         env.addConstant(c, Environment.NullaryFunction,
                         sort2SMTType(SortedConstantTerm sortOf c)._1)
         true
       }
       case Some(f : IFunction) => functionTypeFromSort(f) match {
         case Some(t) => {
           env.addFunction(f, t)
           true
         }
         case None => {
           warn("cannot reconstruct type of symbol " + name)
           false
         }
       }
       case Some(p : Predicate) => predTypeFromSort(p) match {
         case Some(t) => {
           env.addPredicate(p, t)
           true
         }
         case None => {
           warn("cannot reconstruct type of symbol " + name)
           false
         }
       }
       case _ => {
         warn("cannot handle symbol " + name)
         false
       }
     })
  }

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
   * Limit beyond which let-expressions or functions are never inlined
   */
  private var inlineSizeLimit = 100
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
  /**
   * Parse recursive predicates over strings as transducers
   */  
  private var recFunctionsAsTransducers = false

  private def needCertificates : Boolean =
    genProofs || genInterpolants || genUnsatCores

  //////////////////////////////////////////////////////////////////////////////

  private val realAlgebra : PseudoRing with RingWithDivision
                                       with RingWithOrder
                                       with RingWithIntConversions = Rationals

  private val realType = SMTReal(realAlgebra.dom)

  //////////////////////////////////////////////////////////////////////////////

  private var stringTheoryBuilder =
    StringTheoryBuilder(Param.STRING_THEORY_DESC(settings))

  private val defaultStringAlphabetSize = 3 * (1 << 16)
  stringTheoryBuilder setAlphabetSize defaultStringAlphabetSize

  private var usingStrings = false

  private var transducerStringTheory : scala.Option[StringTheory] = None

  private def maybeParseTransducer[A](cont : => A) = {
    if (recFunctionsAsTransducers) {
      transducerStringTheory = stringTheoryBuilder.getTransducerTheory
      if (transducerStringTheory.isEmpty)
        warn("ignoring :parse-transducers, which is not supported by solver " +
             stringTheoryBuilder.name)
    }
    try {
      cont
    } finally {
      transducerStringTheory = None
    }
  }

  private def stringTheory = {
    usingStrings = true
    transducerStringTheory getOrElse stringTheoryBuilder.theory
  }

  private def charType =   SMTChar(stringTheory.CharSort)
  private def stringType = SMTString(stringTheory.StringSort)
  private def regexType =  SMTRegLan(stringTheory.RegexSort)

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

  private var lastReasonUnknown = ""

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Add a new frame to the settings stack; this in particular affects the
   * <code>Environment</code>.
   */
  protected def push : Unit = {
    checkIncremental("push")
    checkNotExtracting("push")
    pushState((functionDefs, nextPartitionNumber, partNameIndexes))
    prover.push
  }

  /**
   * Pop a frame from the settings stack.
   */
  protected def pop : Unit = {
    checkIncremental("pop")
    checkNotExtracting("pop")
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
    inlineSizeLimit      = 100
    totalityAxiom        = true
    functionalityAxiom   = true
    genProofs            = false
    genInterpolants      = false
    genUnsatCores        = false
    recFunctionsAsTransducers = false
    assumptions.clear
    functionDefs         = Map()
    nextPartitionNumber  = 0
    partNameIndexes      = Map()
    stringTheoryBuilder =
      StringTheoryBuilder(Param.STRING_THEORY_DESC(settings))
    stringTheoryBuilder setAlphabetSize defaultStringAlphabetSize
  }

  protected override def addAxiom(f : IFormula) : Unit =
    if (incremental) {
      prover setPartitionNumber -1
      prover addAssertion PartNameEliminator(f)
    } else {
      super.addAxiom(f)
    }

  protected override def addTheory(t : Theory) : Unit = {
    if (incremental)
      prover addTheory t
    super.addTheory(t)
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

  private val predTypeFunction =
    (p : Predicate) => (env lookupSymPartial p.name) match {
      case Some(Environment.Predicate(_, _, t)) => Some(t)
      case _ => None
    }

  private def smtLinearise(f : IFormula) : Unit =
    SMTLineariser(f, constantTypeFunction,
                  functionTypeFunction, predTypeFunction)
  
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
        handleNumAnnot(":inline-size-limit", annot) {
          value => inlineSizeLimit = value.intValueSafe
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
        } ||
        handleBooleanAnnot(":parse-transducers", annot) {
          value => recFunctionsAsTransducers = value
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

        val name = asString(cmd.symbol_)

        if (cmd.numeral_.toInt != 0) {
          warn("treating sort constructor " + name + " as int")
        } else {
          val sort = TSort.createUninterpretedSort(name)
          addTheory(sort.theory)
          env.addSort(name, SMTUnint(sort))
        }

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

      case cmd : HeapDeclCommand => {
        ensureEnvironmentCopy

        val heapSortName = asString(cmd.identifier_1)
        val addressSortName = asString(cmd.identifier_2)
        val objectSortName = asString(cmd.identifier_3)

        val ADTSortNames =
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
            translateHeapCtorList(ADTSortNames, addressSortName, sortNum,
              decl.listconstructordeclc_)
          }

        setupHeap(heapSortName, addressSortName, objectSortName, ADTSortNames,
                  allCtors, cmd.term_)

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
              env.addPredicate(p, SMTFunctionType(args.toList, SMTBool))
              if (incremental)
                prover.addRelation(p)
            }
          } else if (res != SMTBool) {
            // use a constant
            addConstant(res.toSort newConstant name, res)
          } else {
            // use a nullary predicate (propositional variable)
            val p = new Predicate(name, 0)
            env.addPredicate(p, SMTBoolVariableType)
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
            env.addPredicate(p, SMTBoolVariableType)
            if (incremental)
              prover.addRelation(p)
          }
        }

        success
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : FunctionDefCommand => {
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
                                    true, !args.isEmpty)
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

      case cmd : ConstDefCommand => {
        val name = asString(cmd.symbol_)
        val resType = translateSort(cmd.sort_)
        
        // parse the definition of the definition
        val body@(_, bodyType) = translateTerm(cmd.term_, 0)

        if (bodyType != resType)
          throw new Parser2InputAbsy.TranslationException(
              "Body of constant definition has wrong type")

        // use a real function (TODO: better introduce just a constant?)
        val f = MonoSortedIFunction(name, List(), resType.toSort, true, false)
        env.addFunction(f, SMTFunctionType(List(), resType))
    
        if (inlineDefinedFuns && !neverInline(body._1)) {
          functionDefs = functionDefs + (f -> body) 
        } else if (incremental) {
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

      case cmd : RecFunctionDefCommand => maybeParseTransducer {
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

      case cmd : RecFunctionDefsCommand => maybeParseTransducer {
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
        if (incrementalNoExtract) {
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

      case cmd : SimplifyCommand => {
        checkIncremental("simplify")
        checkNotExtracting("simplify")
        val f = asFormula(translateTerm(cmd.term_, -1))
        try {
          val simpF = prover.withTimeout(timeoutPer) { prover simplify f }
          smtLinearise(simpF)
          println
        } catch {
          case SimpleAPI.TimeoutException =>
            error("timeout while simplifying expression")
        }
      }

      //////////////////////////////////////////////////////////////////////////

      case cmd : CheckSatCommand => if (incrementalNoExtract) try {
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
                  for (interpolant <- interpolants) {
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
        val doConfirm = incremental && printSuccess
        reset
        // We have to do this, because incremental and printSuccess are...also
        // reset.
        if (doConfirm)
          println("success")
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
      case PlainIdentifier("Real") =>
        realType
      case IndexedIdentifier("BitVec", width) =>
        SMTBitVec(width.toInt)
      case PlainIdentifier("String") =>
        stringType
      case PlainIdentifier("RegLan") =>
        regexType
      case PlainIdentifier("Char") =>
        charType
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
                          if (a.annotattribute_ == ":pattern");
                          trigs = translateTriggerAttr(a.attrparam_);
                          if !trigs.isEmpty)
                     yield trigs

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
                                            List(TSort.Integer),
                                            TSort.MultipleValueBool,
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
        case Seq(SMTBool, _ : SMTReal, _) | Seq(SMTBool, _, _ : SMTReal) =>
          (ITermITE(asFormula(transArgs(0)),
                    asRealTerm("ite", transArgs(1)),
                    asRealTerm("ite", transArgs(2))),
           realType)
        case Seq(SMTBool, t1, t2) => {
          if (t1 != t2)
            throw new TranslationException(
              "branches of ite need to have consistent type, not " +
              t1 + " and " + t2)
          (ITermITE(asFormula(transArgs(0)),
                    asTerm(transArgs(1)), asTerm(transArgs(2))),
           t1)
        }
      }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    // Hardcoded predicates (which might also operate on booleans)
    
    case PlainSymbol("=") => {
      val transArgs = for (a <- args) yield translateTerm(a, 0)
      (if (transArgs forall (_._2 == SMTBool)) {
         and(for (Seq(a, b) <- (transArgs map (asFormula(_))) sliding 2)
               yield (a <===> b))
       } else {
         val (termArgs, typ) = asRealIntOtherTerms("=", transArgs)
         and(for (Seq(a, b) <- termArgs sliding 2)
               yield translateEq(a, b, typ, polarity))
       },
       SMTBool)
    }
    
    case PlainSymbol("distinct") => {
      val transArgs = for (a <- args) yield translateTerm(a, 0)
      (if (transArgs forall (_._2 == SMTBool))
         transArgs.length match {
           case 0 | 1 => true
           case 2 => ~(asFormula(transArgs(0)) <===> asFormula(transArgs(1)))
           case _ => false
         }
       else {
         val (termArgs, typ) = asRealIntOtherTerms("distinct", transArgs)
         // TODO: special case for arrays?
         distinct(termArgs)
       }, SMTBool)
    }
    
    case PlainSymbol("<=") =>
      (translateChainableRealIntPred("<=", args, _ <= _, realAlgebra.leq _),
       SMTBool)
    case PlainSymbol("<") =>
      (translateChainableRealIntPred("<",  args, _ < _,  realAlgebra.lt _),
       SMTBool)
    case PlainSymbol(">=") =>
      (translateChainableRealIntPred(">=", args, _ >= _, realAlgebra.geq _),
       SMTBool)
    case PlainSymbol(">") =>
      (translateChainableRealIntPred(">",  args, _ > _,  realAlgebra.gt _),
       SMTBool)
    
    case IndexedSymbol("divisible", denomStr) => {
      checkArgNum("divisible", 1, args)
      val denom = i(IdealInt(denomStr))
      val num = VariableShiftVisitor(asTerm(translateTerm(args.head, 0)), 0, 1)
      (ex(num === v(0) * denom), SMTBool)
    }
      
    ////////////////////////////////////////////////////////////////////////////
    // Hardcoded integer and real operations

    case PlainSymbol("+") =>
      asRealIntTerms("+", flatten("+", args)) match {
        case (terms, SMTInteger) =>
          (sum(terms), SMTInteger)
        case (terms, SMTReal(_)) =>
          (realAlgebra.summation(terms : _*), realType)
      }

    case PlainSymbol(op@("-" | "~")) if (args.length == 1) => {
      if (op == "~" && !tildeWarning) {
        warn("interpreting \"~\" as unary minus, like in SMT-LIB 1")
        tildeWarning = true
      }
      asRealIntTerm(op, args.head) match {
        case (t, SMTInteger) => (-t, SMTInteger)
        case (t, SMTReal(_)) => (realAlgebra.minus(t), realType)
      }
    }

    case PlainSymbol("-") =>
      asRealIntTerms("-", args) match {
        case (terms, SMTInteger) =>
          (terms.head - sum(terms.tail), SMTInteger)
        case (terms, SMTReal(_)) =>
          (realAlgebra.minus(terms.head,
                             realAlgebra.summation(terms.tail : _*)), realType)
      }

    case PlainSymbol("*") =>
      asRealIntTerms("*", flatten("*", args)) match {
        case (terms, SMTInteger) =>
          (terms reduceLeft (mult _), SMTInteger)
        case (terms, SMTReal(_)) =>
          (terms reduceLeft (realAlgebra.mul _), realType)
      }

    case PlainSymbol("div") => {
      checkArgNum("div", 2, args)
      val Seq(num, denom) = for (a <- args) yield asTerm(translateTerm(a, 0))
      (mulTheory.eDiv(num, denom), SMTInteger)
    }
       
    case PlainSymbol("mod") => {
      checkArgNum("mod", 2, args)
      val Seq(num, denom) = for (a <- args) yield asTerm(translateTerm(a, 0))
/*      denom match {
        case IIntLit(denomVal) if denomVal.signum > 0 =>
          (ModuloArithmetic.cast2Interval(IdealInt.ZERO, denomVal - 1, num),
           SMTInteger)
        case denom => */
          (mulTheory.eMod(num, denom), SMTInteger)
//      }
    }

    case PlainSymbol("abs") => {
      checkArgNum("abs", 1, args)
      (abs(asTerm(translateTerm(args.head, 0))), SMTInteger)
    }

    case PlainSymbol("/") => {
      checkArgNum("/", 2, args)
      (realAlgebra.div(asRealTerm("/", args(0)),
                       asRealTerm("/", args(1))),
       realType)
    }

    case PlainSymbol("to_real") => {
      checkArgNum("to_real", 1, args)
      (asRealTerm("to_real", args(0)), realType)
    }
      
    case PlainSymbol("to_int") => {
      checkArgNum("to_int", 1, args)
      (realAlgebra.ring2int(asRealTerm("to_int", args(0))), SMTInteger)
    }
      
    case PlainSymbol("is_int") => {
      checkArgNum("is_int", 1, args)
      (realAlgebra.isInt(asRealTerm("to_int", args(0))), SMTBool)
    }
      
    ////////////////////////////////////////////////////////////////////////////
    // Array operations
    
    case PlainSymbol("select") => {
      val transArgs = for (a <- args) yield translateTerm(a, 0)
      transArgs.head._2 match {
        case s@SMTArray(_, resultType) =>
          (IFunApp(s.theory.select,
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
          (IFunApp(s.theory.store,
                   for (a <- transArgs) yield asTerm(a)),
           s)
        case s =>
          throw new Parser2InputAbsy.TranslationException(
            "store has to be applied to an array expression, not " + s)
      }
    }

    case CastSymbol("const", sort) =>
      translateSort(sort) match {
        case s : SMTArray => {
          checkArgNum("const", 1, args)
          val transArg = translateTerm(args(0), 0)
          if (transArg._2 != s.result)
            throw new Parser2InputAbsy.TranslationException(
              "const has to be applied to an expression of the object type")
          (s.theory.const(asTerm(transArg)), s)
        }
        case _ =>
          throw new Parser2InputAbsy.TranslationException(
            "const can only be used with array types")
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
      val width0 = extractBVWidth("concat", type0, args(0))
      val width1 = extractBVWidth("concat", type1, args(1))
      (ModuloArithmetic.bv_concat(i(width0), i(width1), asTerm(a0), asTerm(a1)),
       SMTBitVec(width0 + width1))
    }

    case IndexedSymbol("extract", beginStr, endStr) => {
      checkArgNum("extract", 1, args)
      val begin = beginStr.toInt
      val end = endStr.toInt
      val a0@(transArg0, type0) = translateTerm(args(0), 0)
      val width0 = extractBVWidth("extract", type0, args(0))
      val resType = SMTBitVec(begin - end + 1)
      (ModuloArithmetic.bv_extract(i(begin),
        i(end),
        asTerm(a0)),
        resType)
    }

    case PlainSymbol("bvnot") =>
      translateBVUnaryOp("bvnot", ModuloArithmetic.bv_not, args)
    case PlainSymbol("bvneg") =>
      translateBVUnaryOp("bvneg", ModuloArithmetic.bv_neg, args)

    case PlainSymbol("bvand") =>
      translateBVNAryOp("bvand",  ModuloArithmetic.bv_and, args)
    case PlainSymbol("bvor") =>
      translateBVNAryOp("bvor",   ModuloArithmetic.bv_or, args)
    case PlainSymbol("bvadd") =>
      translateBVNAryOp("bvadd",  ModuloArithmetic.bv_add, args)
    case PlainSymbol("bvsub") =>
      translateBVBinOp("bvsub",  ModuloArithmetic.bv_sub, args)
    case PlainSymbol("bvmul") =>
      translateBVNAryOp("bvmul",  ModuloArithmetic.bv_mul, args)
    case PlainSymbol("bvudiv") =>
      translateBVBinOp("bvudiv", ModuloArithmetic.bv_udiv, args)
    case PlainSymbol("bvsdiv") =>
      translateBVBinOp("bvsdiv", ModuloArithmetic.bv_sdiv, args)
    case PlainSymbol("bvurem") =>
      translateBVBinOp("bvurem", ModuloArithmetic.bv_urem, args)
    case PlainSymbol("bvsrem") =>
      translateBVBinOp("bvsrem", ModuloArithmetic.bv_srem, args)
    case PlainSymbol("bvsmod") =>
      translateBVBinOp("bvsmod", ModuloArithmetic.bv_smod, args)
    case PlainSymbol("bvshl") =>
      translateBVBinOp("bvshl",  ModuloArithmetic.bv_shl, args)
    case PlainSymbol("bvlshr") =>
      translateBVBinOp("bvlshr", ModuloArithmetic.bv_lshr, args)
    case PlainSymbol("bvashr") =>
      translateBVBinOp("bvashr", ModuloArithmetic.bv_ashr, args)
    case PlainSymbol("bvxor") =>
      translateBVBinOp("bvxor",  ModuloArithmetic.bv_xor, args)
    case PlainSymbol("bvxnor") =>
      translateBVBinOp("bvxnor", ModuloArithmetic.bv_xnor, args)

    case PlainSymbol("bvnand") => {
      val (t, tp) = translateBVBinOp("bvnand", ModuloArithmetic.bv_and, args)
      (ModuloArithmetic.bv_not(i(tp.width), t), tp)
    }
    case PlainSymbol("bvnor") => {
      val (t, tp) = translateBVBinOp("bvnor", ModuloArithmetic.bv_or, args)
      (ModuloArithmetic.bv_not(i(tp.width), t), tp)
    }

    case PlainSymbol("bvcomp") => {
      checkArgNum("bvcomp", 2, args)
      val a0@(transArg0, type0) = translateTerm(args(0), 0)
      val a1@(transArg1, type1) = translateTerm(args(1), 0)
      val bits = checkArgBVAgreement("bvcomp", args(0), type0, args(1), type1)
      (ModuloArithmetic.bv_comp(i(bits), asTerm(a0), asTerm(a1)), SMTBitVec(1))
    }

    case PlainSymbol("bvult") =>
      translateBVBinPred("bvult", ModuloArithmetic.bv_ult, args)
    case PlainSymbol("bvule") =>
      translateBVBinPred("bvule", ModuloArithmetic.bv_ule, args)
    case PlainSymbol("bvslt") =>
      translateBVBinPred("bvslt", ModuloArithmetic.bv_slt, args)
    case PlainSymbol("bvsle") =>
      translateBVBinPred("bvsle", ModuloArithmetic.bv_sle, args)

    case PlainSymbol("bvugt") =>
      translateBVBinPredInv("bvugt", ModuloArithmetic.bv_ult, args)
    case PlainSymbol("bvuge") =>
      translateBVBinPredInv("bvuge", ModuloArithmetic.bv_ule, args)
    case PlainSymbol("bvsgt") =>
      translateBVBinPredInv("bvsgt", ModuloArithmetic.bv_slt, args)
    case PlainSymbol("bvsge") =>
      translateBVBinPredInv("bvsge", ModuloArithmetic.bv_sle, args)

    case IndexedSymbol("zero_extend", digitsStr) => {
      checkArgNum("zero_extend", 1, args)
      val digits = digitsStr.toInt
      val (transArg0, type0) = translateTerm(args(0), 0)
      val width = extractBVWidth("zero_extend", type0, args(0))
      (transArg0, SMTBitVec(width + digits))
    }

    case IndexedSymbol("sign_extend", digitsStr) => {
      checkArgNum("sign_extend", 1, args)
      val digits = digitsStr.toInt
      val a0@(transArg0, type0) = translateTerm(args(0), 0)
      val width = extractBVWidth("sign_extend", type0, args(0))
      (ModuloArithmetic.cast2UnsignedBV(width + digits,
         ModuloArithmetic.cast2SignedBV(width, asTerm(a0))),
       SMTBitVec(width + digits))
    }

    case PlainSymbol("bv2nat") | IndexedSymbol("bv2nat", _) => {
      checkArgNum("bv2nat", 1, args)
      val a0@(_, type0) = translateTerm(args(0), 0)
      extractBVWidth("bv2nat", type0, args(0))
      (asTerm(a0), SMTInteger)
    }

    case PlainSymbol("bv2int") | IndexedSymbol("bv2int", _) => {
      checkArgNum("bv2int", 1, args)
      val a0@(_, type0) = translateTerm(args(0), 0)
      val width0 = extractBVWidth("bv2int", type0, args(0))
      (ModuloArithmetic.cast2SignedBV(width0, asTerm(a0)), SMTInteger)
    }

    case IndexedSymbol(op@("nat2bv" | "int2bv"), digitsStr) => {
      checkArgNum(op, 1, args)
      val digits = digitsStr.toInt
      (ModuloArithmetic.cast2UnsignedBV(digits,
                                        asTerm(translateTerm(args(0), 0))),
       SMTBitVec(digits))
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
    // String operations

    case IndexedSymbol("char", valStr) =>
      (stringTheory int2Char IdealInt(valStr), charType)

    case PlainSymbol("str.empty") =>
      (translateStringFun(stringTheory.str_empty, args, List()), stringType)
    case PlainSymbol("str.cons") =>
      (translateStringFun(stringTheory.str_cons, args,
                          List(charType, stringType)), stringType)

    case PlainSymbol("str.head") =>
      (translateStringFun(stringTheory.str_head, args,
                          List(stringType)), charType)
    case PlainSymbol("str.head_code") =>
      (translateStringFun(stringTheory.str_head_code, args,
                          List(stringType)), SMTInteger)
    case PlainSymbol("str.tail") =>
      (translateStringFun(stringTheory.str_tail, args,
                          List(stringType)), stringType)

    case PlainSymbol("str.from.char" | "str.from_char") =>
      (translateStringFun(stringTheory.str_from_char, args,
                          List(charType)), stringType)

    case PlainSymbol("str.from_code") =>
      (translateStringFun(stringTheory.str_from_code, args,
                          List(SMTInteger)), stringType)
    case PlainSymbol("str.to_code") =>
      (translateStringFun(stringTheory.str_to_code, args,
                          List(stringType)), SMTInteger)

    case PlainSymbol("str.++") =>
      (translateNAryStringFun(stringTheory.str_++, args,
                              stringType), stringType)
    case PlainSymbol("str.len") =>
      (translateStringFun(stringTheory.str_len, args,
                          List(stringType)), SMTInteger)

    case PlainSymbol("str.to.int" | "str.to_int") =>
      (translateStringFun(stringTheory.str_to_int, args,
                          List(stringType)), SMTInteger)
    case PlainSymbol("int.to.str" | "int.to_str" | "str.from_int") =>
      (translateStringFun(stringTheory.int_to_str, args,
                          List(SMTInteger)), stringType)

    // str.<

    case PlainSymbol("str.to_re" | "str.to-re" | "str.to.re") =>
      (translateStringFun(stringTheory.str_to_re, args,
                          List(stringType)), regexType)
    case PlainSymbol("re.from.str" | "re.from_str") =>
      (translateStringFun(stringTheory.re_from_str, args,
                          List(stringType)), regexType)

    case PlainSymbol("str.in_re" | "str.in-re" | "str.in.re") =>
      translateStringPred(stringTheory.str_in_re, args,
                          List(stringType, regexType))
    case PlainSymbol("re.none") =>
      (translateStringFun(stringTheory.re_none, args,
                          List()), regexType)
    case PlainSymbol("re.eps") =>
      (translateStringFun(stringTheory.re_eps, args,
                          List()), regexType)
    case PlainSymbol("re.all") =>
      (translateStringFun(stringTheory.re_all, args,
                          List()), regexType)
    case PlainSymbol("re.allchar") =>
      (translateStringFun(stringTheory.re_allchar, args,
                          List()), regexType)
    case PlainSymbol("re.charrange") =>
      (translateStringFun(stringTheory.re_charrange, args,
                          List(charType, charType)), regexType)
    case PlainSymbol("re.range") =>
      (translateStringFun(stringTheory.re_range, args,
                          List(stringType, stringType)), regexType)
    case PlainSymbol("re.++") =>
      (translateNAryStringFun(stringTheory.re_++, args,
                              regexType), regexType)
    case PlainSymbol("re.union") =>
      (translateNAryStringFun(stringTheory.re_union, args,
                              regexType), regexType)
    case PlainSymbol("re.inter") =>
      (translateNAryStringFun(stringTheory.re_inter, args,
                              regexType), regexType)
    case PlainSymbol("re.diff") =>
      (translateNAryStringFun(stringTheory.re_diff, args,
                              regexType), regexType)
    
    case PlainSymbol("re.*") =>
      (translateStringFun(stringTheory.re_*, args,
                          List(regexType)), regexType)

    case PlainSymbol("str.<=") =>
      translateStringPred(stringTheory.str_<=, args,
                          List(stringType, stringType))
    case PlainSymbol("str.at") =>
      (translateStringFun(stringTheory.str_at, args,
                          List(stringType, SMTInteger)), stringType)
    case PlainSymbol("str.char") =>
      (translateStringFun(stringTheory.str_char, args,
                          List(stringType, SMTInteger)), charType)

    case PlainSymbol("str.substr") =>
      (translateStringFun(stringTheory.str_substr, args,
                          List(stringType, SMTInteger, SMTInteger)), stringType)

    case PlainSymbol("str.prefixof") =>
      translateStringPred(stringTheory.str_prefixof, args,
                          List(stringType, stringType))
    case PlainSymbol("str.suffixof") =>
      translateStringPred(stringTheory.str_suffixof, args,
                          List(stringType, stringType))
    case PlainSymbol("str.contains") =>
      translateStringPred(stringTheory.str_contains, args,
                          List(stringType, stringType))

    case PlainSymbol("str.indexof") =>
      (translateStringFun(stringTheory.str_indexof, args,
                          List(stringType, stringType, SMTInteger)), SMTInteger)

    case PlainSymbol("str.replace") =>
      (translateStringFun(stringTheory.str_replace, args,
                          List(stringType, stringType, stringType)), stringType)
    case PlainSymbol("str.replacere" | "str.replace_re") =>
      (translateStringFun(stringTheory.str_replacere, args,
                          List(stringType, regexType, stringType)), stringType)

    case PlainSymbol("str.replaceall" | "str.replace_all") =>
      (translateStringFun(stringTheory.str_replaceall, args,
                          List(stringType, stringType, stringType)), stringType)

    case PlainSymbol("str.replaceallre" | "str.replace_re_all") =>
      (translateStringFun(stringTheory.str_replaceallre, args,
                          List(stringType, regexType, stringType)), stringType)

    case PlainSymbol("str.is-digit") =>
      translateStringPred(stringTheory.char_is_digit, args, List(charType))

    case PlainSymbol("re.+") =>
      (translateStringFun(stringTheory.re_+, args,
                          List(regexType)), regexType)
    case PlainSymbol("re.opt") =>
      (translateStringFun(stringTheory.re_opt, args,
                          List(regexType)), regexType)
    case PlainSymbol("re.comp" | "re.complement") =>
      (translateStringFun(stringTheory.re_comp, args,
                          List(regexType)), regexType)

    case IndexedSymbol("re.^", n) => {
      val Seq(arg) = translateStringArgs("re.^", args, List(regexType))
      val num = n.toInt
      (stringTheory.re_loop(num, num, arg), regexType)
    }
    case IndexedSymbol("re.loop", n1, n2) => {
      val Seq(arg) = translateStringArgs("re.loop", args, List(regexType))
      (stringTheory.re_loop(n1.toInt, n2.toInt, arg), regexType)
    }

    case PlainSymbol("char.code") =>
      (stringTheory.char2Int(
         translateStringArgs("char.code", args, List(charType)).head),
       SMTInteger)
    case PlainSymbol("char.from-int") =>
      (stringTheory.int2Char(
         translateStringArgs("char.from-int", args, List(SMTInteger)).head),
       charType)

    // Function seq.unit provided by Z3
    case PlainSymbol("seq.unit") => {
      checkArgNum("seq.unit", 1, args)
      (stringTheory.str_from_code(asTerm(translateTerm(args(0), 0))),
       stringType)
    }

    case PlainSymbol(id)
      if usingStrings && (stringTheory.extraOps contains id) =>
      stringTheory.extraOps(id) match {
        case Left(f : MonoSortedIFunction) => {
          val argTypes = f.argSorts map (stringSort2SMTType _)
          val resType = stringSort2SMTType(f.resSort)
          (translateStringFun(f, args, argTypes), resType)
        }
        case Right(p : MonoSortedPredicate) => {
          val argTypes = p.argSorts map (stringSort2SMTType _)
          translateStringPred(p, args, argTypes)
        }
        case u =>
          throw new TranslationException("cannot handle string operator " + u)
      }

    case IndexedSymbol(id, indexes @ _*)
      if usingStrings &&
         (stringTheory.extraIndexedOps contains (id, indexes.size)) => {
      val IndNum = indexes.size
      stringTheory.extraIndexedOps((id, IndNum)) match {
        case Left(f : MonoSortedIFunction) => {
          val argTypes   = f.argSorts.drop(IndNum) map (stringSort2SMTType _)
          val stringArgs = translateStringArgs(f.name, args, argTypes)
          val indexArgs  = for (ind <- indexes) yield i(IdealInt(ind))
          val resType    = stringSort2SMTType(f.resSort)
          (IFunApp(f, indexArgs ++ stringArgs), resType)
        }
        case Right(p : MonoSortedPredicate) => {
          val argTypes   = p.argSorts.drop(IndNum) map (stringSort2SMTType _)
          val stringArgs = translateStringArgs(p.name, args, argTypes)
          val indexArgs  = for (ind <- indexes) yield i(IdealInt(ind))
          (IAtom(p, indexArgs ++ stringArgs), SMTBool)
        }
        case u =>
          throw new TranslationException("cannot handle string operator " + u)
      }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Heap operations

    case PlainSymbol(name@"valid") =>
      extractHeap(args) match {
        case Some((heapTerm, heapTheory)) => {
          val argTypes  = List(SMTHeapAddress(heapTheory))
          val transArgs = for (a <- args.tail) yield translateTerm(a, 0)

          if (argTypes != (transArgs map (_._2)))
            throw new TranslationException(
              name + " cannot be applied to arguments of type " +
              heapTheory.HeapSort + ", " +
              (transArgs map (_._2) mkString ", "))

          (IAtom(heapTheory.isAlloc,
                 List(heapTerm) ++ (transArgs map (asTerm(_)))),
           SMTBool)
        }
        case None =>
          unintFunApp(name, sym, args, polarity)
      }

    case PlainSymbol(name@"alloc") =>
      translateHeapFun(_.alloc,
                       args,
                       heap => List(objectType(heap)),
                       heap => SMTADT(heap.AllocResADT, 0)).getOrElse(
      unintFunApp(name, sym, args, polarity))

    case PlainSymbol(name@"read") =>
      translateHeapFun(_.read,
                       args,
                       heap => List(SMTHeapAddress(heap)),
                       objectType(_)).getOrElse(
      unintFunApp(name, sym, args, polarity))

    case PlainSymbol(name@"write") =>
      translateHeapFun(_.write,
                       args,
                       heap => List(SMTHeapAddress(heap), objectType(heap)),
                       SMTHeap(_)).getOrElse(
      unintFunApp(name, sym, args, polarity))

    ////////////////////////////////////////////////////////////////////////////
    // Declared symbols from the environment
    case id => unintFunApp(asString(id), sym, args, polarity)
  }

  private def translateEq(a : ITerm, b : ITerm, t : SMTType,
                          polarity : Int) : IFormula =
    t match {
      /*
      case s@SMTArray(argTypes, resType) if (polarity > 0) => {
        val arity = argTypes.size
        val theory = s.theory
        val args = (for (n <- 0 until arity) yield v(n))
        val matrix =
          translateEq(IFunApp(theory.select,
                              List(VariableShiftVisitor(a, 0, arity)) ++ args),
                      IFunApp(theory.select,
                              List(VariableShiftVisitor(b, 0, arity)) ++ args),
                      resType, polarity)

        quan(for (_ <- 0 until arity) yield Quantifier.ALL, matrix)
      }
       */

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

  private def lookupSym(name : String) : SMTParser2InputAbsy.Env#DSym =
    if (reusedSymbols == null) {
      env lookupSym name
    } else {
      (env lookupSymPartial name) match {
        case Some(res) =>
          res
        case None => {
          importProverSymbol(name)
          env lookupSym name
        }
      }
    }

  private def unintFunApp(id : String,
                          sym : SymbolRef, args : Seq[Term], polarity : Int)
                         : (IExpression, SMTType) =
    lookupSym(id) match {
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
        (v(i, t.toSort), t)
        
      case Environment.Variable(i, SubstExpression(e, t)) =>
        (e, t)

      case r =>
        throw new TranslationException("did not expect " + r)
    }
  
  //////////////////////////////////////////////////////////////////////////////

  private def asRealTerm(op : String, t : Term) : ITerm =
    asRealTerm(op, translateTerm(t, 0))

  private def asRealTerm(op : String,
                         expr : (IExpression, SMTType)) : ITerm = expr match {
    case (expr : ITerm, SMTReal(_)) =>
      expr
    case (expr : ITerm, SMTInteger) =>
      realAlgebra.int2ring(expr)
    case (expr, _) =>
      throw new Parser2InputAbsy.TranslationException(
                   op + " expects a term of type Real, not " + expr)
  }

  private def asRealIntTerm(op : String, t : Term)
                         : (ITerm, SMTType) = translateTerm(t, 0) match {
    case p@(_, SMTReal(_)) =>
      (asTerm(p), realType)
    case p@(_, SMTInteger) =>
      (asTerm(p), SMTInteger)
    case (expr, _) =>
      throw new Parser2InputAbsy.TranslationException(
                   op + " expects a term of type Int or Real, not " +
                   (printer print t))
  }

  private def asRealIntTerms(op : String,
                             args : Seq[Term]) : (Seq[ITerm], SMTType) = {
    val transArgs = for (s <- args) yield translateTerm(s, 0)
    if (transArgs.isEmpty) {
      (List(), SMTInteger)
    } else if (transArgs exists { case (_, SMTReal(_)) => true
                                  case _ => false }) {
      (for (p <- transArgs) yield asRealTerm(op, p), realType)
    } else {
      (for (p <- transArgs) yield asTerm(p, SMTInteger), SMTInteger)
    }
  }

  private def asRealIntOtherTerms(op : String,
                                  args : Seq[(IExpression, SMTType)])
                               : (Seq[ITerm], SMTType) =
    if (args exists (_._2.isInstanceOf[SMTReal])) {
      (args map (asRealTerm(op, _)), realType)
    } else {
      val typ = args.head._2
      if (args exists (_._2 != typ))
        throw new Parser2InputAbsy.TranslationException(
          op + " cannot be applied to " + (args map (_._1) mkString ", "))
      (args map asTerm, typ)
    }

  //////////////////////////////////////////////////////////////////////////////

  private def translateStringFun(f : IFunction,
                                 args : Seq[Term],
                                 argTypes : Seq[SMTType]) : IExpression =
    IFunApp(f, translateStringArgs(f.name, args, argTypes))

  private def translateStringArgs(name : String,
                                  args : Seq[Term],
                                  argTypes : Seq[SMTType]) : Seq[ITerm] = {
    val transArgs = for (a <- args) yield translateTerm(a, 0)
    if (argTypes != (transArgs map (_._2)))
      throw new TranslationException(
        name + " cannot be applied to arguments of type " +
        (transArgs map (_._2) mkString ", "))
    transArgs map (asTerm(_))
  }

  private def translateNAryStringFun(f : IFunction,
                                     args : Seq[Term],
                                     argType : SMTType) : IExpression = {
    val transArgs = for (a <- args) yield translateTerm(a, 0)
    if (!(transArgs forall { case (_, t) => t == argType }))
      throw new TranslationException(
        f.name + " cannot be applied to arguments of type " +
        (transArgs map (_._2) mkString ", "))
    (transArgs.iterator map (asTerm(_))) reduceLeft {
       (s, t) => f(s, t)
     }
  }

  private def translateStringPred(p : Predicate,
                                  args : Seq[Term],
                                  argTypes : Seq[SMTType])
                               : (IExpression, SMTType) = {
    val transArgs = for (a <- args) yield translateTerm(a, 0)
    if (argTypes != (transArgs map (_._2)))
      throw new TranslationException(
        p.name + " cannot be applied to arguments of type " +
        (transArgs map (_._2) mkString ", "))
    (IAtom(p, transArgs map (asTerm(_))), SMTBool)
  }

  private def stringSort2SMTType(s : TSort) : SMTType = {
    val t = stringTheory
    s match {
      case t.CharSort   => charType
      case t.RegexSort  => regexType
      case t.StringSort => stringType
      case s => throw new TranslationException("" + s + " is not a string sort")
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Translate a set of recursive functions to a letter-to-letter transducer
   * over strings.
   */
  private def recFunctions2Transducer(funs : Seq[(IFunction, IFormula)])
                                       : StringTheoryBuilder.SymTransducer = {
    import StringTheoryBuilder._

    val theory = stringTheory
    import theory.{str_empty, str_head, str_head_code, str_tail}

    val stateFuns = funs map (_._1)
    val tracks = stateFuns.head.arity

    object StrHeadReplacer extends ContextAwareVisitor[Unit, IExpression] {
      def postVisit(t : IExpression, ctxt : Context[Unit],
                    subres : Seq[IExpression]) : IExpression = t match {
        case IFunApp(`str_head` | `str_head_code`, Seq(IVariable(ind)))
          if ind >= ctxt.binders.size &&
             ind - ctxt.binders.size < tracks =>
          IVariable(tracks - ind - 1 + 2 * ctxt.binders.size)
        case _ =>
          t update subres
      }
    }

    if (!(stateFuns forall { f => f.arity == tracks }))
      throw new TranslationException(
        "Can only handle transducers with a uniform number of tracks")

    val funs2Index = stateFuns.iterator.zipWithIndex.toMap
    val symTransitions = new ArrayBuffer[TransducerTransition]
    val accepting = new MHashSet[Int]

    for ((f, transitions) <- funs) {
      for (trans <-
             LineariseVisitor(Transform2NNF(transitions), IBinJunctor.Or)) {
        val conjuncts = LineariseVisitor(trans, IBinJunctor.And)

        val (targetConds, otherConds1) = conjuncts partition {
          case EqZ(IFunApp(f, _)) if stateFuns contains f => true
          case _ => false
        }

        val (emptinessConds, otherConds2) = otherConds1 partition {
          case Eq(_ : IVariable, IFunApp(`str_empty`, _)) => true
          case Eq(IFunApp(`str_empty`, _), _ : IVariable) => true
          case _ => false
        }

        val (nonEmptinessConds, otherConds3) = otherConds2 partition {
          case INot(Eq(_ : IVariable, IFunApp(`str_empty`, _))) => true
          case INot(Eq(IFunApp(`str_empty`, _), _ : IVariable)) => true
          case _ => false
        }

        val (blockedTransitionConds, otherConds) = otherConds3 partition {
          c => checkBlockedTransitionCond(c, 0).isDefined
        }

        if (conjuncts.size == emptinessConds.size &&
            (for (IVariable(ind) <-
                    SymbolCollector variables and(emptinessConds))
             yield ind) == (0 until tracks).toSet) {

          accepting += funs2Index(f)

        } else {
          if (!emptinessConds.isEmpty)
            throw new TranslationException(
              "inconsistent string emptiness conditions in transducer: " +
              and(emptinessConds))

          val (epsilons, targetIndex) = targetConds match {
            case Seq(EqZ(IFunApp(targetFun, args)))
              if (stateFuns contains targetFun) =>
              (for ((t, n) <- args.zipWithIndex;
                    trackVar = tracks - n - 1) yield t match {
                 case IVariable(`trackVar`)                         => true
                 case IFunApp(str_tail, Seq(IVariable(`trackVar`))) => false
                 case t =>
                   throw new TranslationException(
                     "unsupported track modifier in transducer: " + t)
               },
               funs2Index(targetFun))
            case c =>
              throw new TranslationException(
                "need exactly one target constraint in transducer, not " + c)
          }
        
          val nonEmptyTracks =
            for (IVariable(n) <-
                   SymbolCollector variables and(nonEmptinessConds))
            yield (tracks - n - 1)
          if (nonEmptyTracks !=
              (for ((false, n) <- epsilons.iterator.zipWithIndex)
               yield n).toSet)
            throw new TranslationException(
              "inconsistent constraints in transducer: " +
              "accessed tracks have to be non-empty strings")

          val constraint = StrHeadReplacer.visit(and(otherConds), Context())
                                          .asInstanceOf[IFormula]

          val blockedTransitions =
            for (f <- blockedTransitionConds) yield {
              val Some((targetFun, quantifiedTracks)) =
                checkBlockedTransitionCond(f, 0)
              BlockedTransition(funs2Index(targetFun), quantifiedTracks)
            }

          symTransitions +=
            TransducerTransition(funs2Index(f), targetIndex,
                                 epsilons, constraint, blockedTransitions)
        }

        () // work-around for Scala 2.12
      }
    }

    SymTransducer(symTransitions, accepting.toSet)
  }

  private def checkBlockedTransitionCond(f : IFormula, quanNum : Int)
                           : scala.Option[(IFunction, Seq[Boolean])] = f match {
    case IQuantified(Quantifier.ALL, g) =>
      checkBlockedTransitionCond(g, quanNum + 1)
    case INot(EqZ(IFunApp(f, args)))
      if args forall (_.isInstanceOf[IVariable]) =>
      Some((f, for (IVariable(ind) <- args) yield (ind < quanNum)))
    case _ =>
      None
  }

  //////////////////////////////////////////////////////////////////////////////

  private def translateBVUnaryOp(name : String, f : IFunction, args : Seq[Term])
                                : (IExpression, SMTType) = {
    checkArgNum(name, 1, args)
    val a0@(transArg0, type0) = translateTerm(args(0), 0)
    (f(i(extractBVWidth(name, type0, args(0))), asTerm(a0)), type0)
  }

  private def extractBVWidth(name : String, t : SMTType, arg : Term) : Int =
    extractBVModulusWidth(name, t, arg)._2

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
    val bits = checkArgBVAgreement(name, args(0), type0, args(1), type1)
    (f(i(bits), asTerm(a0), asTerm(a1)), type0.asInstanceOf[SMTBitVec])
  }

  private def translateBVNAryOp(name : String, f : IFunction, args : Seq[Term])
                              : (ITerm, SMTBitVec) = {
    val flatArgs = flatten(name, args)
    val transArgs = for (a <- flatArgs) yield translateTerm(a, 0)
    val bits = checkArgBVAgreement(name, flatArgs, transArgs.unzip._2)
    ((transArgs.iterator map (asTerm(_))) reduceLeft {
       (s, t) => f(i(bits), s, t)
     },
     SMTBitVec(bits))
  }

  private def translateBVBinPred(name : String, p : Predicate, args : Seq[Term])
                                : (IExpression, SMTType) = {
    checkArgNum(name, 2, args)
    val a0@(transArg0, type0) = translateTerm(args(0), 0)
    val a1@(transArg1, type1) = translateTerm(args(1), 0)
    val bits = checkArgBVAgreement(name, args(0), type0, args(1), type1)
    (p(i(bits), asTerm(a0), asTerm(a1)), SMTBool)
  }

  private def translateBVBinPred(name : String, args : Seq[Term],
                                 op : (Int, ITerm, ITerm) => IFormula)
                                : (IExpression, SMTType) = {
    checkArgNum(name, 2, args)
    val a0@(transArg0, type0) = translateTerm(args(0), 0)
    val a1@(transArg1, type1) = translateTerm(args(1), 0)
    val bits = checkArgBVAgreement(name, args(0), type0, args(1), type1)
    (op(bits, asTerm(a0), asTerm(a1)), SMTBool)
  }

  private def translateBVBinPredInv(name : String, p : Predicate, args : Seq[Term])
                                   : (IExpression, SMTType) = {
    checkArgNum(name, 2, args)
    val a0@(transArg0, type0) = translateTerm(args(0), 0)
    val a1@(transArg1, type1) = translateTerm(args(1), 0)
    val bits = checkArgBVAgreement(name, args(0), type0, args(1), type1)
    (p(i(bits), asTerm(a1), asTerm(a0)), SMTBool)
  }

  private def checkArgBVAgreement(name : String,
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
                                  args : Seq[Term],
                                  types : Seq[SMTType]) : Int =
    types.distinct match {
      case Seq(SMTBitVec(w)) =>
        w
      case _ =>
        throw new Parser2InputAbsy.TranslationException(
          name + " cannot be applied to " +
          ((args map (printer print _)) mkString " ")
        )
    }

  //////////////////////////////////////////////////////////////////////////////
  
  private def translateTriggerAttr(attrparam : AttrParam) : Seq[IExpression] =
        attrparam match {
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

  private def translateTrigger(expr : SExpr) : IExpression = expr match {
    
    case expr : ConstantSExpr => translateSpecConstant(expr.specconstant_)._1
    
    case expr : SymbolSExpr => lookupSym(asString(expr.symbol_)) match {
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
      case Environment.Variable(i, BoundVariable(t)) => v(i, t.toSort)
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
          case "select" => {
            val args = translateSExprTail(expr.listsexpr_)
            (TSort sortOf args.head) match {
              case ExtArray.ArraySort(t) =>
                IFunApp(t.select, args)
              case s =>
                throw new Parser2InputAbsy.TranslationException(
                  "select in a trigger has to be applied to an array term ")
            }
          }
          case "store" => {
            val args = translateSExprTail(expr.listsexpr_)
            (TSort sortOf args.head) match {
              case ExtArray.ArraySort(t) =>
                IFunApp(t.store, args)
              case s =>
                throw new Parser2InputAbsy.TranslationException(
                  "store in a trigger has to be applied to an array term ")
            }
          }
          case funName => lookupSym(funName) match {
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
            case Environment.Variable(i, BoundVariable(t)) => {
              checkArgNumSExpr(printer print funExpr.symbol_,
                               0, expr.listsexpr_.tail)
              v(i, t.toSort)
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
      (i(IdealInt(c.numeral_)),
       SMTInteger)
    case c : HexConstant =>
      (i(IdealInt(c.hexadecimal_ substring 2, 16)),
       SMTBitVec((c.hexadecimal_.size - 2) * 4))
    case c : BinConstant =>
      (i(IdealInt(c.binary_ substring 2, 2)),
       SMTBitVec(c.binary_.size - 2))

    case c : RatConstant => {
      val v = IdealRat(c.rational_)
      (realAlgebra.div(realAlgebra.int2ring(v.num),
                       realAlgebra.int2ring(v.denom)),
       realType)
    }

    case c : StringConstant => {
      import IExpression._

      val escSeq =
        SMTLineariser.unescapeIt(
          c.smtstring_.substring(1, c.smtstring_.size - 1)
                      .iterator.map(_.toInt))

      ((escSeq :\ stringTheory.str_empty()) {
         case (c, s) => stringTheory.str_cons(stringTheory int2Char c, s)
       }, stringType)
    }

    case c : StringSQConstant => {
      import IExpression._

      val escSeq =
        SMTLineariser.unescapeSQString(
          c.smtstringsq_.substring(1, c.smtstringsq_.size - 1))

      ((escSeq :\ stringTheory.str_empty()) {
         case (c, s) => stringTheory.str_cons(stringTheory int2Char c, s)
       }, stringType)
    }
  }
  
  private def translateChainableRealIntPred(
                      op : String,
                      args : Seq[Term],
                      intOp  : (ITerm, ITerm) => IFormula,
                      realOp : (ITerm, ITerm) => IFormula) : IFormula =
    asRealIntTerms(op, args) match {
      case (terms, SMTInteger) =>
        and(for (Seq(a, b) <- terms sliding 2) yield intOp(a, b))
      case (terms, SMTReal(_)) =>
        and(for (Seq(a, b) <- terms sliding 2) yield realOp(a, b))
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
// todo: this is too redundant with translateDataCtorList, need to refactor
  private def translateHeapCtorList(sortNames : Seq[String],
                                    addressSortName : String,
                                    resultSortNum : Int,
                                    constructorDecls : Seq[ConstructorDeclC])
  : (Seq[(String, Heap.CtorSignature)], Seq[Seq[SMTType]]) =
    (for (ctor <- constructorDecls) yield ctor match {
      case ctorDecl : ConstructorDecl => {
        val ctorName = asString(ctorDecl.symbol_)

        val (adtArgs, smtArgs) =
          (for (s <- ctorDecl.listselectordeclc_) yield {
            val selDecl = s.asInstanceOf[SelectorDecl]
            val selName = asString(selDecl.symbol_)

            val (adtSort, smtSort : SMTType) =
              (sortNames indexOf asString(selDecl.sort_)) match {
                case -1 => {
                  selDecl.sort_ match {
                    case s : IdentSort
                      if asString(s.identifier_) == addressSortName =>
                      (Heap.AddressCtor, SMTHeapAddress(null))
                    case _ => val t = translateSort(selDecl.sort_)
                      (Heap.OtherSort(t.toSort), t)
                  }
                }
                case ind =>
                  // we don't have the actual ADT yet, so just put
                  // null for the moment
                  (Heap.ADTSort(ind), SMTADT(null, ind))
              }

            ((selName, adtSort), smtSort)
          }).unzip

        ((ctorName, Heap.CtorSignature(adtArgs, Heap.ADTSort(resultSortNum))),
          smtArgs)
      }

      case ctorDecl : NullConstructorDecl =>
        ((asString(ctorDecl.symbol_),
          Heap.CtorSignature(List(), Heap.ADTSort(resultSortNum))),
          List())
    }).unzip

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
                (sortNames indexOf asString(selDecl.sort_)) match {
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

  //////////////////////////////////////////////////////////////////////////////

  private def addADTToEnv(datatype : ADT) : Unit = {
    val smtDataTypes =
      for (n <- datatype.sorts.indices) yield SMTADT(datatype, n)

    // add types to environment
    for (t <- smtDataTypes)
      env.addSort(t.toString, t)

    // add adt symbols to the environment
    val smtCtorFunctionTypes =
      for ((ctor, ctorNum) <- datatype.constructors.zipWithIndex;
         adtNum = datatype.sortOfCtor(ctorNum)) yield {
      val smtArgSorts = for (arg <- ctor.argSorts) yield
        SMTLineariser.sort2SMTType(arg)._1
      SMTFunctionType(smtArgSorts.toList, smtDataTypes(adtNum))
    }

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
    for ((ctor, ctorNum) <- datatype.constructors.zipWithIndex;
         adtNum = datatype.sortOfCtor(ctorNum);
         ctorIdFun = datatype.ctorIds(adtNum);
         ctorIdTerm = ctorIdFun(v(0)))
    {
      val query = new IFunction("is-" + ctor.name, 1, true, true)
      env.addFunction(query,
        SMTFunctionType(List(smtDataTypes(adtNum)), SMTBool))
      val body = ctorIdTerm === datatype.ctorId2PerSortId(ctorNum)
      functionDefs = functionDefs + (query -> (body, SMTBool))
    }
  }

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

  private def setupHeap(heapSortName : String, addressSortName : String,
                        objectSortName : String, adtSortNames : Seq[String],
                        allCtors : Seq[(Seq[(String, Heap.CtorSignature)],
                         Seq[Seq[SMTType]])],
                        defaultObjectTerm : Term) : Unit = {

    val adtCtors = (allCtors map (_._1)).flatten

    // Throw an error if the Object sort cannot be found as a datatype
    val (objectSort, _) =
      adtSortNames.indexOf(objectSortName) match {
        case -1 => throw new Parser2InputAbsy.TranslationException(
          "Could not find " + objectSortName + " among the given sorts.")
        case n => (Heap.ADTSort(n), n)
      }

    // This gets called during the heap theory construction, before the actual
    // construction is complete; so we need to add the heap ADT sorts to the env
    // to be able to construct the defaultObjectTerm.
    def defObjCtor(objectADT : ADT, allocResADT : ADT) : ITerm = {
      addADTToEnv(objectADT)
      addADTToEnv(allocResADT)
      asTerm(translateTerm(defaultObjectTerm, -1))
    }

    val heap = new Heap(heapSortName, addressSortName, objectSort,
      adtSortNames, adtCtors, defObjCtor)

    // Add the remaining heap sorts to the environment
    env.addSort(addressSortName, SMTHeapAddress(heap))
    env.addSort(heapSortName, SMTHeap(heap))

    // Add heap functions to the environment

    // Some of the heap functions are overloaded, and have to be handled
    // directly in symApp: alloc, read, write, valid

    for (fun <- List(heap.emptyHeap, heap.allocHeap, heap.allocAddr,
                     heap.nullAddr,  heap.counter, heap.nthAddr)) {
      val smtArgSorts = (for (arg <- fun.argSorts) yield
        SMTLineariser.sort2SMTType(arg)._1).toList
      env.addFunction(fun, SMTFunctionType(smtArgSorts,
                             SMTLineariser.sort2SMTType(fun.resSort)._1))
    }

    addTheory(heap)
  }

  protected def extractHeap(args : Seq[Term])
                          : scala.Option[(ITerm, Heap)] =
    args match {
      case Seq(arg0, _*) => {
        val p@(t, s) = translateTerm(arg0, 0)
        s match {
          case SMTHeap(heapTheory) => Some((asTerm(p), heapTheory))
          case _                   => None
        }
      }
      case _ =>
        None
    }

  protected def translateHeapFun(funF      : Heap => IFunction,
                                 args      : Seq[Term],
                                 argTypesF : Heap => Seq[SMTType],
                                 resTypeF  : Heap => SMTType)
                               : scala.Option[(IExpression, SMTType)] =
    for ((heapTerm, heapTheory) <- extractHeap(args)) yield {
      val fun       = funF(heapTheory)
      val argTypes  = argTypesF(heapTheory)
      val transArgs = for (a <- args.tail) yield translateTerm(a, 0)

      if (argTypes != (transArgs map (_._2)))
        throw new TranslationException(
          fun.name + " cannot be applied to arguments of type " +
          heapTheory.HeapSort + ", " +
          (transArgs map (_._2) mkString ", "))

      (IFunApp(fun, List(heapTerm) ++ (transArgs map (asTerm(_)))),
       resTypeF(heapTheory))
    }

  protected def objectType(heapTheory : Heap) : SMTType =
    SMTLineariser.sort2SMTType(heapTheory.ObjectSort)._1

  //////////////////////////////////////////////////////////////////////////////

  protected def registerRecFunctions(
                  funs : Seq[(IFunction, (IExpression, SMTType))]) : Unit =
    if (transducerStringTheory.isDefined) {
      val name = funs.head._1.name
      val transducer =
        recFunctions2Transducer(
          for ((f, trans) <- funs) yield (f, asFormula(trans)))
      stringTheoryBuilder.addTransducer(name, transducer)
    } else {
      for ((f, body) <- funs) {
        // set up a defining equation and formula
        warn("assuming that recursive function " + f.name + " is partial")
        addAxiomEquation(f, body)
      }
    }

  private def addAxiomEquation(f : IFunction,
                               body : (IExpression, SMTType)) : Unit = {
    val (argSorts, resSort) = MonoSortedIFunction.functionType(f)
    val argNum = argSorts.size

    val argVars = for ((s, n) <- argSorts.zipWithIndex) yield v(argNum -n-1, s)
    val resVar  = v(argNum, resSort)
    val lhs     = IFunApp(f, argVars)
    val axiom =
      if (argNum == 0)
        lhs === asTerm(body)
      else
        all(argSorts.reverse ++ List(resSort),
            ITrigger(List(lhs),
                     (lhs === resVar) ==> (asTerm(body) === resVar)))

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
                   "Expected a term of type " +
                   (SMTLineariser smtTypeAsString expectedSort) + ", not " +
                   expr)
  }
}

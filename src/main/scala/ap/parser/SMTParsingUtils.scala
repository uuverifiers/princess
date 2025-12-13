/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2023 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.basetypes.IdealInt
import ap.parser.smtlib._
import ap.parser.smtlib.Absyn._

object SMTParsingUtils {

  /**
   * Parse starting at an arbitrarily specified entry point
   */
  def parseWithEntry[T](input : java.io.Reader,
                        entry : (parser) => T) : T = {
    val l = new Yylex(new Parser2InputAbsy.CRRemover2 (input))
    val p = new parser(l, l.getSymbolFactory)
    
    try { entry(p) } catch {
      case e : Exception =>
        try {
          val msg = {
            "At line " + String.valueOf(l.line_num()) +
            ", near \"" + l.buff() + "\" :" +
            "     " + e.getMessage()
          }
          throw new Parser2InputAbsy.ParseException(msg)
        } catch {
          case _ : java.lang.StringIndexOutOfBoundsException =>
            throw new Parser2InputAbsy.ParseException(
              "Runaway block, probably due to mismatched parentheses")
        }
    }
  }
  
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

  /** Implicit conversion so that we can get a Scala-like iterator from a
   * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  def asString(s : SymbolRef) : String = s match {
    case s : IdentifierRef     => asString(s.identifier_)
    case s : CastIdentifierRef => asString(s.identifier_)
  }

  def asString(id : IndexC) : String = id match {
    case id : NumIndex => id.numeral_
    case id : HexIndex => id.hexadecimal_
    case id : SymIndex => asString(id.symbol_)
  }
  
  def asString(id : Identifier) : String = id match {
    case id : SymbolIdent =>
      asString(id.symbol_)
    case id : IndexIdent =>
      asString(id.symbol_) + "_" + ((id.listindexc_ map asString) mkString "_")
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

  object NumIndexedSymbol1 {
    def unapply(s : SymbolRef) : scala.Option[(String, IdealInt)] = s match {
      case IndexedSymbol(s1, NatLiteral(s2)) => Some((s1, s2))
      case _ => None
    }
  }

  object NumIndexedSymbol2 {
    def unapply(s : SymbolRef)
              : scala.Option[(String, IdealInt, IdealInt)] = s match {
      case IndexedSymbol(s1, NatLiteral(s2), NatLiteral(s3)) => Some((s1, s2, s3))
      case _ => None
    }
  }

  object IndexedIdentifier {
    def unapplySeq(id : Identifier) : scala.Option[Seq[String]] = id match {
      case id : IndexIdent => id.symbol_ match {
        case s : NormalSymbol =>
          Some(List(s.normalsymbolt_) ++ (id.listindexc_ map asString))
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

  val DecLiteral = """([0-9]+)""".r
  val HexLiteral = """#x([0-9a-fA-F]+)""".r
  val BVDecLiteral = """bv([0-9]+)""".r
  val FFDecLiteral = """ff([0-9]+)""".r

  object NatLiteral {
    def unapply(s : String) : scala.Option[IdealInt] = s match {
      case DecLiteral(v) => Some(IdealInt(v))
      case HexLiteral(v) => Some(IdealInt(v, 16))
      case _             => None
    }
  }

  import SMTTypes._
  import IExpression._

  def asTerm(expr : (IExpression, SMTType)) : ITerm = expr match {
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

  def asTerm(expr : (IExpression, SMTType),
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

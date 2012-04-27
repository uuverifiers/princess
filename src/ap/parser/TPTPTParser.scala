/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012      Philipp Ruemmer <ph_r@gmx.net>
 *               2010-2012 NICTA/Peter Baumgartner <Peter.Baumgartner@nicta.com.au>
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

import ap._
import ap.basetypes.IdealInt
import ap.terfor.{Formula, ConstantTerm}
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Quantifier
import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}
import scala.util.parsing.combinator.{JavaTokenParsers, PackratParsers}
import scala.util.matching.Regex

object TPTPTParser {
  
  private type Env = Environment[Type, Type, Rank, Rank]
  
  def apply = new TPTPTParser(new Env)
  
  private case class TypedVar(name : String, t : Type)
  private type SyntaxError = Parser2InputAbsy.ParseException

  case class Type(name: String) {
    override def toString = name
  }
  
  // Types
  private object IType extends Type("$i") // Individuals (of the Herbrand Universe)
  // cannot call the object iType because if so Scala pattern matching assumes i
  // Type is a *variable*
  private object OType extends Type("$o") // Truth values
  private object TType extends Type("$tType") // The type of types (kinds)
  private object IntType extends Type("$int")
  private object RatType extends Type("$rat")
  private object RealType extends Type("$real")
  
  private val preDeclaredTypes = Set(TType, OType, IType, IntType, RatType, RealType)

  // Notice: no space between - and digits
  private val isIntegerConstRegEx = """[+-]?[0-9]+""".r 
  
  // Predefined types: $i: individuals, $o: truth values
  // var types = Set(IType, OType, IntType, raTType, RealType)

  /**
   * Rank: The signature of individual function (and predicate) symbols.
   */

  case class Rank(rank: (List[Type], Type)) {
    def argsTypes = rank._1
    def resType = rank._2
    override def toString = 
      (if (argsTypes.isEmpty) "" else  ((argsTypes mkString " x ") + " → ")) + resType
  }

  // Convenience functions

  private def Rank0(r: Type) = new Rank(List() -> r)
  private def Rank1(r: (Type, Type)) = new Rank(List(r._1) -> r._2)
  private def Rank2(r: ((Type, Type), Type)) = new Rank(List(r._1._1, r._1._2) -> r._2)
  private def Rank3(r: ((Type, Type, Type), Type)) = new Rank(List(r._1._1, r._1._2, r._1._2) -> r._2)

  private object TPTPType extends Enumeration {
    val FOF, TFF, Unknown = Value
  }
     
}

/**
 * A parser for TPTP, both FOF and TFF
 */
class TPTPTParser(_env : Environment[TPTPTParser.Type,
                                     TPTPTParser.Type,
                                     TPTPTParser.Rank,
                                     TPTPTParser.Rank])
      extends Parser2InputAbsy(_env)
      with JavaTokenParsers with PackratParsers {

  import IExpression._
  import TPTPTParser._
  import Parser2InputAbsy.warn
  
  def apply(reader : java.io.Reader)
           : (IFormula, List[IInterpolantSpec], Signature) = {
    parseAll[List[List[IFormula]]](TPTP_input, reader) match {
      case Success(formulas, _) => {
        val tffs = formulas.flatten.filter(_ != null)
        
        val stringConstants = occurringStrings.toSeq.sortWith(_._1 < _._1)
        
        val stringConstantAxioms =
          connect(for (ind1 <- 0 until stringConstants.size;
                       ind2 <- (ind1+1) until stringConstants.size)
                  yield (stringConstants(ind1)._2 =/= stringConstants(ind2)._2),
                  IBinJunctor.And)

        ((getAxioms &&& stringConstantAxioms) ===> connect(tffs, IBinJunctor.Or), List(), env.toSignature)
      }
      case error =>
        throw new SyntaxError(error.toString)
    }
    
  }

  private var tptpType = TPTPType.Unknown

  private val declaredTypes = new MHashSet[Type]

  {
    declaredTypes ++= preDeclaredTypes
  }

  /**
   * Translate boolean-valued functions as predicates or as functions? 
   */
  private var booleanFunctionsAsPredicates = false
  /**
   * Totality axioms?
   */
  private var totalityAxiom = true
  /**
   * Functionality axioms?
   */
  private var functionalityAxiom = true

  protected def defaultFunctionType(f : IFunction) : Rank = tptpType match {
    case TPTPType.FOF =>
      Rank(((for (_ <- 0 until f.arity) yield IType).toList, IType))
    case TPTPType.TFF =>
      Rank(((for (_ <- 0 until f.arity) yield IntType).toList, IntType))
  }

  private var haveConjecture = false

  private val arithmeticOps = Set(
    "$less",
    "$lesseq",
    "$greater",
    "$greatereq",
    "$is_int",
    "$is_rat",
    
    "$uminus",
    "$sum",
    "$difference",
    "$product",
    "$quotient",
    "$quotient_e",
    "$quotient_t",
    "$quotient_f",
    "$remainder_e",
    "$remainder_t",
    "$remainder_f",
    "$floor",
    "$ceiling",
    "$truncate",
    "$round",
    
    "$to_int",
    "$to_rat",
    "$to_real"
  )

  //////////////////////////////////////////////////////////////////////////////
  // Rationals
  
  private var containsRat = false
  
  private def foundRat = if (!containsRat) {
    warn("Problem contains rationals, using incomplete axiomatisation")
    containsRat = true
    
    declareSym("rat_$less",        Rank2((RatType, RatType), OType))
    declareSym("rat_$lesseq",      Rank2((RatType, RatType), OType))
    declareSym("rat_$greater",     Rank2((RatType, RatType), OType))
    declareSym("rat_$greatereq",   Rank2((RatType, RatType), OType))
    declareSym("rat_$is_int",      Rank1((RatType), OType))
    declareSym("rat_$is_rat",      Rank1((RatType), OType))
    
    declareSym("rat_$uminus",      Rank1(RatType, RatType))
    declareSym("rat_$sum",         Rank2((RatType, RatType), RatType))
    declareSym("rat_$difference",  Rank2((RatType, RatType), RatType))
    declareSym("rat_$product",     Rank2((RatType, RatType), RatType))
    declareSym("rat_$quotient",    Rank2((RatType, RatType), RatType))
    declareSym("rat_$quotient_e",  Rank2((RatType, RatType), RatType))
    declareSym("rat_$quotient_t",  Rank2((RatType, RatType), RatType))
    declareSym("rat_$quotient_f",  Rank2((RatType, RatType), RatType))
    declareSym("rat_$remainder_e", Rank2((RatType, RatType), RatType))
    declareSym("rat_$remainder_t", Rank2((RatType, RatType), RatType))
    declareSym("rat_$remainder_f", Rank2((RatType, RatType), RatType))
    declareSym("rat_$floor",       Rank1((RatType), RatType))
    declareSym("rat_$ceiling",     Rank1((RatType), RatType))
    declareSym("rat_$truncate",    Rank1((RatType), RatType))
    declareSym("rat_$round",       Rank1((RatType), RatType))
    
    declareSym("rat_$to_int",      Rank1((RatType), IntType))
    declareSym("rat_$to_rat",      Rank1((RatType), RatType))
    declareSym("rat_$to_real",     Rank1((RatType), RealType))
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Reals
  
  private var containsReal = false
  
  private def foundReal = if (!containsReal) {
    warn("Problem contains reals, using incomplete axiomatisation")
    containsReal = true
    
    declareSym("real_$less",        Rank2((RealType, RealType), OType))
    declareSym("real_$lesseq",      Rank2((RealType, RealType), OType))
    declareSym("real_$greater",     Rank2((RealType, RealType), OType))
    declareSym("real_$greatereq",   Rank2((RealType, RealType), OType))
    declareSym("real_$is_int",      Rank1((RealType), OType))
    declareSym("real_$is_rat",      Rank1((RealType), OType))
    
    declareSym("real_$uminus",      Rank1(RealType, RealType))
    declareSym("real_$sum",         Rank2((RealType, RealType), RealType))
    declareSym("real_$difference",  Rank2((RealType, RealType), RealType))
    declareSym("real_$product",     Rank2((RealType, RealType), RealType))
    declareSym("real_$quotient",    Rank2((RealType, RealType), RealType))
    declareSym("real_$quotient_e",  Rank2((RealType, RealType), RealType))
    declareSym("real_$quotient_t",  Rank2((RealType, RealType), RealType))
    declareSym("real_$quotient_f",  Rank2((RealType, RealType), RealType))
    declareSym("real_$remainder_e", Rank2((RealType, RealType), RealType))
    declareSym("real_$remainder_t", Rank2((RealType, RealType), RealType))
    declareSym("real_$remainder_f", Rank2((RealType, RealType), RealType))
    declareSym("real_$floor",       Rank1((RealType), RealType))
    declareSym("real_$ceiling",     Rank1((RealType), RealType))
    declareSym("real_$truncate",    Rank1((RealType), RealType))
    declareSym("real_$round",       Rank1((RealType), RealType))
    
    declareSym("real_$to_int",      Rank1((RealType), IntType))
    declareSym("real_$to_rat",      Rank1((RealType), RatType))
    declareSym("real_$to_real",     Rank1((RealType), RealType))
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Comments are considered as whitespace and ignored right away
   */
  protected override val whiteSpace = """(\s|%.*|(?m)/\*(\*(?!/)|[^*])*\*/)+""".r
  
  /**
   * The grammar rules
   */
  private lazy val TPTP_input: PackratParser[List[List[IFormula]]] =
    rep(annotated_formula /* | comment */ | include)

  private lazy val annotated_formula = 
    // TPTP_input requires a list, because include abobe returns a list
    ( fof_annotated_logic_formula ^^ { List(_) } ) |
    ( tff_annotated_type_formula ^^ { _ => List() } ) |
    ( tff_annotated_logic_formula ^^ { List(_) } ) 
  // cnf_annotated


  private lazy val fof_annotated_logic_formula =
    ("fof" ^^ { _ => tptpType = TPTPType.FOF }) ~ "(" ~>
    (atomic_word | wholeNumber) ~ "," ~ atomic_word ~ "," ~
    fof_logic_formula <~ ")" ~ "." ^^ {
    case name ~ "," ~ role ~ "," ~ f => 
	role match {
	  case "conjecture" => {
	    haveConjecture = true
        f
	  }
	  // "type" just returns TrueAtom - deal with that above
	  // case "type" => xxx
      case _ => !f // Assume f sits on the premise side
	}
  } 

  /**
   * TFF types
   */

  // In fact, non-null annotations are currently not accepted
  // Slightly rewritten version of the BNF rule in the TPTP report, to discrimate
  // between type and non-type very early, thus helping the parser.
  private lazy val tff_annotated_type_formula =
    ("tff" ^^ { _ => tptpType = TPTPType.TFF }) ~ "(" ~
    (atomic_word | wholeNumber) ~ "," ~ "type" ~ "," ~ tff_typed_atom ~
    ")" <~ "." ^^ { 
    // It's there just for its side effect
    _ => ()
  }

  private lazy val tff_annotated_logic_formula =
    ("tff" ^^ { _ => tptpType = TPTPType.TFF }) ~ "(" ~
    (atomic_word | wholeNumber) ~ "," ~ 
    formula_role_other_than_type ~ "," ~ tff_logic_formula <~ ")" ~ "." ^^ {
      case name ~ "," ~ role ~ "," ~ f => 
	  role match {
	    case "conjecture" => {
	      haveConjecture = true
	      f
	    }
	    case _ => !f // Assume f sits on the premise side
	  }
    } 

  private lazy val formula_role_other_than_type = commit(
    // "type" | 
    "axiom" | "hypothesis" | "definition" | "assumption" | "lemma" | "theorem" | 
    "conjecture" | "negated_conjecture" | "unknown" | atomic_word )


  // tff_typed_atom can appear only at toplevel
  private lazy val tff_typed_atom:PackratParser[Unit] =
     ( ( tff_untyped_atom ~ ":" ~ tff_top_level_type ) ^^ { 
	        // could declare a new type or a symbol of an existing type
       case typeName ~ ":" ~ Rank((Nil, TType)) => {
         // TODO: we have to add guards to encode that uninterpreted domains
         // could be finite
	     declaredTypes += Type(typeName)
	     ()
	     //Sigma += Type(typeName)
         // println("declared")
         // return a dummy
         // TrueAtom
       }
       case symbolName ~ ":" ~ rank =>
         declareSym(symbolName, rank)
     } ) |
     ( "(" ~> tff_typed_atom <~ ")" )
           
         
         /*
         if (rank.argsTypes.isEmpty && 
					  // Prop variables are better handled
					  // by the foreground
					  rank.resType != OType &&
					  (Sigma.BGTypes contains rank.resType) &&
					  Flags.paramsOpSet.value == "BG")
					// only in this case we have a BG operator
					Sigma = Sigma addBG (symbolName -> rank)
				      else
					Sigma += (symbolName -> rank)
				      // return a dummy
				      // println("declared")
				      // TrueAtom
				    }
				  */
     
  private def declareSym(symbolName : String, rank : Rank) : Unit = {
         if (rank.argsTypes contains OType)
           throw new SyntaxError("Error: type declaration for " + 
               symbolName + ": " + rank + ": argument type cannot be $oType")
         
         if (!rank.argsTypes.isEmpty) {
           if (!booleanFunctionsAsPredicates || rank.resType != OType)
             // use a real function
             env.addFunction(new IFunction(symbolName, rank.argsTypes.size,
                                           !totalityAxiom, !functionalityAxiom),
                             rank)
           else
             // use a predicate
             env.addPredicate(new Predicate(symbolName, rank.argsTypes.length),
                              rank)
         } else if (rank.resType != OType)
           // use a constant
           env.addConstant(new ConstantTerm(symbolName), Environment.NullaryFunction,
                           rank.resType)
         else
           // use a nullary predicate (propositional variable)
           env.addPredicate(new Predicate(symbolName, 0), rank)
  }
     
  private lazy val tff_untyped_atom =    atomic_word

  // This results in a Rank in our terminology
  private lazy val tff_top_level_type:PackratParser[Rank] =
    tff_mapping_type |
    ( tff_atomic_type  ^^ { (typ:Type) => Rank0(TypeExistsChecked(typ)) } )

  private lazy val tff_mapping_type:PackratParser[Rank] =
    ( ( tff_unitary_type ~ ">" ~ tff_atomic_type ) ^^
        { case argsTypes ~ ">" ~ resType =>
          Rank((argsTypes map (TypeExistsChecked(_))) -> TypeExistsChecked(resType)) } ) | (
            "(" ~> tff_mapping_type <~ ")" )
    
  private lazy val tff_unitary_type =
    ( tff_atomic_type ^^ { List(_) } ) | ( "(" ~> tff_xprod_type <~ ")" )
    
  private lazy val tff_xprod_type:PackratParser[List[Type]] =
    ( tff_atomic_type ~ "*" ~  rep1sep(tff_atomic_type, "*") ^^ {
      case t1 ~ "*" ~ tail => t1::tail
     } ) |
    ( "(" ~> tff_xprod_type <~ ")" )

  //////////////////////////////////////////////////////////////////////////////
   
  /**
   * TFF formulas
   */

  private lazy val tff_logic_formula =
    tff_binary_formula | tff_unitary_formula
    
  private lazy val tff_binary_formula =
    tff_binary_nonassoc | tff_binary_assoc
    
  private lazy val tff_binary_nonassoc =
    tff_unitary_formula ~ binary_nonassoc_connective ~ tff_unitary_formula ^^ {
      case f1 ~ op ~ f2 => op(f1,f2)
    }
  
  private lazy val tff_binary_assoc =
    tff_or_formula | tff_and_formula
    
  private lazy val tff_or_formula =
    tff_unitary_formula ~ "|" ~ rep1sep(tff_unitary_formula, "|") ^^ {
      case f1 ~ "|" ~ tail => f1::tail reduceLeft { _ | _ }
    }
  
  private lazy val tff_and_formula =     
    tff_unitary_formula ~ "&" ~ rep1sep(tff_unitary_formula, "&") ^^ {
      case f1 ~ "&" ~ tail => {
        f1::tail reduceLeft { _ & _ }
      }
    }
  
  private lazy val tff_unitary_formula:PackratParser[IFormula] = 
    tff_quantified_formula | tff_unary_formula | atom |
    "(" ~> tff_logic_formula <~ ")"
    
  private lazy val tff_unary_formula =
    "~" ~> tff_unitary_formula ^^ { ! _ }
  
  private lazy val tff_quantified_formula:PackratParser[IFormula] = 
    (((forallSign ^^ { _ => Quantifier.ALL.asInstanceOf[Quantifier] } ) |
	    ("?"        ^^ { _ => Quantifier.EX.asInstanceOf[Quantifier] } )) ~ 
	     "[" ~ tff_varlist ~ "]" ^^ { 
		        case q ~ "[" ~ vl ~ "]" => { 
				  for (v <- vl)
				    env.pushVar(v.name, v.t)
				  // Return the partially instantiated Quantifier-Formula
				  val quantify = (f:IFormula) => (f /: vl) { case (f, _) =>  IQuantified(q, f) }
				  (quantify, vl.size)
				}
		     }) ~ ":" ~ tff_unitary_formula ^^ {
		        // Put together the two parts, quantification and formula
		        case (quantTemplate, varNum) ~ ":" ~ f => {
                  for (_ <- 0 until varNum)
                    env.popVar
		          quantTemplate(f)
		        }
		      }


  // Variable list
  private lazy val tff_varlist: PackratParser[List[TypedVar]] =
    rep1sep(tff_var, ",")

  private lazy val tff_var: PackratParser[TypedVar] = 
    ( variableStr ~ ":" ~ tff_atomic_type ^^ { 
        case x ~ ":" ~ typ => TypedVar(x, TypeExistsChecked(typ)) 
      } ) |
    ( variableStr <~ guard(not(":")) ^^ { 
        // default type of variables (in quantifications) is IType
        x => TypedVar(x, IType) 
      } )

  private lazy val tff_atomic_type = 
    // user-defined type
    defined_type | ( atomic_word ^^ { Type(_) } ) 
  // predefined type

  private lazy val defined_type: PackratParser[Type] = 
    (("$oType" | "$o") ^^ { _ => OType }) |
    (("$iType" | ("$i" <~ guard(not("nt")))) ^^ { _ => IType }) |
    ("$tType" ^^ { _ => TType }) |
    ("$int" ^^ { _ => IntType }) |
    ("$rat" ^^ { _ => foundRat; RatType }) |
    ("$real" ^^ { _ => foundReal; RealType })

  //////////////////////////////////////////////////////////////////////////////
    
  /*
   * FOF formulas
   */
  private lazy val fof_logic_formula =
    fof_binary_formula | fof_unitary_formula
    
  private lazy val fof_binary_formula =
    fof_binary_nonassoc | fof_binary_assoc
    
  private lazy val fof_binary_nonassoc =
    fof_unitary_formula ~ binary_nonassoc_connective ~ fof_unitary_formula ^^ {
      case f1 ~ op ~ f2 => op(f1,f2)
    }
  
  private lazy val fof_binary_assoc =
    fof_or_formula | fof_and_formula
    
  private lazy val fof_or_formula =
    fof_unitary_formula ~ "|" ~ rep1sep(fof_unitary_formula, "|") ^^ {
      case f1 ~ "|" ~ tail => f1::tail reduceLeft { _ | _ }
    }
  
  private lazy val fof_and_formula =     
    fof_unitary_formula ~ "&" ~ rep1sep(fof_unitary_formula, "&") ^^ {
      case f1 ~ "&" ~ tail => f1::tail reduceLeft { _ & _ }
    }
  
  private lazy val fof_unitary_formula:PackratParser[IFormula] = 
      fof_quantified_formula | fof_unary_formula | atom |
      "(" ~> fof_logic_formula <~ ")"
      
  private lazy val fof_unary_formula =
    "~" ~> fof_unitary_formula ^^ { !(_) }
  
  private lazy val fof_quantified_formula:PackratParser[IFormula] =
    (((forallSign ^^ { _ => Quantifier.ALL.asInstanceOf[Quantifier] } ) |
      ("?"        ^^ { _ => Quantifier.EX.asInstanceOf[Quantifier] } )) ~ 
       "[" ~ fof_varlist ~ "]" ^^ { 
              case q ~ "[" ~ vl ~ "]" => { 
                for (v <- vl)
                  env.pushVar(v.name, v.t)
                // Return the partially instantiated Quantifier-Formula
                val quantify = (f:IFormula) => (f /: vl) { case (f, _) =>  IQuantified(q, f) }
                (quantify, vl.size)
              } 
           }) ~ ":" ~ fof_unitary_formula ^^ {
              // Put together the two parts, quantification and formula
              case (quantTemplate, varNum) ~ ":" ~ f => {
                for (_ <- 0 until varNum)
                  env.popVar
                quantTemplate(f)
              }
            }


  // Variable list
  private lazy val fof_varlist: PackratParser[List[TypedVar]] = 
    rep1sep(variableStr, ",") ^^ { _ map { TypedVar(_, IType) } } // looks cryptic?

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Definitions common to TFF and FOF
   */

  private lazy val binary_nonassoc_connective = 
    ( "=>" ^^ {
      _ => { (x : IFormula, y : IFormula) => (x ==> y) } } ) |
    ( "<=" <~ guard(not(">")) ^^ {
      _ => { (x : IFormula, y : IFormula) => (y ==> x) } } ) |
    ( "<=>" ^^ {
      _ => { (x : IFormula, y : IFormula) => (x <=> y) } } ) |
    ( "<~>" ^^ {
      _ => { (x : IFormula, y : IFormula) => !(x <=> y) } } ) |
    ( "~|" ^^ {
      _ => { (x : IFormula, y : IFormula) => !(x | y) } } ) |
    ( "~&" ^^ {
      _ => { (x : IFormula, y : IFormula) => !(x & y) } } )

  // Atom
  // Difficulty is determining the type. If fun(args...) has been read 
  // it is possible that fun(args...) is an atom or the lhs of an equation.
  // Determining the type hence nees to be deferred until "=" (or "!=") is 
  // seen (or not). Once that is clear, the signature is extended 
  // appropriately. It can only be done this late because otherwise the signature
  // might be extended unappropriately, and backtracking (in the parser)
  // cannot undo that.

  private lazy val atom : PackratParser[IFormula] =
    ( "$true" ^^ { _ => i(true) }) |
    ( "$false" ^^ { _ => i(false) }) |
    // eqn with lhs a variable
    ( guard(variableStr ~ equalsSign) ~> (constant_or_variable ~ equalsSign ~ term) ^^ { 
	      case x ~ _ ~ t => CheckedEquation(x, t)
      } ) |
    ( guard(variableStr ~ "!=") ~> (constant_or_variable ~ "!=" ~ term) ^^ { 
	      case x ~ _ ~ t => !CheckedEquation(x, t)
      } ) |
    ( bg_constant ~ equalsSign ~ term ^^ { 
	      case c ~ _ ~ t => CheckedEquation(c, t)
      } ) |
    ( bg_constant ~ "!=" ~ term ^^ { 
	  case c ~ _ ~ t => !CheckedEquation(c, t)
      } ) |
  // functor with or without arguments
  (( ( functor ~ "(" ~ termlist ~ ")" ^^ { 
 	       case functor ~ "(" ~ termlist ~ ")" => (functor, termlist) } ) |
     ( functor ~ guard(not("(")) ^^ { 
	       case functor ~ _ => (functor, List()) } ) ) ~
   // Up to here the above could be an atom or the lhs of an equation.
   // The following three cases all return a template for a (dis)equation or an atom
   ( ( equalsSign ~ term ^^ { case _ ~ t =>
	     (functor:String, args:List[(ITerm, Type)]) => { 
//	       if (!(Sigma.ranks contains functor))
//             Sigma += (functor -> Rank((args map { _ => IType }) -> IType))
	       CheckedEquation(CheckedFunTerm(functor, args), t)
	     } 
       } ) |
     ( "!=" ~ term ^^ { 
         case _ ~ t =>
	     (functor:String, args:List[(ITerm, Type)]) => { 
//	       if (!(Sigma.ranks contains functor))
//	         Sigma += (functor -> Rank((args map { _ => IType }) -> IType))
	       !CheckedEquation(CheckedFunTerm(functor, args), t)
	     } 
       } ) |
     ( guard(not(equalsSign | "!=")) ^^ { 
         case _ =>
	     (functor:String, args:List[(ITerm, Type)]) => { 
//	       if (!(Sigma.ranks contains functor))
//             Sigma += (functor -> Rank((args map { _ => IType }) -> OType))
	       CheckedAtom(functor, args)
	     } 
       } ) ) ^^ 
   // Put together the results of the parsing obtained so far
   { case (functor,args) ~ fTemplate => fTemplate(functor,args) } )

  // Terms
  // Parsing (of atoms) is such that whenever a term is to be parsed
  // it is clear it must be a term (no backtracking), hence as soon
  // as a term is found the signature can be extended.
  private lazy val term: PackratParser[(ITerm, Type)] =
    funterm | constant_or_variable | bg_constant
    
  private lazy val variableStr: PackratParser[String] =
    regex(new Regex("[A-Z][a-zA-Z0-9_]*"))
    
/*    lazy val variable : PackratParser[] =
    variableStr ^^ { name => {
      val t = env.loo
    }} } */
    
  private lazy val funterm: PackratParser[(ITerm, Type)] =
    functor ~ "(" ~ termlist ~ ")" ^^ {
      case functor ~ "(" ~ termlist ~ ")" => CheckedFunTerm(functor, termlist)
        
//	      if (!(Sigma.ranks contains functor))
//	        Sigma += (functor -> Rank((termlist map { _ => IType }) -> IType))
	    // todo: check well-sortedness of arguments
//	    CheckedFunTerm(functor, termlist) 
  }

  private lazy val termlist = rep1sep(term, ",")

  // Foreground constant or parameter
  private lazy val constant_or_variable: PackratParser[(ITerm, Type)] = 
    // a constant cannot be followed by a parenthesis, would see a FunTerm instead
    // Use atomic_word instead of functor?
    guard((functor | variableStr) ~ not("(")) ~>
      (functor | variableStr) ^^ { functor => {
        if (!(env isDeclaredSym functor)) {
          if (tptpType != TPTPType.FOF)
            warn("implicit declaration of " + functor)
          declareSym(functor, Rank0(IType))
        }
          
        (env lookupSym functor) match {
          case Environment.Constant(c, _, t) => (i(c), t)
          case Environment.Variable(index, t) => (v(index), t)
          case _ => throw new SyntaxError("Unexpected symbol: " + functor)
        }
      }
  }

  private def fofify(t : Type) = tptpType match {
    case TPTPType.FOF => IType
    case _ => t
  }
      
  // Background literal constant
  private lazy val bg_constant: PackratParser[(ITerm, Type)] =
    (
      (regex(isIntegerConstRegEx) <~ guard(not(regex("[./]".r)))) ^^ { 
	    s => (i(IdealInt(s)), fofify(IntType))
      }
    ) | (
      (regex(isIntegerConstRegEx) ~ "/" ~ regex(isIntegerConstRegEx)) ^^ {
        case num ~ _ ~ denom => {
          foundRat
          val s = num + "/" + denom
          // we currently just introduce the number as a
          // fresh constant
          if (!(env isDeclaredSym s))
            declareSym(s, Rank0(fofify(RatType)))
          (env lookupSym s) match {
            case Environment.Constant(c, _, t) => (i(c), t)
            case _ => throw new SyntaxError("Unexpected symbol: " + functor)
          }
        }
      }
    ) | (
      (regex(isIntegerConstRegEx) ~ "." ~ regex("""[0-9Ee\-]+""".r)) ^^ {
        case int ~ _ ~ frac => {
          foundReal
          val s = int + "." + frac
          // we currently just introduce the number as a
          // fresh constant
          if (!(env isDeclaredSym s))
            declareSym(s, Rank0(fofify(RealType)))
          (env lookupSym s) match {
            case Environment.Constant(c, _, t) => (i(c), t)
            case _ => throw new SyntaxError("Unexpected symbol: " + functor)
          }
        }
      }
    ) | (
      regex(("\"([\\040-\\041\\043-\\0133\\0135-\\0176]|\\\\\"|\\\\\\\\)*\"").r) ^^ {
        case s =>
          (i(occurringStrings.getOrElseUpdate(s, {
             val c = new ConstantTerm ("stringConstant" + occurringStrings.size)
             env.addConstant(c, Environment.NullaryFunction, IType)
             c
           })), IType)
      }
    )
  
  private val occurringStrings =
    new scala.collection.mutable.HashMap[String, ConstantTerm]
    
  // lexical: don't confuse = with => (the lexer is greedy)
  private lazy val equalsSign = "=" <~ guard(not(">"))
  
  private lazy val forallSign = "!" <~ guard(not("="))

  private lazy val functor = keyword | atomic_word

  private lazy val atomic_word: PackratParser[String] = 
    ( regex("""'.*'""".r) ^^ { _.drop(1).dropRight(1) } ) |
    regex("[a-z][a-zA-Z0-9_]*".r)

  private lazy val keyword = regex("[$][a-z_]+".r)

/* Could be specific (but why?)
  lazy val keyword = 
    "$uminus"     |
    "$sum"        |
    "$difference" |
    "$product"    |
    ("$less" <~ guard(not("eq")))   |
    "$lesseq"     |
    ("$greater" <~ guard(not("eq")))  |
    "$greatereq"  |
    "$evaleq"     
*/

  // Parsing of comments is not optimal as they may not appear
  // inside formulas - essentially they are an atom
//  private lazy val comment: PackratParser[List[IFormula]] =
//    """%.*""".r ^^ (x => List(null /* Comment(x) */))

  private lazy val include: PackratParser[List[IFormula]] = 
    "include" ~> "(" ~> atomic_word <~ ")" <~ "." ^^ { case fileName  => {
	    val TPTPHome = System.getenv("TPTP")
	    val filename = (if (TPTPHome == null) "" else TPTPHome + "/") + fileName
	    val reader = new java.io.BufferedReader (
                   new java.io.FileReader(new java.io.File (filename)))
        parseAll[List[List[IFormula]]](TPTP_input, reader) match {
          case Success(formulas, _) =>
            formulas.flatten
          case error =>
            throw new SyntaxError("When reading " + filename + "\n" + error)
	    }
	  } 
  }

  /**
   * CheckedXX: creates an XX, type-checked against sig and varTypes
   */
  private def CheckedEquation(s: (ITerm, Type), t: (ITerm, Type)) = {
    val (s_term, s_type) = s
    val (t_term, t_type) = t
    if (s_type != OType && s_type == t_type) 
      s_term === t_term
    else
      throw new SyntaxError(
         "Error: ill-sorted (dis)equation: between " + s_term + " and " + t_term)
  }

  private def CheckedAtom(pred: String,
                          args: List[(ITerm, Type)])
                         : IFormula = (pred, args map (_._2)) match {
    case ("$less",      Seq(IntType, IntType)) => args(0)._1 < args(1)._1
    case ("$lesseq",    Seq(IntType, IntType)) => args(0)._1 <= args(1)._1
    case ("$greater",   Seq(IntType, IntType)) => args(0)._1 > args(1)._1
    case ("$greatereq", Seq(IntType, IntType)) => args(0)._1 >= args(1)._1
    case ("$evaleq",    Seq(IntType, IntType)) => args(0)._1 === args(1)._1
    case ("$is_int",    Seq(IntType))          => true
    case ("$is_rat",    Seq(IntType))          => true
    case ("$is_real",   Seq(IntType))          => true

    case (pred, argTypes) =>
      if (arithmeticOps contains pred) argTypes(0) match {
        case IntType =>
          // should not happen
          throw new SyntaxError("Unexpected integer operator: " + pred)
        case RatType =>
          checkUnintAtom("rat_" + pred, args map (_._1), argTypes)
        case RealType =>
          checkUnintAtom("real_" + pred, args map (_._1), argTypes)
      } else {
        checkUnintAtom(pred, args map (_._1), argTypes)
      }
  }
  
  private def checkUnintAtom(pred: String, args: Seq[ITerm], argTypes : Seq[Type])
              : IFormula = {
        if (!(env isDeclaredSym pred)) {
          val rank = Rank((argTypes.toList, OType))
          if (tptpType != TPTPType.FOF || (pred contains "-overloaded"))
            warn("implicit declaration or overloading of " + pred + ": " + rank)
          declareSym(pred, rank)
        }

      (env lookupSym pred) match {
        case Environment.Function(f, r) if (r.resType == OType) =>
          if (r.argsTypes != argTypes) {
            // urgs, symbol has been used with different arities
            // -> disambiguation-hack
            checkUnintAtom(pred + "-overloaded", args, argTypes)
          } else {
            // then a predicate has been encoded as a function
            IIntFormula(IIntRelation.EqZero, IFunApp(f, args))
          }
        case Environment.Predicate(p, r) =>
          if (r.argsTypes != argTypes) {
            // urgs, symbol has been used with different arities
            // -> disambiguation-hack
            checkUnintAtom(pred + "-overloaded", args, argTypes)
          } else {
            IAtom(p, args)
          }
        case _ =>
          throw new SyntaxError("Unexpected symbol: " + pred)
      }
  }
  
/*      // Assume that pred has been entered into sig already
    if (Sigma(pred).argsTypes == Sigma.typesOf(args, varTypes))
  Atom(pred, args)
    else
	throw new SyntaxError("Error: ill-sorted atom: " + Atom(pred, args)) */

  private def CheckedFunTerm(fun: String,
                             args: List[(ITerm, Type)])
                            : (ITerm, Type) = (fun, args map (_._2)) match {
    case ("$sum",         Seq(IntType, IntType))  => (args(0)._1 + args(1)._1, IntType)
    case ("$difference",  Seq(IntType, IntType))  => (args(0)._1 - args(1)._1, IntType)
    case ("$product",     Seq(IntType, IntType))  => (mult(args(0)._1, args(1)._1), IntType)
    case ("$uminus",      Seq(IntType))           => (-args(0)._1, IntType)

    case (fun, argTypes) =>
      if (arithmeticOps contains fun) argTypes(0) match {
        case IntType =>
          // should not happen
          throw new SyntaxError("Unexpected integer operator: " + fun)
        case RatType =>
          checkUnintFunTerm("rat_" + fun, args map (_._1), argTypes)
        case RealType =>
          checkUnintFunTerm("real_" + fun, args map (_._1), argTypes)
      } else {
        checkUnintFunTerm(fun, args map (_._1), argTypes)
      }
  }

  private def checkUnintFunTerm(fun: String, args: Seq[ITerm], argTypes : Seq[Type])
                               : (ITerm, Type) = {
        if (!(env isDeclaredSym fun)) {
          val rank = Rank((argTypes.toList, IType))
          if (tptpType != TPTPType.FOF || (fun contains "-overloaded"))
            warn("implicit declaration or overloading of " + fun + ": " + rank)
          declareSym(fun, rank)
        }
        
      (env lookupSym fun) match {
        case Environment.Function(f, r) if (r.resType != OType) =>
          if (r.argsTypes != argTypes) {
            // urgs, symbol has been used with different arities
            // -> disambiguation-hack
            checkUnintFunTerm(fun + "-overloaded", args, argTypes)
          } else {
            (IFunApp(f, args), r.resType)
          }
        case Environment.Constant(c, _, t) => {
          if (!args.isEmpty)
            throw new SyntaxError("Constant does not accept arguments: " + functor)
          (IConstant(c), t)
        }
        case _ =>
          throw new SyntaxError("Unexpected symbol: " + fun)
      }
  }
  
/*      
    // Assume that fun has been entered into sig already
    if (args.isEmpty) {
	// A constant. See if we have a foreground constant or parameter
	if (Sigma.BGRanks contains fun)
	  // We have a parameter
	  Param(fun)
	else
	  // Foreground Constant
        Const(fun) 
    } else if (Sigma(fun).argsTypes == Sigma.typesOf(args, varTypes)) 
	// Type Checking OK 
	FunTerm(fun, args)
    else
	throw new SyntaxError("Error: ill-sorted term: " + FunTerm(fun, args)) */

  private def TypeExistsChecked(typ: Type) = 
    if (declaredTypes contains typ)
      typ
    else
      throw new SyntaxError("Error: type has not been declared: " + typ)
}



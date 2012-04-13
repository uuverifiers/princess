/* *********************************************************************
 * This file is part of the MELIA theorem prover
 *
 * Copyright (c) NICTA/Peter Baumgartner <Peter.Baumgartner@nicta.com.au>
 *
 * MELIA is free software: you can redistribute it
 * and/or modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation, either version 3 of
 * the License, or (at your option) any later version.
 *
 * MELIA is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with MELIA.  If not, see  <http://www.gnu.org/licenses/>. 
 * ********************************************************************* */

package ap.parser

import ap._
import ap.basetypes.IdealInt
import ap.terfor.{Formula, ConstantTerm}
import ap.terfor.conjunctions.Quantifier

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}
import scala.util.parsing.combinator.{JavaTokenParsers, PackratParsers}
import scala.util.matching.Regex

object TPTPTParser {
  
  case class TypedVar(name : String, t : Type)
  type SyntaxError = Parser2InputAbsy.ParseException

  case class Type(name: String) {
    override def toString = name
  }
  
  // Types
  object IType extends Type("$i") // Individuals (of the Herbrand Universe)
  // cannot call the object iType because if so Scala pattern matching assumes i
  // Type is a *variable*
  object OType extends Type("$o") // Truth values
  object TType extends Type("$tType") // The type of types (kinds)
  object IntType extends Type("$int")
  object RatType extends Type("$rat")
  object RealType extends Type("$real")
  
  val declaredTypes = new MHashSet[Type]

  {
    declaredTypes += (TType, OType, IType, IntType, RatType, RealType)
  }

  // Notice: no space between - and digits
  val isIntegerConstRegEx = """[+-]?[0-9]+""".r 
  
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

  def Rank0(r: Type) = new Rank(List() -> r)
  def Rank1(r: (Type, Type)) = new Rank(List(r._1) -> r._2)
  def Rank2(r: ((Type, Type), Type)) = new Rank(List(r._1._1, r._1._2) -> r._2)
  def Rank3(r: ((Type, Type, Type), Type)) = new Rank(List(r._1._1, r._1._2, r._1._2) -> r._2)

}

/**
 * A parser for TPTP, both FOF and TFF
 */
class TPTPTParser(_env : Environment) extends Parser2InputAbsy(_env)
                                      with JavaTokenParsers with PackratParsers {

  import IExpression._
  import TPTPTParser._
  
  def apply(reader : java.io.Reader)
           : (IFormula, List[IInterpolantSpec], Signature) = {
    val tffs =
      parseAll[List[List[IFormula]]](TPTP_input, reader).get.flatten.filter(_ != null)
    (connect(tffs, IBinJunctor.And), List(), env.toSignature)
  }

  val fullSymbolTypes = new MHashMap[Environment.DeclaredSym, Rank]
  
  /**
   * Translate boolean-valued functions as predicates or as functions? 
   */
  private var booleanFunctionsAsPredicates = false

  // Mapping of variables to types - needed, as quantified formuals are entered,
  // and the varTypes map keeps track of all governing (quantified) variables
  var varTypes = List[TypedVar]()
  // Because I did not find a way to pass around signatures as arguments 
  // in parsing, varTypes is built up and restored explictly in a stack
  var varTypesStack = List[List[TypedVar]]() 

  var haveConjecture = false

  /**
   * The grammar rules
   */
  lazy val TPTP_input: PackratParser[List[List[IFormula]]] =
    rep(annotated_formula | comment | include)

  lazy val annotated_formula = 
    // TPTP_input requires a list, because include abobe returns a list
    ( fof_annotated_logic_formula ^^ { List(_) } ) |
    ( tff_annotated_type_formula ^^ { _ => List() } ) |
    ( tff_annotated_logic_formula ^^ { List(_) } ) 
  // cnf_annotated


  lazy val fof_annotated_logic_formula =
    "fof" ~ "(" ~ (atomic_word | wholeNumber) ~ "," ~ atomic_word ~ "," ~
    fof_logic_formula ~ ")" <~ "." ^^ {
    case "fof" ~ "(" ~ name ~ "," ~ role ~ "," ~ f ~ ")" => 
	role match {
	  case "conjecture" => {
	    haveConjecture = true
	    !f
	  }
	  // "type" just returns TrueAtom - deal with that above
	  // case "type" => xxx
	  case _ => f // Assume f sits on the premise side
	}
  } 

  /**
   * TFF types
   */

  // In fact, non-null annotatations are currently not accepted
  // Slightly rewritten version of the BNF rule in the TPTP report, to discrimate
  // between type and non-type very early, thus helping the parser.
  lazy val tff_annotated_type_formula = "tff" ~ "(" ~ (atomic_word | wholeNumber) ~ "," ~ "type" ~ "," ~
                      tff_typed_atom ~ ")" <~ "." ^^ { 
    // It's there just for its side effect
    _ => ()
  }

  lazy val tff_annotated_logic_formula = "tff" ~ "(" ~ (atomic_word | wholeNumber) ~ "," ~ 
                      formula_role_other_than_type ~ "," ~ tff_logic_formula ~ ")" <~ "." ^^ {
    case "tff" ~ "(" ~ name ~ "," ~ role ~ "," ~ f ~ ")" => 
	role match {
	  case "conjecture" => {
	    haveConjecture = true
	    f
	  }
	  case _ => !f // Assume f sits on the premise side
	}
  } 

  lazy val formula_role_other_than_type = commit(
    // "type" | 
    "axiom" | "hypothesis" | "definition" | "assumption" | "lemma" | "theorem" | 
    "conjecture" | "negated_conjecture" | "unknown" | atomic_word )




  // tff_typed_atom can appear only at toplevel
  lazy val tff_typed_atom:PackratParser[Unit] =
     ( ( tff_untyped_atom ~ ":" ~ tff_top_level_type ) ^^ { 
	        // could declare a new type or a symbol of an existing type
       case typeName ~ ":" ~ Rank((Nil, TType)) => { 
	        println("declare type " + Type(typeName))
         //Sigma += Type(typeName)
         // println("declared")
         // return a dummy
         // TrueAtom
       }
       case symbolName ~ ":" ~ rank => {
         println("declare rank " + (symbolName -> rank))
         if (rank.argsTypes contains OType)
           throw new SyntaxError("Error: type declaration for " + 
               symbolName + ": " + rank + ": argument type cannot be $oType")
         // todo: generalize: can we do something sensible
         // if all argtypes are foreground types?
         // eg "car" would fall under this scheme.
         
         if (rank.argsTypes.isEmpty) {
           env.addConstant(new ConstantTerm(symbolName), Environment.Universal)
         } else {
           val f = new IFunction(symbolName, rank.argsTypes.size, true, true)
           env.addFunction(f, false)
         }
       }
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
     
  lazy val tff_untyped_atom =    atomic_word

  // This results in a Rank in our terminology
  lazy val tff_top_level_type:PackratParser[Rank] =
    tff_mapping_type |
    ( tff_atomic_type  ^^ { (typ:Type) => Rank0(TypeExistsChecked(typ)) } )

  lazy val tff_mapping_type:PackratParser[Rank] =
    ( ( tff_unitary_type ~ ">" ~ tff_atomic_type ) ^^
        { case argsTypes ~ ">" ~ resType =>
          Rank((argsTypes map (TypeExistsChecked(_))) -> TypeExistsChecked(resType)) } ) | (
            "(" ~> tff_mapping_type <~ ")" )
    
  lazy val tff_unitary_type =    ( tff_atomic_type ^^ { List(_) } ) | 
                            ( "(" ~> tff_xprod_type <~ ")" )
  lazy val tff_xprod_type:PackratParser[List[Type]] =
                            ( tff_atomic_type ~ "*" ~  rep1sep(tff_atomic_type, "*") ^^ {
				  case t1 ~ "*" ~ tail => t1::tail
				  } ) |
                            ( "(" ~> tff_xprod_type <~ ")" )

  /**
   * TFF formulas
   */

  lazy val tff_logic_formula =   tff_binary_formula | tff_unitary_formula
  lazy val tff_binary_formula =  tff_binary_nonassoc | tff_binary_assoc
  lazy val tff_binary_nonassoc = tff_unitary_formula ~ 
			      binary_nonassoc_connective ~ 
			      tff_unitary_formula ^^ {
				case f1 ~ op ~ f2 => op(f1,f2)
			      }
  lazy val tff_binary_assoc =  tff_or_formula | tff_and_formula
  lazy val tff_or_formula =
    tff_unitary_formula ~ "|" ~ rep1sep(tff_unitary_formula, "|") ^^ {
				  case f1 ~ "|" ~ tail => {
				      f1::tail reduceLeft { _ | _ }
				  }
			      }
  lazy val tff_and_formula =     
    tff_unitary_formula ~ "&" ~ rep1sep(tff_unitary_formula, "&") ^^ {
				  case f1 ~ "&" ~ tail => {
				      f1::tail reduceLeft { _ & _ }
				  }
    }
  lazy val tff_unitary_formula:PackratParser[IFormula] = 
                tff_quantified_formula | 
			      tff_unary_formula |
                            atom |
			       "(" ~> tff_logic_formula <~ ")"
  lazy val tff_unary_formula = "~" ~> tff_unitary_formula ^^ { ! _ }
  
  lazy val tff_quantified_formula:PackratParser[IFormula] = 
    (((forallSign ^^ { _ => Quantifier.ALL.asInstanceOf[Quantifier] } ) |
	    ("?"        ^^ { _ => Quantifier.EX.asInstanceOf[Quantifier] } )) ~ 
	     "[" ~ tff_varlist ~ "]" ^^ { 
		        case q ~ "[" ~ vl ~ "]" => { 
				  // remember current varTypes for later restoration
				  varTypesStack ::= varTypes
				  varTypes ++= vl
				  for (v <- vl)
				    env pushVar v.name
				  // Return the partially instantiated Quantifier-Formula
				  (f:IFormula) => (f /: vl) { case (f, _) =>  IQuantified(q, f) }
				} 
		     }) ~ ":" ~ tff_unitary_formula ^^ {
		        // Put together the two parts, quantification and formula
		        case quantTemplate ~ ":" ~ f => {
			      // restore varTypes as it was before
		          varTypes = varTypesStack.head
		          varTypesStack = varTypesStack.tail
                for (v <- varTypes)
                  env.popVar
		          quantTemplate(f)
		        } 
		      }


  // Variable list
  lazy val tff_varlist: PackratParser[List[TypedVar]] =  rep1sep(tff_var, ",")

  lazy val tff_var: PackratParser[TypedVar] = 
    ( variableStr ~ ":" ~ tff_atomic_type ^^ { 
	      case x ~ ":" ~ typ => TypedVar(x, TypeExistsChecked(typ)) 
      } ) |
    ( variableStr <~ guard(not(":")) ^^ { 
	      // default type of variables (in quantifications) is IType
	      x => TypedVar(x, IType) 
      } )

  lazy val tff_atomic_type = 
    // user-defined type
    defined_type |
    ( atomic_word ^^ { Type(_) } ) 
  // predefined type

  lazy val defined_type: PackratParser[Type] = 
    (("$oType" | "$o") ^^ { _ => OType }) |
    (("$iType" | ("$i" <~ guard(not("nt")))) ^^ { _ => IType }) |
    ("$tType" ^^ { _ => TType }) |
    ("$int" ^^ { _ => IntType })
   // $real | $rat | $int 

  /*
   * FOF formulas
   */


  lazy val fof_logic_formula =
    fof_binary_formula | fof_unitary_formula
  lazy val fof_binary_formula =
    fof_binary_nonassoc | fof_binary_assoc
  lazy val fof_binary_nonassoc =
    fof_unitary_formula ~ binary_nonassoc_connective ~ fof_unitary_formula ^^ {
      case f1 ~ op ~ f2 => op(f1,f2)
    }
  lazy val fof_binary_assoc =
    fof_or_formula | fof_and_formula
  lazy val fof_or_formula =
    fof_unitary_formula ~ "|" ~ rep1sep(fof_unitary_formula, "|") ^^ {
      case f1 ~ "|" ~ tail => f1::tail reduceLeft { _ | _ }
    }
  lazy val fof_and_formula =     
    fof_unitary_formula ~ "&" ~ rep1sep(fof_unitary_formula, "&") ^^ {
      case f1 ~ "&" ~ tail => f1::tail reduceLeft { _ & _ }
    }
  lazy val fof_unitary_formula:PackratParser[IFormula] = 
      fof_quantified_formula | fof_unary_formula | atom |
      "(" ~> fof_logic_formula <~ ")"
  lazy val fof_unary_formula = "~" ~> fof_unitary_formula ^^ { !(_) }
  lazy val fof_quantified_formula:PackratParser[IFormula] =
    (((forallSign ^^ { _ => Quantifier.ALL.asInstanceOf[Quantifier] } ) |
      ("?"        ^^ { _ => Quantifier.EX.asInstanceOf[Quantifier] } )) ~ 
       "[" ~ fof_varlist ~ "]" ^^ { 
              case q ~ "[" ~ vl ~ "]" => { 
                // remember current varTypes for later restoration
                varTypesStack ::= varTypes
                varTypes ++= vl
                for (v <- vl)
                  env pushVar v.name
                // Return the partially instantiated Quantifier-Formula
                (f:IFormula) => (f /: vl) { case (f, _) =>  IQuantified(q, f) }
              } 
           }) ~ ":" ~ fof_unitary_formula ^^ {
              // Put together the two parts, quantification and formula
              case quantTemplate ~ ":" ~ f => {
                // restore varTypes as it was before
                varTypes = varTypesStack.head
                varTypesStack = varTypesStack.tail
                for (v <- varTypes)
                  env.popVar
                quantTemplate(f)
              } 
            }


  // Variable list
  lazy val fof_varlist: PackratParser[List[TypedVar]] = 
    rep1sep(variableStr, ",") ^^ { _ map { TypedVar(_, IType) } } // looks cryptic?

 /**
* Definitions common to TFF and FOF
*/

  lazy val binary_nonassoc_connective = 
			      ( "=>" ^^ {
			        _ => { (x : IFormula, y : IFormula) => (x ==> y) } } ) |
			      ( "<=" <~ guard(not(">")) ^^ {
			        _ => { (x : IFormula, y : IFormula) => (y ==> x) } } ) |
			      ( "<=>" ^^ {
			        _ => { (x : IFormula, y : IFormula) => (x <=> y) } } ) |
			      ( "<~>" ^^ {
                  _ => { (x : IFormula, y : IFormula) => !(x <=> y) } } ) 

  // Atom
  // Difficulty is determining the type. If fun(args...) has been read 
  // it is possible that fun(args...) is an atom or the lhs of an equation.
  // Determining the type hence nees to be deferred until "=" (or "!=") is 
  // seen (or not). Once that is clear, the signature is extended 
  // appropriately. It can only be done this late because otherwise the signature
  // might be extended unappropriately, and backtracking (in the parser)
  // cannot undo that.

  lazy val atom : PackratParser[IFormula] =
    ( "$true" ^^ { _ => i(true) }) |
    ( "$false" ^^ { _ => i(false) }) |
    // eqn with lhs a variable
    ( constant_or_variable ~ equalsSign ~ term ^^ { 
	      case x ~ _ ~ t => CheckedEquation(x, t)
      } ) |
    ( constant_or_variable ~ "!=" ~ term ^^ { 
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
  lazy val term: PackratParser[(ITerm, Type)] =
    funterm | constant_or_variable | bg_constant
    
  lazy val variableStr: PackratParser[String] =
    regex(new Regex("[A-Z][a-zA-Z0-9_]*"))
    
/*    lazy val variable : PackratParser[] =
    variableStr ^^ { name => {
      val t = env.loo
    }} } */
    
  lazy val funterm: PackratParser[(ITerm, Type)] =
    functor ~ "(" ~ termlist ~ ")" ^^ {
      case functor ~ "(" ~ termlist ~ ")" => {
        (env lookupSym functor) match {
          case Environment.Function(f, false) =>
            (IFunApp(f, for ((t, _) <- termlist) yield t), IntType)
          case _ =>
            throw new SyntaxError("Unexpected symbol: " + functor)
        }
        
//	      if (!(Sigma.ranks contains functor))
//	        Sigma += (functor -> Rank((termlist map { _ => IType }) -> IType))
	    // todo: check well-sortedness of arguments
//	    CheckedFunTerm(functor, termlist) 
    }
  }

  lazy val termlist = rep1sep(term, ",")

  // Foreground constant or parameter
  lazy val constant_or_variable: PackratParser[(ITerm, Type)] = 
    // a constant cannot be followed by a parenthesis, would see a FunTerm instead
    // Use atomic_word instead of functor?
    guard(functor ~ not("(")) ~> functor ^^ { functor => 
      (env lookupSym functor) match {
        case Environment.Constant(c, _) => (i(c), IntType)
        case Environment.Variable(index, false) => (v(index), IntType)
        case _ => throw new SyntaxError("Unexpected symbol: " + functor)
      }
      
//	    if (!(Sigma.ranks contains functor)) 
//	      Sigma += (functor -> Rank0(IType))
  }

  // Background literal constant
  lazy val bg_constant = regex(isIntegerConstRegEx) ^^ { 
	  s => (i(IdealInt(s)), IntType)
  }
  
  // lexical: don't confuse = with => (the lexer is greedy)
  lazy val equalsSign = "=" <~ guard(not(">"))
  
  lazy val forallSign = "!" <~ guard(not("="))

  lazy val functor = keyword | atomic_word

  lazy val atomic_word: PackratParser[String] = 
    ( regex("""'.*'""".r) ^^ { _.drop(1).dropRight(1) } ) |
    regex("[a-z][a-zA-Z0-9_]*".r)

  lazy val keyword = regex("[$][a-z]+".r)

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
  lazy val comment: PackratParser[List[IFormula]] =
    """%.*""".r ^^ (x => List(null /* Comment(x) */))

  lazy val include: PackratParser[List[IFormula]] = 
    "include" ~> "(" ~> atomic_word <~ ")" <~ "." ^^ { case fileName  => {
	    val TPTPHome = System.getenv("TPTP")
	    val filename = (if (TPTPHome == null) "" else TPTPHome + "/") + fileName
	    val reader = new java.io.BufferedReader (
                   new java.io.FileReader(new java.io.File (filename)))
	    parseAll[List[List[IFormula]]](TPTP_input, reader).get.flatten
	  } 
  }

  /**
   * CheckedXX: creates an XX, type-checked against sig and varTypes
   */
  def CheckedEquation(s: (ITerm, Type), t: (ITerm, Type)) = {
    val (s_term, s_type) = s
    val (t_term, t_type) = t
    if (s_type != OType && s_type == t_type) 
      s_term === t_term
    else
      throw new SyntaxError(
         "Error: ill-sorted (dis)equation: between " + s_term + " and " + t_term)
  }

  def CheckedAtom(pred: String, args: List[(ITerm, Type)]) : IFormula = pred match {
    case "$less"      => binaryIntPred(pred, args)( _ < _ )
    case "$lesseq"    => binaryIntPred(pred, args)( _ <= _ )
    case "$greater"   => binaryIntPred(pred, args)( _ > _ )
    case "$greatereq" => binaryIntPred(pred, args)( _ >= _ )
    case "$evaleq"    => binaryIntPred(pred, args)( _ === _ )
//    case "$divides"   => binaryIntPred(pred, args)( _ <= _ )
  
    case pred => (env lookupSym pred) match {
     case Environment.Predicate(p) =>
       IAtom(p, for ((t, _) <- args) yield t)
     case _ =>
       throw new SyntaxError("Unexpected symbol: " + functor)
    }
  }
  
  private def binaryIntPred(tptpOp : String, args: List[(ITerm, Type)])
                           (op : (ITerm, ITerm) => IFormula) : IFormula = {
    checkArgTypes(tptpOp, args, List(IntType, IntType))
    op(args(0)._1, args(1)._1)
  }
  
  private def checkArgTypes(op : String,
                            args: List[(ITerm, Type)],
                            types : List[Type]) : Unit =
    if (types != (args map (_._2)))
      throw new SyntaxError("Incorrect arguments for " + op + ": " + (args map (_._1)))
  
/*      // Assume that pred has been entered into sig already
    if (Sigma(pred).argsTypes == Sigma.typesOf(args, varTypes))
  Atom(pred, args)
    else
	throw new SyntaxError("Error: ill-sorted atom: " + Atom(pred, args)) */

  def CheckedFunTerm(fun: String, args: List[(ITerm, Type)]) : (ITerm, Type) =
    (env lookupSym fun) match {
       case Environment.Function(f, false) =>
         (IFunApp(f, for ((t, _) <- args) yield t), IntType)
       case Environment.Constant(c, _) => {
         if (!args.isEmpty)
           throw new SyntaxError("Constant does not accept arguments: " + functor)
         (IConstant(c), IntType)
       }
       case _ =>
         throw new SyntaxError("Unexpected symbol: " + functor)
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

  def TypeExistsChecked(typ: Type) = 
    if (declaredTypes contains typ)
      typ
    else
      throw new SyntaxError("Error: type has not been declared: " + typ)
}



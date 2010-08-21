/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010 Philipp Ruemmer <ph_r@gmx.net>
 *                    Angelo Brillout <bangelo@inf.ethz.ch>
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

package ap.interpolants

import scala.util.Sorting
import scala.collection.mutable.{Stack => MStack, Map => MMap, HashMap => MHashMap}

import ap._
import ap.basetypes.IdealInt
import ap.parser._
import ap.parameters.{PreprocessingSettings, GoalSettings, Param}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction, Quantifier}
import ap.terfor.TerForConvenience._
import ap.terfor.{TermOrder, ConstantTerm}
import ap.proof.ModelSearchProver
import ap.util.{Debug, Seqs}

/**
 * Abstract class providing some functionality commonly needed for
 * interpolation-based software verification, e.g., axioms and prover for
 * bitvector arithmetic, arrays, etc.
 */
abstract class SoftwareInterpolationFramework {

  private val AC = Debug.AC_MAIN

  protected var interpolationProblemBasename = ""
  protected var interpolationProblemNum = 0

  //////////////////////////////////////////////////////////////////////////////
  
  private val preludeEnv = new Environment
  private val functionEncoder = new FunctionEncoder
  
  private val (backgroundPred, preludeOrder) = Console.withOut(Console.err) {
    print("Reading prelude ... ")
    val reader = ResourceFiles.preludeReader
    val (iBackgroundPredRaw, _, signature) = Parser2InputAbsy(reader, preludeEnv)
    reader.close

    val (iBackgroundFors, _, signature2) =
      Preprocessing(iBackgroundPredRaw, List(), signature,
                    PreprocessingSettings.DEFAULT, functionEncoder)
    functionEncoder.clearAxioms
    
    val iBackgroundPred =
      IExpression.connect(for (INamedPart(_, f) <- iBackgroundFors.elements)
                            yield f,
                          IBinJunctor.Or)
    implicit val order = signature2.order
    
    val res = InputAbsy2Internal(iBackgroundPred, order)
    
    // we put the (possibly extended) order back into the environment, so that
    // we can continue parsing the transition relations with it
    preludeEnv.order = order

    val reducedRes = ReduceWithConjunction(Conjunction.TRUE, order)(conj(res))
    
    println("done")
    (reducedRes, order)
  }

  protected val preludeSignature = preludeEnv.toSignature
  
  protected val frameworkVocabulary = new FrameworkVocabulary(preludeEnv)
  import frameworkVocabulary.{select, store}
                                                              
  //////////////////////////////////////////////////////////////////////////////

  private val preprocSettings =
    Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(PreprocessingSettings.DEFAULT,
                                                     Set(select, store))
  private val interpolationSettings =
    Param.PROOF_CONSTRUCTION.set(GoalSettings.DEFAULT, true)
  private val validityCheckSettings =
    GoalSettings.DEFAULT

  protected lazy val interpolationProver = {
    val prover = ModelSearchProver emptyIncProver interpolationSettings
    prover.conclude(backgroundPred, preludeOrder)
  }
  
  protected lazy val validityCheckProver = {
    val prover = ModelSearchProver emptyIncProver validityCheckSettings
    prover.conclude(backgroundPred, preludeOrder)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private val simplifier = new InterpolantSimplifier (select, store)
  
  protected def toInputAbsyAndSimplify(c : Conjunction) : IFormula = {
	val internalInter = Internal2InputAbsy(c, functionEncoder.predTranslation)
//    ap.util.Timer.measure("simplifying") {
      simplifier(internalInter)
//    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  protected def parseProblem(reader : java.io.Reader) : (IFormula, Signature) = {
    val (problem, _, sig) = Parser2InputAbsy(reader, preludeEnv.clone)
    (problem, sig)
  }

  protected def toNamedParts(f : IFormula, sig : Signature) = {
    val (iProblemParts, _, sig2) =
      Preprocessing(f, List(), sig, preprocSettings, functionEncoder)
    functionEncoder.clearAxioms
    implicit val order = sig2.order
    
    val namedParts =
      Map() ++ (for (INamedPart(name, f) <- iProblemParts)
                yield (name -> conj(InputAbsy2Internal(f, order))))

    (namedParts, sig2)
  }
  
  protected def toInternal(f : IFormula,
                           sig : Signature) : (Conjunction, TermOrder) = {
    val (parts, sig2) = toNamedParts(f, sig)
    implicit val order = sig2.order
    (disj(for ((_, f) <- parts) yield f), order)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Read a given problem, split it into the different parts, try to
   * simplify bitvector expressions as far as possible, and convert it to
   * internal presentation. Bitvector simplifications are done based on the type
   * declarations inSigned, inUnsigned, and inArray. The problem will also be
   * restructured such that the type declaration of a constant occurs in the
   * first part in which the constant is used (sorted the partitions
   * lexicographically according to their name).
   */
  protected def parseAndSimplify(input : java.io.Reader)
                                : (Map[PartName, Conjunction], Signature) = {
    import IExpression._
    import IBinJunctor._
    
    val (problem, signature) = parseProblem(input)

    // turn the formula into a list of its named parts
    val fors = PartExtractor(problem)
    val namedParts =
      Map() ++ (for (INamedPart(name, f) <- fors.elements) yield (name -> f))
    
    // extract the given type assumptions, which we then add to the first
    // partition where the declared symbol is used
    val assumptions = namedParts.getOrElse(PartName.NO_NAME, i(false))
    
    val (typeAssumptions, otherAssumptions) =
      LineariseVisitor(Transform2NNF(assumptions), Or) partition {
        case INot(IAtom(frameworkVocabulary.inSigned | frameworkVocabulary.inUnsigned,
                        Seq(Const(_), IConstant(_)))) |
             INot(IAtom(frameworkVocabulary.inArray, Seq(IConstant(_)))) =>
          true
        case _ =>
          false
      }
    
    val namedPartsWithoutTypeAssumptions =
      namedParts + (PartName.NO_NAME -> connect(otherAssumptions, Or))
    
    // simplify expressions and re-inject the type assumptions
    val env = new SymbolRangeEnvironment
    env.inferRanges(assumptions, frameworkVocabulary)
    
    val simplifier = new BitvectorSimplifier(env, frameworkVocabulary)

    var remainingTypeAssumptions = typeAssumptions
    val simplifiedParts =
      for (name <- sortNamesLex(namedPartsWithoutTypeAssumptions) ++
                   List(PartName.NO_NAME)) yield {
        val namedFor = namedPartsWithoutTypeAssumptions(name)
        
        env.push
        env.inferRanges(namedFor, frameworkVocabulary)
        val simplifiedFor = simplifier.visit(namedFor, {})._1.asInstanceOf[IFormula]
        env.pop
        
        val occurringConsts = SymbolCollector constants simplifiedFor
        val (usedAssumptions, unusedAssumptions) =
          remainingTypeAssumptions partition (
            (c) => (SymbolCollector constants c) subsetOf occurringConsts)

        val simplifiedForWithAssumptions =
          simplifiedFor ||| connect(usedAssumptions, Or)
        remainingTypeAssumptions = unusedAssumptions
        
        INamedPart(name, simplifiedForWithAssumptions)
      }
    
    val simplifiedRes = connect(simplifiedParts, Or) |
                        INamedPart(PartName.NO_NAME, connect(otherAssumptions, Or))
    
    toNamedParts(simplifiedRes, signature)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  protected def dumpInterpolationProblem(transitionParts : Map[PartName, Conjunction],
               	                         sig : Signature) : Unit =
    if (interpolationProblemBasename == "") {
      // nothing to do
    } else {
      import IExpression._
    
      val simpParts =
        for (n <- (if (transitionParts contains PartName.NO_NAME)
                     List(PartName.NO_NAME)
                   else
                     List()) ++
                   sortNamesLex(transitionParts)) yield {
        val f = !transitionParts(n)
        val sf = PresburgerTools.eliminatePredicates(f, !backgroundPred, sig.order)
        INamedPart(n, Internal2InputAbsy(sf, Map()))
      }

      val filename = interpolationProblemBasename + interpolationProblemNum + ".pri"
      interpolationProblemNum = interpolationProblemNum + 1
      
      Console.withOut(new java.io.FileOutputStream(filename)) {
        PrincessLineariser(!connect(simpParts, IBinJunctor.And),
                           sig updateOrder sig.order.resetPredicates)
      }
    }

  //////////////////////////////////////////////////////////////////////////////

  protected def genInterpolants(formulas : Seq[Conjunction],
                                commonFormula : Conjunction,
                                order : TermOrder)
                               : Either[Conjunction, Iterator[Conjunction]] = {
//    ap.util.Timer.measure("solving") {
       interpolationProver.conclude(formulas ++ List(commonFormula), order)
                          .checkValidity(false)
//    }
    match {
      case Left(counterexample) =>
        Left(counterexample)
      case Right(cert) => {
        println("Found proof (size " + cert.inferenceCount + ")")

        Right {
          var lastInterpolant = Conjunction.TRUE
          for (i <- Iterator.range(1, formulas.size)) yield
            if (formulas(i-1).isFalse) {
              // no need to generate a new interpolant, just take the previous
              // one
              lastInterpolant
            } else {
              val iContext =
                InterpolationContext (formulas take i, formulas drop i,
                                      List(commonFormula, backgroundPred),
                                      order)
//              ap.util.Timer.measure("interpolating") {
                lastInterpolant = Interpolator(cert, iContext)
                lastInterpolant
//              }
          }}
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Sort the transition relations lexicographically according to their name;
   * NO_NAME is ignored and removed
   */
  protected def sortNamesLex[A](transitionParts : Map[PartName, A]) : Seq[PartName] = {
    val names = (transitionParts.keySet - PartName.NO_NAME).toArray
    Sorting.stableSort(names, (x : PartName, y : PartName) => x.toString < y.toString)
    names
  }

  protected def simplifyBitvectorFor(f : IFormula,
                                     typeAssumptions : IFormula) : IFormula = {
    val env = new SymbolRangeEnvironment
    env.inferRanges(typeAssumptions, frameworkVocabulary)
    env.inferRanges(f, frameworkVocabulary)
    
    val simplifier = new BitvectorSimplifier(env, frameworkVocabulary)
    
    simplifier.visit(f, {})._1.asInstanceOf[IFormula]
  }
  
}

////////////////////////////////////////////////////////////////////////////////

object ResourceFiles {

  private val preludeFile = "wolverine_resources/prelude.pri"
//  private val commOpsFile = "/resources/commutativeOperators.list"

  private def toReader(stream : java.io.InputStream) =
    new java.io.BufferedReader (new java.io.InputStreamReader(stream))

  private def resourceAsStream(filename : String) =
//    ResourceFiles.getClass.getResourceAsStream(filename)
    new java.io.FileInputStream(filename)
  
  def preludeReader = toReader(resourceAsStream(preludeFile))
//  def commOpsReader = toReader(resourceAsStream(commOpsFile))
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Extended version of the InputAbsy simplifier that also rewrites certain
 * array expressions:
 *    \exists int a; x = store(a, b, c)
 * is replaced with
 *    select(x, b) = c 
 */
class InterpolantSimplifier(select : IFunction, store : IFunction)
      extends ap.parser.Simplifier {
  import IBinJunctor._
  import IIntRelation._
  import IExpression._
  import Quantifier._

  private class StoreRewriter(depth : Int) {
    var foundProblem : Boolean = false
    var storeArgs : Option[(ITerm, ITerm)] = None

    def rewrite(t : ITerm) : ITerm = t match {
      case IPlus(t1, t2) => rewrite(t1) +++ rewrite(t2)
      case IFunApp(`store`, Seq(IVariable(`depth`), t1, t2)) => {
        if (storeArgs != None)
          foundProblem = true
        storeArgs = Some(shiftVariables(t1), shiftVariables(t2))
        0
      }
      case _ => shiftVariables(t)
    }
    
    private def shiftVariables(t : ITerm) : ITerm = {
      if ((SymbolCollector variables t) contains IVariable(depth))
        foundProblem = true
      VariableShiftVisitor(t, depth + 1, -1)
    }
  }
  
  private def rewriteEquation(t : ITerm, depth : Int) : Option[IFormula] = {
    val rewriter = new StoreRewriter(depth)
    val newT = rewriter rewrite t

    rewriter.storeArgs match {
      case Some((t1, t2)) if (!rewriter.foundProblem) =>
        Some(select(-newT, t1) === t2)
      case _ =>
        None
    }
  }
  
  private def translate(f : IFormula,
                        negated : Boolean,
                        depth : Int) : Option[IFormula] = f match {
      
    case IQuantified(q, subF) if (q == (if (negated) ALL else EX)) =>
      for (res <- translate(subF, negated, depth + 1)) yield IQuantified(q, res)
        
    case IIntFormula(EqZero, t) if (!negated) =>
      rewriteEquation(t, depth)
    
    case INot(IIntFormula(EqZero, t)) if (negated) =>
      for (f <- rewriteEquation(t, depth)) yield !f
        
    case _ => None
  }
  
  private def elimStore(expr : IExpression) : IExpression = expr match {
    case IQuantified(EX, f) =>  translate(f, false, 0) getOrElse expr
    case IQuantified(ALL, f) => translate(f, true, 0) getOrElse expr
    case _ => expr
  }

  protected override def furtherSimplifications(expr : IExpression) = elimStore(expr)
}

////////////////////////////////////////////////////////////////////////////////

class FrameworkVocabulary(preludeEnv : Environment) {
  private def lookupFun(n : String) = preludeEnv.lookupSym(n) match {
    case Environment.Function(f) => f
    case _ => throw new Error("Expected " + n + " to be defined as a function");
  }
  
  private def lookupPred(n : String) = preludeEnv.lookupSym(n) match {
    case Environment.Predicate(p) => p
    case _ => throw new Error("Expected " + n + " to be defined as a predicate");
  }
  
  val select = lookupFun("select")
  val store = lookupFun("store")
  val pair = lookupFun("pair")
  val proj1 = lookupFun("proj1")
  val proj2 = lookupFun("proj2")
  
  val addSigned = lookupFun("addSigned")
  val addUnsigned = lookupFun("addUnsigned")
  val subSigned = lookupFun("subSigned")
  val subUnsigned = lookupFun("subUnsigned")
  val mulSigned = lookupFun("mulSigned")
  val mulUnsigned = lookupFun("mulUnsigned")
  val minusSigned = lookupFun("minusSigned")
  val minusUnsigned = lookupFun("minusUnsigned")

  val inSigned = lookupPred("inSigned")
  val inUnsigned = lookupPred("inUnsigned")
  val inArray = lookupPred("inArray")
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class to store information about the value range of constants; this
 * information is later used to simplify expressions
 */
class SymbolRangeEnvironment {
  import IExpression._
  
  private val frames = new MStack[MMap[ConstantTerm, Interval]]
  frames.push(new MHashMap)
  
  private def topFrame = frames.top
  
  def push = frames.push(topFrame.clone)
  
  def pop = frames.pop
  
  def addRange(c : ConstantTerm, iv : Interval) = (topFrame get c) match {
    case Some(oldIV) => topFrame += (c -> (oldIV meet iv))
    case None => topFrame += (c -> iv)
  }
  
  def apply(c : ConstantTerm) = topFrame get c

  /**
   * Extract information from the inSigned and inUnsigned predicates in a
   * formula in the succedent
   */
  def inferRanges(f : IFormula, voc : FrameworkVocabulary) =
    for (conj <- LineariseVisitor(Transform2NNF(f), IBinJunctor.Or)) conj match {
      case INot(IAtom(voc.inSigned, Seq(SignConst(base, 1), IConstant(c)))) =>
        addRange(c, (Interval signed base))
      case INot(IAtom(voc.inUnsigned, Seq(SignConst(base, 1), IConstant(c)))) =>
        addRange(c, (Interval unsigned base))
      case _ => // nothing
    }
  
}

object Interval {
  def apply(v : IdealInt) : Interval = Interval(v, v)
  def signed(base : IdealInt) = Interval(-base, base - 1)
  def unsigned(base : IdealInt) = Interval(0, base * 2 - 1)
}

case class Interval(lower : IdealInt, upper : IdealInt) {
  def meet(that : Interval) =
    Interval(this.lower max that.lower, this.upper min that.upper)
  def join(that : Interval) =
    Interval(this.lower min that.lower, this.upper max that.upper)
    
  def subsetOf(that : Interval) =
    (this.lower >= that.lower) && (this.upper <= that.upper)
    
  def +(that : Interval) =
    Interval(this.lower + that.lower, this.upper + that.upper)
  def -(that : Interval) = this + (that * IdealInt.MINUS_ONE)
  def *(that : IdealInt) : Interval =
    if (that.isPositive)
      Interval(lower * that, upper * that)
    else
      Interval(upper * that, lower * that)
  def *(that : Interval) : Interval =
    (this * that.lower) join (this * that.upper)
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class to simplify bit-vector expressions using information about the range of
 * operands. In particular, bit-vector operations are replaced with simple
 * Presburger operations if it is guaranteed that no overflows can occur
 */
class BitvectorSimplifier(ranges : SymbolRangeEnvironment,
                          voc : FrameworkVocabulary)
      extends CollectingVisitor[Unit, (IExpression, Option[Interval])] {
  import IExpression._
  
  /**
   * Map from unary bit-vector operations to Presburger operations
   */
  private val unaryBitvectorOps
              : Map[IFunction,
                    (// range of the operand/result type
                     IdealInt => Interval,
                     // corresponding operation on intervals
                     Interval => Interval,
                     // corresponding operation on Presburger terms
                     // (might only be defined for some operands)
                     PartialFunction[ITerm, ITerm])] =
    Map(voc.minusSigned ->   (Interval signed _,
                              _ * IdealInt.MINUS_ONE,
                              { case x => -x }),
        voc.minusUnsigned -> (Interval unsigned _,
                              _ * IdealInt.MINUS_ONE,
                              { case x => -x }))
  
  /**
   * Map from binary bit-vector operations to Presburger operations
   */
  private val binBitvectorOps
              : Map[IFunction,
                    (// range of the operand/result type
                     IdealInt => Interval,
                     // corresponding operation on intervals
                     (Interval, Interval) => Interval,
                     // corresponding operation on Presburger terms
                     // (might only be defined for some operands)
                     PartialFunction[(ITerm, ITerm), ITerm])] =
    Map(voc.addSigned ->   (Interval signed _,
                            _ + _,
                            { case (x, y) => x + y }),
        voc.addUnsigned -> (Interval unsigned _,
                            _ + _,
                            { case (x, y) => x + y }),
        voc.subSigned ->   (Interval signed _,
                            (x, y) => x + y * IdealInt.MINUS_ONE,
                            { case (x, y) => x - y }),
        voc.subUnsigned -> (Interval unsigned _,
                            (x, y) => x + y * IdealInt.MINUS_ONE,
                            { case (x, y) => x - y }),
        voc.mulSigned ->   (Interval signed _,
                            _ * _,
                            { case (Const(v), x) => x * v
                              case (x, Const(v)) => x * v }),
        voc.mulUnsigned -> (Interval unsigned _,
                            _ * _,
                            { case (Const(v), x) => x * v
                              case (x, Const(v)) => x * v }))
  
  private def toFirst(subres : Seq[(IExpression, Option[Interval])]) =
    for ((a, _) <- subres) yield a
  
  override def preVisit(t : IExpression, arg : Unit) : PreVisitResult = t match {
    case t : ITrigger =>
      // don't descend below triggers
      ShortCutResult((t, None))
    case _ => super.preVisit(t, arg)
  }
  
  def postVisit(t : IExpression, arg : Unit,
                subres : Seq[(IExpression, Option[Interval])])
               : (IExpression, Option[Interval]) = t match {
    case IIntLit(v) => (t, Some(Interval(v)))
    case IConstant(c) => (t, ranges(c))
    case IVariable(_) => (t, None)
    case ITimes(coeff, _) =>
      (t update toFirst(subres),
       for (i <- subres(0)._2) yield (i * coeff))
    case IPlus(_, _) =>
      (t update toFirst(subres),
       for (i1 <- subres(0)._2; i2 <- subres(1)._2) yield (i1 + i2))

    case IFunApp(fun, Seq(SignConst(base, 1), _))
      // unary bit-vector operators
      if (unaryBitvectorOps contains fun) => {
        val (typeCtor, intervalOp, presburgerOp) = unaryBitvectorOps(fun)
        val typeRange = typeCtor(base)
        val t1 = subres(1)._1.asInstanceOf[ITerm]
        
        if ((presburgerOp isDefinedAt t1) &&
            (subres(1)._2 exists (_ subsetOf typeRange))) {
          val iv = intervalOp(subres(1)._2.get)

          if (iv subsetOf typeRange)
            // then we know that there are no overflows and can just apply
            // normal Presburger operations
            (presburgerOp(t1), Some(iv))
          else
            // if the operands are at least within the correct range, it is
            // guaranteed that the result also is
            (t update toFirst(subres), Some(typeRange))
        } else {
          (t update toFirst(subres), None)
        }
      }

    // special handling of unsigned multiplications: if it seems advantageous,
    // add an explicit negation operator
    case IFunApp(voc.mulUnsigned, Seq(SignConst(base, 1), _, _))
      if ((subres(1)._2 exists (_ subsetOf (Interval unsigned base))) &&
          (subres(2)._2 exists (_ subsetOf Interval(base + 1, base * 2 - 1)))) => {
      
      val Seq(_, (t1 : ITerm, Some(i1)), (t2 : ITerm, Some(i2))) = subres

      postVisit(t, arg,
                List(subres(0),
                     (voc.minusUnsigned(base, t1), Some(Interval unsigned base)),
                     (base * 2 - t2, Some(Interval(base * 2) - i2))))
    }

    case IFunApp(fun, Seq(SignConst(base, 1), _, _))
      // binary bit-vector operators
      if (binBitvectorOps contains fun) => {
        val (typeCtor, intervalOp, presburgerOp) = binBitvectorOps(fun)
        val typeRange = typeCtor(base)
        
        val Seq(_, (t1 : ITerm, _), (t2 : ITerm, _)) = subres
        
        if ((presburgerOp isDefinedAt (t1, t2)) &&
            (subres(1)._2 exists (_ subsetOf typeRange)) &&
            (subres(2)._2 exists (_ subsetOf typeRange))) {
          val iv = intervalOp(subres(1)._2.get, subres(2)._2.get)

          if (iv subsetOf typeRange)
            // then we know that there are no overflows and can just apply
            // normal Presburger operations
            (presburgerOp(t1, t2), Some(iv))
          else
            // if the operands are at least within the correct range, it is
            // guaranteed that the result also is
            (t update toFirst(subres), Some(typeRange))
        } else {
          (t update toFirst(subres), None)
        }
      }

    case _ =>
      (t update toFirst(subres), None)
  }
  
}
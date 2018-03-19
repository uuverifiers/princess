package ap.connection; // 

import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction}
import ap.terfor.preds.{Atom, PredConj, Predicate}
import ap.connection.connection.BREUOrder
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Debug}

object PseudoClause {



  var DEBUGPrint = true
  var nextPredicate = 0
  var nextTerm = 0  
  def dprintln(str : String) = if (DEBUGPrint) println(str)


  //
  //
  //
  // CONVERSION TO CNF ...
  //
  //
  //
  //

  def convertNegFunEq(funEq : Atom) : (FunEquation, NegEquation, BREUOrder) = {
    dprintln("convertNegFunEq(" + funEq + ")")
    val fun = funEq.pred

    // val res = funEq(funEq.length-1).lastTerm.constants.head

    val args = funEq.init
    dprintln("\targs: " + args.mkString(", "))

    val res = funEq.last
    dprintln("\tres: " + res)    

    val newTerm = new ConstantTerm("DUMMY_TERM_" + nextTerm)
    val newBREUOrder = List((newTerm, false))
    val newTermOrder = funEq.order.extend(newTerm)

    val negEqLC = LinearCombination(List((ap.basetypes.IdealInt.ONE, newTerm), (ap.basetypes.IdealInt.MINUS_ONE, res)), newTermOrder)
    dprintln("\tnegEqLC: " + negEqLC)

    nextTerm += 1
    val lc = LinearCombination(newTerm, newTermOrder)
    val newFunEq = FunEquation(Atom(fun, args ++ List(lc), newTermOrder))
    dprintln("\tnewFunEq: " + newFunEq)
    // val newEq = NegEquation(res.constants.head, newTerm)
    val (lhs, rhs, newEq) = eqTerms(negEqLC, newTermOrder)
    val eq = NegEquation(lhs, rhs)
    dprintln("\teq: " + eq)
    (newFunEq, eq, newBREUOrder)
  }


  /**
    *  AND THIS IS UNDER DOUBLE NEGATION?

    * Here conj is pseudo-literal. 
    * This means it is an actual conjunction...
    * 
    * Here we sometimes get a negated conjunction. I do not know why...
    */
  def conjToPseudoLiteral(conj : Conjunction, funPreds : Set[Predicate]) : (List[FunEquation], Node) = {
    dprintln("conjToPseudoLiteral(" + conj + ")")
    dprintln("\tfunPreds: " + funPreds.mkString(","))
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.positiveEqs.size == 0)
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.negativeEqs.size <= 1)
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.size == 0)    
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    val funEqs =
      (for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList

    val negFunEqs =
      (for (p <- conj.predConj.negativeLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList


    dprintln("\tfunEqs: " + funEqs.mkString(", "))
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, negFunEqs.length == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////    

    // Two cases, either we have a negative equation or a ordinary literal
    if (conj.arithConj.negativeEqs.size == 1) {
      dprintln("ArithEqs")
      val eq = conj.arithConj.negativeEqs(0)
      dprintln("\t" + eq)
      val (c, d, newOrder) = eqTerms(eq, conj.order)
      dprintln("\tc" + c)
      dprintln("\td" + d)
      // Should we update the order?
      val tempPred = new Predicate("tempPred_" + nextPredicate, 1)
      nextPredicate += 1
      val a1: Atom = Atom(tempPred, List(LinearCombination(c, newOrder)), newOrder)
      dprintln("\ta1: " + a1)
      val a2: Atom = Atom(tempPred, List(LinearCombination(d, newOrder)), newOrder)
      dprintln("\ta2: " + a2)            
      val ret = (List(FunEquation(a1), FunEquation(a2)), NegEquation(c, d))
      dprintln("\tret: " + ret)
      ret
    } else {
      // There should only be one non-equational literal
      val posPredLits =
        (for (p <- conj.predConj.positiveLits.iterator; if !(p.predicates subsetOf funPreds)) yield PositiveLiteral(p)).toList

      val negPredLits =
        (for (p <- conj.predConj.negativeLits.iterator; if !(p.predicates subsetOf funPreds)) yield NegativeLiteral(p)).toList


      dprintln("posPredLits: "+ posPredLits.mkString(","))
      dprintln("negPreDLtis: "+ negPredLits.mkString(","))
      val singleLits = (posPredLits ++ negPredLits).toList

      //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
      Debug.assertInt(ConnectionProver.AC, singleLits.length <= 1)
      //-END-ASSERTION-//////////////////////////////////////////////////////////

      if (singleLits.isEmpty)
        (funEqs.toList.tail, funEqs.toList.head)
      else
        (funEqs.toList, singleLits.head)
    }
  }


  private def toConstant(lc : LinearCombination, order : TermOrder) : (ConstantTerm, TermOrder) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ConnectionProver.AC,
      (lc.isConstant &&
        (lc.constant.isZero || lc.constant.isOne)) ||
        (lc.size == 1 &&
          lc.leadingCoeff.isOne &&
          lc.leadingTerm.isInstanceOf[ConstantTerm]))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (lc.isConstant) {
      val c = new ConstantTerm ("int_" + lc.constant)
      (c, order.extend(c))
    } else {
      (lc.leadingTerm.asInstanceOf[ConstantTerm], order)
    }
  }

  private def eqTerms(lc : LinearCombination, order : TermOrder) :  (ConstantTerm, ConstantTerm, TermOrder) = {
    lc.size match {
      case 1 => {
        val (c1, order1) = toConstant(lc, order)
        val (c2, order2) = toConstant(LinearCombination.ZERO, order1)
        (c1, c2, order2)
      }
      case 2 if (lc.constants.size == 1 && lc.leadingCoeff.isOne) =>
        val (c2, newOrder) = toConstant(LinearCombination(-lc.constant), order)
        (lc.leadingTerm.asInstanceOf[ConstantTerm], c2, newOrder)
      case 2 => {
        //-BEGIN-ASSERTION-////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC,
          lc.size == 2 &&
            lc.getCoeff(0).isOne && lc.getCoeff(1).isMinusOne &&
            lc.getTerm(0).isInstanceOf[ConstantTerm] &&
            lc.getTerm(1).isInstanceOf[ConstantTerm])
        //-END-ASSERTION-//////////////////////////////////////////////
        
        (lc.getTerm(0).asInstanceOf[ConstantTerm], lc.getTerm(1).asInstanceOf[ConstantTerm], order)
      }
    }
  }  


  /**
    *  THIS FUNCTION IS UNDER ONE NEGATION?
    * 
    * Here conj is a disjunction
    * Each literal in predConj.positiveLits/negativeLits is a literal
    * each conjunction in negatedConjs is a pseudo-lietral
    * 
    *  So it seems we should be able to put positive fun equations to other branches? (If we change quantifiers)
    */
  def disjunctionToClause(conj : Conjunction, funPreds : Set[Predicate]) : (PseudoClause, BREUOrder) = {
    dprintln("disjToClause(" + conj + ")")
    var newBREUOrder = List() : BREUOrder
    var newOrder = conj.order

    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.positiveEqs.size == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////


    dprintln("ArithEqs")
    dprintln("\tnegativeEqs: " + conj.arithConj.negativeEqs.mkString(", "))

    // We are under negation so every positive equality is negative nd v.v.
    val arithLiterals =
      (for (eq <- conj.arithConj.negativeEqs) yield {
        dprintln("" + eq)
        val (c, d, tmpOrder) = eqTerms(eq, newOrder)
        newOrder = tmpOrder
        dprintln("\tc" + c)
        dprintln("\td" + d)
        // Should we update the order?
        // val tempPred = new Predicate("tempPred_" + nextPredicate , 1)
        // nextPredicate += 1
        // val a1: Atom = Atom(tempPred, List(LinearCombination(c, newOrder)), newOrder)
        // val a2: Atom = Atom(tempPred, List(LinearCombination(d, newOrder)), newOrder)
        new PseudoLiteral(List(), Equation(c, d))
      })
    dprintln("\tarithLiterals: " + arithLiterals.mkString(","))

    val funEqs = 
      (for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield {
        val (feq, neq, tmpBREUOrder) = convertNegFunEq(p)
        newBREUOrder ++= tmpBREUOrder
        new PseudoLiteral(List(feq), neq)
      }).toList

    val negFunEqs =
      (for (p <- conj.predConj.negativeLits.iterator; if p.predicates subsetOf funPreds) yield (new PseudoLiteral(List(), FunEquation(p)))).toList
    dprintln("negFunEqs: " + negFunEqs.mkString(", "))

    


    // One of these should be negated...    
    val posPredLits =
      (for (p <- conj.predConj.positiveLits.iterator; if !(p.predicates subsetOf funPreds)) yield new PseudoLiteral(List(), NegativeLiteral(p))).toList

    val negPredLits =
      (for (p <- conj.predConj.negativeLits.iterator; if !(p.predicates subsetOf funPreds)) yield new PseudoLiteral(List(), PositiveLiteral(p))).toList


    dprintln("posPreDLits: " + posPredLits)
    dprintln("negPredLits: " + negPredLits)

    val pseudoLiterals =
      for (n <- conj.negatedConjs) yield {
        val (feq, lit) = conjToPseudoLiteral(n, funPreds)
        new PseudoLiteral(feq, lit)
      }

    // val funLiterals =
    //   for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield {
    //     val (feq, neq, tmpBREUOrder) = convertNegFunEq(p)
    //     newBREUOrder ++= tmpBREUOrder        
    //     new PseudoLiteral(List(feq), neq)
    //   }

    val ret = (new PseudoClause((negFunEqs ++ funEqs ++ arithLiterals ++ posPredLits ++ negPredLits ++ pseudoLiterals).toList), newBREUOrder)
    dprintln("resClause: " + ret)
    ret
  }



  // Converting one conjunction to a pseudoclause (which consists of consists pseudoliterals).
  // Three are two cases.
  // (A) It is a single positive or negative literal (this corresponds to a unit-clause)

  // (B) Negated conjs is larger than 0, and we have a disjunction (and then the predconj should be empty)
  def conjToClause(conj : Conjunction, funPreds : Set[Predicate]) : (PseudoClause, BREUOrder) = {
    dprintln("conjToClause(" + conj + ")")

    val predConj = conj.predConj
    val arithConj = conj.arithConj

    var breuOrder = List() : BREUOrder
    var termOrder = conj.order    

    val singleLiterals =
      (for (p <- predConj.positiveLits; if p.predicates subsetOf funPreds) yield new PseudoLiteral(List(), FunEquation(p))) ++
        (for (p <- predConj.positiveLits; if !(p.predicates subsetOf funPreds)) yield new PseudoLiteral(List(), PositiveLiteral(p))) ++
    (for (p <- predConj.negativeLits; if !(p.predicates subsetOf funPreds)) yield new PseudoLiteral(List(), NegativeLiteral(p))) ++
    (for (eq <- arithConj.negativeEqs) yield {
      dprintln("Negative ArithEqs")
      dprintln("\t" + eq)
      val (c, d, newOrder) = eqTerms(eq, conj.order)
      dprintln("\tc" + c)
      dprintln("\td" + d)
      new PseudoLiteral(List(), NegEquation(c, d))
    }) ++
    (for (eq <- arithConj.positiveEqs) yield {
      dprintln("Positive ArithEqs")
      dprintln("\t" + eq)
      val (c, d, newOrder) = eqTerms(eq, conj.order)
      dprintln("\tc" + c)
      dprintln("\td" + d)
      new PseudoLiteral(List(), Equation(c, d))
    })        

    val funEqs =
      (for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList    

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.inEqs.size == 0)
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 1 || singleLiterals.length == 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    dprintln("\tsingleLiterals: " + singleLiterals.mkString(","))

    val (pl, bo) = 
      if (!singleLiterals.isEmpty)
        (new PseudoClause(singleLiterals.toList), List())
      else
        disjunctionToClause(conj.negatedConjs(0), funPreds)

    // Move all universals to the front
    val newBo = bo.filter(_._2) ++ bo.filter(!_._2)
    (pl, newBo)
  }  


  def fromConjunction(conj : Conjunction, funPreds : Set[Predicate], debug : Boolean = false) : (PseudoClause, BREUOrder) = {
    DEBUGPrint = debug
    val (pc, order) = conjToClause(conj, funPreds)
    dprintln("" + conj)
    dprintln("->" + pc + " $ " + order)
    (pc, order)
  }
}



class PseudoClause(val pseudoLiterals : Seq[PseudoLiteral]) {
  override def toString = {
    pseudoLiterals.mkString(" v ")
  }
  def head : PseudoLiteral = pseudoLiterals.head
  def isUnit : Boolean = pseudoLiterals.length == 1
  def reverse : PseudoClause = new PseudoClause(pseudoLiterals.reverse)
  val length = pseudoLiterals.length

  def apply(i : Int) = pseudoLiterals(i)
}

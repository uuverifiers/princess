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




  def singleConjunctionToLits(conj : Conjunction, extraFunEqs : List[FunEquation], funPreds : Set[Predicate]) : List[PseudoLiteral] = {
    dprintln("singleConjLits(" + conj + ", " + extraFunEqs.mkString(", ") + ", " + funPreds.mkString(", ") + ")")

    val funEqs =
      (for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList

    val negFunEqs =
      (for (p <- conj.predConj.negativeLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList

    dprintln("\tfunEqs: " + funEqs.mkString(", "))


    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, negFunEqs.length == 0)
    Debug.assertInt(ConnectionProver.AC, funEqs.length == 0)    
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.size == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////    

    // Either we have an equation a negequation a positive pred or a negative pred

    // val asd1 = 
    //   (for (eq <- conj.arithConj.negativeEqs) yield {
    //     dprintln("NegArithEqs")
    //     dprintln("\t" + eq)
    //     val (c, d, newOrder) = eqTerms(eq, conj.order)
    //     dprintln("\tc" + c)
    //     dprintln("\td" + d)
    //     // Should we update the order?
    //     val tempPred = new Predicate("tempPred_" + nextPredicate, 1)
    //     nextPredicate += 1
    //     val a1: Atom = Atom(tempPred, List(LinearCombination(c, newOrder)), newOrder)
    //     dprintln("\ta1: " + a1)
    //     val a2: Atom = Atom(tempPred, List(LinearCombination(d, newOrder)), newOrder)
    //     dprintln("\ta2: " + a2)
    //     val ret = (List(FunEquation(a1), FunEquation(a2)), NegEquation(c, d))
    //     dprintln("\tret: " + ret)
    //     ret
    //   }).toList : Seq[(List[FunEquation], Node)]

    // val asd2 = 
    //   (for (eq <- conj.arithConj.positiveEqs) yield {
    //   dprintln("Positive ArithEqs")
    //   dprintln("\t" + eq)
    //   val (c, d, newOrder) = eqTerms(eq, conj.order)
    //   dprintln("\tc" + c)
    //   dprintln("\td" + d)
    //   (List() : List[FunEquation], Equation(c, d))
    //   }).toList : Seq[(List[FunEquation], Node)]

    val asd3 = 
      (for (p <- conj.predConj.positiveLits.iterator; if !(p.predicates subsetOf funPreds)) yield (List() : List[FunEquation], PositiveLiteral(p))).toList : Seq[(List[FunEquation], Node)]

    val asd4 =
      (for (p <- conj.predConj.negativeLits.iterator; if !(p.predicates subsetOf funPreds)) yield (List() : List[FunEquation], NegativeLiteral(p))).toList : Seq[(List[FunEquation], Node)]

    val literals : Seq[(List[FunEquation], Node)] = asd3 ++ asd4

    dprintln("Literals: " + literals.mkString(", "))
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, literals.length >= 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    (for ((a, b) <- literals) yield new PseudoLiteral(extraFunEqs ++ a, b)).toList
  }


  /**
    *  AND THIS IS UNDER DOUBLE NEGATION?

    * Here conj is pseudo-literal. 
    * This means it is an actual conjunction...
    * 
    */

  def conjToPseudoLiteralsAux(conj : Conjunction, funPreds : Set[Predicate]) : List[PseudoLiteral] = {
    dprintln("conjToPseudoLiterals(" + conj + ")")
    dprintln("\tfunPreds: " + funPreds.mkString(","))
    // WE NEED TO CONVERT THIS TO SEVERAL LITERALS!!

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.size < 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    val funEqs =
      (for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList

    val negFunEqs =
      (for (p <- conj.predConj.negativeLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList

    dprintln("\tfunEqs: " + funEqs.mkString(", "))


    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, negFunEqs.length == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////    

    // Either we have an equation a negequation a positive pred or a negative pred

    // val asd1 = 
    //   (for (eq <- conj.arithConj.negativeEqs) yield {
    //     dprintln("NegArithEqs")
    //     dprintln("\t" + eq)
    //     val (c, d, newOrder) = eqTerms(eq, conj.order)
    //     dprintln("\tc" + c)
    //     dprintln("\td" + d)
    //     // Should we update the order?
    //     val tempPred = new Predicate("tempPred_" + nextPredicate, 1)
    //     nextPredicate += 1
    //     val a1: Atom = Atom(tempPred, List(LinearCombination(c, newOrder)), newOrder)
    //     dprintln("\ta1: " + a1)
    //     val a2: Atom = Atom(tempPred, List(LinearCombination(d, newOrder)), newOrder)
    //     dprintln("\ta2: " + a2)
    //     val ret = (List(FunEquation(a1), FunEquation(a2)), NegEquation(c, d))
    //     dprintln("\tret: " + ret)
    //     ret
    //   }).toList : Seq[(List[FunEquation], Node)]

    // val asd2 = 
    //   (for (eq <- conj.arithConj.positiveEqs) yield {
    //   dprintln("Positive ArithEqs")
    //   dprintln("\t" + eq)
    //   val (c, d, newOrder) = eqTerms(eq, conj.order)
    //   dprintln("\tc" + c)
    //   dprintln("\td" + d)
    //   (List() : List[FunEquation], Equation(c, d))
    //   }).toList : Seq[(List[FunEquation], Node)]

    val asd3 = 
      (for (p <- conj.predConj.positiveLits.iterator; if !(p.predicates subsetOf funPreds)) yield (List() : List[FunEquation], PositiveLiteral(p))).toList : Seq[(List[FunEquation], Node)]

    val asd4 =
      (for (p <- conj.predConj.negativeLits.iterator; if !(p.predicates subsetOf funPreds)) yield (List() : List[FunEquation], NegativeLiteral(p))).toList : Seq[(List[FunEquation], Node)]

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, asd3.length <= 0)
    Debug.assertInt(ConnectionProver.AC, asd4.length <= 0)
    Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 1)    
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    val nc = conj.negatedConjs(0)
    dprintln("nc: " + conj.negatedConjs(0))
    val lits =  singleConjunctionToLits(nc, funEqs, funPreds)
    lits.toList
  }

  def conjToPseudoLiteralAux(conj : Conjunction, funPreds : Set[Predicate]) : PseudoLiteral = {
    dprintln("conjToPseudoLiteral(" + conj + ")")
    dprintln("\tfunPreds: " + funPreds.mkString(","))
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.positiveEqs.size <= 1)
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

    // Either we have an equation a negequation a positive pred or a negative pred

    val asd1 = 
      (for (eq <- conj.arithConj.negativeEqs) yield {
        dprintln("NegArithEqs")
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
      }).toList : Seq[(List[FunEquation], Node)]

    val asd2 = 
      (for (eq <- conj.arithConj.positiveEqs) yield {
      dprintln("Positive ArithEqs")
      dprintln("\t" + eq)
      val (c, d, newOrder) = eqTerms(eq, conj.order)
      dprintln("\tc" + c)
      dprintln("\td" + d)
      (List() : List[FunEquation], Equation(c, d))
      }).toList : Seq[(List[FunEquation], Node)]

    val asd3 = 
      (for (p <- conj.predConj.positiveLits.iterator; if !(p.predicates subsetOf funPreds)) yield (List() : List[FunEquation], PositiveLiteral(p))).toList : Seq[(List[FunEquation], Node)]

    val asd4 =
      (for (p <- conj.predConj.negativeLits.iterator; if !(p.predicates subsetOf funPreds)) yield (List() : List[FunEquation], NegativeLiteral(p))).toList : Seq[(List[FunEquation], Node)]

    val literal : Seq[(List[FunEquation], Node)] = asd1 ++ asd2 ++ asd3 ++ asd4

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, literal.length <= 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    if (literal.isEmpty)
      new PseudoLiteral(funEqs.tail, funEqs.head)
    else
      new PseudoLiteral(literal.head._1 ++ funEqs, literal.head._2)
  }


  def conjToPseudoLiterals(conj : Conjunction, funPreds : Set[Predicate]) : List[PseudoLiteral] = {
    if (conj.negatedConjs.length == 0) {
      List(conjToPseudoLiteralAux(conj, funPreds))
    } else {
      conjToPseudoLiteralsAux(conj, funPreds)
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
      (for (n <- conj.negatedConjs) yield {
        conjToPseudoLiterals(n, funPreds)
      }).flatten

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

    val topLevelFunEqs : Seq[FunEquation] =
      (for (p <- predConj.positiveLits; if p.predicates subsetOf funPreds) yield FunEquation(p))

    val topLevelLiteral : Seq[Node] =
        (for (p <- predConj.positiveLits; if !(p.predicates subsetOf funPreds)) yield PositiveLiteral(p)) ++
    (for (p <- predConj.negativeLits; if !(p.predicates subsetOf funPreds)) yield new NegativeLiteral(p)) ++
    (for (eq <- arithConj.negativeEqs) yield {
      dprintln("Negative ArithEqs")
      dprintln("\t" + eq)
      val (c, d, newOrder) = eqTerms(eq, conj.order)
      dprintln("\tc" + c)
      dprintln("\td" + d)
      NegEquation(c, d)
    }) ++
    (for (eq <- arithConj.positiveEqs) yield {
      dprintln("Positive ArithEqs")
      dprintln("\t" + eq)
      val (c, d, newOrder) = eqTerms(eq, conj.order)
      dprintln("\tc" + c)
      dprintln("\td" + d)
      Equation(c, d)
    })        

    val funEqs =
      (for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList    

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ConnectionProver.AC, conj.arithConj.inEqs.size == 0)
    //-END-ASSERTION-//////////////////////////////////////////////////////////

    dprintln("TopLevelFunEqs: " + topLevelFunEqs.mkString(","))
    dprintln("topLevelLiteral: " + topLevelLiteral.mkString(","))    
    val (pl, bo) : (PseudoClause, BREUOrder) = 
      if (topLevelLiteral.isEmpty && topLevelFunEqs.isEmpty) {
        disjunctionToClause(conj.negatedConjs(0), funPreds)
      } else {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
        Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.length == 0)
        Debug.assertInt(ConnectionProver.AC, topLevelLiteral.length <= 1)        
        //-END-ASSERTION-//////////////////////////////////////////////////////////
        if (topLevelLiteral.isEmpty)
          (new PseudoClause(List(new PseudoLiteral(topLevelFunEqs.toList.tail, topLevelFunEqs.head))), List())
        else
          (new PseudoClause(List(new PseudoLiteral(topLevelFunEqs.toList, topLevelLiteral.head))), List())
      }

    // Move all universals to the front
    val newBo = bo.filter(_._2) ++ bo.filter(!_._2)
    (pl, newBo)
  }  


  def fromConjunction(conj : Conjunction, funPreds : Set[Predicate], debug : Boolean = false) : (PseudoClause, BREUOrder) = {
    DEBUGPrint = debug
    val (pc, order) = conjToClause(conj, funPreds)
    dprintln("" + conj)
    dprintln("->" + pc + " $ " + order)
    (pc , order)
  }







  // When we convert a formula ...

  // On the way down we have to propagate all functional equations
  // On the way up we collect all PseudoLiterals

  // What about the ordering ...
  // if something is introduced, variables further down can see it, right?
  // So the order should be extended on the way up such that the new symbols are placed after the old ones (or v.v.) Lets Try!

  def ctc(conj : Conjunction, funEqs : List[FunEquation], funPreds : Set[Predicate], negated : Boolean) : (List[PseudoLiteral], BREUOrder) = {
    dprintln("ctc")
    dprintln("conj: " + conj)

    var newBREUOrder = List() : BREUOrder

    val (newFunEqs, newLiterals) : (List[FunEquation], List[PseudoLiteral]) = 
      if (negated) {

        // NEGATED CASE

        // Extract all funEqs (i.e., negative funPreds)
        val nfe =
          (for (p <- conj.predConj.negativeLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList ++ funEqs

        // Extract all literals at this level (i.e., positive/negative !funPreds, positive funPreds, positive/negative arithConjs)

        // positive !funPreds => negative !funPreds
        val lits1 =
          (for (p <- conj.predConj.positiveLits.iterator; if !(p.predicates subsetOf funPreds)) yield new PseudoLiteral(nfe, NegativeLiteral(p))).toList

        // negative !funPreds => positive !funPreds
        val lits2 =
          (for (p <- conj.predConj.negativeLits.iterator; if !(p.predicates subsetOf funPreds)) yield new PseudoLiteral(nfe, PositiveLiteral(p))).toList

        // positive funPreds => negative funPreds
        val lits3 =
          (for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield {
            val (feq, neq, tmpBREUOrder) = convertNegFunEq(p)
            newBREUOrder ++= tmpBREUOrder
            new PseudoLiteral(nfe ++ List(feq), neq)
          }).toList

        // positive arithConjs => negative arithConjs
        val lits4 =
          (for (eq <- conj.arithConj.positiveEqs) yield {
            val (c, d, _) = eqTerms(eq, conj.order)
            new PseudoLiteral(nfe, NegEquation(c, d))
          }).toList

        // negative arithConjs => positive arithConjs
        val lits5 =
          (for (eq <- conj.arithConj.negativeEqs) yield {
            val (c, d, _) = eqTerms(eq, conj.order)
            new PseudoLiteral(nfe, Equation(c, d))
          }).toList
        (nfe, lits1 ++ lits2 ++ lits3 ++ lits4 ++ lits5)
      } else {
        // POSITIVE CASE

        // Extract all funEqs (i.e., positive funPreds)
        val nfe =
          (for (p <- conj.predConj.positiveLits.iterator; if p.predicates subsetOf funPreds) yield FunEquation(p)).toList ++ funEqs

        // Extract all literals at this level (i.e., positive/negative !funPreds, negative funPreds, positive/negative arithConjs)

        // positive !funPreds
        val lits1 =
          (for (p <- conj.predConj.positiveLits.iterator; if !(p.predicates subsetOf funPreds)) yield new PseudoLiteral(nfe, PositiveLiteral(p))).toList

        // negative !funPreds
        val lits2 =
          (for (p <- conj.predConj.negativeLits.iterator; if !(p.predicates subsetOf funPreds)) yield new PseudoLiteral(nfe, NegativeLiteral(p))).toList

        // negative funPreds
        val lits3 =
          (for (p <- conj.predConj.negativeLits.iterator; if p.predicates subsetOf funPreds) yield {
            val (feq, neq, tmpBREUOrder) = convertNegFunEq(p)
            newBREUOrder ++= tmpBREUOrder
            new PseudoLiteral(nfe ++ List(feq), neq)
          }).toList

        // positive arithConjs
        val lits4 =
          (for (eq <- conj.arithConj.positiveEqs) yield {
            val (c, d, _) = eqTerms(eq, conj.order)
            new PseudoLiteral(nfe, Equation(c, d))
          }).toList

        // negative arithConjs
        val lits5 =
          (for (eq <- conj.arithConj.negativeEqs) yield {
            val (c, d, _) = eqTerms(eq, conj.order)
            new PseudoLiteral(nfe, NegEquation(c, d))
          }).toList
        (nfe, lits1 ++ lits2 ++ lits3 ++ lits4 ++ lits5)
      }

    dprintln("newFunEqs: " + newFunEqs.mkString(","))
    dprintln("newLiterals: " + newLiterals.mkString(", "))
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // Debug.assertInt(ConnectionProver.AC, conj.negatedConjs.size <= 1)
    //-END-ASSERTION-//////////////////////////////////////////////////////////
    if (conj.negatedConjs.size == 0) {
      if (newLiterals.length == 0) {
        (List(new PseudoLiteral(newFunEqs.tail, newFunEqs.head)), newBREUOrder)
      } else {
        (newLiterals, newBREUOrder)
      }
    } else {
      var deeperLiterals = List() : List[PseudoLiteral]
      var deeperOrder = List() : BREUOrder
      for (nc <- conj.negatedConjs) {
        val (dlit, dord) = ctc(nc, newFunEqs, funPreds, !negated)
        deeperLiterals ++= dlit
        deeperOrder ++= dord
      }
      (newLiterals ++ deeperLiterals, deeperOrder ++ newBREUOrder)
    }
  }


  def CTC(conj : Conjunction, funPreds : Set[Predicate], debug : Boolean = false) : (PseudoClause, BREUOrder) = {
    DEBUGPrint = debug    
    dprintln(" CTC")
    dprintln("-----")
    dprintln("conj: " + conj)
    dprintln("funPreds: " + funPreds.mkString(", "))
    val (lits, ord) = ctc(conj, List() : List[FunEquation], funPreds, false)
    (new PseudoClause(lits), ord)
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

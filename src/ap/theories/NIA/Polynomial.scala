package ap.theories.NIA

import scala.annotation.tailrec
import scala.collection.mutable.Map
import ap.terfor.ConstantTerm
import ap.terfor.TermOrder
import ap.basetypes.IdealInt
import scala.math.Ordering.Implicits.infixOrderingOps
import ap.util.Debug
import ap.util.PriorityQueueWithIterators



/**
  * There are two kinds of orderings, one for ConstantTerms and one for Monomials
  * (the latter utilizes the former). The ConstantTerm ordering is supposed to be
  * controlled by the user of the class (by using ListOrdering) but StringOrdering
  * exists as a fallback if the order is uninteresting.
  */


/**
  * ConstantTerm orderings
  * 
  */
class StringOrdering extends Ordering[ConstantTerm] {
  def compare(c1 : ConstantTerm, c2 : ConstantTerm) : Int = {
    c1.toString.compare(c2.toString)
  }
}

// If an element is earlier in list it has lower order
class ListOrdering(list : List[ConstantTerm]) extends Ordering[ConstantTerm] {
  def compare(c1 : ConstantTerm, c2 : ConstantTerm) : Int = {
    val i1 = list indexOf c1
    val i2 = list indexOf c2

    if (i1 >= 0 && i2 < 0)
      1
    else if (i2 >= 0 && i1 < 0)
      -1 
    else if (i1 >= 0 && i2 >= 0)
      i2 - i1
    else
      c1.toString.compare(c2.toString)
  }
}



/**
  * Monomial orderings
  * 
  */

// Thrown when a class doesn't specify a monomial ordering
case class creatingDegenOrdering(smth : String) extends Exception

// Every monomial ordering must have a ConstantTerm ordering)
abstract class monomialOrdering(val termOrdering : Ordering[ConstantTerm]) extends Ordering[Monomial] {
  // Placed here since it is common to many ordering
  def lexcompare(keys1 : List[(ConstantTerm, Int)], keys2 : List[(ConstantTerm, Int)]) : Int = {
    // If either monomial is now empty, we are done
    if (keys1 == Nil && keys2 == Nil)
      0
    else if (keys1 == Nil)
      -1
    else if (keys2 == Nil)
      1
    else {
      // Compare head element lexicographically
      val (v1, e1) = keys1.head
      val (v2, e2) = keys2.head

      if (v1.toString > v2.toString)
        1
      else if(v2.toString > v1.toString)
        -1
      // If v1.toString == v2.toString, check exponent
      else if (e1 > e2)
        1
      else if (e2 > e1)
        -1
      else
        lexcompare(keys1.tail, keys2.tail)
    }
  }
}

// Exception class, shouldn't be used
class DegenOrdering(implicit termOrdering : Ordering[ConstantTerm] = new StringOrdering) extends monomialOrdering(termOrdering) {
  throw new creatingDegenOrdering("Creating Degen Ordering!")
  def compare(m1 : Monomial, m2 : Monomial) : Int = 0
}

// Order by lexicographical ordering
class LexOrdering(termOrdering : Ordering[ConstantTerm]) extends monomialOrdering(termOrdering) {
  def compare(m1 : Monomial, m2 : Monomial) : Int = {
    lexcompare(m1.pairs, m2.pairs)
  }
}

// Graded Lexicographical ordering
class GlexOrdering(termOrdering : Ordering[ConstantTerm]) extends monomialOrdering(termOrdering) {
  def compare(m1 : Monomial, m2 : Monomial) : Int = {
    // Start by checking order, otherwise do lexicographical ordering
    if (m1.order > m2.order)
      1
    else if (m2.order > m1.order)
      -1
    else
      lexcompare(m1.pairs, m2.pairs)
  }
}


// Graded Reverse Lexicographical ordering (Using the termOrdering!)
class GrevlexOrdering(termOrdering : Ordering[ConstantTerm]) extends monomialOrdering(termOrdering) {
  def compare(m1 : Monomial, m2 : Monomial) : Int = {
    if (m1.order > m2.order)
      1
    else if (m2.order > m1.order)
      -1
    else {
      // Basically like lexcompare, but using termOredring.compare instead
      def compare_keys(keys1 : List[(ConstantTerm, Int)], keys2 : List[(ConstantTerm, Int)]) : Int = {
        if (keys1 == Nil && keys2 == Nil)
          0
        else if (keys1 == Nil)
          1
        else if (keys2 == Nil)
          -1
        else {
          val (v1, e1) = keys1.head
          val (v2, e2) = keys2.head

          val cmp = termOrdering.compare(v1, v2)

          if (cmp > 0)
            1
          else if (cmp < 0)
            -1
          else if (e1 > e2)
            1
          else if (e2 > e1)
            -1
          else
            compare_keys(keys1.tail, keys2.tail)
        }
      }

      compare_keys(m1.pairs, m2.pairs)
    }
  }
}



// The ConstantTerms in list are given highest order according to the sorting of list
// Falling back on ordering if not found in list
class PartitionOrdering(val list : List[ConstantTerm], implicit val ordering : monomialOrdering) extends monomialOrdering(ordering.termOrdering) {
  def compare(m1 : Monomial, m2 : Monomial) : Int = {
    def compare_keys(keys1 : List[(ConstantTerm, Int)], keys2 : List[(ConstantTerm, Int)]) : Int = {
      // If one of the monomials are empty, that is smaller
      if (keys1 == Nil && keys2 == Nil)
        0
      else if (keys1 == Nil)
        -1
      else if (keys2 == Nil)
        1
      else {
        val (v1, e1) = keys1.head
        val (v2, e2) = keys2.head

        val i1 = list indexOf v1
        val i2 = list indexOf v2

        // If only one of the keys contains a defined element, that is greater
        if (i1 >= 0 && i2 < 0)
          1
        else if (i2 >= 0 && i1 < 0)
          -1
        else if (i1 >= 0 && i2 >= 0) {
          if (i1 < i2)
            1
          else if (i2 < i1)
            -1
          else if (e1 > e2)
            1
          else if (e2 > e1)
            -1
          else
            compare_keys(keys1.tail, keys2.tail)
        }
        else
          ordering.compare(new Monomial(keys1), new Monomial(keys2))
      }
    }

    compare_keys(m1.pairs, m2.pairs)
  }
}


/**
  * The pairs withing the list of a monomial are sorted in descending order 
  * (e.g. [(z,3), (y,2), (x,1)] instead of [(x,1), (y,2), (z,3)] for "xyyzzz")
  *
  */
class Monomial(val pairs : List[(ConstantTerm, Int)])(implicit val ordering : monomialOrdering) {
  implicit val _ = ordering.termOrdering

  def isConstant = !(pairs.exists(x => x._2 > 0))

  def isEmpty = (pairs.size == 0)

  def isLinear = (order <= 1)

  def variables = (for ((ct, _) <- pairs) yield ct).toSet

  def size = pairs.size

  override def equals(other : Any) = {
    other match {
      case that : Monomial => (this.pairs == that.pairs)
      case _ => false
    }
  }

  def order = (for ((_, c) <- pairs) yield c).sum



  def isDividedBy(that : Monomial) : Boolean = {
    // Compares if for all pairs (x,y) in thatList, there is a pair (x,y') in thisList s.t. y' >= y
    def checkLists(thisList : List[(ConstantTerm, Int)], thatList : List[(ConstantTerm, Int)]) : Boolean = {
      (thisList, thatList) match {
        case (_, Nil) => true
        case (Nil, _) => false
        case ((thisV, thisE) :: thisTail, (thatV, thatE) :: thatTail) =>
          if (thisV < thatV)
          // Since Monomials are sorted, we can quit here
            false
          else if (thisV > thatV)
            checkLists(thisTail, thatList)
          else if (thisE >= thatE)
            checkLists(thisTail, thatTail)
          else
            false
      }
    }

    checkLists(this.pairs, that.pairs)
  }

  override def toString() : String = {
    if (isEmpty)
      "EmptyMonomial!"
    else
      (for ((v,e) <- pairs)
      yield
        if (e == 1)
          "(" + v + ")"
        else
          "(" + v + "^" + e + ")").mkString("*")
  }

  def hasCommonVariables(that : Monomial) : Boolean = {
    def commonElements(list1 : List[(ConstantTerm, Int)], list2 : List[(ConstantTerm, Int)]) : Boolean = {
      (list1, list2) match {
        case (Nil, _) => false
        case (_, Nil) => false
        case ((h1, _) :: t1, (h2, _) :: t2) => 
          if (h1 > h2)
            commonElements(t1, list2)
          else if (h1 < h2)
            commonElements(list1, t2)
          else
            true
      }
    }

    commonElements(this.pairs, that.pairs)
  }

  def LCM(that : Monomial) : Monomial = {
    def mergeLists(list1 : List[(ConstantTerm, Int)], list2 : List[(ConstantTerm, Int)]) : List[(ConstantTerm, Int)] = {
      (list1, list2) match {
        case (Nil, l2) => l2
        case (l1, Nil) => l1
        case ((v1, e1) :: t1, (v2, e2) :: t2) =>
          if (v1 > v2)
            (v1, e1) :: mergeLists(t1, list2)
          else if (v1 < v2)
            (v2, e2) :: mergeLists(list1, t2)
          else
            (v1, e1.max(e2)) :: mergeLists(t1, t2)
      }
    }

    new Monomial(mergeLists(this.pairs, that.pairs))
  }

  def divisors() : List[Monomial] = {
    def genDivisors(list : List[(ConstantTerm, Int)]) : List[List[(ConstantTerm, Int)]] = {
      if (list == Nil) {
        List(List()) : List[List[(ConstantTerm, Int)]]
      } else {
        val (k, v) = list.head
        val rest = genDivisors(list.tail)
        (for 
          (i <- 0 to v.intValue;
          r <- rest)
        yield
        {
          if (i == 0)
            r
          else
            (k, i) :: r
        }).toList
      }
    }

    for (kv <- genDivisors(this.pairs))
      yield
        new Monomial(kv)
  }

  def divide(ct : ConstantTerm, exp : IdealInt) : Monomial = {
    new Monomial(pairs diff List((ct, exp)))
  }

  // PRE: this.isDividedBy(that)
  def /(that : Monomial) : Monomial = {
    var newMon = this
    for ((ct, exp) <- that.pairs)
      newMon = newMon.divide(ct, exp)
    newMon
  }
}

class Term(coeff : IdealInt, monomial : Monomial)(implicit val ordering : monomialOrdering) {
  Debug.assertPre(Debug.AC_NIA, !coeff.isZero)

  def isZero = (coeff.isZero)
  def isConstant = (monomial.isConstant)

  override def toString() : String = {
    if (monomial.isEmpty)
      "" + coeff
    else
      (if (coeff.intValue == 1)
        ""
      else if (coeff.intValue == -1)
        "-"
      else
        coeff) + (for {(v, e) <- monomial.pairs} yield {if (e == 1) "(" + v + ")" else "(" + v + "^" + e + ")"}).mkString("*")
  }

  def order : Int = monomial.order

  def variables : Set[ConstantTerm] = monomial.variables

  def >(that : Term)(implicit ordering : monomialOrdering) = this.m > that.m

  // Maybe add GCD calculation on this.c and that.c
  def LCM(that : Term) = new Term(this.c*that.c, this.m.LCM(that.m))

  def mul(that : IdealInt) : Term = new Term(this.c * that, this.m)

  def *(that : Term) : Term = {
    def mulMon(list1 : List[(ConstantTerm, Int)], list2 : List[(ConstantTerm, Int)]) : List[(ConstantTerm, Int)] = {
      if (list1 == Nil)
        list2
      else if (list2 == Nil)
        list1
      else {
        val (v1, e1) = list1.head
        val (v2, e2) = list2.head

        val cmp = ordering.termOrdering.compare(v1, v2)

        if (cmp > 0)
          list1.head :: mulMon(list1.tail, list2)
        else if (cmp < 0)
          list2.head :: mulMon(list1, list2.tail)
        else
          (v1, e1+e2) :: mulMon(list1.tail, list2.tail)
      }
    }

    new Term(this.c*that.c, new Monomial(mulMon(this.m.pairs, that.m.pairs)))
  }

  def /(that : Term) : Term = {
    def divMon(list1 : List[(ConstantTerm, Int)], list2 : List[(ConstantTerm, Int)]) : List[(ConstantTerm, Int)] = {
      if (list1 == Nil)
        list2
      else if (list2 == Nil)
        list1
      else {
        val (v1, e1) = list1.head
        val (v2, e2) = list2.head

        val cmp = ordering.termOrdering.compare(v1, v2)

        if (cmp > 0)
          list1.head :: divMon(list1.tail, list2)
        else if (cmp < 0)
          list2.head :: divMon(list1, list2.tail)
        else if (e1-e2 == 0)
          divMon(list1.tail, list2.tail)
        else
          (v1, e1-e2) :: divMon(list1.tail, list2.tail)
      }
    }

    new Term(this.c / that.c, new Monomial(divMon(this.m.pairs, that.m.pairs)))
  }

  def isLinear : Boolean = m.isLinear

  def neg() = new Term(-coeff, monomial)

  def c = coeff
  def m = monomial

  def isDividedBy(that : Term) = this.m.isDividedBy(that.m)
  def hasCommonVariables(that : Term) = this.m.hasCommonVariables(that.m)
}


/**
  *  INVARIANT: If t1 is before t2 in list, then t1 > t2
  * 
  * TODO: Fix zero-polynomial representation
  */
class Polynomial(val terms : List[Term])(implicit val ordering : monomialOrdering = new DegenOrdering) {

  def isZero = this.toString == "0"
  def isLinear = !terms.exists(t => !t.isLinear)
  def isConstant = !terms.exists(t => !t.isConstant)

  def containsTerm(term : Term) : Boolean = terms.exists(t => t == term)

  def neg() : Polynomial = new Polynomial(for (t <- terms) yield t.neg())
  def normalized : Polynomial = if (terms.head.c < 0) neg() else this

  def size : Int = terms.length

  def variables : Set[ConstantTerm] = (for (t <- terms) yield (t.variables)).flatten.toSet

  def order = (0 /: terms)((c, n) => c.max(n.order))

  override def toString() : String =  {
    terms match {
      case Nil => "0"
      case t => t.foldLeft("") ((str, term) => str + (if (term.c > 0) " +" else " ") + term.toString)
    }
  } 

  def LT : Term = {
    Debug.assertPre(Debug.AC_NIA, !isZero)
    terms.head
  }

  def LM : Monomial = LT.m

  def LCM(that : Polynomial) : Term = this.LT.LCM(that.LT)

  def merge_terms_aux(terms1 : List[Term], terms2 : List[Term]) : List[Term] = {
    (terms1, terms2) match {
      case (Nil, terms2) => terms2
      case (terms1, Nil) => terms1
      case (h1 :: t1, h2 :: t2) => 
        if (h1 > h2)
          h1 :: (merge_terms_aux(t1, h2::t2))
        else if (h2 > h1)
          h2 :: (merge_terms_aux(h1::t1, t2))
        else if ((h1.c + h2.c).isZero)
          merge_terms_aux(t1, t2)
        else
          new Term(h1.c + h2.c, h1.m) :: merge_terms_aux(t1, t2)
    }
  }

  def merge_terms(terms1 : List[Term], terms2 : List[Term]) : List[Term] = {
    val newterms1 = terms1.filter(x => !x.isZero)
    val newterms2 = terms2.filter(x => !x.isZero)

    merge_terms_aux(newterms1, newterms2)
  }

  def mul(that : IdealInt) : Polynomial = {
    val newTerms = 
      for (t <- terms)
        yield
          new Term(that*t.c, t.m)
    new Polynomial(for (t <- terms) yield { new Term(that*t.c, t.m) })
  }

  def +(that : Term) : Polynomial = new Polynomial(merge_terms(this.terms, List(that)))
  def -(that : Term) : Polynomial = this + that.neg()

  def +(that : Polynomial) : Polynomial = new Polynomial(merge_terms(this.terms, that.terms))
  def -(that : Polynomial) : Polynomial = this + that.neg()

  def *(that : Polynomial) : Polynomial =
    (for (t1 <- this.terms; t2 <- that.terms) yield t1*t2).foldLeft(new Polynomial(List()))  ((retPoly, term) => retPoly + term)

  def SPOL(that : Polynomial) : Polynomial = {
    val lcm = LCM(that)

    val newf = this*(new Polynomial(List(lcm/this.LT)))
    val newg = that*(new Polynomial(List(lcm/that.LT)))

    newf - newg
  }

  def ReduceBy(that : Polynomial) : Polynomial = {
    Debug.assertPre(Debug.AC_NIA, this.LT.isDividedBy(that.LT))

    def gcd(a: IdealInt, b: IdealInt):IdealInt=if (b.isZero) a.abs else gcd(b, a%b)
    def lcm(a: IdealInt, b: IdealInt)=(a*b).abs/gcd(a,b)

    val lcmm = lcm(this.LT.c.abs, that.LT.c.abs)

    val newf = this.mul(lcmm/this.LT.c.abs)
    val gmul = new Polynomial(List(newf.LT/that.LT))

    val newg = that * gmul

    newf - newg
  }

  def simplifyBy(that : Polynomial) : Polynomial = {
    for (t <- this.terms) {
      if (t.isDividedBy(that.LT)) {
        def gcd(a: IdealInt, b: IdealInt):IdealInt=if (b.isZero) a.abs else gcd(b, a%b)
        def lcm(a: IdealInt, b: IdealInt)=(a*b).abs/gcd(a,b)

        val lcmm = lcm(t.c.abs, that.LT.c.abs)

        val newf = this.mul(lcmm/t.c.abs)
        val gmul = new Polynomial(List((t.mul(lcmm/t.c.abs))/that.LT))
        // val gmul = new Polynomial(List((newf.LT * lcmm/c.abs)/that.LT))

        val newg = that * gmul

        return (newf - newg)
      }
    }

    this
  }
}


/**
  * Represents a collection of polynomials
  * 
  * By keeping a map and a priorityqueue in parallell, the data structure supports:
  * -- Finding the smallest element (keeping it ordered)
  * -- Finding all polynomias with a LT containing some variables
  * 
  */

class Basis(implicit val ordering : monomialOrdering) {

  class PolynomialOrdering extends Ordering[Polynomial] {
    def compare(p1 : Polynomial, p2 : Polynomial) = p2.size.compare(p1.size)
  }

  implicit val _ = new PolynomialOrdering
  var polyMap = Map() : Map[String, List[Polynomial]]
  val polyQueue = new PriorityQueueWithIterators() : PriorityQueueWithIterators[Polynomial]


  def toList : List[Polynomial] = polyMap.values.toList.flatten
  def toSet : Set[Polynomial] = toList.toSet

  def size : Int = toList.size

  def isEmpty= (this.size == 0)

  def copy() : Basis = {
    val newBasis = new Basis
    for (p <- this.toList)
      newBasis.add(p)

    newBasis
  }

  override def toString : String = {
    val list = this.toList
    (for (i <- 0 until list.length)
    yield
      "(" + i +") " + list(i)).mkString("\n")
  }


  def add(poly : Polynomial) : Unit = {
    Debug.assertPre(Debug.AC_NIA, !poly.isZero)

    val curList = polyMap.getOrElse(poly.LM.toString, List()) : List[Polynomial]

    if (!curList.exists(x => x == poly))
    {
      polyMap = (polyMap += (poly.LM.toString -> (poly :: curList)))
      polyQueue.enqueue(poly)
    }
  }

  def addBasis(b : Basis) : Unit = {
    for (p <- b.toList)
      this.add(p) 
  }

  // Retrieves a polynomial and removes it from the basis
  def get() : Polynomial = {
    val retPoly = polyQueue.dequeue

    val newList = (polyMap(retPoly.LM.toString) diff List(retPoly))
    if (newList == List())
      polyMap = polyMap -= retPoly.LM.toString
    else
      polyMap = polyMap += (retPoly.LM.toString -> newList)

    retPoly
  }

  def remove(i : Int) : Unit = {
    for (a <- 0 until i)
      get()
  }

  // Heuristic for selecting which polynomials to use for reducing
  def selectReductor(list : List[Polynomial]) : Polynomial = {
    list.reduceLeft((l, r) => {
        ordering.compare(l.LM, r.LM) match {
          case x if x > 0 => r
          case _ => l
        }
      })
  }

  // Returns poly reduced with respect to basis
  @tailrec
  final def ReducePolynomial(poly : Polynomial) : Polynomial = {
    if (poly.isZero)
      return poly

    val possibilities =
      (for (divMon <- poly.LM.divisors)
      yield {
        for (p <- this.polyMap.getOrElse(divMon.toString, List());
          if (p != poly))
        yield {
          Debug.assertPre(Debug.AC_NIA, poly.LT.isDividedBy(p.LT))
          p
        }
      }).flatten

    if (possibilities == Nil)
      return poly

    val redPoly = poly.ReduceBy(selectReductor(possibilities))

    if (redPoly.isZero)
      return redPoly

    ReducePolynomial(redPoly)
  }

  // Reduces this basis w.r.t. itself
  def Simplify() : Basis = {
    val newPolys = for(p <- this.toList) yield ReducePolynomial(p)

    var newBasis = new Basis()

    for (p <- this.toList.reverse) {
      var newPoly = p
      for (pp <- newBasis.toList)
        newPoly = newPoly.simplifyBy(pp)

      Debug.assertPost(Debug.AC_NIA, !newPoly.isZero)

      newBasis.add(newPoly)
    }

    newBasis
  }
}

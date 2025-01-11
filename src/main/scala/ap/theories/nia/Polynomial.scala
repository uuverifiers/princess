/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C)      2014-2025 Philipp Ruemmer <ph_r@gmx.net>
 *                    2014 Peter Backeman <peter.backeman@it.uu.se>
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

package ap.theories.nia

import ap.basetypes.IdealInt
import ap.terfor.{ConstantTerm, TermOrder, OneTerm}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import scala.math.Ordering.Implicits.infixOrderingOps
import ap.util.{Debug, Timeout, Seqs}

import scala.collection.immutable.BitSet
import scala.collection.mutable.{HashMap => MHashMap, PriorityQueue,
                                 ArrayBuffer, LinkedHashMap, Map}
import scala.annotation.tailrec


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
object StringOrdering extends Ordering[ConstantTerm] {
  def compare(c1 : ConstantTerm, c2 : ConstantTerm) : Int =
    Seqs.lexCombineInts(c1.name compare c2.name,
                        c1.hashCode compare c2.hashCode)
}

// If an element is earlier in list it has lower order
class ListOrdering(list : Seq[ConstantTerm]) extends Ordering[ConstantTerm] {
  private val indexes = list.iterator.zipWithIndex.toMap

  def compare(c1 : ConstantTerm, c2 : ConstantTerm) : Int =
    (indexes get c1, indexes get c2) match {
      case (Some(_), None) =>
        1
      case (None, Some(_)) =>
        -1
      case (Some(i1), Some(i2)) =>
        i2 - i1
      case _ =>
        StringOrdering.compare(c1, c2)
    }

  override def toString =
    "ListOrdering(" + list + ")"
}


/**
 * Monomial orderings
 * 
 */

// Every monomial ordering must have a ConstantTerm ordering)
abstract class MonomialOrdering(val termOrdering : Ordering[ConstantTerm])
               extends Ordering[Monomial] {
  // Placed here since it is common to many ordering
  def lexcompare(keys1 : List[(ConstantTerm, Int)],
                 keys2 : List[(ConstantTerm, Int)]) : Int = {
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

      Seqs.lexCombineInts(StringOrdering.compare(v1, v2),
                          // If v1 == v2, check exponent
                          e1 compare e2,
                          lexcompare(keys1.tail, keys2.tail))
    }
  }
}

private object DegenOrdering {
  // Thrown when a class doesn't specify a monomial ordering
  object DegenOrderingException extends Exception("Creating Degen Ordering!")
}

// Exception class, shouldn't be used
private class DegenOrdering(implicit termOrdering : Ordering[ConstantTerm] =
                            StringOrdering)
      extends MonomialOrdering(termOrdering) {
  throw DegenOrdering.DegenOrderingException
  def compare(m1 : Monomial, m2 : Monomial) : Int = 0
}

////////////////////////////////////////////////////////////////////////////////

// Order by lexicographical ordering
class LexOrdering(termOrdering : Ordering[ConstantTerm])
      extends MonomialOrdering(termOrdering) {
  def compare(m1 : Monomial, m2 : Monomial) : Int = {
    lexcompare(m1.pairs, m2.pairs)
  }
}

/**
 * Graded Lexicographical ordering
 */
class GlexOrdering(termOrdering : Ordering[ConstantTerm])
      extends MonomialOrdering(termOrdering) {
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


/**
 * Graded Reverse Lexicographical ordering (Using the termOrdering!)
 */
class GrevlexOrdering(termOrdering : Ordering[ConstantTerm])
      extends MonomialOrdering(termOrdering) {
  def compare(m1 : Monomial, m2 : Monomial) : Int = {
    if (m1.order > m2.order)
      1
    else if (m2.order > m1.order)
      -1
    else {
      // Basically like lexcompare, but using termOrdering.compare instead
      def compare_keys(keys1 : List[(ConstantTerm, Int)],
                       keys2 : List[(ConstantTerm, Int)]) : Int = {
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

  override def toString : String =
    "GrevlexOrdering(" + termOrdering + ")"
}


object PartitionOrdering {

  private class PartitionedTermOrdering(list : Seq[ConstantTerm],
                                        backup : Ordering[ConstantTerm])
                extends Ordering[ConstantTerm] {
    private val indexes = list.iterator.zipWithIndex.toMap
    def compare(c1 : ConstantTerm, c2 : ConstantTerm) : Int =
      (indexes get c1, indexes get c2) match {
        case (Some(_), None)      =>  1
        case (None, Some(_))      => -1
        case (Some(i1), Some(i2)) => i1 - i2
        case _ =>                    backup.compare(c1, c2)
      }
  }

}

/**
 * The ConstantTerms in list are given highest order according
 * to the sorting of list. Falling back on ordering if not found in list
 */
class PartitionOrdering(val list : Seq[ConstantTerm],
                        implicit val backup : MonomialOrdering)
      extends MonomialOrdering(new PartitionOrdering.PartitionedTermOrdering(
                                 list, backup.termOrdering)) {
  private val indexes = list.iterator.zipWithIndex.toMap
  def compare(m1 : Monomial, m2 : Monomial) : Int = {
    def compare_keys(keys1 : List[(ConstantTerm, Int)],
                     keys2 : List[(ConstantTerm, Int)]) : Int =
      (keys1, keys2) match {
        // If one of the monomials are empty, that is smaller
        case (Nil, Nil) =>  0
        case (Nil, _  ) => -1
        case (_,   Nil) =>  1

        case ((v1, e1) :: tail1, (v2, e2) :: tail2) =>
          (indexes get v1, indexes get v2) match {
            // If only one of the keys contains a defined element,
            // that is greater
            case (None, None) =>
              backup.compare(Monomial(keys1), Monomial(keys2))
            case (_ , None) =>  1
            case (None,  _) => -1
            case (Some(i1), Some(i2)) =>
              if (i1 < i2)
                -1
              else if (i2 < i1)
                1
              else if (e1 > e2)
                1
              else if (e2 > e1)
                -1
              else
                compare_keys(tail1, tail2)
          }
      }

    compare_keys(m1.pairs, m2.pairs)
  }

  override def toString =
    "PartitionOrdering(" + list + ", " + backup + ")"
}

////////////////////////////////////////////////////////////////////////////////

object Monomial {
  type PairList = List[(ConstantTerm, Int)]

  def fromConstantTerm(c : ConstantTerm)
                      (implicit ordering : MonomialOrdering) =
    Monomial(List((c, 1)))
}

/**
 * The pairs withing the list of a monomial are sorted in descending order 
 * (e.g. [(z,3), (y,2), (x,1)] instead of [(x,1), (y,2), (z,3)] for "xyyzzz")
 */
case class Monomial(val pairs : Monomial.PairList)
                   (implicit val ordering : MonomialOrdering) {
  import Monomial._

  implicit val o : Ordering[ConstantTerm] = ordering.termOrdering

  lazy val isConstant = !(pairs.exists(x => x._2 > 0))

  def isEmpty = pairs.isEmpty

  def isLinear = (order <= 1)

  lazy val variables = (for ((ct, _) <- pairs) yield ct).toSet

  lazy val size = pairs.size

  lazy val order = (for ((_, c) <- pairs.iterator) yield c).sum

  def isDividedBy(that : Monomial) : Boolean = {
    // Compares if for all pairs (x,y) in thatList,
    // there is a pair (x,y') in thisList s.t. y' >= y
    def checkLists(thisList : PairList, thatList : PairList) : Boolean = {
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

  override def toString : String = {
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
    def commonElements(list1 : PairList, list2 : PairList) : Boolean = {
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

  def lcm(that : Monomial) : Monomial = {
    def mergeLists(list1 : PairList, list2 : PairList) : PairList = {
      (list1, list2) match {
        case (Nil, l2) => l2
        case (l1, Nil) => l1
        case ((v1, e1) :: t1, (v2, e2) :: t2) =>
          if (v1 > v2)
            (v1, e1) :: mergeLists(t1, list2)
          else if (v1 < v2)
            (v2, e2) :: mergeLists(list1, t2)
          else
            (v1, e1 max e2) :: mergeLists(t1, t2)
      }
    }

    Monomial(mergeLists(this.pairs, that.pairs))
  }

  def gcd(that : Monomial) : Monomial = {
    def intersectLists(list1 : PairList, list2 : PairList) : PairList = {
      (list1, list2) match {
        case (Nil, l2) => Nil
        case (l1, Nil) => Nil
        case ((v1, e1) :: t1, (v2, e2) :: t2) =>
          if (v1 > v2)
            intersectLists(t1, list2)
          else if (v1 < v2)
            intersectLists(list1, t2)
          else
            (v1, e1 min e2) :: intersectLists(t1, t2)
      }
    }

    Monomial(intersectLists(this.pairs, that.pairs))
  }

  def divisors : List[Monomial] = {
    def genDivisors(list : PairList) : List[PairList] = {
      if (list.isEmpty) {
        List[PairList](List())
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
        Monomial(kv)
  }

  def *(that : Monomial) : Monomial =
    Monomial(mulLists(this.pairs, that.pairs))

  private def mulLists(list1 : PairList, list2 : PairList) : PairList =
    if (list1 == Nil)
      list2
    else if (list2 == Nil)
      list1
    else {
      val (v1, e1) = list1.head
      val (v2, e2) = list2.head

      val cmp = ordering.termOrdering.compare(v1, v2)

      if (cmp > 0)
        list1.head :: mulLists(list1.tail, list2)
      else if (cmp < 0)
        list2.head :: mulLists(list1, list2.tail)
      else
        (v1, e1+e2) :: mulLists(list1.tail, list2.tail)
    }

  def /(that : Monomial) : Monomial =
    Monomial(divLists(this.pairs, that.pairs))

  private def divLists(list1 : PairList, list2 : PairList) : PairList =
    if (list1 == Nil)
      list2
    else if (list2 == Nil)
      list1
    else {
      val (v1, e1) = list1.head
      val (v2, e2) = list2.head

      val cmp = ordering.termOrdering.compare(v1, v2)

      if (cmp > 0)
        list1.head :: divLists(list1.tail, list2)
      else if (cmp < 0)
        list2.head :: divLists(list1, list2.tail)
      else if (e1-e2 == 0)
        divLists(list1.tail, list2.tail)
      else
        (v1, e1-e2) :: divLists(list1.tail, list2.tail)
    }
}

////////////////////////////////////////////////////////////////////////////////

case class CoeffMonomial(coeff : IdealInt, monomial : Monomial)
               (implicit val ordering : MonomialOrdering) {
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(Debug.AC_NIA, !coeff.isZero)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  import Monomial.PairList

  def isZero = coeff.isZero
  def isConstant = monomial.isConstant

  override def toString() : String = {
    if (monomial.isEmpty)
      "" + coeff
    else
      (if (coeff.isOne)
        ""
      else if (coeff.isMinusOne)
        "-"
      else
        coeff) +
      (for ((v, e) <- monomial.pairs)
       yield (if (e == 1) "(" + v + ")"
              else "(" + v + "^" + e + ")")).mkString("*")
  }

  def order : Int = monomial.order

  def variables : Set[ConstantTerm] = monomial.variables

  def >(that : CoeffMonomial) = this.m > that.m

  // Maybe add GCD calculation on this.c and that.c
  def lcm(that : CoeffMonomial) = CoeffMonomial(this.c*that.c, this.m.lcm(that.m))

  def mul(that : IdealInt) : CoeffMonomial = CoeffMonomial(this.c * that, this.m)

  def *(that : CoeffMonomial) : CoeffMonomial =
    CoeffMonomial(this.c * that.c, this.m * that.m)

  def /(that : CoeffMonomial) : CoeffMonomial =
    CoeffMonomial(this.c / that.c, this.m / that.m)

  def isLinear : Boolean = m.isLinear

  def neg = CoeffMonomial(-coeff, monomial)

  def c = coeff
  def m = monomial

  def isDividedBy(that : CoeffMonomial) = this.m.isDividedBy(that.m)
  def hasCommonVariables(that : CoeffMonomial) = this.m.hasCommonVariables(that.m)
}

////////////////////////////////////////////////////////////////////////////////

object Polynomial {
  type CoeffMonomialList = List[CoeffMonomial]

  /**
   * Converts an LinearCombination (Princess) to a Polynomial (Groebner).
   * This method assumes that the TermOrder and the used MonomialOrdering
   * are compatible, so that the elements of the linear combination are
   * sorted correctly.
   */
  def fromLinearCombination
          (lc : LinearCombination)
          (implicit ordering : MonomialOrdering) : Polynomial =
    Polynomial((for ((coeff, t) <- lc.iterator)
                yield CoeffMonomial(
                        coeff,
                        t match {
                          case t : ConstantTerm => Monomial fromConstantTerm t
                          case OneTerm          => Monomial(List())
                        })).toList)

  /**
   * Converts an atom (Princess) to a Polynomial (Groebner).
   * This method assumes that the TermOrder and the used MonomialOrdering
   * are compatible, so that the elements of the arguments are
   * sorted correctly.
   */
  def fromMulAtom(a : Atom)
                 (implicit ordering : MonomialOrdering) : Polynomial = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_NIA, a.pred == GroebnerMultiplication._mul)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    (fromLinearCombination(a(0)) * fromLinearCombination(a(1))) -
      fromLinearCombination(a(2))
  }

  /**
   * Converts an LinearCombination (Princess) to a Polynomial (Groebner).
   */
  def fromLinearCombinationGen
                    (lc : LinearCombination)
                    (implicit ordering : MonomialOrdering) : Polynomial = {
    var retPoly = Polynomial(List())

    for ((coeff, term) <- lc) {
      retPoly +=
        (term match {
          case (OneTerm) =>
            new CoeffMonomial(coeff, Monomial(List()))
          case (x : ConstantTerm) =>
            new CoeffMonomial(coeff, Monomial(List((x, 1))))
        })
    }
    retPoly
  }

  /**
   * Converts an atom (Princess) to a Polynomial (Groebner).
   */
  def fromMulAtomGen(a : Atom)
                    (implicit ordering : MonomialOrdering) : Polynomial =
    (fromLinearCombinationGen(a(0)) * fromLinearCombinationGen(a(1))) -
      fromLinearCombinationGen(a(2))

}

/**
 * INVARIANT: If t1 is before t2 in list, then t1 > t2
 * 
 * TODO: Fix zero-polynomial representation
 */
case class Polynomial(val terms : Polynomial.CoeffMonomialList)
                     (implicit val ordering : MonomialOrdering =
                        new DegenOrdering) {
  import Polynomial._

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(Debug.AC_NIA,
                   (terms sliding 2) forall { case Seq(a, b) => a > b
                                              case _ => true })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def isZero = terms.isEmpty
  lazy val isLinear = terms.forall(t => t.isLinear)
  lazy val isConstant = terms.forall(t => t.isConstant)

  def containsTerm(term : CoeffMonomial) : Boolean = terms contains term

  def neg : Polynomial = Polynomial(for (t <- terms) yield t.neg)
  def normalized : Polynomial = if (terms.head.c < 0) neg else this

  def size : Int = terms.size

  lazy val variables : Set[ConstantTerm] =
    (for (t <- terms.iterator; c <- t.variables.iterator) yield c).toSet

  lazy val order = (0 /: terms)((c, n) => c.max(n.order))

  override def toString() : String =  {
    terms match {
      case Nil =>
        "0"
      case t => t.foldLeft("") {
        (str, term) => str + (if (term.c > 0) " +" else " ") + term.toString
      }
    }
  } // + " -> " + lt

  def lt : CoeffMonomial = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_NIA, !isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    terms.head
  }

  def lm : Monomial = lt.m

  def lcm(that : Polynomial) : CoeffMonomial = this.lt.lcm(that.lt)

  private def merge_terms_aux(terms1 : CoeffMonomialList,
                              terms2 : CoeffMonomialList) : CoeffMonomialList = {
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
          CoeffMonomial(h1.c + h2.c, h1.m) :: merge_terms_aux(t1, t2)
    }
  }

  private def merge_terms(terms1 : CoeffMonomialList, terms2 : CoeffMonomialList) : CoeffMonomialList = {
    val newterms1 = terms1.filter(x => !x.isZero)
    val newterms2 = terms2.filter(x => !x.isZero)

    merge_terms_aux(newterms1, newterms2)
  }

  def mul(that : IdealInt) : Polynomial =
    Polynomial(for (t <- terms) yield CoeffMonomial(that*t.c, t.m))

  def +(that : CoeffMonomial) : Polynomial =
    Polynomial(merge_terms(this.terms, List(that)))
  def -(that : CoeffMonomial) : Polynomial =
    this + that.neg

  def /(that : CoeffMonomial) : Polynomial =
    Polynomial(for (t <- terms) yield (t / that))

  def +(that : Polynomial) : Polynomial =
    Polynomial(merge_terms(this.terms, that.terms))
  def -(that : Polynomial) : Polynomial =
    this + that.neg

  def *(that : Polynomial) : Polynomial =
    (for (t1 <- this.terms.iterator; t2 <- that.terms.iterator)
     yield t1*t2).foldLeft(Polynomial(List())) {
      (retPoly, term) => retPoly + term
    }

  def spol(that : Polynomial) : Polynomial = {
    val l = lcm(that)

    val newf = this*(Polynomial(List(l/this.lt)))
    val newg = that*(Polynomial(List(l/that.lt)))

    newf - newg
  }

  def reduceBy(that : Polynomial) : Polynomial =
    if (!this.isZero && (this.lt isDividedBy that.lt)) {
      Timeout.check
      val newf = this.mul((this.lt.c lcm that.lt.c) / this.lt.c.abs)
      val gmul = Polynomial(List(newf.lt / that.lt))
      val newg = that * gmul
      (newf - newg) reduceBy that
    } else {
      this
    }

  def simplifyBy(reducers : Monomial => Option[Polynomial]) : Polynomial = {
    val newPolys =
      for (t <- this.terms.iterator;
           reducerOption = reducers(t.m);
           if (reducerOption.isDefined))
      yield {
        val that = reducerOption.get

        val lcmm = t.c lcm that.lt.c

        val newf = this.mul(lcmm/t.c.abs)
        val gmul = Polynomial(List((t.mul(lcmm/t.c.abs))/that.lt))

        newf - (that * gmul)
      }

    if (newPolys.hasNext)
      newPolys.next() simplifyBy reducers
    else
      this
  }

  def simplifyBy(that : Polynomial) : Polynomial = {
    for (t <- this.terms) {
      if (t.isDividedBy(that.lt)) {

        val lcmm = t.c lcm that.lt.c

        val newf = this.mul(lcmm/t.c.abs)
        val gmul = Polynomial(List((t.mul(lcmm/t.c.abs))/that.lt))

        val newg = that * gmul

        return (newf - newg)
      }
    }

    this
  }

  // The greatest common factor of all the monomials of this polynomial
  def commonFactor : Monomial = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_NIA, !isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    (for (t <- terms.reverseIterator) yield t.monomial) reduceLeft (_ gcd _)
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Represents a collection of polynomials
 * 
 * By keeping a map and a priorityqueue in parallel,
 * the data structure supports:
 * -- Finding the smallest element (keeping it ordered)
 * -- Finding all polynomials with a LT containing some variables
 */
class Basis(implicit val ordering : MonomialOrdering) {

  implicit val o : Ordering[Polynomial] = new Ordering[Polynomial] {
    def compare(p1 : Polynomial, p2 : Polynomial) =
      // p2.size.compare(p1.size)
      ap.util.Seqs.lexCompare(p2.terms.iterator map (_.m),
                              p1.terms.iterator map (_.m))
  }

  val polyMap = new LinkedHashMap[Monomial, List[Polynomial]]
  val polyQueue = new PriorityQueue[Polynomial]
  val labels = new MHashMap[Polynomial, BitSet]

  def labelFor(p : Polynomial) : BitSet = labels(p)

  def polyIterator : Iterator[Polynomial] =
    for (l <- polyMap.valuesIterator; p <- l.iterator) yield p

  def toList : List[Polynomial] = polyIterator.toList
  def toArray : Array[Polynomial] = polyIterator.toArray
  def toSet : Set[Polynomial] = polyIterator.toSet

  def isEmpty = polyMap.isEmpty

  def containsUnit : Option[Polynomial] =
    if (isEmpty) {
      None
    } else {
      val p = polyIterator.next()
      if (p.isConstant && !p.isZero)
        Some(p)
      else
        None
    }

  def copy : Basis = {
    val newBasis = new Basis
    val newMap = newBasis.polyMap

    for ((m, l) <- polyMap.iterator)
      newMap.put(m, l)
    newBasis.polyQueue ++= polyIterator

    newBasis
  }

  override def toString : String =
    (for ((p, i) <- polyIterator.zipWithIndex)
     yield "(" + i +") {" + (labelFor(p) mkString ", ") +
           "}\n\t" + p).mkString("\n")

  def add(poly : Polynomial, label : BitSet) : Unit = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_NIA, !poly.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val curList = polyMap.getOrElse(poly.lm, List())

    if (!(curList contains poly)) {
      polyMap.put(poly.lm, poly :: curList)
      polyQueue enqueue poly
      labels.put(poly, label)
    }
  }

  def add(polys : Iterable[(Polynomial, BitSet)]) : Unit =
    for (p <- polys)
      add(p._1, p._2)

  def addBasis(b : Basis) : Unit =
    for (p <- b.polyIterator)
      add(p, b labelFor p)

  // Retrieves a polynomial and removes it from the basis
  def get : (Polynomial, BitSet) = {
    val retPoly = polyQueue.dequeue

    val oldList = polyMap.getOrElse(retPoly.lm, List())
    val newList = oldList diff List(retPoly)

    if (newList.size == oldList.size) {
      // element had already been removed, recurse
      get
    } else {
      if (newList.isEmpty)
        polyMap -= retPoly.lm
      else
        polyMap.put(retPoly.lm, newList)

      val label = labelFor(retPoly)
      labels -= retPoly

      (retPoly, label)
    }
  }

  def remove(i : Int) : Unit = {
    for (_ <- 0 until i)
      get
  }

  // Returns poly reduced with respect to this basis
  def reducePolynomial(poly : Polynomial,
                       label : BitSet) : (Polynomial, BitSet) = {
    if (poly.isZero)
      return (poly, label)

    val reducers =
      for (divMon <- poly.lm.divisors.sorted.iterator;
           p <- this.polyMap.getOrElse(divMon, List()).iterator)
      yield p

    if (reducers.hasNext) {
      val reducer = reducers.next()
      val redPoly = poly reduceBy reducer
      val newLabel = label | labelFor(reducer)

      if (redPoly.isZero)
        (redPoly, newLabel)
      else
        reducePolynomial(redPoly, newLabel)
    } else {
      (poly, label)
    }
  }

  // Returns poly reduced with respect to two bases
  def reducePolynomial(andAlso : Basis,
                       poly : Polynomial,
                       label : BitSet) : (Polynomial, BitSet) = {
    if (poly.isZero)
      return (poly, label)

    val reducers =
      for (divMon <- poly.lm.divisors.sorted.iterator;
           p <- this.polyMap.getOrElse(divMon, List()).iterator ++
                andAlso.polyMap.getOrElse(divMon, List()).iterator)
      yield p

    if (reducers.hasNext) {
      val reducer = reducers.next()
      val redPoly = poly reduceBy reducer
      val newLabel =
        label | labels.getOrElse(reducer, andAlso labelFor reducer)

      if (redPoly.isZero)
        (redPoly, newLabel)
      else
        reducePolynomial(andAlso, redPoly, newLabel)
    } else {
      (poly, label)
    }
  }

  /**
   * Reduce each polynomial in this basis using <code>poly</code>,
   * give back all modified polynomials.
   */
  def reduceBy(poly : Polynomial, label : BitSet)
              : Seq[(Polynomial, BitSet)] = {
    val res = new ArrayBuffer[(Polynomial, BitSet)]
    val keysToRemove = new ArrayBuffer[Monomial]

    polyMap transform { case (key, polyList) => {
        val newPolyList =
          for (p <- polyList;
               reduced = p reduceBy poly;
               if ({
                 if (reduced.isZero) {
                   // drop this polynomial
                   labels -= p
                   false
                 } else if (reduced == p) {
                   // nothing has changed
                   true
                 } else {
                   res += ((reduced, labelFor(p) | label))
                   labels -= p
                   false
                 }
               }))
          yield p

        if (newPolyList.isEmpty)
          keysToRemove += key

        newPolyList
      }}

    polyMap --= keysToRemove

    res.toSeq
  }

  // Simplifies this basis w.r.t. itself, assuming that already
  // all polynomials are reduced w.r.t. each other. This method
  // will remove all elements from the basis it is applied to.
  def simplify : Basis = {
    val newBasis = new Basis

    while (!this.isEmpty) {
      Timeout.check

      val (nextPoly, nextLabel) = this.get
      var usedLabels = nextLabel

      val simpPoly = nextPoly simplifyBy { m => {
        val reducers =
          for (divMon <- m.divisors.sorted.iterator;
               p <- newBasis.polyMap.getOrElse(divMon, List()).iterator)
          yield p
        if (reducers.hasNext) {
          val reducer = reducers.next()
          usedLabels = usedLabels | (newBasis labelFor reducer)
          Some(reducer)
        } else {
          None
        }
      }}

//      println("" + nextPoly + " -> " + simpPoly)

      if (!simpPoly.isZero)
        newBasis.add(simpPoly, usedLabels)
    }

    newBasis
  }
}

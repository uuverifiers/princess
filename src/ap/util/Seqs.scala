/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2014 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.util;

import scala.util.Sorting
import scala.collection.mutable.{ArrayBuilder, HashSet => MHashSet}
import scala.reflect.ClassTag

object Seqs {

  private val AC = Debug.AC_SEQ_UTILS

  /**
   * Lexicographic comparison of two lists of things
   */
  def lexCompare[T](it1 : Iterator[T], it2 : Iterator[T])
                   (implicit ord : Ordering[T]): Int = {
    while (true) {
      if (it1.hasNext) {
        if (!it2.hasNext)
          return 1      
      } else {
        if (it2.hasNext)
          return -1
        else
          return 0      
      }      
      
      val compRes = ord.compare(it1.next, it2.next)
      if (compRes != 0) return compRes
    }
    
    throw new Error // never reached
  }

  def lexCompareOrdering[T](it1 : Iterator[T], it2 : Iterator[T])
                           (implicit ord : Ordering[T]) : Int = {
    while (true) {
      if (it1.hasNext) {
        if (!it2.hasNext)
          return 1      
      } else {
        if (it2.hasNext)
          return -1
        else
          return 0      
      }      
      
      val compRes = ord.compare(it1.next, it2.next)
      if (compRes != 0) return compRes
    }
    
    throw new Error // never reached
  }

  /**
   * Interpret the given integers as results of a <code>compare</code>
   * function (negative, zero, positive for less, equal, greater) and combine
   * them lexicographically
   */
  def lexCombineInts(int1 : Int, int2 : => Int) : Int = {
    if (int1 == 0) int2 else int1
  }
  
  def lexCombineInts(int1 : Int, _int2 : => Int, _int3 : => Int) : Int = {
    if (int1 == 0) {
      val int2 = _int2
      if (int2 == 0) {
        _int3
      } else {
        int2
      }      
    } else {
      int1
    }
  }
   
  def lexCombineInts(int1 : Int, _int2 : => Int,
                     _int3 : => Int, _int4 : => Int) : Int = {
    if (int1 == 0) {
      val int2 = _int2
      if (int2 == 0) {
        val int3 = _int3
        if (int3 == 0) {
          _int4
        } else {
          int3
        }      
      } else {
        int2
      }      
    } else {
      int1
    }
  }
   
  /**
   * Compute a polynomial hashcode for a sequence of things
   */
  def computeHashCode[A](a : Iterator[A], init : Int, multiplier : Int) =
    (init /: a)((hash, el) => hash * multiplier + el.hashCode)

  def computeHashCode[A](a : Iterable[A], init : Int, multiplier : Int) =
    (init /: a)((hash, el) => hash * multiplier + el.hashCode)

  //////////////////////////////////////////////////////////////////////////////

  abstract class BS_Result
  case class Found(index : Int) extends BS_Result
  case class NotFound(nextBiggerElement : Int) extends BS_Result

  /**
   * Binary search for an element in a sorted random-access sequent. The result
   * is either <code>Found(i)</code>, where <code>i</code> is the index of some
   * occurrence of <code>wanted</code> in <code>seq</code>, or
   * <code>NotFound(i)</code>, where <code>i</code> is the index of the
   * next-bigger element in <code>seq</code>. Note, that elements are never
   * compared with <code>==<code>, only with <code>(a compare b) == 0</code> 
   */
  def binSearch[T](seq : IndexedSeq[T], begin : Int, end : Int, wanted : T)
                  (implicit ord : Ordering[T]) : BS_Result = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC,
                    end >= begin &&
                    Logic.forall(begin, end - 1,
                                 (i:Int) => ord.lteq(seq(i), seq(i+1))))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    def post(res:BS_Result) = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(AC,
                       res match {
                       case Found(i) => i >= begin && i < end &&
                         ord.compare(seq(i), wanted) == 0
                       case NotFound(i) => i >= begin && i <= end &&
                         (i == begin || ord.lt(seq(i-1), wanted)) &&
                         (i == end || ord.gt(seq(i), wanted))
                       })
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      res
    }
    
    var lo : Int = begin
    var hi : Int = end
      
    while ( lo + 1 < hi ) {
      val mid = (lo + hi) / 2
      val c = ord.compare(seq(mid), wanted)
      if (c < 0) {
        lo = mid + 1
      } else if (c > 0) {
        hi = mid
      } else {
        return post(Found(mid))
      }
    }
      
    if (lo == hi) {
      post(NotFound(hi))
    } else {
      val c = ord.compare(seq(lo), wanted)
      if (c < 0) {
        post(NotFound(hi))
      } else if (c > 0) {
        post(NotFound(lo))
      } else {
        post(Found(lo))
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Remove all duplicates from a sorted sequence. It is assumed that duplicates
   * can only occur immediately following each other
   */
  def removeDuplicates[A](s : IndexedSeq[A]) : IndexedSeq[A] = {
    val it = s.iterator
    if (it.hasNext) {
      val resBuf = Vector.newBuilder[A]
      var prevEl = it.next
      resBuf += prevEl
      
      for (el <- it) {
        if (el != prevEl) {
          prevEl = el
          resBuf += el
        }
      }
      
      val res = resBuf.result
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(AC, Logic.forall(0, res.size,
                                        i => Logic.forall(i+1, res.size,
                                          j => res(i) != res(j))))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      res
    } else {
      s
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  abstract class FAS_RESULT[+A]
  case class FilteredSorted[A](res : Array[A]) extends FAS_RESULT[A]
  case class FoundBadElement[A](badElement : A) extends FAS_RESULT[A]

  /**
   * Filter a sequence of objects in order to detect the existence of certain
   * bad objects (<code>badEl</code>) and to remove certain unnecessary objects
   * (<code>skipEl</code>). If a bad element is found,
   * <code>FoundBadElement</code> is returned, otherwise a sorted array with the
   * elements that were kept is created and returned.
   */
  def filterAndSort[A : ClassTag]
                   (it : Iterator[A],
                    skipEl : A => Boolean, badEl : A => Boolean,
                    trafo : A => A,
                    comesBefore : (A, A) => Boolean)
                                                            : FAS_RESULT[A] = {
    val buf = ArrayBuilder.make[A]
    while (it.hasNext) {
      val el = it.next
      if (badEl(el)) return FoundBadElement(el)
      if (!skipEl(el)) buf += trafo(el)
    }

    val ar = buf.result
    Sorting.stableSort(ar, comesBefore)

    FilteredSorted(ar)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Return the first <code>Some(x)</code> of the given sequence, or
   * <code>None</code> if none exists
   */
  def some[A](vals : Iterator[Option[A]]) : Option[A] = {
    while (vals.hasNext) {
      val n = vals.next
      if (n.isDefined) return n
    }
    None
  }
   
  def some[A](vals : Iterable[Option[A]]) : Option[A] =
    some(vals.iterator)

  //////////////////////////////////////////////////////////////////////////////

  def disjointSeq[A](a : scala.collection.Set[A], b : Iterator[A]) : Boolean = {
    while (b.hasNext) {
      if (a contains b.next)
        return false
    }
    true
  }

  def disjointSeq[A](a : scala.collection.Set[A], b : Iterable[A]) : Boolean =
    disjointSeq(a, b.iterator)

  def disjointSeq[A](a1 : scala.collection.Set[A], a2 : scala.collection.Set[A],
                     b : Iterable[A]) : Boolean =
    disjointSeq(a1, a2, b.iterator)

  def disjointSeq[A](a1 : scala.collection.Set[A], a2 : scala.collection.Set[A],
                     b : Iterator[A]) : Boolean =  {
    while (b.hasNext) {
      val x = b.next
      if ((a1 contains x) && (a2 contains x))
        return false
    }
    true
  }

  def disjoint[A](a : scala.collection.Set[A],
                  b : scala.collection.Set[A]) : Boolean =
    if (a.size < b.size)
      disjointSeq(b, a)
    else
      disjointSeq(a, b)
    
  /**
   * Determine whether 3 given sets have any elements in common
   */
  def disjoint[A](a : scala.collection.Set[A],
                  b : scala.collection.Set[A],
                  c : scala.collection.Set[A]) : Boolean = {
    val asize = a.size
    val bsize = b.size
    val csize = c.size
    if (asize <= bsize && asize <= csize)
      disjointSeq(b, c, a)
    else if (bsize <= asize && bsize <= csize)
      disjointSeq(a, c, b)
    else
      disjointSeq(a, b, c)
  }
    
  //////////////////////////////////////////////////////////////////////////////

  def toArray[A : ClassTag](els : Iterator[A]) : Array[A] = {
    val buf = ArrayBuilder.make[A]
    buf ++= els
    buf.result
  }
    
  //////////////////////////////////////////////////////////////////////////////

  /**
   * reduceLeft that also works for empty sequences
   */
  def reduceLeft[A](els : Iterator[A], f : (A, A) => A) : Option[A] =
    if (els.hasNext) {
      var res = els.next
      while (els.hasNext) res = f(res, els.next)
      Some(res)
    } else {
      None
    }

  /**
   * reduceLeft that also works for empty sequences
   */
  def reduceLeft[A](els : Iterable[A], f : (A, A) => A) : Option[A] =
    reduceLeft(els.iterator, f)
    
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Compute the maximum of a sequence of ints. If the sequence
   * is empty, <code>0</code> is returned
   */
  def max(it : Iterator[Int]) : Int =
    if (it.hasNext) {
      var res = it.next
      for (t <- it) res = res max t
      res
    } else {
      0
    }

  /**
   * Compute the minimum of a sequence of ints. If the sequence
   * is empty, <code>0</code> is returned
   */
  def min(it : Iterator[Int]) : Int =
    if (it.hasNext) {
      var res = it.next
      for (t <- it) res = res min t
      res
    } else {
      0
    }

  /**
   * Compute the maximum of a sequence of ints. If the sequence
   * is empty, <code>0</code> is returned
   */
  def max(els : Iterable[Int]) : Int = max(els.iterator)
    
  /**
   * Determine a maximum element of a sequence of things under a given measure
   */
/*  def max[A, B <% Ordered[B]](it : Iterable[A], measure : (A) => B) : A =
    max(it.iterator, measure) */

  /**
   * Determine a maximum element of a sequence of things under a given measure
   */
  def max[A, B <% Ordered[B]](it : Iterator[A], measure : (A) => B) : A = {
    if (!it.hasNext) throw new NoSuchElementException

    var res = it.next
    var resSize = measure(res)
    while (it.hasNext) {
      val next = it.next
      val nextSize = measure(next)
      if (nextSize > resSize) {
        res = next
        resSize = nextSize
      }
    }
    res
  }

  /**
   * Determine a minimum element of a sequence of things under a given measure
   */
  def min[A, B <% Ordered[B]](it : Iterable[A], measure : (A) => B) : A =
    min(it.iterator, measure)

  /**
   * Determine a minimum element of a sequence of things under a given measure
   */
  def min[A, B <% Ordered[B]](it : Iterator[A], measure : (A) => B) : A = {
    if (!it.hasNext) throw new NoSuchElementException

    var res = it.next
    var resSize = measure(res)
    while (it.hasNext) {
      val next = it.next
      val nextSize = measure(next)
      if (nextSize < resSize) {
        res = next
        resSize = nextSize
      }
    }
    res
  }
     
  def minOption[A, B <% Ordered[B]](it : Iterator[A],
                                    measure : (A) => Option[B]) : Option[A] = {
    var res : Option[A] = None
    var resSize : Option[B] = None

    while (it.hasNext) {
      val next = it.next
      measure(next) match {
        case None => // nothing
        case s@Some(nextSize) =>
          resSize match {
            case Some(size) if (nextSize >= size) => // nothing
            case _ => {
              res = Some(next)
              resSize = s
            }
          }
      }
    }
    
    res
  }
     
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Split a sequence of things into two sequences, one with all the elements
   * for which certain predicate holds, and one with the elements for which the
   * predicate does not hold
   */
  def split[A](els : Iterator[A], firstKind : (A) => Boolean)
                              : (Vector[A], Vector[A]) = {
    val res1 = Vector.newBuilder[A]
    val res2 = Vector.newBuilder[A]
    while (els.hasNext) {
      val n = els.next
      if (firstKind(n))
        res1 += n
      else
        res2 += n
    }
    (res1.result, res2.result)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Determine whether <code>a</code> occurs in <code>b</code> as a sub-sequence
   */
  def subSeq[A](a : Iterator[A], b : Iterator[A]) : Boolean = {
    while (a.hasNext) {
      val const = a.next
      do {
        if (!b.hasNext) return false
      } while (const != b.next)
    }
    true    
  }

  /**
   * Determine whether <code>a</code> occurs in <code>b</code> as a sub-sequence
   */
  def subSeq[A](a : Iterator[A], aFilter : scala.collection.Set[A],
                b : Iterator[A]) : Boolean = {
    while (a.hasNext) {
      val const = a.next
      if (aFilter contains const) {
        do {
          if (!b.hasNext) return false
        } while (const != b.next)
      }
    }
    true    
  }

  /**
   * Determine whether the two given sequences/iterables contain
   * reference-identical objects.
   */
  def identicalSeqs[A <: AnyRef](a : Iterable[A], b : Iterable[A]) : Boolean = {
    val aIt = a.iterator
    val bIt = b.iterator
    while (aIt.hasNext) {
      if (!bIt.hasNext || !(aIt.next eq bIt.next))
        return false
    }
    !bIt.hasNext
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Merge two sequences that are sorted in strictly descending order and
   * produce a descending sequence with all elements occurring in at least one
   * of the sequences
   */
  def mergeSortedSeqs[A](a : IndexedSeq[A], b : IndexedSeq[A])
                        (implicit ord : Ordering[A]) : IndexedSeq[A] = {
    if (a.isEmpty)
      return b
    if (b.isEmpty)
      return a
    
    val res = Vector.newBuilder[A]
    val aIt = a.iterator
    val bIt = b.iterator
    
    var aNext = aIt.next
    var bNext = bIt.next
      
    while (true) {
      val c = ord.compare(aNext, bNext)
      
      if (c > 0) {
        res += aNext
        if (aIt.hasNext) {
          aNext = aIt.next
        } else {
          res += bNext
          res ++= bIt
          return res.result
        }
      } else if (c < 0) {
        res += bNext
        if (bIt.hasNext) {
          bNext = bIt.next
        } else {
          res += aNext
          res ++= aIt
          return res.result
        }
      } else {
        // both elements are considered equal, so we drop one of them
        if (aIt.hasNext) {
          aNext = aIt.next            
        } else {
          res += bNext
          res ++= bIt
          return res.result
        }
      }
    }
    
    null // never reached
  }

  //////////////////////////////////////////////////////////////////////////////

  def count[A](els : Iterable[A], p : (A) => Boolean) : Int =
    count(els.iterator, p)

  def count[A](els : Iterator[A], p : (A) => Boolean) : Int = {
    var res : Int = 0
    while (els.hasNext)
      if (p(els.next))
        res = res + 1
    res
  }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Given to sequences that are totally sorted in the same descending order,
   * determine those elements in <code>newSeq</code> that also occur in
   * <code>oldSeq</code>, and those elements in <code>newSeq</code> that do not
   * occur in <code>oldSeq</code>.
   */
  def diff[A](newSeq : IndexedSeq[A], oldSeq : IndexedSeq[A])
             (implicit ord : Ordering[A])
             : (IndexedSeq[A], IndexedSeq[A]) = {
    def post(resOld : IndexedSeq[A], resNew : IndexedSeq[A]) = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(AC, {
        val (checkOld, checkNew) = newSeq partition (oldSeq contains _)
        (resOld sameElements checkOld) && (resNew sameElements checkNew)
      })
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      (resOld, resNew)
    }

    if (newSeq.isEmpty)
      return post(newSeq, newSeq)

    if (oldSeq.isEmpty)
      return post(IndexedSeq.empty, newSeq)

    val resOld = Vector.newBuilder[A]
    val resNew = Vector.newBuilder[A]

    val newIt = newSeq.iterator
    val oldIt = oldSeq.iterator
    var oldEl = oldIt.next
    var c : Int = 0
    
    while (newIt.hasNext) {
      val newEl = newIt.next
      c = ord.compare(newEl, oldEl)
      
      while (c < 0)
        if (oldIt.hasNext) {
          oldEl = oldIt.next
          c = ord.compare(newEl, oldEl)
        } else {
          resNew += newEl
          resNew ++= newIt
          return post(resOld.result, resNew.result)
        }
      
      if (c > 0)
        resNew += newEl
      else
        resOld += newEl
    }
    
    post(resOld.result, resNew.result)
  }
  
  /**
   * Given to sequences that are totally sorted in the same descending order,
   * determine those elements that only occur in <code>seq0</code>, those that
   * occur in both sequences, and those that only occur in <code>seq1</code>.
   */
  def diff3[A](seq0 : IndexedSeq[A], seq1 : IndexedSeq[A])
              (implicit ord : Ordering[A])
              : (IndexedSeq[A], IndexedSeq[A], IndexedSeq[A]) = {
    def post(res : (IndexedSeq[A], IndexedSeq[A], IndexedSeq[A])) = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(AC, {
        val (left, common, right) = res
        val (ccommon, cleft) = diff(seq0, seq1)
        val (_, cright) = diff(seq1, seq0)
        (cleft sameElements left) &&
        (ccommon sameElements common) &&
        (cright sameElements right)
      })
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      res
    }

    if (seq0.isEmpty)
      return post(seq0, seq0, seq1)

    if (seq1.isEmpty)
      return post(seq0, seq1, seq1)

    val left = Vector.newBuilder[A]
    val common = Vector.newBuilder[A]
    val right = Vector.newBuilder[A]

    val seq0It = seq0.iterator
    val seq1It = seq1.iterator
    var seq0El = seq0It.next
    var seq1El = seq1It.next
    
    while (true) {
      val c = ord.compare(seq0El, seq1El)
    
      if (c < 0)
        right += seq1El
      else if (c > 0)
        left += seq0El
      else
        common += seq0El

      if (c <= 0) {
        if (seq1It.hasNext) {
          seq1El = seq1It.next
        } else {
          if (c < 0)
            left += seq0El
          left ++= seq0It
          return post(left.result, common.result, right.result)
        }
      }

      if (c >= 0) {
        if (seq0It.hasNext) {
          seq0El = seq0It.next
        } else {
          if (c > 0)
            right += seq1El
          right ++= seq1It
          return post(left.result, common.result, right.result)
        }
      }
    }
    
    null // never reached
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Compute the intersection of two sequences in (strictly) ascending
   * order. The procedure uses binary search on the second list, and
   * should in particular perform well if the second list is much bigger
   * than the first list.
   * <code>compare</code> should return a negative number of the
   * <code>a</code> argument is smaller than the <code>b</code> argument,
   * a positive number if <code>a</code> argument is bigger than
   * <code>b</code>, <code>0</code> otherwise.
   */
  def binIntersect[A, B](aEls : Iterator[A], bEls : IndexedSeq[B],
                         compare : (A, B) => Int) : Iterator[(A, B)] =
    new Iterator[(A, B)] {
      private val bSize = bEls.size

      private var nextPair : (A, B) = null
      private var nextBIndex : Int = -1      

      private def findNext : Unit = {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(AC, nextBIndex < bSize - 1)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        var newBIndex = nextBIndex + 1
        var newB = bEls(newBIndex)
        
        while (aEls.hasNext) {
          val nextA = aEls.next
          var step = 1

          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, nextBIndex + step == newBIndex)
          //-END-ASSERTION-/////////////////////////////////////////////////////

          var c = compare(nextA, newB)
          while (c > 0) {
            if (newBIndex == bSize - 1)
              // no further B elements
              return

            nextBIndex = newBIndex
            step = step * 2
            newBIndex = (nextBIndex + step) min (bSize - 1)

            newB = bEls(newBIndex)
            c = compare(nextA, newB)
          }

          if (c < 0) {
            // sought element is between nextBIndex and newBIndex;
            // use binary search to find exact index

            while (nextBIndex + 1 < newBIndex) {
              val mid = (nextBIndex + newBIndex) / 2
              val midB = bEls(mid)
              c = compare(nextA, midB)
              if (c < 0) {
                newBIndex = mid
                newB = midB
              } else {
                nextBIndex = mid
                if (c == 0) {
                  // found it
                  nextPair = (nextA, midB)
                  return
                }
              }
            }

            // B element does not exist, search for the next A element ...

          } else {
            // c == 0, we have found the exact index
            nextBIndex = newBIndex
            nextPair = (nextA, newB)
            return
          }
        }

        nextBIndex = bSize
      }

      def hasNext : Boolean =
        if (nextPair != null) {
          true
        } else if (nextBIndex < bSize - 1) {
          findNext
          nextPair != null
        } else {
          false
        }

      def next : (A, B) = {
        if (nextPair == null)
          findNext
        val res = nextPair
        nextPair = null
        res
      }
    }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Determine all elements that occur in more than one of the given collections
   */
  def findDuplicates[A](els : Iterator[A]) : Set[A] = {
    val seenEls, duplicates = new MHashSet[A]
    
    for (e <- els)
      (if (seenEls contains e) duplicates else seenEls) += e
    
    duplicates.toSet
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Iterator over exactly two elements
   */
  def doubleIterator[A](a : A, b : A) = new Iterator[A] {
    private var i = 0
    def hasNext = i < 2
    def next = {
      i = i + 1
      i match {
        case 1 => a
        case 2 => b
      }
    }
  }
  
  /**
   * Iterator over exactly three elements
   */
  def tripleIterator[A](a : A, b : A, c : A) = new Iterator[A] {
    private var i = 0
    def hasNext = i < 3
    def next = {
      i = i + 1
      i match {
        case 1 => a
        case 2 => b
        case 3 => c
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Lazily convert a function (over naturals) to a stream
   */
  def toStream[A](f : Int => A) : Stream[A] =
    toStreamHelp(0, f)
  
  private def toStreamHelp[A](n : Int, f : Int => A) : Stream[A] =
    f(n) #:: toStreamHelp(n + 1, f)
}

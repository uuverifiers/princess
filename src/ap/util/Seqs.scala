/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.util;

import scala.util.Sorting
import scala.collection.mutable.ArrayBuffer

object Seqs {

  private val AC = Debug.AC_SEQ_UTILS

  /**
   * Lexicographic comparison of two lists of things
   */
  def lexCompare[T <% Ordered[T]](it1 : Iterator[T], it2 : Iterator[T]) : Int = {
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
      
      val compRes = it1.next compare it2.next
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
  def binSearch[T <% Ordered[T]](seq : RandomAccessSeq[T],
                                 begin : Int, end : Int, wanted : T) : BS_Result = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(AC,
                    end >= begin &&
                    Logic.forall(begin, end - 1,
                                 (i:Int) => seq(i) <= seq(i+1)))
    def post(res:BS_Result) = {
      Debug.assertPost(AC,
                       res match {
                       case Found(i) => i >= begin && i < end &&
                         (seq(i) compare wanted) == 0
                       case NotFound(i) => i >= begin && i <= end &&
                         (i == begin || seq(i-1) < wanted) &&
                         (i == end || seq(i) > wanted)
                       })
      res
    }
    ////////////////////////////////////////////////////////////////////////////
    
    var lo : Int = begin
    var hi : Int = end
      
    while ( lo + 1 < hi ) {
      val mid = (lo + hi) / 2
      val c = (seq(mid) compare wanted)
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
      val c = (seq(lo) compare wanted)
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
  def removeDuplicates[A](s : Seq[A]) : Seq[A] = {
    val it = s.elements
    if (it.hasNext) {
      val res = new ArrayBuffer[A]
      var prevEl = it.next
      res += prevEl
      
      for (el <- it) {
        if (el != prevEl) {
          prevEl = el
          res += el
        }
      }
      
      //////////////////////////////////////////////////////////////////////////
      Debug.assertPost(AC, Logic.forall(0, res.size,
                                        i => Logic.forall(i+1, res.size,
                                          j => res(i) != res(j))))
      //////////////////////////////////////////////////////////////////////////
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
  def filterAndSort[A](it : Iterator[A],
                       skipEl : A => Boolean, badEl : A => Boolean,
                       trafo : A => A,
                       comesBefore : (A, A) => Boolean)
                                                            : FAS_RESULT[A] = {
    val buf = new ArrayBuffer[A]
    while (it.hasNext) {
      val el = it.next
      if (badEl(el)) return FoundBadElement(el)
      if (!skipEl(el)) buf += trafo(el)
    }

    val ar = buf.toArray
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
    some(vals.elements)

  //////////////////////////////////////////////////////////////////////////////

  def disjointSeq[A](a : scala.collection.Set[A], b : Iterator[A]) : Boolean =
    Logic.forall(for (x <- b) yield !(a contains x))

  def disjointSeq[A](a : scala.collection.Set[A], b : Iterable[A]) : Boolean =
    disjointSeq(a, b.elements)

  def disjointSeq[A](a1 : scala.collection.Set[A], a2 : scala.collection.Set[A],
                     b : Iterable[A]) : Boolean =
    disjointSeq(a1, a2, b.elements)

  def disjointSeq[A](a1 : scala.collection.Set[A], a2 : scala.collection.Set[A],
                     b : Iterator[A]) : Boolean =
    Logic.forall(for (x <- b) yield !((a1 contains x) && (a2 contains x)))

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

  def toRandomAccess[A](els : Iterator[A]) : RandomAccessSeq[A] = {
    val buf = new ArrayBuffer[A]
    buf ++= els
    buf.readOnly
  }
    
  def toRandomAccess[A](els : Iterable[A]) : RandomAccessSeq[A] = toArray(els)

  def toArray[A](els : Iterator[A]) : Array[A] = {
    val buf = new ArrayBuffer[A]
    buf ++= els
    buf.toArray
  }

  def toArray[A](els : Iterable[A]) : Array[A] = els match {
    case els : Collection[A] => {
      // size is finite and known
      val res = new Array[A] (els.size)
      els.copyToArray(res, 0)
      res
    }
    case _ => toArray(els.elements)
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
    reduceLeft(els.elements, f)
    
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
  def max(els : Iterable[Int]) : Int = max(els.elements)
    
  /**
   * Determine a maximum element of a sequence of things under a given measure
   */
  def max[A, B <% Ordered[B]](it : Iterable[A], measure : (A) => B) : A =
    max(it.elements, measure)

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
    min(it.elements, measure)

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
                                  : (RandomAccessSeq[A], RandomAccessSeq[A]) = {
    val res1 = new ArrayBuffer[A]
    val res2 = new ArrayBuffer[A]
    while (els.hasNext) {
      val n = els.next
      if (firstKind(n))
        res1 += n
      else
        res2 += n
    }
    (res1, res2)
  }

  def split[A](els : Iterable[A], firstKind : (A) => Boolean)
                                : (RandomAccessSeq[A], RandomAccessSeq[A]) =
    split(els.elements, firstKind)

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

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Merge two sequences that are sorted in strictly descending order and
   * produce a descending sequence with all elements occurring in at least one
   * of the sequences
   */
  def mergeSortedSeqs[A <% Ordered[A]]
                     (a : RandomAccessSeq[A], b : RandomAccessSeq[A]) : RandomAccessSeq[A] = {
    if (a.isEmpty)
      return b
    if (b.isEmpty)
      return a
    
    val res = new ArrayBuffer[A]
    val aIt = a.elements
    val bIt = b.elements
    
    var aNext = aIt.next
    var bNext = bIt.next
      
    while (true) {
      val c = aNext compare bNext
      
      if (c > 0) {
        res += aNext
        if (aIt.hasNext) {
          aNext = aIt.next
        } else {
          res += bNext
          res ++= bIt
          return res
        }
      } else if (c < 0) {
        res += bNext
        if (bIt.hasNext) {
          bNext = bIt.next
        } else {
          res += aNext
          res ++= aIt
          return res
        }
      } else {
        // both elements are considered equal, so we drop one of them
        if (aIt.hasNext) {
          aNext = aIt.next            
        } else {
          res += bNext
          res ++= bIt
          return res            
        }
      }
    }
    
    res // please the compiler
  }

  //////////////////////////////////////////////////////////////////////////////

  def count[A](els : Iterable[A], p : (A) => Boolean) : Int =
    count(els.elements, p)

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
  def diff[A <% Ordered[A]](newSeq : Seq[A], oldSeq : Seq[A]) : (Seq[A], Seq[A]) = {
    ////////////////////////////////////////////////////////////////////////////
    def post(res : (Seq[A], Seq[A])) = {
      Debug.assertPost(AC, {
        val (resOld, resNew) = res
        val (checkOld, checkNew) = newSeq partition (oldSeq contains _)
        (resOld sameElements checkOld) && (resNew sameElements checkNew)
      })
      res
    }
    ////////////////////////////////////////////////////////////////////////////

    if (newSeq.isEmpty)
      return post(newSeq, newSeq)

    if (oldSeq.isEmpty)
      return post(List(), newSeq)

    val resOld = new ArrayBuffer [A]
    val resNew = new ArrayBuffer [A]

    val newIt = newSeq.elements
    val oldIt = oldSeq.elements
    var oldEl = oldIt.next
    var c : Int = 0
    
    while (newIt.hasNext) {
      val newEl = newIt.next
      c = newEl compare oldEl
      
      while (c < 0)
        if (oldIt.hasNext) {
          oldEl = oldIt.next
          c = newEl compare oldEl
        } else {
          resNew += newEl
          resNew ++= newIt
          return post(resOld, resNew)
        }
      
      if (c > 0)
        resNew += newEl
      else
        resOld += newEl
    }
    
    post(resOld, resNew)
  }
  
  /**
   * Given to sequences that are totally sorted in the same descending order,
   * determine those elements that only occur in <code>seq0</code>, those that
   * occur in both sequences, and those that only occur in <code>seq1</code>.
   */
  def diff3[A <% Ordered[A]](seq0 : Seq[A], seq1 : Seq[A])
                                          : (Seq[A], Seq[A], Seq[A]) = {
    ////////////////////////////////////////////////////////////////////////////
    def post(res : (Seq[A], Seq[A], Seq[A])) = {
      Debug.assertPost(AC, {
        val (left, common, right) = res
        val (ccommon, cleft) = diff(seq0, seq1)
        val (_, cright) = diff(seq1, seq0)
        (cleft sameElements left) &&
        (ccommon sameElements common) &&
        (cright sameElements right)
      })
      res
    }
    ////////////////////////////////////////////////////////////////////////////

    if (seq0.isEmpty)
      return post(seq0, seq0, seq1)

    if (seq1.isEmpty)
      return post(seq0, seq1, seq1)

    val left = new ArrayBuffer [A]
    val common = new ArrayBuffer [A]
    val right = new ArrayBuffer [A]

    val seq0It = seq0.elements
    val seq1It = seq1.elements
    var seq0El = seq0It.next
    var seq1El = seq1It.next
    
    while (true) {
      val c = seq0El compare seq1El
    
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
          return post(left, common, right)
        }
      }

      if (c >= 0) {
        if (seq0It.hasNext) {
          seq0El = seq0It.next
        } else {
          if (c > 0)
            right += seq1El
          right ++= seq1It
          return post(left, common, right)
        }
      }
    }
    
    null // never reached
  }

  //////////////////////////////////////////////////////////////////////////////

  def unzip[A, B](seq : Seq[(A, B)]) : (Seq[A], Seq[B]) = {
    val lefts = new Array[A] (seq.size)
    val rights = new Array[B] (seq.size)
    
    var i = 0
    while (i < seq.size) {
      lefts(i) = seq(i)._1
      rights(i) = seq(i)._2
      i = i + 1
    }
    
    (lefts, rights)
  }
  
}

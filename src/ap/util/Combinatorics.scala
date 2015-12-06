/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014 Philipp Ruemmer <ph_r@gmx.net>
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

object Combinatorics {

  def genSubsequences[A](seq : Seq[A], num : Int) : Iterator[List[A]] =
    if (num == 0)
      Iterator single List()
    else
      for (i <- (0 until (seq.size - num + 1)).iterator;
           p = seq(i);
           s <- genSubsequences(seq.view(i + 1, seq.size), num - 1))
      yield p :: s

  def genSubsequencesWithDups[A](seq : Seq[A], num : Int) : Iterator[List[A]] =
    if (num == 0)
      Iterator single List()
    else
      for (i <- (0 until seq.size).iterator;
           p = seq(i);
           s <- genSubsequencesWithDups(seq.view(i, seq.size), num - 1))
      yield p :: s

  def cartesianProduct[A](seqs : List[Seq[A]]) : Iterator[List[A]] = seqs match {
    case List() =>
      Iterator single List()
    case s :: otherSeqs =>
      for (rem <- cartesianProduct(otherSeqs); a <- s.iterator) yield a :: rem
  }

  def genSubsequences[A](seqs : Seq[Seq[A]],
                         nums : Seq[Int]) : Iterator[List[A]] = {
    val subSeqs =
      (for ((seq, num) <- seqs.iterator zip nums.iterator)
       yield genSubsequences(seq, num).toSeq).toList
    for (comb <- cartesianProduct(subSeqs)) yield comb.flatten
  }

  def genSubsequencesWithDups[A](seqs : Seq[Seq[A]],
                                 nums : Seq[Int]) : Iterator[List[A]] = {
    val subSeqs =
      (for ((seq, num) <- seqs.iterator zip nums.iterator)
       yield genSubsequencesWithDups(seq, num).toSeq).toList
    for (comb <- cartesianProduct(subSeqs)) yield comb.flatten
  }

  def genCoveredVectors(nums : List[Int]) : Iterator[List[Int]] = nums match {
    case List() =>
      Iterator single List()
    case n :: otherNums =>
      for (vec <- genCoveredVectors(otherNums); i <- (0 to n).iterator)
      yield i :: vec
  }

  def genSubMultisets[A](seq : Seq[A]) : Iterator[List[A]] = {
    val uniqueEls = seq.distinct.toList
    val elNums = for (a <- uniqueEls) yield (seq count (_ == a))

    for (nums <- genCoveredVectors(elNums))
    yield (for ((num, el) <- nums.iterator zip uniqueEls.iterator;
                _ <- (0 until num).iterator) yield el).toList
  }

}
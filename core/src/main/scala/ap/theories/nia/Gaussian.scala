/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C)      2014-2019 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.basetypes.{IdealInt, IdealRat}
import ap.util.LRUCache

import scala.collection.immutable.BitSet


object Gaussian {
  private val cache = new LRUCache[Vector[Vector[IdealInt]],
                                   List[(Array[IdealInt], BitSet)]](3)

  def apply(array : Vector[Vector[IdealInt]]) =
    cache(array) { (new Gaussian(array)).getRows }
}


// Assuming rectangular matrix
class Gaussian private (array : Vector[Vector[IdealInt]]) {
  val rows = array.length
  val cols = array(0).length

  override def toString : String =
    (for (a <- array) yield a.mkString(" ")).mkString("\n")

  /**
   * Reduced linear rows with the originating row labels.
   */
  val getRows : List[(Array[IdealInt], BitSet)] = {
    val matrix = Array.tabulate(rows) { r =>
      Array.tabulate(cols) { c => IdealRat(array(r)(c)) }
    }
    val rowComb = Array.tabulate(rows) { r =>
      Array.tabulate(rows) { c =>
        if (r == c) IdealRat.ONE else IdealRat.ZERO
      }
    }

    var pivotRow = 0
    var col = 0

    while (pivotRow < rows && col < cols) {
      var pivot = pivotRow
      while (pivot < rows && matrix(pivot)(col).isZero)
        pivot += 1

      if (pivot < rows) {
        if (pivot != pivotRow) {
          val tmp = matrix(pivotRow); matrix(pivotRow) = matrix(pivot); matrix(pivot) = tmp
          val ctmp = rowComb(pivotRow); rowComb(pivotRow) = rowComb(pivot); rowComb(pivot) = ctmp
        }

        val pivotValue = matrix(pivotRow)(col)
        var c = col
        while (c < cols) {
          matrix(pivotRow)(c) = matrix(pivotRow)(c) / pivotValue
          c += 1
        }
        var l = 0
        while (l < rows) {
          rowComb(pivotRow)(l) = rowComb(pivotRow)(l) / pivotValue
          l += 1
        }

        var r = 0
        while (r < rows) {
          if (r != pivotRow) {
            val factor = matrix(r)(col)
            if (!factor.isZero) {
              c = col
              while (c < cols) {
                matrix(r)(c) = matrix(r)(c) - (factor * matrix(pivotRow)(c))
                c += 1
              }
              l = 0
              while (l < rows) {
                rowComb(r)(l) = rowComb(r)(l) - (factor * rowComb(pivotRow)(l))
                l += 1
              }
            }
          }
          r += 1
        }

        pivotRow += 1
      }

      col += 1
    }

    (for {
      r <- 0 until rows
      row = normaliseRow(matrix(r))
      if row.exists(x => !x.isZero)
      label = BitSet() ++
        (for (i <- 0 until rows;
              if !rowComb(r)(i).isZero)
         yield i)
    } yield (row, label)).toList
  }

  private def normaliseRow(row : Array[IdealRat]) : Array[IdealInt] = {
    if (row.forall(_.isZero))
      return Array.fill(cols)(IdealInt.ZERO)

    val lcmDenom =
      IdealInt.lcm(for (x <- row.iterator; if !x.isZero) yield x.denom)

    val intRow =
      Array.tabulate(cols) { i =>
        val x = row(i)
        if (x.isZero) IdealInt.ZERO else x.num * (lcmDenom / x.denom)
      }

    val gcdAbs =
      IdealInt.gcd(for (x <- intRow.iterator; if !x.isZero) yield x.abs)

    if (!gcdAbs.isZero && !gcdAbs.isOne)
      for (i <- 0 until cols)
        intRow(i) = intRow(i) / gcdAbs

    val firstNZ = intRow.find(x => !x.isZero)
    if (firstNZ.exists(_.signum < 0))
      for (i <- 0 until cols)
        intRow(i) = -intRow(i)

    intRow
  }
}

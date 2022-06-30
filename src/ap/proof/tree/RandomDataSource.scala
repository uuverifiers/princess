/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.tree;

import scala.util.Random
import scala.collection.mutable.Buffer

/**
 * Class to produce data needed to randomise proof construction.
 */
abstract class RandomDataSource {

  /**
   * Tell whether the class actually produces random data. If not,
   * <code>nextBoolean</code> will always return <code>false</code>,
   * <code>nextInt</code> will always return <code>0</code>.
   */
  def isRandom : Boolean

  /**
   * Produce a random Boolean value.
   */
  def nextBoolean : Boolean

  /**
   * Produce a random integer value.
   */
  def nextInt : Int

  /**
   * Produce a random integer value in the range <code>[0, bound)</code>.
   */
  def nextInt(bound : Int) : Int

  /**
   * Pick a random elements of the given sequence.
   */
  def pick[A](objects : IndexedSeq[A]) : A =
    objects(nextInt(objects.size))

  /**
   * Shuffle the given buffer
   */
  def shuffle[A](seq : Buffer[A]) : Unit =
    if (isRandom) {
      val N = seq.size
      for (i <- 0 until (N - 1)) {
        val newI = nextInt(N - i) + i
        if (newI != i) {
          val t = seq(i)
          seq(i) = seq(newI)
          seq(newI) = t
        }
      }
    }

  /**
   * Shuffle the given sequence
   */
  def shuffleSeq[A](seq : Seq[A]) : Seq[A] = {
    val buf = seq.toBuffer
    shuffle(buf)
    buf.toIndexedSeq
  }

  /**
   * Shuffle the given sequence, and return the new ordering
   */
  def shuffleWithPerm[A](seq : Buffer[A]) : Seq[Int] = {
    val N = seq.size
    val res = (0 until N).toArray
    
    if (isRandom)
      for (i <- 0 until (N - 1)) {
        val newI = nextInt(N - i) + i
        if (newI != i) {
          val t = seq(i)
          seq(i) = seq(newI)
          seq(newI) = t
          val t2 = res(i)
          res(i) = res(newI)
          res(newI) = t2
        }
      }

    res
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Source producing non-random data.
 */
object NonRandomDataSource extends RandomDataSource {
  def isRandom : Boolean = false
  def nextBoolean : Boolean = false
  def nextInt : Int = 0
  def nextInt(bound : Int) : Int = 0
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Source producing random data.
 */
class SeededRandomDataSource(seed : Int) extends RandomDataSource {
  private val rand = new Random (seed)

  def isRandom : Boolean = true
  def nextBoolean : Boolean = rand.nextBoolean
  def nextInt : Int = rand.nextInt
  def nextInt(bound : Int) : Int = rand nextInt bound
}

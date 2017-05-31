/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.tree;

import scala.util.Random

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

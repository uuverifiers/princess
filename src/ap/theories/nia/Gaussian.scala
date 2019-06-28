/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C)      2014-2019 Philipp Ruemmer <ph_r@gmx.net>
 *                    2014 Peter Backeman <peter.backeman@it.uu.se>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
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

package ap.theories.nia

import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{TerForConvenience, TermOrder, ConstantTerm}
import ap.terfor.preds.Atom
import ap.terfor.equations.EquationConj
import ap.terfor.TerForConvenience._
import ap.SimpleAPI
import ap.parser._
import ap.util.{Debug, LRUCache}

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

  //
  //  GAUSSIAN ELIMINATION PART
  // 

  val getRows : List[(Array[IdealInt], BitSet)] =
    // prevent confusing debugging output from here
    Console.withOut(ap.CmdlMain.NullStream) {

    // Startup engine
    SimpleAPI.withProver { p =>
    import p._

    // Create flags for the individual rows
    val rowFlags = createConstantsRaw("rowFlags", 0 until rows)
    // Create temporary constants
    val vars = createConstantsRaw("var", 0 until cols)

    makeExistentialRaw(rowFlags)
    makeExistentialRaw(vars)

    val colIndex = vars.iterator.zipWithIndex.toMap
    val rowIndex = rowFlags.iterator.zipWithIndex.toMap

    setMostGeneralConstraints(true)

    val o = order

    // Convert each row to an equation
    val eqs = EquationConj(
      for (r <- 0 until rows) yield {
        val terms =
          (Iterator single ((IdealInt.MINUS_ONE, rowFlags(r)))) ++
          (for (p@(coeff, v) <- array(r).iterator zip vars.iterator;
                if !coeff.isZero)
           yield p)
        LinearCombination(terms, o)
      }, o)

    addAssertion(eqs)

    // run system
    ???

    // Convert constraints back to a matrix (encoding polynomials)

    def lcToRow(lc : LinearCombination) : Array[IdealInt] = {
      val res = Array.fill[IdealInt](cols)(IdealInt.ZERO)
      for ((coeff, t : ConstantTerm) <- lc.iterator)
        for (col <- colIndex get t)
          res(col) = coeff
      res
    }

    def lcToLabel(lc : LinearCombination) : BitSet =
      BitSet() ++ (for ((_, t : ConstantTerm) <- lc.iterator;
                        row <- (rowIndex get t).iterator)
                   yield row)

    val constraint = getConstraintRaw.negate

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(Debug.AC_NIA,
                    constraint.size == constraint.arithConj.positiveEqs.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    (for (lc <- constraint.arithConj.positiveEqs.iterator;
          if {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(Debug.AC_NIA, lc.constant.isZero)
            //-END-ASSERTION-///////////////////////////////////////////////////
            true
          };
          matrixRow = lcToRow(lc);
          if matrixRow exists (_.signum != 0);
          label = lcToLabel(lc))
      yield (matrixRow, label)).toList

    }
  }
}

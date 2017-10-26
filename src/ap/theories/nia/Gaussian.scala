/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C)      2014-2017 Philipp Ruemmer <ph_r@gmx.net>
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
import ap.terfor.TerForConvenience._
import ap.SimpleAPI
import ap.parser._
import ap.util.Debug

import scala.collection.immutable.BitSet



// Assuming rectangular matrix
class Gaussian(array : Array[Array[IdealInt]]) {
  val rows = array.length
  val cols = array(0).length

  override def toString : String =
    (for (a <- array) yield a.mkString(" ")).mkString("\n")

  //
  //  GAUSSIAN ELIMINATION PART
  // 

  def getRows : List[(Array[IdealInt], BitSet)] =
    // prevent confusing debugging output from here
    Console.withOut(ap.CmdlMain.NullStream) {

    // Startup engine
    SimpleAPI.withProver { p =>
    import p._

    // Create flags for the individual rows
    val rowFlags = createExistentialConstants(rows)
    // Create temporary constants
    val vars = createExistentialConstants(cols)

    val colIndex =
      vars.iterator.map({ case (c : IConstant) => c.c }).zipWithIndex.toMap
    val rowIndex =
      rowFlags.iterator.map({ case (c : IConstant) => c.c }).zipWithIndex.toMap

    setMostGeneralConstraints(true)

    // Convert each row to an equation
    for (r <- 0 until rows) {
      var formula = 0 : ap.parser.ITerm
      for (c <- 0 until cols)
        if (array(r)(c) != 0)
          formula = formula + array(r)(c)*vars(c)

      !! (formula === rowFlags(r))
    }

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

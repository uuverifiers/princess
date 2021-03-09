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

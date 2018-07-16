/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.strings

import ap.theories.TheoryBuilder

/**
 * Interface to construct string theory objects with complex parameters.
 */
class SeqStringTheoryBuilder extends StringTheoryBuilder {

  import TheoryBuilder.TheoryBuilderException

  val name = "SeqString"

  def setBitWidth(w : Int) : Unit = bitWidth match {
    case None =>
      bitWidth = Some(w)
    case Some(`w`) =>
      // nothing
    case Some(oldWidth) =>
      throw new TheoryBuilderException(
        "Inconsistent string bit-widths: " + oldWidth + " and " + w)
  }

  private var bitWidth : Option[Int] = None

  lazy val theory = SeqStringTheory(bitWidth.get)

}
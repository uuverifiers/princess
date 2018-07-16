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

package ap.theories

object TheoryBuilder {

  def apply(desc : String) : TheoryBuilder = {
    val (className, params) = (desc indexOf ":") match {
      case -1  => (desc, "")
      case ind => (desc take ind, desc drop (ind + 1))
    }
    
    val cl = try {
      Class forName (className + "Builder")
    } catch {
      case _ : ClassNotFoundException =>
        throw new Exception("Instantiation of theory " + className + " failed")
    }
    val builder = cl.newInstance.asInstanceOf[TheoryBuilder]

    if (params != "")
      builder parseParameters params

    builder
  }

  class TheoryBuilderException(msg : String) extends Exception(msg)

}

/**
 * Interface to construct theory objects with complex parameters.
 */
abstract class TheoryBuilder {

  import TheoryBuilder._

  type T <: Theory

  val name : String

  /**
   * Retrieve the constructed theory object. After calling this function,
   * other configuration functions of the factory cannot be used anymore.
   */
  def theory : T

  /**
   * Parse textual theory parameters.
   */
  def parseParameters(str : String) : Unit =
    for (s <- str split ",")
      parseParameter(s)

  /**
   * Parse a single textual theory parameter.
   */
  def parseParameter(str : String) : Unit =
    throw new TheoryBuilderException(
      "Parameter " + str + " is not supported by theory " + name)

}
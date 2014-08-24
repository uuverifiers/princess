/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

package ap.util

object CmdlParser {

  /**
   * An boolean option of the kind "+opt" or "-opt"
   */
  object Opt {
    def unapply(arg : String) : Option[(String, Boolean)] =
      if (arg startsWith "+")
        Some(arg substring 1, true)
      else if (arg startsWith "-")
        Some((arg substring 1, false))
      else
        None
  }
  
  /**
   * An assignment of the kind "-var13=4" or "-xxx=hallo". The assigned value
   * is here only decoded to a string
   */  
  object ValueOpt {
    def unapply(arg : String) : Option[(String, String)] =
      if ((arg startsWith "-") && (arg contains "=")) {
        val i = arg indexOf "="
        Some(arg.substring(1, i), arg substring (i+1))
      } else {
        None
      }
  }

  /**
   * A value that represents an integer, like in "-var13=4"
   */  
  object IntVal {
    def unapply(arg : String) : Option[Int] =
      try {
        Some(arg.toInt) 
      } catch {
        case _ : NumberFormatException => None
      }
  }

  class UnknownArgumentException(arg : String)
      extends Exception("Unknown argument: " + arg)

}

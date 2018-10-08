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

package ap;

import ap.parameters.{GlobalSettings, Param}

import scala.collection.JavaConversions

/**
 * A simple class to simulate commandline calls of Princess from within
 * Java applications.
 */
object JavaWrapper {

  import DialogUtil.asString
  import JavaConversions.asScalaBuffer

  /**
   * Read inputs through a reader. The format of the problem has to be specified
   * using the option <code>-inputFormat=<value></code>. Use the option
   * <code>+quiet</code> to disable debugging output on <code>stderr</code>.
   */
  def readFromReader(input : java.io.Reader,
                     options : java.util.List[String]) : String = {
    var readOnce = false
    read(() => {
           if (readOnce)
             throw new Exception("Cannot read input multiple times")
           readOnce = true
           input
         },
         options)
  }

  /**
   * Read inputs from a string. The format of the problem has to be specified
   * using the option <code>-inputFormat=<value></code>. Use the option
   * <code>+quiet</code> to disable debugging output on <code>stderr</code>.
   */
  def readFromString(input : String,
                     options : java.util.List[String]) : String =
    read(() => new java.io.BufferedReader (
                 new java.io.StringReader(input)),
         options)

  /**
   * Read inputs from a string. The format of the problem has to be specified
   * using the option <code>-inputFormat=<value></code>. Use the option
   * <code>+quiet</code> to disable debugging output on <code>stderr</code>.
   */
  def readFromFile(file : java.io.File,
                   options : java.util.List[String]) : String =
    read(() => new java.io.BufferedReader (
                 new java.io.FileReader(file)),
         options)

  /**
   * Read inputs from a reader, with the possibility to read multiple times
   * and run portfolio solvers. The format of the problem has to be
   * specified using the option <code>-inputFormat=<value></code>. Use the
   * option <code>+quiet</code> to disable debugging output on
   * <code>stderr</code>.
   */
  def read(input : () => java.io.Reader,
           options : java.util.List[String]) : String = {
    val (settings, inputs) =
      GlobalSettings.fromArguments(options, GlobalSettings.DEFAULT)

    Console.withErr(if (Param.QUIET(settings))
                      CmdlMain.NullStream
                    else
                      Console.err) {

      if (!inputs.isEmpty)
        throw new Exception ("Did not expect any filenames")

      val filename = "<reader>"

      implicit val format = CmdlMain.determineInputFormat(filename, settings)
      asString {
        CmdlMain.proveProblems(settings, filename, input, false)
      }
    }
  }

}

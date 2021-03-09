/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018 Philipp Ruemmer <ph_r@gmx.net>
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

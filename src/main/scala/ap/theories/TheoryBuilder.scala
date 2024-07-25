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

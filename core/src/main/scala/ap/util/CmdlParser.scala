/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2023 Philipp Ruemmer <ph_r@gmx.net>
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

  /**
   * A value that represents an integer, like in "-var13=4"
   */  
  object LongVal {
    def unapply(arg : String) : Option[Long] =
      try {
        Some(arg.toLong)
      } catch {
        case _ : NumberFormatException => None
      }
  }

  class UnknownArgumentException(arg : String)
      extends Exception("Unknown argument: " + arg)

}

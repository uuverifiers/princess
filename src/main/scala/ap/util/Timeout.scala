/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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

import scala.util.DynamicVariable

object Timeout {
  
  private val checker : DynamicVariable[() => Unit] = new DynamicVariable(() => {})
  
  def raise : Unit = throw Timeout(None)
  
  /**
   * Check whether a timeout has occurred. In this case, on object of class
   * <code>Timeout</code> is thrown
   */
  def check : Unit = checker.value.apply

  /**
   * Execute code in the context of a given timeout checker <code>c</code>,
   * which is a function that raises <code>Timeout</code> in case a timeout
   * occurred
   */
  def withChecker[A](c : () => Unit)(comp : => A) : A =
    checker.withValue(c)(comp)
  
  /**
   * Run some computation for at most <code>millis</code> milliseconds. If a
   * timeout occurs, do <code>timeoutComp</code> instead.
   */
  def withTimeoutMillis[A](millis : Long)(comp: => A)(timeoutComp: => A) : A = {
    val timeBefore = System.currentTimeMillis
    val stoppingCond = () => {
      if (System.currentTimeMillis - timeBefore > millis)
        raise
    }

    catchTimeout{
      withChecker(stoppingCond) {
        comp
      }
    } {
      case _ => timeoutComp
    }
  }

  /**
   * Apply a conversion function to the argument of a possible raised timeout.
   * The idea is that the timeout argument should describe the partial
   * (unfinished) results that had been computed before the timeout
   */
  def unfinished[A](comp : => A)(errorHandler : PartialFunction[Any, Any]) : A =
    try { comp } catch {
      case Timeout(x) => {
        // avoid nested timeouts
        val newRes = withChecker(() => {}) {
          (errorHandler.orElse[Any, Any] { case _ => x })(x)
        }
        throw Timeout(newRes)
      }
    }

  def unfinishedValue[A](errorValue : Any)(comp : => A) : A =
    try { comp } catch {
      case Timeout(_) => throw Timeout(errorValue)
    }
  
  def catchTimeout[A](comp : => A)(errorHandler : (Any) => A) : A =
    try { comp } catch {
      case Timeout(x) => errorHandler(x)
    }
  
}

/**
 * Object that is thrown in case of a timeout (or the user stopped the proof
 * search)
 */
case class Timeout(unfinishedResult : Any) extends Exception

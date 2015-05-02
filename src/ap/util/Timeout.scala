/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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

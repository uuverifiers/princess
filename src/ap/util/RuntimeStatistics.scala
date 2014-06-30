/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.util;

/**
 * Object to keep track of some prover statistics, such as
 * the number of problems loaded and the amount of time spent
 * constructing proofs.
 */
object RuntimeStatistics {

  val firstLoadExtraTime : Long        = 2000

  val initialSlowdown : Double         = 5.0
  val slowdownHalftime : Long          = 4000

  val calculationSamplingPeriod : Long = 1000

  private var loadCount : Int = 0
  private var totalProofTime : Long = 0
  
  private def loadExtraTime = firstLoadExtraTime / (1 + loadCount)

  private def warmupSlowdown(proofTime : Long) : Double =
    if (longRunning)
      1.0
    else
      (initialSlowdown - 1.0) *
         slowdownHalftime / (slowdownHalftime + proofTime) + 1.0

//    (initialSlowdown - 1.0) * scala.math.pow(2.0, -proofTime / slowdownHalftime) + 1.0

  private def longRunning =
    totalProofTime > (slowdownHalftime * 30.0)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Method used by the <code>ParallelProver</code>. Given the
   * regular initial runtime of a proof task, recommend an increased
   * runtime to account for class loading and JVM warmup time.
   */
  def recommendInitialProofRuntime(regularInitial : Long)
                                  : Long = synchronized {
    println(loadCount)
    println(warmupSlowdown(totalProofTime))

    var leftTodo : Long  = regularInitial
    var allocated : Long = 0

    while (leftTodo > 0) {
      val slowdown = warmupSlowdown(totalProofTime + allocated)
      val effectivePeriod = (calculationSamplingPeriod / slowdown).toLong
      if (effectivePeriod <= leftTodo) {
        allocated = allocated + calculationSamplingPeriod
        leftTodo = leftTodo - effectivePeriod
      } else {
        allocated = allocated + (leftTodo * slowdown).toLong
        leftTodo = 0
      }
    }

    allocated + loadExtraTime
  }

  /**
   * Method used by the <code>ParallelProver</code>. Inform this
   * object that a proof task has started up and initial ran for
   * <code>runtime</code>. The result is a recommended bonus time
   * that should be awarded to the proof task, to compensate
   * class loading and JVM warmup delays.
   */
  def recordInitialProofRuntime(runtime : Long) : Long = synchronized {
    if (longRunning) {
      totalProofTime = totalProofTime + runtime
      loadCount = loadCount + 1
      0
    } else {
      val loadExtra = loadExtraTime
      val bonus =
        if (loadExtra <= runtime) {
          val b = recordProofRuntime(runtime - loadExtra)
          totalProofTime = totalProofTime + loadExtra
          b + loadExtra
        } else {
          recordProofRuntime(runtime)
        }

      loadCount = loadCount + 1

      bonus
    }
  }

  /**
   * Method used by the <code>ParallelProver</code>. Inform this
   * object that a proof task ran for
   * <code>runtime</code>. The result is a recommended bonus time
   * that should be awarded to the proof task, to compensate
   * class loading and JVM warmup delays.
   */
  def recordProofRuntime(runtime : Long) : Long = synchronized {
    if (longRunning) {
      totalProofTime = totalProofTime + runtime
      0
    } else {
      var leftTime : Long      = runtime
      var effectiveTime : Long = 0

      while (leftTime > 0) {
        val slowdown = warmupSlowdown(totalProofTime)
        if (calculationSamplingPeriod <= leftTime) {
          leftTime = leftTime - calculationSamplingPeriod
          totalProofTime = totalProofTime + calculationSamplingPeriod
          effectiveTime =
            effectiveTime + (calculationSamplingPeriod / slowdown).toLong
        } else {
          totalProofTime = totalProofTime + leftTime
          effectiveTime = effectiveTime + (leftTime / slowdown).toLong
          leftTime = 0
        }
      }

      runtime - effectiveTime
    }
  }

}
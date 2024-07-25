/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.util;

/**
 * Object to keep track of some prover statistics, such as
 * the number of problems loaded and the amount of time spent
 * constructing proofs. This class is only used from the
 * <code>ParallelFileProver</code>.
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
//    println("Load count: " + loadCount)
//    println("Current assumed warm-up slowdown: " +
//            warmupSlowdown(totalProofTime))


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

//    regularInitial + loadExtraTime
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

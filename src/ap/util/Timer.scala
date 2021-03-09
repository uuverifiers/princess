/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2018 Philipp Ruemmer <ph_r@gmx.net>
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

import scala.collection.mutable.{ArrayStack => Stack, HashMap, ArrayBuilder}
import scala.util.Sorting

import java.lang.Thread

/**
 * Object for measuring the time needed by the various tasks, methods, etc.
 * The object, in particular, supports nested operations that call each other
 * and correctly measures the time spent in each of the operations.
 *
 * The current implementation of the timer is not thread-safe;
 * if we detect that the class is used from multiple threads
 * we disable time measurements altogether. Calls are still counted.
 */
object Timer {

  private var startTime : Long = _
  private val runningOps = new Stack[String]

  // accumulated time spent in each operation
  private val accumulatedTimes = new HashMap[String, Long] {
    override def default(op : String) : Long = 0
  }
  // number of call to each operation
  private val callCounters = new HashMap[String, Int] {
    override def default(op : String) : Int = 0
  }
  
  private def addTime : Unit = {
    val now = System.nanoTime
    if (!runningOps.isEmpty) {
      val op = runningOps.top
      accumulatedTimes += (op -> (accumulatedTimes(op) + now - startTime))
    }
    startTime = now
  }
  
  private var lastThread : Thread = null
  private var timerDisabled = false

  def measure[A](op : String)(comp : => A) : A =
    if (timerDisabled) {

      synchronized {
        callCounters += (op -> (callCounters(op) + 1))
      }
      comp

    } else {

      if (lastThread == null) {
        lastThread = Thread.currentThread
      } else if (!(lastThread eq Thread.currentThread)) {
        Console.err.println(
          "Warning: disabling ap.util.Timer due to multi-threading")
        timerDisabled = true
        return measure(op)(comp)
      }

      addTime
      callCounters += (op -> (callCounters(op) + 1))
      runningOps push op
    
      try {
        comp
      } finally {
        if (!timerDisabled) {
          addTime
          runningOps.pop
        }
      }

    }
  
  def reset : Unit = {
    accumulatedTimes.clear
    callCounters.clear
    runningOps.clear
    lastThread    = null
    timerDisabled = false
  }
  
  override def toString : String = {
    val resBuf = ArrayBuilder.make[(String, Int, Long)]

    for ((op, time) <- accumulatedTimes)
      resBuf += ((op, callCounters(op), if (timerDisabled) 0l else time))

    val resAr = resBuf.result
    Sorting.stableSort(resAr)

    val table =
    (for ((op, count, time) <- resAr) yield {
      var paddedOp = op
      // HACK: for some reason, the <code>RichString.format</code> method does
      // not work
      while (paddedOp.size < 40)
        paddedOp = paddedOp + " "
      
      val timeInMS = time.toDouble / 1000000.0
          
      (paddedOp + "\t" + count + "\t" + timeInMS + "ms")
    }) mkString "\n"
    
    val totalTime =
      if (timerDisabled) 0l else (0l /: accumulatedTimes.valuesIterator)(_ + _)
    val totalTimeInMS =
      totalTime.toDouble / 1000000.0
    
    val totalCalls = (0 /: callCounters.valuesIterator)(_ + _)
    
    val total = "Total: " + totalCalls + ", " + totalTimeInMS + "ms"
    
    table + "\n" + total
  }
  
}

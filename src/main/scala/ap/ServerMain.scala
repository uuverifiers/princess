/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014-2024 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.util.CmdlParser

import scala.collection.mutable.ArrayBuffer
import java.util.concurrent.Semaphore

import java.net._

object ServerMain {

  // shutdown after 30min inactivity
  private val InactivityTimeout = 30 * 60 * 1000
  private val TicketLength = 40
  private val MaxThreadNum = 16
  private val MaxWaitNum   = 32
  private val WatchdogInit = 300

  private var lastActiveTime = System.currentTimeMillis
  private val serverSem = new Semaphore (MaxThreadNum)

  //////////////////////////////////////////////////////////////////////////////

  def main(args : Array[String]) : Unit = {
    val predefPort = args match {
      case Array(CmdlParser.IntVal(v)) => Some(v)
      case _ => None
    }

    val socket =
      new ServerSocket(predefPort getOrElse 0, MaxWaitNum,
                       InetAddress getByName "localhost")
    val port = socket.getLocalPort

    socket.setSoTimeout(InactivityTimeout / 2)

    Console.withOut(Console.err) {
      CmdlMain.printGreeting
      println()
      println("Daemon started on port " + port)
    }

    val r = new scala.util.Random
    val ticket =
      (for (_ <- 0 until TicketLength) yield r.nextPrintableChar) mkString ""

    println(port)
    println(ticket)

    ////////////////////////////////////////////////////////////////////////////
    // The main loop

    var serverRunning = true
    while (serverRunning) {

      // Get a token to serve another request
      serverSem.acquire

      try {
        val clientSocket = socket.accept
  
        val thread = new Thread(new Runnable {
          def run : Unit = Console.withErr(CmdlMain.NullStream) {
  
          val inputReader =
            new java.io.BufferedReader(
            new java.io.InputStreamReader(clientSocket.getInputStream))
          val outStream =
            clientSocket.getOutputStream

          val receivedTicket = inputReader.readLine
          if (ticket == receivedTicket) {
            val arguments = new ArrayBuffer[String]
    
            var str = inputReader.readLine
            var done = false
            while (!done && str != null) {
              str.trim match {
                case "PROVE_AND_EXIT" => {
                  done = true
                  Console.withOut(outStream) {
                    var checkNum = 0
                    var lastPing = System.currentTimeMillis
                    var cancel = false
                    var watchdogCounter = WatchdogInit
                    var watchdogCont = true

                    // watchdog that makes sure that the system
                    // is shut down eventually, in case the normal
                    // timeout fails
                    val watchdog = new Thread(new Runnable { def run : Unit = {
                      while (watchdogCont) {
                        Thread sleep 1000
                        watchdogCounter = watchdogCounter - 1
                        if (watchdogCounter <= 0) {
                          println("ERROR: hanging system, shutting down")
                          java.lang.System exit 1
                        }
                      }
                    }})

                    watchdog.start
 
                    try {
                      CmdlMain.doMain(arguments.toArray, {
                        checkNum = checkNum + 1
                        watchdogCounter = WatchdogInit
                        cancel || (checkNum % 50 == 0 && {
                          val currentTime = System.currentTimeMillis
                          while (inputReader.ready) {
                            inputReader.read
                            lastPing = currentTime
                          }
                          cancel = currentTime - lastPing > 3000
                          cancel
                        })
                      })
                    } finally {
                      watchdogCont = false
                    }
                  }
                }
                case str =>
                  arguments += str
              }
    
              if (!done)
                str = inputReader.readLine
            }
          }
    
          inputReader.close
          outStream.flush
          clientSocket.close
  
          // Put back the token
          lastActiveTime = System.currentTimeMillis
          serverSem.release
        }})

        thread.start
  
      } catch {
        case _ : SocketTimeoutException => {
          // check whether any other thread is still active
          serverSem.release

          if (serverSem.availablePermits == MaxThreadNum &&
              System.currentTimeMillis - lastActiveTime > InactivityTimeout) {
            Console.err.println("Shutting down inactive Princess daemon")
            serverRunning = false
          }
        }
      }
    }

  }

}

/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014-2016 Philipp Ruemmer <ph_r@gmx.net>
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
      println
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
  
        val thread = new Thread(new Runnable { def run : Unit = {
          Console setErr CmdlMain.NullStream
  
          val inputReader =
            new java.io.BufferedReader(
            new java.io.InputStreamReader(clientSocket.getInputStream))
    
          val receivedTicket = inputReader.readLine
          if (ticket == receivedTicket) {
            val arguments = new ArrayBuffer[String]
    
            var str = inputReader.readLine
            var done = false
            while (!done && str != null) {
              str.trim match {
                case "PROVE_AND_EXIT" => {
                  done = true
                  Console.withOut(clientSocket.getOutputStream) {
                    var checkNum = 0
                    var lastPing = System.currentTimeMillis
                    var cancel = false
  
                    CmdlMain.doMain(arguments.toArray, {
                      checkNum = checkNum + 1
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

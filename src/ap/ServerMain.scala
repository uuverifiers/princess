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

package ap;

import ap.util.CmdlParser

import scala.collection.mutable.ArrayBuffer
import scala.actors.Actor._
import scala.actors.{Actor, TIMEOUT}

import java.net._

object ServerMain {

  private val InactivityTimeout = 15 * 60 * 1000 // shutdown after 15min inactivity
  private val TicketLength = 40
  private val MaxThreadNum = 16
  private val MaxWaitNum   = 32

  private object ThreadToken

  //////////////////////////////////////////////////////////////////////////////

  def main(args : Array[String]) : Unit = {

    // since some of the actors in the class use blocking file operations,
    // we have to disable the actor-fork-join stuff to prevent deadlocks
    sys.props += ("actors.enableForkJoin" -> "false")

    val predefPort = args match {
      case Array(CmdlParser.IntVal(v)) => Some(v)
      case _ => None
    }

    val socket =
      new ServerSocket(predefPort getOrElse 0, MaxWaitNum,
                       InetAddress getByName "localhost")
    val port = socket.getLocalPort

    socket.setSoTimeout(InactivityTimeout)

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

    val serverActor = self
    for (_ <- 0 until MaxThreadNum)
      serverActor ! ThreadToken

    ////////////////////////////////////////////////////////////////////////////
    // The main loop

    var serverRunning = true
    while (serverRunning) try {

      // Get a token to serve another request
      receive {
        case ThreadToken => // nothing
      }

      val clientSocket = socket.accept

      actor {
        val inputReader =
          new java.io.BufferedReader(
          new java.io.InputStreamReader(clientSocket.getInputStream))
  
        val receivedTicket = inputReader.readLine
        if (ticket == receivedTicket) {
          val arguments = new ArrayBuffer[String]
          arguments += "+quiet"
  
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
	serverActor ! ThreadToken
      }

    } catch {
      case _ : SocketTimeoutException => {
        // check whether any other thread is still active

        var joinedThreads = 1
        var timeout = false
        while (!timeout && joinedThreads < MaxThreadNum)
          receiveWithin(0) {
            case ThreadToken => {
              joinedThreads = joinedThreads + 1
            }
            case TIMEOUT => {
              // there are still some threads running
              timeout = true
              for (_ <- 0 until joinedThreads)
                serverActor ! ThreadToken
            }
          }

        if (!timeout) {
          Console.err.println("Shutting down inactive Princess daemon")
          serverRunning = false
        }
      }
    }

  }

}
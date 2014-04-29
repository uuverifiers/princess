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

import java.net._

object ServerMain {

  def main(args : Array[String]) : Unit = {

    val predefPort = args match {
      case Array(CmdlParser.IntVal(v)) => Some(v)
      case _ => None
    }

    val socket =
      new ServerSocket(predefPort getOrElse 0, 1,
                       InetAddress getByName "localhost")
    val port = socket.getLocalPort

    socket.setSoTimeout(15 * 60 * 1000) // timeout of 15min

    Console.withOut(Console.err) {
      CmdlMain.printGreeting
      println
      println("Daemon started on port " + port)
    }

    val r = new scala.util.Random
    val ticket =
      (for (_ <- 0 until 40) yield r.nextPrintableChar) mkString ""

    println(port)
    println(ticket)

    try {

    while (true) {
      val clientSocket = socket.accept
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
              Console.withOut(clientSocket.getOutputStream) {
                CmdlMain.main(arguments.toArray)
              }
              done = true
            }
            case str =>
              arguments += str
          }

          if (!done)
            str = inputReader.readLine
        }
      }

      inputReader.close
    }

    } catch {
      case _ : SocketTimeoutException =>
        Console.err.println("Shutting down Princess daemon after 15min inactivity")
    }

  }

}
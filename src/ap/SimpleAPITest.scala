/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012 Philipp Ruemmer <ph_r@gmx.net>
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

package ap

import ap.parser._

object SimpleAPITest extends App {
  val p = SimpleAPI.spawn
  
  import IExpression._
  import SimpleAPI.ProverStatus

  println("-- Declaration of symbols")
  
  val c = p.createConstant("c")
  val d = p.createConstant("d")
  val r = p.createBooleanVariable("r")
  val s = p.createBooleanVariable("s")
  
  println("-- Adding some assertions (uses methods from IExpression._)")
  
  p !! (r & (c === d + 15))
  p !! (d >= 100)
  p !! (r ==> s)
  println(p??)

  println("-- Scoping (locally add assertions, declare symbols, etc)")
  
  p.scope {
    p !! (s ==> c <= -100)
    println(p??)
  }
  
  println(p??)

  println("-- Shorter notation via importing")

  p.scope {
    import p._
    
    val x, y, z = createConstant
    
    !! (x >= 0)
    !! (y >= x + 1)
    !! (z >= y * 2)
    println(??)
    
    !! (z === 20)
    println(??)

    !! (ex(a => a >= 0 & z + a === 0))
    println(??)
  }

  println("-- Asynchronous interface")
  
  println(p checkSat false)  // non-blocking
  println(p getStatus false) // non-blocking
  println(p getStatus true)  // blocking, equivalent to println(??)
  
  println("-- Asynchronous interface, busy waiting")
  
  println(p checkSat false)
  while ((p getStatus false) == ProverStatus.Running) {}
  println(p getStatus false)
  
  println("-- Stopping computations")
  
  println(p checkSat false)  // non-blocking
  println(p getStatus false) // non-blocking
  println(p.stop)            // blocks until prover has actually stopped
  println(p getStatus false) // non-blocking
  
  println("-- Stopping computation after a while")
  
  println(p checkSat false)  // non-blocking
  
  {
    println("Wait for 30ms ...")
    val m = System.currentTimeMillis
    while (System.currentTimeMillis < m + 30) {}
  }
  
  println(p.stop)            // blocks until prover has actually stopped

  
  p.shutDown
}

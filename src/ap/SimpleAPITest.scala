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
  val p = SimpleAPI.spawnWithAssertions
  
  import IExpression._
  import SimpleAPI.ProverStatus

  println("-- Declaration of symbols")
  
  val c = p.createConstant("c")
  val d = p.createConstant("d")
  val r = p.createBooleanVariable("r")
  val s = p.createBooleanVariable("s")

  println(p???) // no assertions, Sat
  
  println("-- Adding some assertions (uses methods from IExpression._)")
  
  p !! (r & (c === d + 15))
  p !! (d >= 100)
  p !! (r ==> s)
  println(p???) // still Sat

  println("-- Scoping (locally add assertions, declare symbols, etc)")
  
  p.scope {
    p !! (s ==> c <= -100)
    println(p???) // Unsat
  }
  
  println(p???) // Sat again

  println("-- Shorter notation via importing")

  p.scope {
    import p._
    
    val x, y, z = createConstant
    
    !! (x >= 0)
    !! (y >= x + 1)
    !! (z >= y * 2)
    println(???) // Sat
    
    !! (z === 20)
    println(???) // Sat

    scope {
      println("---- Nesting scopes")
  
      !! (ex(a => a >= 0 & z + a === 0))
      println(???) // Unsat
    }
    
    val f = createFunction("f", 1)
    !! (f(x) === f(z) + 1)
    println(???) // Sat
    
    val a, b = createConstant
    !! (f(a) === 0 & f(b) === 1)
    !! (a === b)
    println(???) // Unsat
  }

  println("-- Validity mode")

  p.scope {
    val x = p.createConstant
    
    p !! (x > 5)
    println(p.???) // Sat
    println("x = " + p.eval(x))     // x = 6
    println("2*x = " + p.eval(2*x)) // 2*x = 12
    
    p ?? (x > 0)   // prover switches to "validity" mode, and from now on
                   // answers Valid/Invalid instead of Unsat/Sat
    println(p.???) // Valid
  }

  println("-- Theory of arrays")
  
  p.scope {
    import p._

    val a, b = createConstant
    
    !! (a === store(store(store(b, 2, 2), 1, 1), 0, 0))
    
    println(???) // Sat
    
    scope {
      !! (a === store(b, 0, 1))
      println(???) // Unsat
    }
    
    scope {
      ?? (select(a, 2) > select(a, 1))
      println(???) // Valid
    }
    
    scope {
      !! (all(x => (select(a, x) === x + 1)))
      println(???) // Unsat
    }
  }
  
  println("-- Asynchronous interface")
  
  println(p checkSat false)  // non-blocking, Running
  println(p getStatus false) // non-blocking, Running
  println(p getStatus true)  // blocking, equivalent to println(??), Sat
  
  println("-- Asynchronous interface, busy waiting")
  
  println(p checkSat false) // Running
  while ((p getStatus false) == ProverStatus.Running) {}
  println(p getStatus false) // Sat
  
  println("-- Stopping computations")
  
  println(p checkSat false)  // non-blocking, Running
  println(p getStatus false) // non-blocking, Running
  println(p.stop)            // blocks until prover has actually stopped, Unknown
  println(p getStatus false) // non-blocking, Unknown
  
  println("-- Stopping computation after a while")
  
  println(p checkSat false)  // non-blocking, Running
  
  {
    println("Wait for 30ms ...")
    val m = System.currentTimeMillis
    while (System.currentTimeMillis < m + 30) {}
  }
  
  println(p.stop)            // blocks until prover has actually stopped, Sat

  
  p.shutDown
}

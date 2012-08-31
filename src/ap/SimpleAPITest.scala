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
  ap.util.Debug.enableAllAssertions(false)
  val p = SimpleAPI.spawn // WithAssertions
  
  import IExpression._
  import SimpleAPI.ProverStatus

  println("-- Declaration of symbols")
  
  val c, d = p.createConstant
  val r, s, v = p.createBooleanVariable

  println(p???) // no assertions, Sat
  
  println("-- Adding some assertions (uses methods from IExpression._)")
  
  p !! (r & (c === d + 15))
  p !! (d >= 100)
  p !! (r ==> s)
  println(p???) // still Sat

  println("-- Querying the model")
  
  println("r = " + p.eval(r))             // r = true
  println("r & !s = " + p.eval(r & !s))   // r & !s = false
  println("v = " + p.eval(v))             // v = true (arbitrary, value of v
                                          //          is not fixed by assertions)
  
  println("-- Scoping (locally add assertions, declare symbols, etc)")
  
  p.scope {
    p !! (s ==> c <= -100)
    println(p???) // Unsat
  }
  
  println(p???) // Sat again

  println("-- Shorter notation via importing")

  import p._
    
  scope {
    val x, y, z = createConstant
    
    !! (x >= 0)
    !! (y >= x + 1)
    !! (z >= y * 2)
    println(???) // Sat
    
    !! (z === 20)
    println(???) // Sat

    scope {
      println("---- Nesting scopes and use of quantifiers")
  
      !! (ex(a => a >= 0 & z + a === 0))
      println(???) // Unsat
    }
    
    println("---- Declaring functions")

    val f = createFunction("f", 1)
    !! (f(x) === f(z) + 1)
    println(???) // Sat
    
    println("f(x) + f(z) = " + eval(f(x) + f(z)))       // f(x) + f(z) = -1
    println("(f(x) === f(z)) = " + eval(f(x) === f(z))) // (f(x) === f(z)) = false
    
    val a, b = createConstant
    !! (f(a) === 0 & f(b) === 1)
    !! (a === b)
    println(???) // Unsat
  }

  println("-- Validity mode")

  scope {
    val x = createConstant
    
    !! (x > 5)
    println(???) // Sat
    println("x = " + eval(x))     // x = 6
    println("2*x = " + eval(2*x)) // 2*x = 12
    
    ?? (x > 0)   // prover switches to "validity" mode, and from now on
                 // answers Valid/Invalid instead of Unsat/Sat
    println(???) // Valid
  }

  println("-- Theory of arrays")
  
  scope {
    val a, b = createConstant
    
    !! (a === store(store(store(b, 2, 2), 1, 1), 0, 0))
    
    println(???) // Sat
    println("select(a, 1) = " + eval(select(a, 1)))   // select(a, 1) = 1
    println("select(a, 10) = " + eval(select(a, 10))) // select(a, 10) = 0
    
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

  //////////////////////////////////////////////////////////////////////////////
  
  reset

  println("-- Generating a larger amount of constraints")

  scope {
    val vars = (for (_ <- 0 to 1000) yield createConstant).toArray
    
    for (i <- 0 until 1000)
      !! (vars(i+1) === vars(i) + 1)
  
//    !! (connect(for (i <- 0 until 1000) yield (vars(i+1) === vars(i) + 1), IBinJunctor.And))
    
    println(???)
    println(eval(vars(1000)))
  }
  
  p.shutDown
}

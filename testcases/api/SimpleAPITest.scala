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

import ap._
import ap.parser._

object SimpleAPITest extends App {
  ap.util.Debug.enableAllAssertions(true)
  val p = SimpleAPI.spawnWithAssertions
  
  import IExpression._
  import SimpleAPI.ProverStatus

  def part(str : String) = {
    println
    println("-- " + str)
  }
  
  part("Declaration of symbols")
  
  val c, d = p.createConstant
  val r, s, v = p.createBooleanVariable

  println(p???) // no assertions, Sat
  
  part("Adding some assertions (uses methods from IExpression._)")
  
  p !! (r & (c === d + 15))
  p !! (d >= 100)
  p !! (r ==> s)
  println(p???) // still Sat

  part("Querying the model")
  
  println("r = " + p.eval(r))             // r = true
  println("r & !s = " + p.eval(r & !s))   // r & !s = false
  println("v = " + p.eval(v))             // v = true (arbitrary, value of v
                                          //          is not fixed by assertions)
  
  part("Scoping (locally add assertions, declare symbols, etc)")
  
  p.scope {
    p !! (s ==> c <= -100)
    println(p???) // Unsat
  }
  
  println(p???) // Sat again

  part("Shorter notation via importing")

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
      part("Nesting scopes and use of quantifiers")
  
      !! (ex(a => a >= 0 & z + a === 0))
      println(???) // Unsat
    }
    
    part("Declaring functions")

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

  part("Generating different models for the same formula")

  scope {
    val p1, p2, p3 = createBooleanVariable
    !! (p1 | !p2 | p3)
    !! (p2 | c <= -100)
    
    def dn[A](value : Option[A]) : String = value match {
      case Some(v) => v.toString
      case None => "-"
    }

    println("  p1  \t  p2  \t  p3")
    println("------------------------")
    while (??? == ProverStatus.Sat) {
      println("  " + dn(evalPartial(p1)) + "\t  "
                   + dn(evalPartial(p2)) + "\t  "
                   + dn(evalPartial(p3)))
      nextModel(false)
    }
  }

  part("Incremental solving")
  
  scope {
    val p1, p2, p3 = createBooleanVariable
    !! (p1 | !p2 | p3)
    !! (p2 | c <= -100)
    
    println("  p1  \t  p2  \t  p3")
    println("------------------------")
    while (??? == ProverStatus.Sat) {
      println("  " + eval(p1) + "\t  "
                   + eval(p2) + "\t  "
                   + eval(p3))
      !! (or(for (p <- List(p1, p2, p3)) yield (p </> eval(p))))
    }
  }

  part("Validity mode")

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

  part("Theory of arrays")
  
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
  
  part("Non-trivial quantifiers")
  
  scope {
    ?? (ex(x => 0 <= x & x < 10 & (2*x === c | x === d)))
    println(???)   // Invalid
    !! (c === 4 & false)
    println(???)   // Valid
  }

  part("Asynchronous interface")
  
  !! (true)
  println(p checkSat false)  // non-blocking, Running
  println(p getStatus false) // non-blocking, Running
  println(p getStatus true)  // blocking, equivalent to println(??), Sat
  
  part("Asynchronous interface, busy waiting")
  
  !! (true)
  println(p checkSat false) // Running
  while ((p getStatus false) == ProverStatus.Running) {}
  println(p getStatus false) // Sat
  
  part("Stopping computations")
  
  !! (true)
  p checkSat false                // non-blocking, Running
  p getStatus false               // non-blocking, usually still Running
  p.stop                          // blocks until prover has actually stopped, Unknown
  (p getStatus false) match {     // non-blocking, usually Unknown (unless prover
    case ProverStatus.Unknown |   // was already finished when calling "stop")
         ProverStatus.Sat =>
      println("expected result")
    case _ =>
      println("oops")
  }  

  part("Stopping computation after a while")
  
  !! (true)
  println(p checkSat false)  // non-blocking, Running
  
  {
    println("Wait for 30ms ...")
    val m = System.currentTimeMillis
    while (System.currentTimeMillis < m + 30) {}
  }
  
  println(p.stop)            // blocks until prover has actually stopped, Sat

  //////////////////////////////////////////////////////////////////////////////
  
  reset

  part("Interpolation")
  
  scope {
    setConstructProofs(true)
    val c = createConstant("c")
    val d = createConstant("d")
    val e = createConstant("e")

    setPartitionNumber(0)
    !! (0 <= c)

    setPartitionNumber(1)
    !! (c < d)

    setPartitionNumber(2)
    !! (0 > e & e > d)

    println(???)  // Unsat
    println(getInterpolants(Seq(Set(0), Set(1), Set(2))))
    println(getInterpolants(Seq(Set(1), Set(0), Set(2))))
  }

  part("Interpolation with functions")

  scope {
    setConstructProofs(true)
    val f = createFunction("f", 1)
    val c = createConstant("c")

    setPartitionNumber(0)
    !! (f(c) === 5)

    setPartitionNumber(1)
    !! (c === 3)

    setPartitionNumber(2)
    !! (f(3) < 0)

    println(???)  // Unsat
    println(getInterpolants(Seq(Set(0), Set(1), Set(2))))
    println(getInterpolants(Seq(Set(0, 2), Set(1))))
  }

  part("Interpolation with arrays")

  scope {
    setConstructProofs(true)
    val a = createConstant("a")
    val b = createConstant("b")

    setPartitionNumber(0)
    !! (store(a, 0, 1) === b)

    setPartitionNumber(1)
    !! (select(b, 0) === 2)

    println(???)  // Unsat
    println(getInterpolants(Seq(Set(0), Set(1))))
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  reset

  part("Generating a larger amount of constraints")

  scope {
    val vars = createConstants(101)
    
    for (i <- 0 until 100)
      !! (vars(i+1) === vars(i) + 1)
    
    println(???)                                        // Sat
    println("" + vars(100) + " = " + eval(vars(100)))   // c100 = 100
    
    scope {
      ?? (vars(0) >= 0 ==> vars(100) >= 0)
      println(???)                                        // Valid
    }
  }
  
  p.shutDown
}

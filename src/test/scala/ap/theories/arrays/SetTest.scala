/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2020-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.arrays

import ap.SimpleAPI
import ap.parser._
import ap.theories.arrays._

import org.scalacheck.Properties
import ap.util.ExtraAssertions

class SetTest extends Properties("SetTest") with ExtraAssertions {

  val expectedOutput = """Sat
Valid
Unsat
Valid
Valid
Valid
Valid
Valid
Invalid
Valid
Sat
Valid
Unsat
"""

  import IExpression._

  property("settest") = checkOutput(expectedOutput) {
  ap.util.Debug.enableAllAssertions(true)

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    val setTheory = new SetTheory(Sort.Integer)
    addTheory(setTheory)

    import setTheory.{contains, subsetOf, union, isect, compl, set, emptySet}

    val s = createConstant("s", setTheory.sort)
    val t = createConstant("t", setTheory.sort)
    val u = createConstant("u", setTheory.sort)
    val v = createConstant("v", setTheory.sort)

    val x = createConstant("x")
    val y = createConstant("y")
    val z = createConstant("z")

    !! (contains(s, x))
    !! (!contains(s, y))
    !! (u === union(s, t))

    println(???) // sat
//    println(partialModel)

    scope {
      ?? (contains(u, x))
      println(???) // valid
    }

    scope {
      !! (v === isect(s, t))
      !! (contains(v, y))
      println(???) // unsat
    }

    scope {
      ?? (compl(isect(s, t)) === union(compl(s), compl(t)))
      println(???) // valid
    }

    scope {
      ?? (isect(compl(s), compl(t)) === compl(union(s, t)))
      println(???) // valid
    }

    scope {
      ?? (subsetOf(isect(s, t), s) & subsetOf(s, union(s, t)))
      println(???) // valid
    }

    scope {
      ?? ((subsetOf(s, t) & subsetOf(t, s)) <=> (s === t))
      println(???) // valid
    }

    scope {
      ?? ((union(s, t) === isect(s, t)) <=> (s === t))
      println(???) // valid
    }

    scope {
      ?? (set(x, y) === emptySet)
      println(???) // invalid
    }

    scope {
      ?? ((set(x, y) === set(x)) <=> (x === y))
      println(???) // valid
    }

    scope {
      !! (set(x, y, z) === set(1, 2, 3))
      println(???) // sat
      ?? (x > 0)
      println(???) // valid
    }

    scope {
      !! (union(union(set(1), set(2)), union(set(3), set(4))) ===
          union(union(set(1), set(2)), union(set(3), set(5))))
      println(???) // unsat
    }

  }
  }
}

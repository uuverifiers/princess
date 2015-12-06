/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

import ap.parser._

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

/**
 * Class for keeping track of instantiated theories.
 */
object TheoryRegistry {

  private val theories = new ArrayBuffer[Theory]

  private val theoryIndex = new MHashMap[AnyRef, Theory]

  def lookupSymbol(f : IFunction) : Option[Theory] = synchronized {
    theoryIndex get f
  }

  def lookupSymbol(p : IExpression.Predicate) : Option[Theory] = synchronized {
    theoryIndex get p
  }

  def register(t : Theory) = synchronized {
    theories += t
    for (f <- t.functions)
      theoryIndex.put(f, t)
    for (p <- t.predicates)
      theoryIndex.put(p, t)
  }

}
/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.util;

import scala.util.Random
import scala.util.DynamicVariable

/**
 * A collect of methods for writing runtime assertions and inserting debugging
 * information. In particular, here the different categories and types of
 * assertions are defined and can be switched on and off.
 */
object Debug {

  /** Types of assertions, essentially the place where an assertion is put */
  abstract class ASSERTION_TYPE
  case object AT_METHOD_PRE extends ASSERTION_TYPE
  case object AT_METHOD_POST extends ASSERTION_TYPE
  case object AT_METHOD_INTERNAL extends ASSERTION_TYPE
  case object AT_OBJECT_CONSTRUCTION extends ASSERTION_TYPE

  /** Categories of assertions, essentially the software unit that the assertion
   * belongs to */
  abstract class ASSERTION_CATEGORY
  case object AC_MAIN extends ASSERTION_CATEGORY
  case object AC_SIMPLE_API extends ASSERTION_CATEGORY
  case object AC_BASE_TYPE extends ASSERTION_CATEGORY
  case object AC_SEQ_UTILS extends ASSERTION_CATEGORY
  case object AC_MAP_UTILS extends ASSERTION_CATEGORY
  case object AC_SET_UTILS extends ASSERTION_CATEGORY
  case object AC_QUEUE_WITH_ITERATORS extends ASSERTION_CATEGORY  
  case object AC_TERM_ORDER extends ASSERTION_CATEGORY
  case object AC_LINEAR_COMB extends ASSERTION_CATEGORY
  case object AC_EQUATIONS extends ASSERTION_CATEGORY
  case object AC_INEQUALITIES extends ASSERTION_CATEGORY
  case object AC_OMEGA extends ASSERTION_CATEGORY
  case object AC_PROPAGATION extends ASSERTION_CATEGORY
  case object AC_MODEL_FINDER extends ASSERTION_CATEGORY
  case object AC_PROP_CONNECTIVES extends ASSERTION_CATEGORY
  case object AC_ELIM_CONJUNCTS extends ASSERTION_CATEGORY  
  case object AC_VARIABLES extends ASSERTION_CATEGORY
  case object AC_SUBSTITUTIONS extends ASSERTION_CATEGORY
  case object AC_PREDICATES extends ASSERTION_CATEGORY
  case object AC_PROOF_TREE extends ASSERTION_CATEGORY
  case object AC_CONSTRAINT_SIMPLIFIER extends ASSERTION_CATEGORY
  case object AC_PROVER extends ASSERTION_CATEGORY
  case object AC_GOAL extends ASSERTION_CATEGORY
  case object AC_FACTS_TASK extends ASSERTION_CATEGORY
  case object AC_ELIM_FACTS_TASK extends ASSERTION_CATEGORY  
  case object AC_COMPLEX_FORMULAS_TASK extends ASSERTION_CATEGORY
  case object AC_PARSER extends ASSERTION_CATEGORY
  case object AC_ENVIRONMENT extends ASSERTION_CATEGORY
  case object AC_INPUT_ABSY extends ASSERTION_CATEGORY
  case object AC_PARAMETERS extends ASSERTION_CATEGORY
  case object AC_CLAUSE_MATCHER extends ASSERTION_CATEGORY
  case object AC_CONSTANT_FREEDOM extends ASSERTION_CATEGORY
  case object AC_ALIAS_ANALYSER extends ASSERTION_CATEGORY
  case object AC_PRESBURGER_TOOLS extends ASSERTION_CATEGORY
  case object AC_CERTIFICATES extends ASSERTION_CATEGORY
  case object AC_CERTIFICATE_LINEARISER extends ASSERTION_CATEGORY
  case object AC_COMPUTATION_LOGGER extends ASSERTION_CATEGORY
  case object AC_INTERPOLATION extends ASSERTION_CATEGORY
  case object AC_INTERPOLATION_IMPLICATION_CHECKS extends ASSERTION_CATEGORY

  private val everythingEnabled : (ASSERTION_TYPE, ASSERTION_CATEGORY) => Boolean =
    (at, ac) => true
  
  private val everythingDisabled : (ASSERTION_TYPE, ASSERTION_CATEGORY) => Boolean =
    (at, ac) => false 
  
  val enabledAssertions =
    new DynamicVariable[(ASSERTION_TYPE, ASSERTION_CATEGORY) => Boolean] (everythingEnabled)
  
  def enableAllAssertions(v : Boolean) = (enabledAssertions.value_= ((at, ac) => v))
  
  def assertTrue(at : ASSERTION_TYPE, ac : ASSERTION_CATEGORY,
                 assertion : => Boolean, message : => String) : Unit = {
    if (enabledAssertions.value(at, ac)) assert(assertion, message)
  }

  def assertTrue(at : ASSERTION_TYPE, ac : ASSERTION_CATEGORY,
                 assertion : => Boolean) : Unit = {
    if (enabledAssertions.value(at, ac)) assert(assertion)
  }

  def withoutAssertions[A](comp : => A) : A =
    enabledAssertions.withValue(everythingDisabled) { comp }
  
  /** Preconditions of methods */
  def assertPre(ac : ASSERTION_CATEGORY, assertion : => Boolean) : Unit =
    assertTrue(AT_METHOD_PRE, ac, assertion)

  def assertPreFast(ac : ASSERTION_CATEGORY, assertion : => Boolean) : Unit =
    assertTrue(AT_METHOD_PRE, ac, withoutAssertions(assertion))

  /** Postconditions of methods */
  def assertPost(ac : ASSERTION_CATEGORY, assertion : => Boolean) : Unit =
    assertTrue(AT_METHOD_POST, ac, assertion)

  def assertPostFast(ac : ASSERTION_CATEGORY, assertion : => Boolean) : Unit =
    assertTrue(AT_METHOD_POST, ac, withoutAssertions(assertion))

  /** Method-internal assertions (invariants) */
  def assertInt(ac : ASSERTION_CATEGORY, assertion : => Boolean) : Unit =
    assertTrue(AT_METHOD_INTERNAL, ac, assertion)

  def assertIntFast(ac : ASSERTION_CATEGORY, assertion : => Boolean) : Unit =
    assertTrue(AT_METHOD_INTERNAL, ac, withoutAssertions(assertion))

  /** Assertions about the construction of an object of a class */
  def assertCtor(ac : ASSERTION_CATEGORY, assertion : => Boolean) : Unit =
    assertTrue(AT_OBJECT_CONSTRUCTION, ac, assertion)
  
  def assertCtor(ac : ASSERTION_CATEGORY,
                 assertion : => Boolean, message : => String) : Unit =
    assertTrue(AT_OBJECT_CONSTRUCTION, ac, assertion, message)

  //////////////////////////////////////////////////////////////////////////////
  // The following functions for generating random numbers should only be used
  // in assertions and testcases
    
  private var randGen = new Random
    
  def initRandomGen(seed : Int) = {
    randGen = new Random (seed)
  }
  
  def random(lowerBound : Int, upperBound : Int) : Int =
    randGen.nextInt(upperBound - lowerBound) + lowerBound
  
  def randoms(lowerBound : Int, upperBound : Int) : Iterator[Int] =
    new Iterator[Int] {
      private val range = upperBound - lowerBound
      def hasNext = true
      def next = randGen.nextInt(range) + lowerBound
    }

  //////////////////////////////////////////////////////////////////////////////

  def signum(x : Int) : Int = {
    if (x < 0)
      -1
    else if (x > 0)
      1
    else
      0
  }
}

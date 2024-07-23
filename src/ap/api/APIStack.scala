/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.api

import ap._
import ap.parser._
import ap.proof.ModelSearchProver
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import ap.proof.theoryPlugins.Plugin
import ap.theories.TheoryCollector

import Signature.PredicateMatchConfig

import scala.collection.mutable.{ArrayStack, LinkedHashMap}

class APIStack {

  import SimpleAPI.ProverStatus

  var currentProver          : ModelSearchProver.IncProver = _
  var needExhaustiveProver   : Boolean = false
  var matchedTotalFunctions  : Boolean = false
  var ignoredQuantifiers     : Boolean = false
  var currentOrder           : TermOrder = _
  var existentialConstants   : Set[IExpression.ConstantTerm] = _
  var functionalPreds        : Set[IExpression.Predicate] = _
  var predicateMatchConfig   : PredicateMatchConfig = Map()
  var functionEnc            : FunctionEncoder = _
  var formulaeInProver       : LinkedHashMap[Conjunction, Int] =
                                 new LinkedHashMap[Conjunction, Int]
  var currentPartitionNum    : Int = SimpleAPI.COMMON_PART_NR
  var constructProofs        : Boolean = false
  var mostGeneralConstraints : Boolean = false
  var validityMode           : Boolean = _
  var lastStatus             : ProverStatus.Value = _
  var theoryPlugin           : Option[Plugin] = None
  var theoryCollector        : TheoryCollector = _
  var abbrevFunctions        : Set[IFunction] = Set()
  var abbrevPredicates       : Map[IExpression.Predicate,
                                   (Int, IExpression.Predicate)] = Map()

  def pushAPIFrame = {
    storedStates push (currentProver, needExhaustiveProver,
                       matchedTotalFunctions, ignoredQuantifiers,
                       currentOrder, existentialConstants,
                       functionalPreds, predicateMatchConfig,
                       functionEnc.clone, formulaeInProver.clone,
                       currentPartitionNum,
                       constructProofs, mostGeneralConstraints,
                       validityMode, lastStatus,
                       theoryPlugin, theoryCollector.clone,
                       abbrevFunctions,
                       abbrevPredicates)
  }

  def popAPIFrame = {
    val (oldProver, oldNeedExhaustiveProver,
         oldMatchedTotalFunctions, oldIgnoredQuantifiers,
         oldOrder, oldExConstants,
         oldFunctionalPreds, oldPredicateMatchConfig, oldFunctionEnc,
         oldFormulaeInProver, oldPartitionNum, oldConstructProofs,
         oldMGCs, oldValidityMode, oldStatus,
         oldTheoryPlugin, oldTheories,
         oldAbbrevFunctions, oldAbbrevPredicates) =
      storedStates.pop()
    currentProver          = oldProver
    needExhaustiveProver   = oldNeedExhaustiveProver
    matchedTotalFunctions  = oldMatchedTotalFunctions
    ignoredQuantifiers     = oldIgnoredQuantifiers
    currentOrder           = oldOrder
    existentialConstants   = oldExConstants
    functionalPreds        = oldFunctionalPreds
    predicateMatchConfig   = oldPredicateMatchConfig
    functionEnc            = oldFunctionEnc
    formulaeInProver       = oldFormulaeInProver
    currentPartitionNum    = oldPartitionNum
    constructProofs        = oldConstructProofs
    mostGeneralConstraints = oldMGCs
    validityMode           = oldValidityMode
    lastStatus             = oldStatus
    theoryPlugin           = oldTheoryPlugin
    theoryCollector        = oldTheories
    abbrevFunctions        = oldAbbrevFunctions
    abbrevPredicates       = oldAbbrevPredicates
  }

  def resetAPIConfig = {
    formulaeInProver.clear
    currentOrder           = TermOrder.EMPTY
    functionalPreds        = Set()
    predicateMatchConfig   = Map()
    functionEnc            = null
    abbrevFunctions        = Set()
    abbrevPredicates       = Map()
    theoryPlugin           = None
    theoryCollector        = new TheoryCollector
  }

  def resetAPIFormulas = {
    currentProver          = null
    needExhaustiveProver   = false
    matchedTotalFunctions  = false
    ignoredQuantifiers     = false
    lastStatus             = ProverStatus.Unknown
    validityMode           = false
    currentPartitionNum    = SimpleAPI.COMMON_PART_NR
  }

  def resetAPIOptions = {
    existentialConstants   = Set()
    constructProofs        = false
    mostGeneralConstraints = false
  }

  def frameNum : Int = storedStates.size

  def clearStack = storedStates.clear

  private val storedStates =
    new ArrayStack[(ModelSearchProver.IncProver,
                    Boolean,
                    Boolean,
                    Boolean,
                    TermOrder,
                    Set[IExpression.ConstantTerm],
                    Set[IExpression.Predicate],
                    PredicateMatchConfig,
                    FunctionEncoder,
                    LinkedHashMap[Conjunction, Int],
                    Int,
                    Boolean,
                    Boolean,
                    Boolean,
                    ProverStatus.Value,
                    Option[Plugin],
                    TheoryCollector,
                    Set[IFunction],
                    Map[IExpression.Predicate, (Int, IExpression.Predicate)])]

}

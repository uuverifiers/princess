/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2023 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.util;

import ap.{JavaWrapper, CmdlMain}
import CmdlMain.NullStream

import scala.collection.JavaConverters._

/**
 * Class to run some standard proof-tasks, with the goal of making
 * sure that all the relevant classes have been loaded into the JVM,
 * and JIT compilation has been started.
 */
object Warmup {

  def apply() : Unit = {
    Console.err.println("Doing warm-up exercises ...")
    Console.withOut(NullStream) { Console.withErr(NullStream) {
      JavaWrapper.readFromString(prob1, List("-inputFormat=smtlib").asJava)
    }}
  }

  val prob1 = """
(set-logic AUFLIA)
(set-info :source | Burns mutual exclusion protocol. This is a benchmark of the haRVey theorem prover. It was translated to SMT-LIB by Leonardo  de Moura |)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(set-option :boolean-functions-as-predicates true)
(declare-fun s_0 (Int) Bool)
(declare-fun s_1 (Int) Bool)
(declare-fun s_2 (Int) Bool)
(declare-fun s_3 (Int) Bool)
(declare-fun s_4 (Int) Bool)
(declare-fun s_5 (Int) Bool)
(declare-fun s (Int Int) Bool)
(declare-fun flag (Int) Bool)
(declare-fun p () Int)
(assert (not (=> (and 
(forall ((?p Int)) (=> (not (flag ?p)) (or (s_0 ?p) (s_1 ?p) (s_2 ?p)))) 
(forall ((?p Int)) 
(forall ((?q Int)) (=> (s_2 ?p) (not (s ?p ?q))))) 
(forall ((?p Int)) 
(forall ((?q Int)) (=> (and (< ?q ?p) (flag ?q) (or (s_5 ?p) (s_4 ?p) (and (s_3 ?p) (s ?p ?q)))) (and (not (s_5 ?q)) (not (and (s_4 ?q) (s ?q ?p))))))) 
(forall ((?p Int)) (=> (s_0 ?p) (not (or (s_1 ?p) (s_2 ?p) (s_3 ?p) (s_4 ?p) (s_5 ?p))))) 
(forall ((?p Int)) (=> (s_1 ?p) (not (or (s_2 ?p) (s_3 ?p) (s_4 ?p) (s_5 ?p))))) 
(forall ((?p Int)) (=> (s_2 ?p) (not (or (s_3 ?p) (s_4 ?p) (s_5 ?p))))) 
(forall ((?p Int)) (=> (s_3 ?p) (not (or (s_4 ?p) (s_5 ?p))))) 
(forall ((?p Int)) (=> (s_4 ?p) (not (s_5 ?p)))) 
(forall ((?q Int)) (let ((?v_0 (not (= ?q p)))) (=> (and ?v_0 (=> ?v_0 (s_0 ?q))) (not (or (=> ?v_0 (s_1 ?q)) (s_2 ?q) (s_3 ?q) (s_4 ?q) (s_5 ?q)))))) 
(forall ((?q Int)) (=> (=> (not (= ?q p)) (s_1 ?q)) (not (or (s_2 ?q) (s_3 ?q) (s_4 ?q) (s_5 ?q))))) 
(forall ((?q Int)) (=> (s_2 ?q) (not (or (s_3 ?q) (s_4 ?q) (s_5 ?q))))) 
(forall ((?q Int)) (=> (s_3 ?q) (not (or (s_4 ?q) (s_5 ?q))))) 
(forall ((?q Int)) (=> (s_4 ?q) (not (s_5 ?q)))) (s_0 p)) (and 
(forall ((?r Int)) (let ((?v_1 (not (= ?r p)))) (=> (not (and ?v_1 (=> ?v_1 (flag ?r)))) (or (and ?v_1 (=> ?v_1 (s_0 ?r))) (=> ?v_1 (s_1 ?r)) (s_2 ?r))))) 
(forall ((?r Int)) 
(forall ((?q Int)) (=> (s_2 ?r) (not (s ?r ?q))))) 
(forall ((?r Int)) 
(forall ((?q Int)) (let ((?v_2 (not (= ?q p)))) (=> (and (< ?q ?r) ?v_2 (=> ?v_2 (flag ?q)) (or (s_5 ?r) (s_4 ?r) (and (s_3 ?r) (s ?r ?q)))) (and (not (s_5 ?q)) (not (and (s_4 ?q) (s ?q ?r))))))))))))
(check-sat)
(exit)

  """

}

/**
 * This file is part of ePrincess, a theorem prover based on 
 * Bounded Rigid E-Unification (http://user.it.uu.se/~petba168/breu/) 
 * incoporated into the Princess theorem prover
 * <http://www.philipp.ruemmer.org/princess.shtml>
 * 
 * Copyright (C) 2009-2016 Peter Backeman <peter@backeman.se>
 * Copyright (C) 2009-2016 Philipp Ruemmer <ph_r@gmx.net>
 *
 * ePrincess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * ePrincess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with ePrincess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.connection;

import ap.terfor.ConstantTerm

package object connection {

  // We use a special kind of clause,
  // where each literal is a list of literals (to allow equations)
  type Clause = List[List[Node]]
  type OrderNode = (List[Node], List[(ConstantTerm, Boolean)])
  type OrderClause = List[OrderNode]
  type BREUOrder = List[(ConstantTerm, Boolean)]  

  def clauseToString(clause : OrderClause) : String =
    (for ((nodes, _) <- clause) yield {
      nodes.mkString("^")
    }).mkString(" v ")
}

abstract class Connection
case class ConnectionNegEq(node : Int) extends Connection
case class ConnectionCompLits(node1 : Int, node2 : Int) extends Connection

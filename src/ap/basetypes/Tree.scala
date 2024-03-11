/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2015-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.basetypes;

import scala.collection.mutable.Stack

object Leaf {
  def apply[D](d : D) = Tree(d, List())
  def unapply[D](t : Tree[D]) : Option[D] = t match {
    case Tree(d, List()) => Some(d)
    case _ => None
  }
}

/**
 * Polymorphic class for representing finite trees, with
 * unbounded branching.
 */
case class Tree[D](d : D, children : List[Tree[D]]) {
  def map[E](f : D => E) : Tree[E] = {
    val newD = f(d)
    Tree(newD, children map (_ map f))
  }
  def mapUpDown(f : D => D) : Tree[D] = {
    val newD = f(d)
    val newChildren = children map (_ map f)
    Tree(f(newD), newChildren)
  }
  def foreach[U](f : D => U) : Unit = {
    f(d)
    for (c <- children) c foreach f
  }
  def foreachPostOrder[U](f : D => U) : Unit = {
    for (c <- children) c foreachPostOrder f
    f(d)
  }
  def zip[E](t : Tree[E]) : Tree[(D, E)] = t match {
    case Tree(e, children2) =>
      Tree((d, e),
           for ((c1, c2) <- children zip children2)
           yield (c1 zip c2))
  }
  def unzip[D1, D2](implicit asPair: D => (D1, D2)): (Tree[D1], Tree[D2]) = {
    val (children1, children2) = (for (c <- children) yield c.unzip).unzip
    val (d1, d2) = asPair(d)
    (Tree(d1, children1), Tree(d2, children2))
  }
  def subtrees : Tree[Tree[D]] =
    Tree(this, for (c <- children) yield c.subtrees)
  def toList : List[D] = iterator.toList
  def toSeq = toList
  def toSet = iterator.toSet
  def iterator = new Iterator[D] {
    val todo = new Stack[Tree[D]]
    todo push Tree.this
    def hasNext = !todo.isEmpty
    def next() = {
      val Tree(data, children) = todo.pop
      for (x <- children)
        todo push x
      data
    }
  }

  def prettyPrint : Unit =
    prettyPrint("")

  def prettyPrint(indent : String) : Unit = {
    val newIndent = indent + "   "
    println(indent + d)
    for (c <- children) (c prettyPrint newIndent)
  }

  def size = iterator.size
}

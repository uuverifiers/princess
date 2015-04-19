/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2015 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

package ap.basetypes;

import scala.collection.mutable.ArrayStack

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
    val todo = new ArrayStack[Tree[D]]
    todo push Tree.this
    def hasNext = !todo.isEmpty
    def next = {
      val Tree(data, children) = todo.pop
      todo ++= children
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

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

/**
 * Background predicate for the BAPA decision procedure and interpolator
 */

\predicates {
  subsetOf(int, int);
  setEq(int, int);
  isEmpty(int);
  inSet(int, int);
}

\functions {
  int union(int, int);
  int intersection(int, int);
  int complementation(int);
  int size(int);
  int difference(int, int);
  int singleton(int);

  int emptySet, universalSet;
}

\problem {

////////////////////////////////////////////////////////////////////////////////
// Axioms describing intersection and complementation

  \forall int x, y; {intersection(x, y)}
                 intersection(x, y) = intersection(y, x)
->
  \forall int x, y, z; {intersection(intersection(x, y), z)}
                 intersection(intersection(x, y), z) = intersection(intersection(x, z), y)
->
  \forall int x, y, z; {intersection(x, intersection(y, z))}
      intersection(x, intersection(y, z)) = intersection(intersection(x, y), z)
->
  \forall int x; {intersection(x, x)}
                 intersection(x, x) = x
->
  \forall int x, y; {intersection(intersection(x, y), y)}
                 intersection(intersection(x, y), y) = intersection(x, y)

->
  \forall int x; {complementation(complementation(x))}
                 complementation(complementation(x)) = x
->
  \forall int x; {intersection(x, complementation(x))}
                 intersection(x, complementation(x)) = emptySet
->
  size(emptySet) = 0
->
  complementation(emptySet) = universalSet
->
  complementation(universalSet) = emptySet
->
  \forall int x; {intersection(x, emptySet)}
                 intersection(x, emptySet) = emptySet
->
  \forall int x; {intersection(emptySet, x)}
                 intersection(emptySet, x) = emptySet
->
  \forall int x; {intersection(x, universalSet)}
                 intersection(x, universalSet) = x
->
  \forall int x; {intersection(universalSet, x)}
                 intersection(universalSet, x) = x

////////////////////////////////////////////////////////////////////////////////
// Everything is negated (the definitions are premisses)

->
  \forall int x, y; {union(x, y)} union(x, y) = union(x, y)
  

-> false
}

/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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
 * Background predicate for the Princess-Wolverine interface
 */

\predicates {
  inArray(int);
  inSigned(int, int);
  inUnsigned(int, int);
}

\functions {
  \relational \partial int shiftLeft(int, int);

  \relational \partial int addSigned(int, int, int);
  \relational \partial int addUnsigned(int, int, int);
}

\problem {

////////////////////////////////////////////////////////////////////////////////
// Bit-shifts (which are used in most of the other definitions)

  \forall int x, y; {shiftLeft(x, y)} (
    y > 32 -> shiftLeft(x, y) = shiftLeft(4*1024*1024*1024*x, y-32))
&
  \forall int x; {shiftLeft(x, 32)}
    shiftLeft(x, 32) = 4*1024*1024*1024*x
&
  \forall int x; {shiftLeft(x, 31)}
    shiftLeft(x, 31) = 2*1024*1024*1024*x
&
  \forall int x, y; {shiftLeft(x, y)} (
    y < 31 & y > 0 -> shiftLeft(x, y) = shiftLeft(2*x, y-1))
&
  \forall int x; {shiftLeft(x, 0)} shiftLeft(x, 0) = x
&

////////////////////////////////////////////////////////////////////////////////
// Domain predicates

  \forall int x, width; (width != 32 -> inSigned(width, x) ->
    \exists int y; (y = shiftLeft(1, width - 1) & x >= -y & x < y))
&
  \forall int x, width; (width != 32 -> inUnsigned(width, x) ->
    x >= 0 & x < shiftLeft(1, width))
&

  \forall int x; (inSigned(32, x) ->
    x >= -2*1024*1024*1024 & x < 2*1024*1024*1024)
&
  \forall int x; (inUnsigned(32, x) ->
    x >= 0 & x < 4*1024*1024*1024)
&

////////////////////////////////////////////////////////////////////////////////
// Addition with overflow

  \forall int x, y, res, width; {addSigned(width, x, y)} (
    width != 32 -> addSigned(width, x, y) = res ->
    \exists int corr; (corr = shiftLeft(1, width) &
                       (res = x + y | res = x + y - corr |
                                      res = x + y + corr)) &
    inSigned(width, res)
  )
&
  \forall int x, y, res; {addSigned(32, x, y)} (
    addSigned(32, x, y) = res ->
    (res = x + y | res = x + y - 4*1024*1024*1024 |
                   res = x + y + 4*1024*1024*1024) &
    res >= -2*1024*1024*1024 & res < 2*1024*1024*1024
  )

/* This version currently does not perform well due to rounding
  \forall int x, y, res, width; {addSigned(width, x, y)} (
    addSigned(width, x, y) = res ->
    \exists int k; res = x + y + shiftLeft(k, width) &
    inSigned(width, res)
  ) */

&

  \forall int x, y, res, width; {addUnsigned(width, x, y)} (
    width != 32 -> addUnsigned(width, x, y) = res ->
    (res = x + y | res = x + y - shiftLeft(1, width)) &
    inUnsigned(width, res)
  )
&
  \forall int x, y, res; {addUnsigned(32, x, y)} (
    addUnsigned(32, x, y) = res ->
    (res = x + y | res = x + y - 4*1024*1024*1024) &
    res >= 0 & res < 4*1024*1024*1024
  )

/* This version currently does not perform well due to rounding
  \forall int x, y, res, width; {addUnsigned(width, x, y)} (
    addUnsigned(width, x, y) = res ->
    \exists int k; res = x + y + shiftLeft(k, width) &
    inUnsigned(width, res)
  ) */


////////////////////////////////////////////////////////////////////////////////
// Everything is negated (the definitions are premisses)

-> false
}
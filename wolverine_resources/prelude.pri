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
  \partial int select(int, int);
  \partial int store(int, int, int);

  \partial \relational int shiftLeft(int, int);
  \partial \relational int shiftRight(int, int);

  \relational \partial int addSigned(int, int, int);
  \relational \partial int addUnsigned(int, int, int);

  \relational \partial int mulSigned(int, int, int);
  \relational \partial int mulUnsigned(int, int, int);

  \relational \partial int divSigned(int, int, int);
  \relational \partial int divUnsigned(int, int, int);

  \relational \partial int subSigned(int, int, int);
  \relational \partial int subUnsigned(int, int, int);
  
  \relational \partial int minusSigned(int, int);
  \relational \partial int minusUnsigned(int, int);
  
// Bit-wise boolean operations that are independent of
// the number of bits
  \partial \relational int and(int, int);

// Modulo, which we assume not reveal any overflows (correct?)
  \partial \relational int mod(int, int);

// General (unbounded) multiplication
  \partial \relational int mul(int, int);

// General (unbounded) division
  \partial \relational int div(int, int);

// Absolute value
  \partial \relational int abs(int);

// Arith-1 functions  
  \partial \relational int equals(int, int);
  \partial \relational int lessThan(int, int);
  \partial \relational int lessEqual(int, int);
  \partial \relational int bitNegU1(int);

// Typecasts
  \relational \partial int signed2unsigned(int, int);

// Pairs
  \partial int pair(int, int);
  \partial int proj1(int);
  \partial int proj2(int);

}

\problem {

////////////////////////////////////////////////////////////////////////////////
// Array axioms
        \forall int ar, ind, val;
             {select(store(ar, ind, val), ind)}
             select(store(ar, ind, val), ind) = val
->
        \forall int ar, ind1, ind2, val;
             {select(store(ar, ind1, val), ind2)}
             (ind1 != ind2 ->
              select(store(ar, ind1, val), ind2) = select(ar, ind2))
->

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
    16 <= y & y < 31 -> shiftLeft(x, y) = shiftLeft(64*1024*x, y-16))
&
  \forall int x, y; {shiftLeft(x, y)} (
    y < 16 & y > 0 -> shiftLeft(x, y) = shiftLeft(2*x, y-1))
&
  \forall int x; {shiftLeft(x, 0)} shiftLeft(x, 0) = x
&

  \forall int x, y, res; {shiftRight(x, y)} (
    shiftRight(x, y) = res ->
    \exists int subres, diff; (
      subres = shiftLeft(res, y) & diff = shiftLeft(1, y) & (
      x >= 0 & subres <= x & subres + diff > x
      |
      x < 0 & subres >= x & subres - diff < x
    )))
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
    inUnsigned(32, res)
  )

/* This version currently does not perform well due to rounding
  \forall int x, y, res, width; {addUnsigned(width, x, y)} (
    addUnsigned(width, x, y) = res ->
    \exists int k; res = x + y + shiftLeft(k, width) &
    inUnsigned(width, res)
  ) */

////////////////////////////////////////////////////////////////////////////////
// Unary minus with overflow

&
  \forall int x, res; {minusSigned(32, x)} (
    minusSigned(32, x) = res ->
    (res = -x | res = -x - 4*1024*1024*1024) &
    inSigned(32, res)
  )

&
  \forall int width, x, res; {minusSigned(width, x)} (
    width != 32 -> minusSigned(width, x) = res ->
    (res = -x | res = -x - shiftLeft(1, width)) &
    inSigned(width, res)
  )

&
  \forall int x, res; {minusUnsigned(32, x)} (
    minusUnsigned(32, x) = res ->
    (res = -x | res = -x + 4*1024*1024*1024) &
    inUnsigned(32, res)
  )

&
  \forall int width, x, res; {minusUnsigned(width, x)} (
    width != 32 -> minusUnsigned(width, x) = res ->
    (res = -x | res = -x + shiftLeft(1, width)) &
    inUnsigned(width, res)
  )

////////////////////////////////////////////////////////////////////////////////
// Subtraction with overflow

&
  \forall int width, x, y; {subSigned(width, x, y)}
    subSigned(width, x, y) = addSigned(width, x, minusSigned(width, y))
&
  \forall int width, x, y; {subUnsigned(width, x, y)}
    subUnsigned(width, x, y) = addUnsigned(width, x, minusUnsigned(width, y))

////////////////////////////////////////////////////////////////////////////////
// Bit-wise and. This mainly does a case analysis over the second
// argument, which means that it is usually more
// efficient to have constant values as the second argument

&
  \forall int x; {and(x, 0)} and(x, 0) = 0
&
  \forall int x; {and(x, -1)} and(x, -1) = x
&
  \forall int x, y, res; {and(x, y)}
      ((y >= 1 | y <= -2) -> and(x, y) = res ->
       \exists int k, l, m, n, subres; (
           and(k, l) = subres &
           x = 2*k + m & y = 2*l + n & m >= 0 & m <= 1 & (
             n = 0 & res = subres * 2
             |
             n = 1 & res = subres * 2 + m
       )))
&

////////////////////////////////////////////////////////////////////////////////
// Modulo

  \forall int x, y, res; {mod(x, y)}
      (mod(x, y) = res & y != 0 ->
       \exists int k; mul(k, y) + res = x &
       0 <= res & (res < y | res < -y))
&

////////////////////////////////////////////////////////////////////////////////
// General multiplication (on the unbounded integers)

  \forall int x; {mul(x, 0)} mul(x, 0) = 0
&
  \forall int x; {mul(x, -1)} mul(x, -1) = -x
&
  \forall int x, y, res; {mul(x, y)}
      ((y >= 1 | y <= -2) -> mul(x, y) = res ->
       \exists int l, n, subres; (
           mul(2*x, l) = subres &
           y = 2*l + n & (
             n = 0 & res = subres
             |
             n = 1 & res = subres + x
       )))
&
  \forall int x, y, res, width; {mulUnsigned(width, x, y)} (
    mulUnsigned(width, x, y) = res ->
    \exists int k; res = mul(x, y) + shiftLeft(k, width) &
    inUnsigned(width, res)
  )
&
  \forall int x, y, res, width; {mulSigned(width, x, y)} (
    mulSigned(width, x, y) = res ->
    \exists int k; res = mul(x, y) + shiftLeft(k, width) &
    inSigned(width, res)
  )
&

////////////////////////////////////////////////////////////////////////////////
// General division (on the unbounded integers)

  \forall int x, y, res; {div(x, y)} (
      y != 0 ->
      \exists int mulres; (
         mul(div(x, y), y) = mulres &
         mulres <= x & (mulres > x + y | mulres > x - y)
      )
  )
&
  \forall int x, y, res, width; {divUnsigned(width, x, y)} (
    divUnsigned(width, x, y) = div(x, y)
  )
&
  \forall int x, y, res, width; {divSigned(width, x, y)} (
    divSigned(width, x, y) = res ->
    \exists int divres; (divres = div(x, y) &
                         (res = divres | res = divres - shiftLeft(1, width))) &
    inSigned(width, res)
  )
&

////////////////////////////////////////////////////////////////////////////////
// Absolute value

  \forall int x; {abs(x)} (x >= 0 -> abs(x) = x)
&
  \forall int x; {abs(x)} (x <  0 -> abs(x) = -x)
&

////////////////////////////////////////////////////////////////////////////////
// Arith-1 Functions
// Equals

  \forall int x, y; {equals(x, y)} (x = y -> equals(x, y) = 1)
&
  \forall int x, y; {equals(x, y)} (x != y -> equals(x, y) = 0)
&

// LessEqual

  \forall int x, y; {lessEqual(x, y)} (x <= y -> lessEqual(x, y) = 1)
&
  \forall int x, y; {lessEqual(x, y)} (x > y -> lessEqual(x, y) = 0)
&

// LessThan

  \forall int x, y; {lessThan(x, y)} (x < y -> lessThan(x, y) = 1)
&
  \forall int x, y; {lessThan(x, y)} (x >= y -> lessThan(x, y) = 0)
&

// BitNegU1

  \forall int x; {bitNegU1(x)} (x = 0 -> bitNegU1(x) = 1)
&
  \forall int x; {bitNegU1(x)} (x != 0 -> bitNegU1(x) = 0)
&

////////////////////////////////////////////////////////////////////////////////
// Typecasts
// Signed to Unsigned
  \forall int x; {signed2unsigned(32, x)} (
    x < 0 -> signed2unsigned(32, x) = x + 4*1024*1024*1024)
&
  \forall int x; {signed2unsigned(32, x)} (
    x >= 0 -> signed2unsigned(32, x) = x)
&
  \forall int width, x; {signed2unsigned(width, x)} (
    x < 0 -> signed2unsigned(width, x) = x + shiftLeft(1, width))
&
  \forall int width, x; {signed2unsigned(width, x)} (
    x >= 0 -> signed2unsigned(width, x) = x)
&

////////////////////////////////////////////////////////////////////////////////
// Pairs

  \forall int x, y; {pair(x, y)} (proj1(pair(x, y)) = x)
&
  \forall int x, y; {pair(x, y)} (proj2(pair(x, y)) = y)
&
  \forall int x, y; {proj1(x), proj2(x)} (pair(proj1(x), proj2(x)) = x)

////////////////////////////////////////////////////////////////////////////////
// Everything is negated (the definitions are premisses)

-> false
}

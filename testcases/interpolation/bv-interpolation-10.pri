/**
 * Example that led to an assertion failure earlier.
 */

\functions {
  bv[8] y3, y4, y5, x5, x4, x3;
}

\problem {
  \part[A] (y5 = y4 + 1 &
            x5 = x4 + y4 &
            x5.\as[signed bv[8]] < 0)
&
  \part[B] (y4 = y3 + 1 &
            x4 = x3 + y3)
&
  \part[C] (y3.\as[signed bv[8]] > -5 & y3.\as[signed bv[8]] < 8 &
            x3 > 20 & x3 < 40)

-> false
}

\interpolant { C; B; A }

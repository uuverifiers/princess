;; This buffer is for notes you don't want to save, and for Lisp evaluation.
;; If you want to create a file, visit that file with C-x C-f,
;; then enter the text in that file's own buffer.

\problem { \part[p0] false -> \part[p1] true }
interpolate.


\functions { int x, y, z; }
\problem { \part[p0] x >= 0 -> \part[p1] y >= x + 1  -> \part[p2] z = y - 5 -> \part[p3] z >= -10}
interpolate.

\functions { int A, B; }
\problem {
  intersection(intersection(A, emptySet), B) = emptySet
}
checkValidity.

\functions { int A, B, C; }
\problem {
  intersection(intersection(A, emptySet), B) = C
}
checkValidity.


\functions { int A, B, C; }
\problem {
  intersection(intersection(A, B), C) = emptySet
}
checkValidity.


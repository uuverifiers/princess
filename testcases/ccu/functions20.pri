\functions {
  int f(int);
  int a, b, c, d, e;
}

\problem {
  (a = d & d = b | a = e & e = b)
->
  f(a) = a
->
  f(b) = c
->
  a = c
}

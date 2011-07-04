\problem {
  \forall int a;
  (\eps int div; (2*div <= a & 2*div >= a - 1)) * 2 +                 // div
  (\eps int mod; (mod >= 0 & mod < 2 & \exists int x; a - mod = 2*x)) // mod
  = a
}
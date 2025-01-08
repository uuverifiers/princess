
\functions {
  bv[53] x;
  bv[11] y;
  bv[12] z;
  bv[106] a;
  bv[53] b;
  bv[11] c;
  bv[106] d;
}

\problem {
9007199254740991 >= x & x >= 0 &
2047 >=  y & y >= 0 &
4095 >= z & z >= 0 & 
	81129638414606681695789005144063 >= a & a >= 0 & 
	a[104:52] = b &  //extract siginificand
	x[52:52] = 1.\as[bv[1]] &  //Normal number in havoc statement
        
	a[105:105] = 0.\as[bv[1]] &  // check if it needs normalization
	a[52:52] = 1 &  // Round bit in rounding

	z[10:0] = c & //extract exponent
	d = a & 
	(2*y -1023).\as[bv[12]] = z & 
	x.\as[int] * x.\as[int] = d

-> false
}
	

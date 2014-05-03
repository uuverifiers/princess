tff(bool, type, bool: $tType).

tff(true, type, true: bool).

tff(false, type, false: bool).

tff(true_False, axiom, ~ (true = false)).

tff(bool_inversion, axiom, ![U:bool]: ((U = true) | (U = false))).

tff(andb, type, andb: (bool * bool) > bool).

tff(andb_def, axiom, ![Y:bool]: ((andb(true, Y) = Y) & (andb(false,
  Y) = false))).

tff(orb, type, orb: (bool * bool) > bool).

tff(orb_def, axiom, ![Y:bool]: ((orb(true, Y) = true) & (orb(false,
  Y) = Y))).

tff(xorb, type, xorb: (bool * bool) > bool).

tff(xorb_def, axiom, ($let_tf(y = true, ((xorb(true, y) = false)
  & (xorb(false, y) = true))) & $let_tf(y = false, ((xorb(true, y) = true)
  & (xorb(false, y) = false))))).

tff(notb, type, notb: bool > bool).

tff(notb_def, axiom, ((notb(true) = false) & (notb(false) = true))).

tff(implb, type, implb: (bool * bool) > bool).

tff(implb_def, axiom, ![X:bool]: ((implb(X, true) = true) & $let_tf(y =
  false, ((implb(true, y) = false) & (implb(false, y) = true))))).


tff(x, type, a: bool).
tff(x, type, b: bool).
tff(x, type, c: bool).

tff(conj, conjecture, andb(a, b) = a | andb(a, b) = b).

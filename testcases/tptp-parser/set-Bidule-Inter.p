tff(uni, type, uni: $tType).

tff(ty, type, ty: $tType).

tff(sort, type, sort: (ty * uni) > $o).

tff(witness, type, witness: ty > uni).

tff(witness_sort, axiom, ![A:ty]: sort(A, witness(A))).

tff(int, type, int: ty).

tff(real, type, real: ty).

tff(map, type, map: (ty * ty) > ty).

tff(get, type, get: (ty * ty * uni * uni) > uni).

tff(get_sort, axiom, ![A:ty, B:ty]: ![X:uni, X1:uni]: sort(B, get(B, A, X,
  X1))).

tff(set, type, set: (ty * ty * uni * uni * uni) > uni).

tff(set_sort, axiom, ![A:ty, B:ty]: ![X:uni, X1:uni, X2:uni]: sort(map(A, B),
  set(B, A, X, X1, X2))).

tff(select_eq, axiom, ![A:ty, B:ty]: ![M:uni]: ![A1:uni, A2:uni]: ![B1:uni]:
  (sort(B, B1) => ((A1 = A2) => (get(B, A, set(B, A, M, A1, B1),
  A2) = B1)))).

tff(select_neq, axiom, ![A:ty, B:ty]: ![M:uni]: ![A1:uni, A2:uni]: (sort(A,
  A1) => (sort(A, A2) => ![B1:uni]: (~ (A1 = A2) => (get(B, A, set(B, A, M,
  A1, B1), A2) = get(B, A, M, A2)))))).

tff(const, type, const: (ty * ty * uni) > uni).

tff(const_sort, axiom, ![A:ty, B:ty]: ![X:uni]: sort(map(A, B), const(B, A,
  X))).

tff(const1, axiom, ![A:ty, B:ty]: ![B1:uni, A1:uni]: (sort(B, B1) => (get(B,
  A, const(B, A, B1), A1) = B1))).

tff(bool, type, bool: $tType).

tff(bool1, type, bool1: ty).

tff(true, type, true: bool).

tff(false, type, false: bool).

tff(match_bool, type, match_bool: (ty * bool * uni * uni) > uni).

tff(match_bool_sort, axiom, ![A:ty]: ![X:bool, X1:uni, X2:uni]: sort(A,
  match_bool(A, X, X1, X2))).

tff(match_bool_True, axiom, ![A:ty]: ![Z:uni, Z1:uni]: (sort(A, Z)
  => (match_bool(A, true, Z, Z1) = Z))).

tff(match_bool_False, axiom, ![A:ty]: ![Z:uni, Z1:uni]: (sort(A, Z1)
  => (match_bool(A, false, Z, Z1) = Z1))).

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

tff(a, type, a: $tType).

tff(a1, type, a1: ty).

tff(mem, type, mem: (ty * uni * uni) > $o).

tff(map_a_bool, type, map_a_bool: $tType).

tff(mem1, type, mem1: (a * map_a_bool) > $o).

tff(t2tb, type, t2tb: map_a_bool > uni).

tff(t2tb_sort, axiom, ![X:map_a_bool]: sort(map(a1, bool1), t2tb(X))).

tff(tb2t, type, tb2t: uni > map_a_bool).

tff(bridgeL, axiom, ![I:map_a_bool]: (tb2t(t2tb(I)) = I)).

tff(bridgeR, axiom, ![J:uni]: (sort(map(a1, bool1), J)
  => (t2tb(tb2t(J)) = J))).

tff(t2tb1, type, t2tb1: bool > uni).

tff(t2tb_sort1, axiom, ![X:bool]: sort(bool1, t2tb1(X))).

tff(tb2t1, type, tb2t1: uni > bool).

tff(bridgeL1, axiom, ![I:bool]: (tb2t1(t2tb1(I)) = I)).

tff(bridgeR1, axiom, ![J:uni]: (sort(bool1, J) => (t2tb1(tb2t1(J)) = J))).

tff(t2tb2, type, t2tb2: a > uni).

tff(t2tb_sort2, axiom, ![X:a]: sort(a1, t2tb2(X))).

tff(tb2t2, type, tb2t2: uni > a).

tff(bridgeL2, axiom, ![I:a]: (tb2t2(t2tb2(I)) = I)).

tff(bridgeR2, axiom, ![J:uni]: (sort(a1, J) => (t2tb2(tb2t2(J)) = J))).

tff(mem_def2, axiom, ![X:a, S:map_a_bool]: (mem1(X, S) <=> (tb2t1(get(bool1,
  a1, t2tb(S), t2tb2(X))) = true))).

tff(mem_def3, axiom, ![A:ty]: ![X:uni, S:uni]: (mem(A, X, S)
  <=> (tb2t1(get(bool1, A, S, X)) = true))).

tff(is_empty, type, is_empty: (ty * uni) > $o).

tff(is_empty_def2, axiom, ![S:map_a_bool]: (is_empty(a1, t2tb(S)) <=> ![X:a]:
  ~ mem1(X, S))).

tff(is_empty_def3, axiom, ![A:ty]: ![S:uni]: ((is_empty(A, S) => ![X:uni]: ~
  mem(A, X, S)) & (![X:uni]: (sort(A, X) => ~ mem(A, X, S)) => is_empty(A,
  S)))).

tff(union, type, union: (ty * uni * uni) > uni).

tff(union_sort, axiom, ![A:ty]: ![X:uni, X1:uni]: sort(map(A, bool1),
  union(A, X, X1))).

tff(union_def2, axiom, ![A:ty]: ![S1:uni, S2:uni]: ![X:uni]:
  (tb2t1(get(bool1, A, union(A, S1, S2), X)) = orb(tb2t1(get(bool1, A, S1,
  X)), tb2t1(get(bool1, A, S2, X))))).

tff(inter, type, inter: (ty * uni * uni) > uni).

tff(inter_sort, axiom, ![A:ty]: ![X:uni, X1:uni]: sort(map(A, bool1),
  inter(A, X, X1))).

tff(inter1, type, inter1: (map_a_bool * map_a_bool) > map_a_bool).

tff(inter_def1, axiom, ![S1:map_a_bool, S2:map_a_bool]: ![X:a]:
  (tb2t1(get(bool1, a1, t2tb(inter1(S1, S2)),
  t2tb2(X))) = andb(tb2t1(get(bool1, a1, t2tb(S1), t2tb2(X))),
  tb2t1(get(bool1, a1, t2tb(S2), t2tb2(X)))))).

tff(inter_def2, axiom, ![A:ty]: ![S1:uni, S2:uni]: ![X:uni]:
  (tb2t1(get(bool1, A, inter(A, S1, S2), X)) = andb(tb2t1(get(bool1, A, S1,
  X)), tb2t1(get(bool1, A, S2, X))))).

tff(diff, type, diff: (ty * uni * uni) > uni).

tff(diff_sort, axiom, ![A:ty]: ![X:uni, X1:uni]: sort(map(A, bool1), diff(A,
  X, X1))).

tff(diff_def1, axiom, ![A:ty]: ![S1:uni, S2:uni]: ![X:uni]: (tb2t1(get(bool1,
  A, diff(A, S1, S2), X)) = andb(tb2t1(get(bool1, A, S1, X)),
  notb(tb2t1(get(bool1, A, S2, X)))))).

tff(equal, type, equal: (ty * uni * uni) > $o).

tff(equal_def, axiom, ![A:ty]: ![S1:uni, S2:uni]: ((equal(A, S1, S2) => ![X:
  uni]: (tb2t1(get(bool1, A, S1, X)) = tb2t1(get(bool1, A, S2, X)))) & (![X:
  uni]: (sort(A, X) => (tb2t1(get(bool1, A, S1, X)) = tb2t1(get(bool1, A, S2,
  X)))) => equal(A, S1, S2)))).

tff(equal_is_eq, axiom, ![A:ty]: ![S1:uni, S2:uni]: (sort(map(A, bool1), S1)
  => (sort(map(A, bool1), S2) => (equal(A, S1, S2) => (S1 = S2))))).

tff(subset, type, subset: (ty * uni * uni) > $o).

tff(subset_def2, axiom, ![S1:map_a_bool, S2:map_a_bool]: (subset(a1,
  t2tb(S1), t2tb(S2)) <=> ![X:a]: (mem1(X, S1) => mem1(X, S2)))).

tff(subset_def3, axiom, ![A:ty]: ![S1:uni, S2:uni]: ((subset(A, S1, S2)
  => ![X:uni]: (mem(A, X, S1) => mem(A, X, S2))) & (![X:uni]: (sort(A, X)
  => (mem(A, X, S1) => mem(A, X, S2))) => subset(A, S1, S2)))).

tff(complement, type, complement: (ty * uni) > uni).

tff(complement_sort, axiom, ![A:ty]: ![X:uni]: sort(map(A, bool1),
  complement(A, X))).

tff(complement_def, axiom, ![A:ty]: ![S:uni]: ![X:uni]: (tb2t1(get(bool1, A,
  complement(A, S), X)) = notb(tb2t1(get(bool1, A, S, X))))).

tff(a2, type, a2: map_a_bool).

tff(b, type, b: map_a_bool).

tff(c, type, c: map_a_bool).

tff(inter2, conjecture, ![S1:map_a_bool, S2:map_a_bool]: ![X:a]: (mem1(X,
  inter1(S1, S2)) => mem1(X, S1))).

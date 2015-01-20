%--------------------------------------------------------------------------
% File     : SET787-1 : TPTP v6.1.0. Released v2.7.0.
% Domain   : Set Theory
% Problem  : un_eq_Union_2_c2
% Version  : Especial.
% English  :

% Refs     : [Men03] Meng (2003), Email to G. Sutcliffe
% Source   : [Men03]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v6.1.0, 0.07 v6.0.0, 0.00 v5.4.0, 0.05 v5.3.0, 0.11 v5.2.0, 0.06 v5.1.0, 0.12 v5.0.0, 0.07 v4.1.0, 0.15 v4.0.1, 0.18 v4.0.0, 0.09 v3.7.0, 0.00 v3.4.0, 0.08 v3.3.0, 0.14 v3.2.0, 0.15 v3.1.0, 0.27 v2.7.0
% Syntax   : Number of clauses     :   14 (   2 non-Horn;   3 unit;  11 RR)
%            Number of atoms       :   26 (   2 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :   15 (   4 constant; 0-2 arity)
%            Number of variables   :   28 (   4 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : Problem coming out of an Isabelle proof.
%--------------------------------------------------------------------------
%----two clauses for UnionE
cnf(clause119,axiom,
    ( ~ member(U,union(V))
    | member(U,unionE_sk1(U,V)) )).

cnf(clause120,axiom,
    ( ~ member(U,union(V))
    | member(unionE_sk1(U,V),V) )).

%----two clauses for subsetI
cnf(clause131,axiom,
    ( member(subsetI_sk1(A,B),A)
    | subset(A,B) )).

cnf(clause132,axiom,
    ( ~ member(subsetI_sk1(A,B),B)
    | subset(A,B) )).

%----consE
cnf(clause112,axiom,
    ( ~ member(U,cons(V,W))
    | U = V
    | member(U,W) )).

%----UnI1
cnf(unI1,axiom,
    ( ~ member(C,A)
    | member(C,un(A,B)) )).

%----UnI2
cnf(unI2,axiom,
    ( ~ member(C,B)
    | member(C,un(A,B)) )).

%----emptyE
cnf(clause158,axiom,
    ( ~ member(X,eptset) )).

%----converseI
cnf(clause10,axiom,
    ( ~ member(pair(U,V),W)
    | member(pair(V,U),converse(W)) )).

%----converseD
cnf(converseD,axiom,
    ( ~ member(pair(A,B),converse(R))
    | member(pair(B,A),R) )).

%----two clauses for converseE
cnf(converseE_1,axiom,
    ( ~ member(YX,converse(R))
    | YX = pair(converseE_sk2(YX),converseE_sk1(YX)) )).

cnf(converseE_2,axiom,
    ( ~ member(YX,converse(R))
    | member(pair(converse_sk1(YX),converse_sk2(YX)),R) )).

%----lemma Un_eq_Union: "A Un B = Union({A, B})"
%Set {A,B} is represented as cons(A,cons(B,0)).
cnf(un_eq_Union_2_c1,negated_conjecture,
    ( member(sk2,union(cons(a,cons(b,eptset)))) )).

cnf(un_eq_Union_2_c2,negated_conjecture,
    ( ~ member(sk2,un(a,b)) )).

%--------------------------------------------------------------------------

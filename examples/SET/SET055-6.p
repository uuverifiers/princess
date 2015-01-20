%--------------------------------------------------------------------------
% File     : SET055-6 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Equality is reflexive
% Version  : [Qua92] axioms.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.11 v6.1.0, 0.00 v5.1.0, 0.09 v5.0.0, 0.29 v4.1.0, 0.12 v4.0.1, 0.20 v4.0.0, 0.14 v3.4.0, 0.25 v3.3.0, 0.00 v3.1.0, 0.17 v2.7.0, 0.00 v2.1.0, 0.12 v2.0.0
% Syntax   : Number of clauses     :  159 (   8 non-Horn;  30 unit;  94 RR)
%            Number of atoms       :  332 (   0 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   39 (   9 constant; 0-3 arity)
%            Number of variables   :  378 (  26 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
%----Don't include von Neuman-Bernays-Godel set theory axioms because
%----equality is incomplete
%include('Axioms/SET004-0.ax').
%--------------------------------------------------------------------------
cnf(symmetry,axiom,
    ( ~ equalish(X,Y)
    | equalish(Y,X) )).

cnf(transitivity,axiom,
    ( ~ equalish(X,Y)
    | ~ equalish(Y,Z)
    | equalish(X,Z) )).

cnf(apply_substitution1,axiom,
    ( ~ equalish(D,E)
    | equalish(apply(D,F),apply(E,F)) )).

cnf(apply_substitution2,axiom,
    ( ~ equalish(G,H)
    | equalish(apply(I,G),apply(I,H)) )).

cnf(cantor_substitution1,axiom,
    ( ~ equalish(J,K)
    | equalish(cantor(J),cantor(K)) )).

cnf(complement_substitution1,axiom,
    ( ~ equalish(L,M)
    | equalish(complement(L),complement(M)) )).

cnf(compose_substitution1,axiom,
    ( ~ equalish(N,O)
    | equalish(compose(N,P),compose(O,P)) )).

cnf(compose_substitution2,axiom,
    ( ~ equalish(Q,R)
    | equalish(compose(S,Q),compose(S,R)) )).

cnf(cross_product_substitution1,axiom,
    ( ~ equalish(T,U)
    | equalish(cross_product(T,V),cross_product(U,V)) )).

cnf(cross_product_substitution2,axiom,
    ( ~ equalish(W,X)
    | equalish(cross_product(Y,W),cross_product(Y,X)) )).

cnf(diagonalise_substitution1,axiom,
    ( ~ equalish(Z,A1)
    | equalish(diagonalise(Z),diagonalise(A1)) )).

cnf(symmetric_difference_substitution1,axiom,
    ( ~ equalish(B1,C1)
    | equalish(symmetric_difference(B1,D1),symmetric_difference(C1,D1)) )).

cnf(symmetric_difference_substitution2,axiom,
    ( ~ equalish(E1,F1)
    | equalish(symmetric_difference(G1,E1),symmetric_difference(G1,F1)) )).

cnf(domain_substitution1,axiom,
    ( ~ equalish(H1,I1)
    | equalish(domain(H1,J1,K1),domain(I1,J1,K1)) )).

cnf(domain_substitution2,axiom,
    ( ~ equalish(L1,M1)
    | equalish(domain(N1,L1,O1),domain(N1,M1,O1)) )).

cnf(domain_substitution3,axiom,
    ( ~ equalish(P1,Q1)
    | equalish(domain(R1,S1,P1),domain(R1,S1,Q1)) )).

cnf(domain_of_substitution1,axiom,
    ( ~ equalish(T1,U1)
    | equalish(domain_of(T1),domain_of(U1)) )).

cnf(first_substitution1,axiom,
    ( ~ equalish(V1,W1)
    | equalish(first(V1),first(W1)) )).

cnf(flip_substitution1,axiom,
    ( ~ equalish(X1,Y1)
    | equalish(flip(X1),flip(Y1)) )).

cnf(image_substitution1,axiom,
    ( ~ equalish(Z1,A2)
    | equalish(image(Z1,B2),image(A2,B2)) )).

cnf(image_substitution2,axiom,
    ( ~ equalish(C2,D2)
    | equalish(image(E2,C2),image(E2,D2)) )).

cnf(intersection_substitution1,axiom,
    ( ~ equalish(F2,G2)
    | equalish(intersection(F2,H2),intersection(G2,H2)) )).

cnf(intersection_substitution2,axiom,
    ( ~ equalish(I2,J2)
    | equalish(intersection(K2,I2),intersection(K2,J2)) )).

cnf(inverse_substitution1,axiom,
    ( ~ equalish(L2,M2)
    | equalish(inverse(L2),inverse(M2)) )).

cnf(not_homomorphism1_substitution1,axiom,
    ( ~ equalish(N2,O2)
    | equalish(not_homomorphism1(N2,P2,Q2),not_homomorphism1(O2,P2,Q2)) )).

cnf(not_homomorphism1_substitution2,axiom,
    ( ~ equalish(R2,S2)
    | equalish(not_homomorphism1(T2,R2,U2),not_homomorphism1(T2,S2,U2)) )).

cnf(not_homomorphism1_substitution3,axiom,
    ( ~ equalish(V2,W2)
    | equalish(not_homomorphism1(X2,Y2,V2),not_homomorphism1(X2,Y2,W2)) )).

cnf(not_homomorphism2_substitution1,axiom,
    ( ~ equalish(Z2,A3)
    | equalish(not_homomorphism2(Z2,B3,C3),not_homomorphism2(A3,B3,C3)) )).

cnf(not_homomorphism2_substitution2,axiom,
    ( ~ equalish(D3,E3)
    | equalish(not_homomorphism2(F3,D3,G3),not_homomorphism2(F3,E3,G3)) )).

cnf(not_homomorphism2_substitution3,axiom,
    ( ~ equalish(H3,I3)
    | equalish(not_homomorphism2(J3,K3,H3),not_homomorphism2(J3,K3,I3)) )).

cnf(not_subclass_element_substitution1,axiom,
    ( ~ equalish(L3,M3)
    | equalish(not_subclass_element(L3,N3),not_subclass_element(M3,N3)) )).

cnf(not_subclass_element_substitution2,axiom,
    ( ~ equalish(O3,P3)
    | equalish(not_subclass_element(Q3,O3),not_subclass_element(Q3,P3)) )).

cnf(ordered_pair_substitution1,axiom,
    ( ~ equalish(R3,S3)
    | equalish(ordered_pair(R3,T3),ordered_pair(S3,T3)) )).

cnf(ordered_pair_substitution2,axiom,
    ( ~ equalish(U3,V3)
    | equalish(ordered_pair(W3,U3),ordered_pair(W3,V3)) )).

cnf(power_class_substitution1,axiom,
    ( ~ equalish(X3,Y3)
    | equalish(power_class(X3),power_class(Y3)) )).

cnf(range_substitution1,axiom,
    ( ~ equalish(Z3,A4)
    | equalish(range(Z3,B4,C4),range(A4,B4,C4)) )).

cnf(range_substitution2,axiom,
    ( ~ equalish(D4,E4)
    | equalish(range(F4,D4,G4),range(F4,E4,G4)) )).

cnf(range_substitution3,axiom,
    ( ~ equalish(H4,I4)
    | equalish(range(J4,K4,H4),range(J4,K4,I4)) )).

cnf(range_of_substitution1,axiom,
    ( ~ equalish(L4,M4)
    | equalish(range_of(L4),range_of(M4)) )).

cnf(regular_substitution1,axiom,
    ( ~ equalish(N4,O4)
    | equalish(regular(N4),regular(O4)) )).

cnf(restrict_substitution1,axiom,
    ( ~ equalish(P4,Q4)
    | equalish(restrict(P4,R4,S4),restrict(Q4,R4,S4)) )).

cnf(restrict_substitution2,axiom,
    ( ~ equalish(T4,U4)
    | equalish(restrict(V4,T4,W4),restrict(V4,U4,W4)) )).

cnf(restrict_substitution3,axiom,
    ( ~ equalish(X4,Y4)
    | equalish(restrict(Z4,A5,X4),restrict(Z4,A5,Y4)) )).

cnf(rotate_substitution1,axiom,
    ( ~ equalish(B5,C5)
    | equalish(rotate(B5),rotate(C5)) )).

cnf(second_substitution1,axiom,
    ( ~ equalish(D5,E5)
    | equalish(second(D5),second(E5)) )).

cnf(singleton_substitution1,axiom,
    ( ~ equalish(F5,G5)
    | equalish(singleton(F5),singleton(G5)) )).

cnf(successor_substitution1,axiom,
    ( ~ equalish(H5,I5)
    | equalish(successor(H5),successor(I5)) )).

cnf(sum_class_substitution1,axiom,
    ( ~ equalish(J5,K5)
    | equalish(sum_class(J5),sum_class(K5)) )).

cnf(union_substitution1,axiom,
    ( ~ equalish(L5,M5)
    | equalish(union(L5,N5),union(M5,N5)) )).

cnf(union_substitution2,axiom,
    ( ~ equalish(O5,P5)
    | equalish(union(Q5,O5),union(Q5,P5)) )).

cnf(unordered_pair_substitution1,axiom,
    ( ~ equalish(R5,S5)
    | equalish(unordered_pair(R5,T5),unordered_pair(S5,T5)) )).

cnf(unordered_pair_substitution2,axiom,
    ( ~ equalish(U5,V5)
    | equalish(unordered_pair(W5,U5),unordered_pair(W5,V5)) )).

cnf(compatible_substitution1,axiom,
    ( ~ equalish(X5,Y5)
    | ~ compatible(X5,Z5,A6)
    | compatible(Y5,Z5,A6) )).

cnf(compatible_substitution2,axiom,
    ( ~ equalish(B6,C6)
    | ~ compatible(D6,B6,E6)
    | compatible(D6,C6,E6) )).

cnf(compatible_substitution3,axiom,
    ( ~ equalish(F6,G6)
    | ~ compatible(H6,I6,F6)
    | compatible(H6,I6,G6) )).

cnf(function_substitution1,axiom,
    ( ~ equalish(J6,K6)
    | ~ function(J6)
    | function(K6) )).

cnf(homomorphism_substitution1,axiom,
    ( ~ equalish(L6,M6)
    | ~ homomorphism(L6,N6,O6)
    | homomorphism(M6,N6,O6) )).

cnf(homomorphism_substitution2,axiom,
    ( ~ equalish(P6,Q6)
    | ~ homomorphism(R6,P6,S6)
    | homomorphism(R6,Q6,S6) )).

cnf(homomorphism_substitution3,axiom,
    ( ~ equalish(T6,U6)
    | ~ homomorphism(V6,W6,T6)
    | homomorphism(V6,W6,U6) )).

cnf(inductive_substitution1,axiom,
    ( ~ equalish(X6,Y6)
    | ~ inductive(X6)
    | inductive(Y6) )).

cnf(member_substitution1,axiom,
    ( ~ equalish(Z6,A7)
    | ~ member(Z6,B7)
    | member(A7,B7) )).

cnf(member_substitution2,axiom,
    ( ~ equalish(C7,D7)
    | ~ member(E7,C7)
    | member(E7,D7) )).

cnf(one_to_one_substitution1,axiom,
    ( ~ equalish(F7,G7)
    | ~ one_to_one(F7)
    | one_to_one(G7) )).

cnf(operation_substitution1,axiom,
    ( ~ equalish(H7,I7)
    | ~ operation(H7)
    | operation(I7) )).

cnf(single_valued_class_substitution1,axiom,
    ( ~ equalish(J7,K7)
    | ~ single_valued_class(J7)
    | single_valued_class(K7) )).

cnf(subclass_substitution1,axiom,
    ( ~ equalish(L7,M7)
    | ~ subclass(L7,N7)
    | subclass(M7,N7) )).

cnf(subclass_substitution2,axiom,
    ( ~ equalish(O7,P7)
    | ~ subclass(Q7,O7)
    | subclass(Q7,P7) )).

%----GROUP 1:          AXIOMS AND BASIC DEFINITIONS.

%----Axiom A-1:  sets are classes (omitted because all objects are
%----classes).

%----Definition of < (subclass).
%----a:x:a:y:((x < y) <=> a:u:((u e x) ==> (u e y))).
cnf(subclass_members,axiom,
    ( ~ subclass(X,Y)
    | ~ member(U,X)
    | member(U,Y) )).

cnf(not_subclass_members1,axiom,
    ( member(not_subclass_element(X,Y),X)
    | subclass(X,Y) )).

cnf(not_subclass_members2,axiom,
    ( ~ member(not_subclass_element(X,Y),Y)
    | subclass(X,Y) )).

%----Axiom A-2: elements of classes are sets.
%----a:x:(x < universal_class).
cnf(class_elements_are_sets,axiom,
    ( subclass(X,universal_class) )).

%----Axiom A-3: principle of extensionality.
%----a:x:a:y:((x = y) <=> (x < y) & (y < x)).
cnf(equal_implies_subclass1,axiom,
    ( ~ equalish(X,Y)
    | subclass(X,Y) )).

cnf(equal_implies_subclass2,axiom,
    ( ~ equalish(X,Y)
    | subclass(Y,X) )).

cnf(subclass_implies_equal,axiom,
    ( ~ subclass(X,Y)
    | ~ subclass(Y,X)
    | equalish(X,Y) )).

%----Axiom A-4: existence of unordered pair.
%----a:u:a:x:a:y:((u e {x, y}) <=> (u e universal_class)
%----& (u = x | u = y)).
%----a:x:a:y:({x, y} e universal_class).
cnf(unordered_pair_member,axiom,
    ( ~ member(U,unordered_pair(X,Y))
    | equalish(U,X)
    | equalish(U,Y) )).

%----(x e universal_class), (u = x) --> (u e {x, y}).
cnf(unordered_pair2,axiom,
    ( ~ member(X,universal_class)
    | member(X,unordered_pair(X,Y)) )).

%----(y e universal_class), (u = y) --> (u e {x, y}).
cnf(unordered_pair3,axiom,
    ( ~ member(Y,universal_class)
    | member(Y,unordered_pair(X,Y)) )).

cnf(unordered_pairs_in_universal,axiom,
    ( member(unordered_pair(X,Y),universal_class) )).

%----Definition of singleton set.
%----a:x:({x} = {x, x}).
cnf(singleton_set,axiom,
    ( equalish(unordered_pair(X,X),singleton(X)) )).

%----See Theorem (SS6) for memb.

%----Definition of ordered pair.
%----a:x:a:y:([x,y] = {{x}, {x, {y}}}).
cnf(ordered_pair,axiom,
    ( equalish(unordered_pair(singleton(X),unordered_pair(X,singleton(Y))),ordered_pair(X,Y)) )).

%----Axiom B-5'a: Cartesian product.
%----a:u:a:v:a:y:(([u,v] e cross_product(x,y)) <=> (u e x) & (v e y)).
cnf(cartesian_product1,axiom,
    ( ~ member(ordered_pair(U,V),cross_product(X,Y))
    | member(U,X) )).

cnf(cartesian_product2,axiom,
    ( ~ member(ordered_pair(U,V),cross_product(X,Y))
    | member(V,Y) )).

cnf(cartesian_product3,axiom,
    ( ~ member(U,X)
    | ~ member(V,Y)
    | member(ordered_pair(U,V),cross_product(X,Y)) )).

%----See Theorem (OP6) for 1st and 2nd.

%----Axiom B-5'b: Cartesian product.
%----a:z:(z e cross_product(x,y) --> ([first(z),second(z)] = z)
cnf(cartesian_product4,axiom,
    ( ~ member(Z,cross_product(X,Y))
    | equalish(ordered_pair(first(Z),second(Z)),Z) )).

%----Axiom B-1: E (element relation).
%----(E < cross_product(universal_class,universal_class)).
%----a:x:a:y:(([x,y] e E) <=> ([x,y] e cross_product(universal_class,
%----universal_class)) (x e y)).
cnf(element_relation1,axiom,
    ( subclass(element_relation,cross_product(universal_class,universal_class)) )).

cnf(element_relation2,axiom,
    ( ~ member(ordered_pair(X,Y),element_relation)
    | member(X,Y) )).

cnf(element_relation3,axiom,
    ( ~ member(ordered_pair(X,Y),cross_product(universal_class,universal_class))
    | ~ member(X,Y)
    | member(ordered_pair(X,Y),element_relation) )).

%----Axiom B-2: * (intersection).
%----a:z:a:x:a:y:((z e (x * y)) <=> (z e x) & (z e y)).
cnf(intersection1,axiom,
    ( ~ member(Z,intersection(X,Y))
    | member(Z,X) )).

cnf(intersection2,axiom,
    ( ~ member(Z,intersection(X,Y))
    | member(Z,Y) )).

cnf(intersection3,axiom,
    ( ~ member(Z,X)
    | ~ member(Z,Y)
    | member(Z,intersection(X,Y)) )).

%----Axiom B-3: complement.
%----a:z:a:x:((z e ~(x)) <=> (z e universal_class) & -(z e x)).
cnf(complement1,axiom,
    ( ~ member(Z,complement(X))
    | ~ member(Z,X) )).

cnf(complement2,axiom,
    ( ~ member(Z,universal_class)
    | member(Z,complement(X))
    | member(Z,X) )).

%---- Theorem (SP2) introduces the null class O.

%----Definition of + (union).
%----a:x:a:y:((x + y) = ~((~(x) * ~(y)))).
cnf(union,axiom,
    ( equalish(complement(intersection(complement(X),complement(Y))),union(X,Y)) )).

%----Definition of & (exclusive or). (= symmetric_difference).
%----a:x:a:y:((x y) = (~(x * y) * ~(~(x) * ~(y)))).
cnf(symmetric_difference,axiom,
    ( equalish(intersection(complement(intersection(X,Y)),complement(intersection(complement(X),complement(Y)))),symmetric_difference(X,Y)) )).

%----Definition of restriction.
%----a:x(restrict(xr,x,y) = (xr * cross_product(x,y))).
%----This is extra to the paper
cnf(restriction1,axiom,
    ( equalish(intersection(Xr,cross_product(X,Y)),restrict(Xr,X,Y)) )).

cnf(restriction2,axiom,
    ( equalish(intersection(cross_product(X,Y),Xr),restrict(Xr,X,Y)) )).

%----Axiom B-4: D (domain_of).
%----a:y:a:z:((z e domain_of(x)) <=> (z e universal_class) &
%---- -(restrict(x,{z},universal_class) = O)).
%----next is subsumed by A-2.
%------> (domain_of(x) < universal_class).
cnf(domain1,axiom,
    ( ~ equalish(restrict(X,singleton(Z),universal_class),null_class)
    | ~ member(Z,domain_of(X)) )).

cnf(domain2,axiom,
    ( ~ member(Z,universal_class)
    | equalish(restrict(X,singleton(Z),universal_class),null_class)
    | member(Z,domain_of(X)) )).

%----Axiom B-7: rotate.
%----a:x:(rotate(x) <  cross_product(cross_product(universal_class,
%----universal_class),universal_class)).
%----a:x:a:u:a:v:a:w:(([[u,v],w] e rotate(x)) <=> ([[u,v],w]]
%---- e cross_product(cross_product(universal_class,universal_class),
%----universal_class)) & ([[v,w],u]] e x).
cnf(rotate1,axiom,
    ( subclass(rotate(X),cross_product(cross_product(universal_class,universal_class),universal_class)) )).

cnf(rotate2,axiom,
    ( ~ member(ordered_pair(ordered_pair(U,V),W),rotate(X))
    | member(ordered_pair(ordered_pair(V,W),U),X) )).

cnf(rotate3,axiom,
    ( ~ member(ordered_pair(ordered_pair(V,W),U),X)
    | ~ member(ordered_pair(ordered_pair(U,V),W),cross_product(cross_product(universal_class,universal_class),universal_class))
    | member(ordered_pair(ordered_pair(U,V),W),rotate(X)) )).

%----Axiom B-8: flip.
%----a:x:(flip(x) <  cross_product(cross_product(universal_class,
%----universal_class),universal_class)).
%----a:z:a:u:a:v:a:w:(([[u,v],w] e flip(x)) <=> ([[u,v],w]
%----e cross_product(cross_product(universal_class,universal_class),
%----universal_class)) & ([[v,u],w] e x).
cnf(flip1,axiom,
    ( subclass(flip(X),cross_product(cross_product(universal_class,universal_class),universal_class)) )).

cnf(flip2,axiom,
    ( ~ member(ordered_pair(ordered_pair(U,V),W),flip(X))
    | member(ordered_pair(ordered_pair(V,U),W),X) )).

cnf(flip3,axiom,
    ( ~ member(ordered_pair(ordered_pair(V,U),W),X)
    | ~ member(ordered_pair(ordered_pair(U,V),W),cross_product(cross_product(universal_class,universal_class),universal_class))
    | member(ordered_pair(ordered_pair(U,V),W),flip(X)) )).

%----Definition of inverse.
%----a:y:(inverse(y) = domain_of(flip(cross_product(y,V)))).
cnf(inverse,axiom,
    ( equalish(domain_of(flip(cross_product(Y,universal_class))),inverse(Y)) )).

%----Definition of R (range_of).
%----a:z:(range_of(z) = domain_of(inverse(z))).
cnf(range_of,axiom,
    ( equalish(domain_of(inverse(Z)),range_of(Z)) )).

%----Definition of domain.
%----a:z:a:x:a:y:(domain(z,x,y) = first(notsub(restrict(z,x,{y}),O))).
cnf(domain,axiom,
    ( equalish(first(not_subclass_element(restrict(Z,X,singleton(Y)),null_class)),domain(Z,X,Y)) )).

%----Definition of range.
%----a:z:a:x:(range(z,x,y) = second(notsub(restrict(z,{x},y),O))).
cnf(range,axiom,
    ( equalish(second(not_subclass_element(restrict(Z,singleton(X),Y),null_class)),range(Z,X,Y)) )).

%----Definition of image.
%----a:x:a:xr:((xr image x) = range_of(restrict(xr,x,V))).
cnf(image,axiom,
    ( equalish(range_of(restrict(Xr,X,universal_class)),image(Xr,X)) )).

%----Definition of successor.
%----a:x:(successor(x) = (x + {x})).
cnf(successor,axiom,
    ( equalish(union(X,singleton(X)),successor(X)) )).

%----Explicit definition of successor_relation.
%------> ((cross_product(V,V) * ~(((E ^ ~(inverse((E + I)))) +
%----(~(E) ^ inverse((E + I)))))) = successor_relation).
%----Definition of successor_relation from the Class Existence Theorem.
%----a:x:a:y:([x,y] e successor_relation <=> x e V & successor(x) = y).
%----The above FOF does not agree with the book
cnf(successor_relation1,axiom,
    ( subclass(successor_relation,cross_product(universal_class,universal_class)) )).

cnf(successor_relation2,axiom,
    ( ~ member(ordered_pair(X,Y),successor_relation)
    | equalish(successor(X),Y) )).

%----This is what's in the book and paper. Does not change axiom.
% input_clause(successor_relation3,axiom,
%     [--equalish(successor(X),Y),
%      --member(X,universal_class),
%      ++member(ordered_pair(X,Y),successor_relation)]).

%----This is what I got by email from Quaife
cnf(successor_relation3,axiom,
    ( ~ equalish(successor(X),Y)
    | ~ member(ordered_pair(X,Y),cross_product(universal_class,universal_class))
    | member(ordered_pair(X,Y),successor_relation) )).

%----Definition of inductive a:x:(inductive(x) <=> null_class
%----e x & (successor_relation image x) < x)).
cnf(inductive1,axiom,
    ( ~ inductive(X)
    | member(null_class,X) )).

cnf(inductive2,axiom,
    ( ~ inductive(X)
    | subclass(image(successor_relation,X),X) )).

cnf(inductive3,axiom,
    ( ~ member(null_class,X)
    | ~ subclass(image(successor_relation,X),X)
    | inductive(X) )).

%----Axiom C-1: infinity.
%----e:x:((x e V) & inductive(x) & a:y:(inductive(y) ==> (x < y))).
%----e:x:((x e V) & (O e x) & ((successor_relation image x) < x)
%----        & a:y:((O e y) & ((successor_relation image y) < y) ==>
%----(x < y))).
cnf(omega_is_inductive1,axiom,
    ( inductive(omega) )).

cnf(omega_is_inductive2,axiom,
    ( ~ inductive(Y)
    | subclass(omega,Y) )).

cnf(omega_in_universal,axiom,
    ( member(omega,universal_class) )).

%----These were commented out in the set Quaife sent me, and are not
%----in the paper true --> (null_class e omega).
%----true --> ((successor_relation image omega) < omega).
%----(null_class e y), ((successor_relation image y) < y) -->
%----(omega < y). true --> (omega e universal_class).

%----Definition of U (sum class).
%----a:x:(sum_class(x) = domain_of(restrict(E,V,x))).
cnf(sum_class_definition,axiom,
    ( equalish(domain_of(restrict(element_relation,universal_class,X)),sum_class(X)) )).

%----Axiom C-2: U (sum class).
%----a:x:((x e V) ==> (sum_class(x) e V)).
cnf(sum_class2,axiom,
    ( ~ member(X,universal_class)
    | member(sum_class(X),universal_class) )).

%----Definition of P (power class).
%----a:x:(power_class(x) = ~((E image ~(x)))).
cnf(power_class_definition,axiom,
    ( equalish(complement(image(element_relation,complement(X))),power_class(X)) )).

%----Axiom C-3: P (power class).
%----a:u:((u e V) ==> (power_class(u) e V)).
cnf(power_class2,axiom,
    ( ~ member(U,universal_class)
    | member(power_class(U),universal_class) )).

%----Definition of compose.
%----a:xr:a:yr:((yr ^ xr) < cross_product(V,V)).
%----a:u:a:v:a:xr:a:yr:(([u,v] e (yr ^ xr)) <=> ([u,v]
%----e cross_product(V,V)) & (v e (yr image (xr image {u})))).
cnf(compose1,axiom,
    ( subclass(compose(Yr,Xr),cross_product(universal_class,universal_class)) )).

cnf(compose2,axiom,
    ( ~ member(ordered_pair(Y,Z),compose(Yr,Xr))
    | member(Z,image(Yr,image(Xr,singleton(Y)))) )).

cnf(compose3,axiom,
    ( ~ member(Z,image(Yr,image(Xr,singleton(Y))))
    | ~ member(ordered_pair(Y,Z),cross_product(universal_class,universal_class))
    | member(ordered_pair(Y,Z),compose(Yr,Xr)) )).

%----7/21/90 eliminate SINGVAL and just use FUNCTION.
%----Not eliminated in TPTP - I'm following the paper
cnf(single_valued_class1,axiom,
    ( ~ single_valued_class(X)
    | subclass(compose(X,inverse(X)),identity_relation) )).

cnf(single_valued_class2,axiom,
    ( ~ subclass(compose(X,inverse(X)),identity_relation)
    | single_valued_class(X) )).

%----Definition of function.
%----a:xf:(function(xf) <=> (xf < cross_product(V,V)) & ((xf
%----^ inverse(xf)) < identity_relation)).
cnf(function1,axiom,
    ( ~ function(Xf)
    | subclass(Xf,cross_product(universal_class,universal_class)) )).

cnf(function2,axiom,
    ( ~ function(Xf)
    | subclass(compose(Xf,inverse(Xf)),identity_relation) )).

cnf(function3,axiom,
    ( ~ subclass(Xf,cross_product(universal_class,universal_class))
    | ~ subclass(compose(Xf,inverse(Xf)),identity_relation)
    | function(Xf) )).

%----Axiom C-4: replacement.
%----a:x:((x e V) & function(xf) ==> ((xf image x) e V)).
cnf(replacement,axiom,
    ( ~ function(Xf)
    | ~ member(X,universal_class)
    | member(image(Xf,X),universal_class) )).

%----Axiom D: regularity.
%----a:x:(-(x = O) ==> e:u:((u e V) & (u e x) & ((u * x) = O))).
cnf(regularity1,axiom,
    ( equalish(X,null_class)
    | member(regular(X),X) )).

cnf(regularity2,axiom,
    ( equalish(X,null_class)
    | equalish(intersection(X,regular(X)),null_class) )).

%----Definition of apply (apply).
%----a:xf:a:y:((xf apply y) = sum_class((xf image {y}))).
cnf(apply,axiom,
    ( equalish(sum_class(image(Xf,singleton(Y))),apply(Xf,Y)) )).

%----Axiom E: universal choice.
%----e:xf:(function(xf) & a:y:((y e V) ==> (y = null_class) |
%----((xf apply y) e y))).
cnf(choice1,axiom,
    ( function(choice) )).

cnf(choice2,axiom,
    ( ~ member(Y,universal_class)
    | equalish(Y,null_class)
    | member(apply(choice,Y),Y) )).

%----GROUP 2:             MORE SET THEORY DEFINITIONS.

%----Definition of one_to_one (one-to-one function).
%----a:xf:(one_to_one(xf) <=> function(xf) & function(inverse(xf))).
cnf(one_to_one1,axiom,
    ( ~ one_to_one(Xf)
    | function(Xf) )).

cnf(one_to_one2,axiom,
    ( ~ one_to_one(Xf)
    | function(inverse(Xf)) )).

cnf(one_to_one3,axiom,
    ( ~ function(inverse(Xf))
    | ~ function(Xf)
    | one_to_one(Xf) )).

%----Definition of S (subset relation).
cnf(subset_relation,axiom,
    ( equalish(intersection(cross_product(universal_class,universal_class),intersection(cross_product(universal_class,universal_class),complement(compose(complement(element_relation),inverse(element_relation))))),subset_relation) )).

%----Definition of I (identity relation).
cnf(identity_relation,axiom,
    ( equalish(intersection(inverse(subset_relation),subset_relation),identity_relation) )).

%----Definition of diagonalization.
%----a:xr:(diagonalise(xr) = ~(domain_of((identity_relation * xr)))).
cnf(diagonalisation,axiom,
    ( equalish(complement(domain_of(intersection(Xr,identity_relation))),diagonalise(Xr)) )).

%----Definition of Cantor class.
cnf(cantor_class,axiom,
    ( equalish(intersection(domain_of(X),diagonalise(compose(inverse(element_relation),X))),cantor(X)) )).

%----Definition of operation.
%----a:xf:(operation(xf) <=> function(xf) & (cross_product(domain_of(
%----domain_of(xf)),domain_of(domain_of(xf))) = domain_of(xf))
%----& (range_of(xf) < domain_of(domain_of(xf))).
cnf(operation1,axiom,
    ( ~ operation(Xf)
    | function(Xf) )).

cnf(operation2,axiom,
    ( ~ operation(Xf)
    | equalish(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf)) )).

cnf(operation3,axiom,
    ( ~ operation(Xf)
    | subclass(range_of(Xf),domain_of(domain_of(Xf))) )).

cnf(operation4,axiom,
    ( ~ function(Xf)
    | ~ equalish(cross_product(domain_of(domain_of(Xf)),domain_of(domain_of(Xf))),domain_of(Xf))
    | ~ subclass(range_of(Xf),domain_of(domain_of(Xf)))
    | operation(Xf) )).

%----Definition of compatible.
%----a:xh:a:xf1:a:af2: (compatible(xh,xf1,xf2) <=> function(xh)
%----& (domain_of(domain_of(xf1)) = domain_of(xh)) & (range_of(xh)
%----< domain_of(domain_of(xf2)))).
cnf(compatible1,axiom,
    ( ~ compatible(Xh,Xf1,Xf2)
    | function(Xh) )).

cnf(compatible2,axiom,
    ( ~ compatible(Xh,Xf1,Xf2)
    | equalish(domain_of(domain_of(Xf1)),domain_of(Xh)) )).

cnf(compatible3,axiom,
    ( ~ compatible(Xh,Xf1,Xf2)
    | subclass(range_of(Xh),domain_of(domain_of(Xf2))) )).

cnf(compatible4,axiom,
    ( ~ function(Xh)
    | ~ equalish(domain_of(domain_of(Xf1)),domain_of(Xh))
    | ~ subclass(range_of(Xh),domain_of(domain_of(Xf2)))
    | compatible(Xh1,Xf1,Xf2) )).

%----Definition of homomorphism.
%----a:xh:a:xf1:a:xf2: (homomorphism(xh,xf1,xf2) <=>
%---- operation(xf1) & operation(xf2) & compatible(xh,xf1,xf2) &
%---- a:x:a:y:(([x,y] e domain_of(xf1)) ==> (((xf2 apply [(xh apply x),
%----(xh apply y)]) = (xh apply (xf1 apply [x,y])))).
cnf(homomorphism1,axiom,
    ( ~ homomorphism(Xh,Xf1,Xf2)
    | operation(Xf1) )).

cnf(homomorphism2,axiom,
    ( ~ homomorphism(Xh,Xf1,Xf2)
    | operation(Xf2) )).

cnf(homomorphism3,axiom,
    ( ~ homomorphism(Xh,Xf1,Xf2)
    | compatible(Xh,Xf1,Xf2) )).

cnf(homomorphism4,axiom,
    ( ~ homomorphism(Xh,Xf1,Xf2)
    | ~ member(ordered_pair(X,Y),domain_of(Xf1))
    | equalish(apply(Xf2,ordered_pair(apply(Xh,X),apply(Xh,Y))),apply(Xh,apply(Xf1,ordered_pair(X,Y)))) )).

cnf(homomorphism5,axiom,
    ( ~ operation(Xf1)
    | ~ operation(Xf2)
    | ~ compatible(Xh,Xf1,Xf2)
    | member(ordered_pair(not_homomorphism1(Xh,Xf1,Xf2),not_homomorphism2(Xh,Xf1,Xf2)),domain_of(Xf1))
    | homomorphism(Xh,Xf1,Xf2) )).

cnf(homomorphism6,axiom,
    ( ~ operation(Xf1)
    | ~ operation(Xf2)
    | ~ compatible(Xh,Xf1,Xf2)
    | ~ equalish(apply(Xf2,ordered_pair(apply(Xh,not_homomorphism1(Xh,Xf1,Xf2)),apply(Xh,not_homomorphism2(Xh,Xf1,Xf2)))),apply(Xh,apply(Xf1,ordered_pair(not_homomorphism1(Xh,Xf1,Xf2),not_homomorphism2(Xh,Xf1,Xf2)))))
    | homomorphism(Xh,Xf1,Xf2) )).

cnf(prove_reflexivity,negated_conjecture,
    ( ~ equalish(x,x) )).

%--------------------------------------------------------------------------

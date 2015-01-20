%--------------------------------------------------------------------------
% File     : SET787-2 : TPTP v6.1.0. Released v2.7.0.
% Domain   : Set Theory
% Problem  : un_eq_Union_2_c2
% Version  : Especial.
% English  :

% Refs     : [Men03] Meng (2003), Email to G. Sutcliffe
% Source   : [Men03]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.50 v6.1.0, 0.64 v6.0.0, 0.70 v5.5.0, 0.90 v5.4.0, 0.85 v5.3.0, 0.83 v5.2.0, 0.88 v5.0.0, 0.86 v4.1.0, 0.85 v4.0.1, 0.73 v4.0.0, 0.55 v3.7.0, 0.40 v3.5.0, 0.45 v3.4.0, 0.50 v3.3.0, 0.64 v3.2.0, 0.69 v3.1.0, 0.73 v2.7.0
% Syntax   : Number of clauses     :  149 (  21 non-Horn;  22 unit; 118 RR)
%            Number of atoms       :  308 (  64 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    9 (   0 propositional; 1-8 arity)
%            Number of functors    :   61 (   5 constant; 0-4 arity)
%            Number of variables   :  450 ( 149 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : Full axiomatization where many axioms are not needed for a
%            solution.
%--------------------------------------------------------------------------
%----A General Axiom Set, it has most of the classical rules found from
%----.thy (after Main.thy). It has been used for Equalities.
%----This file contains direct subset relation axioms.

%----consI1
cnf(clause1,axiom,
    ( member(U,cons(U,V)) )).

%----consI2
cnf(clause2,axiom,
    ( ~ member(U,V)
    | member(U,cons(W,V)) )).

%----nat_succI
cnf(clause3,axiom,
    ( ~ member(U,nat)
    | member(succ(U),nat) )).

%----Inr_iff (direction:Inr(?a) = Inr(?b) <- ?a = ?b)
cnf(clause4,axiom,
    ( U != V
    | inr(U) = inr(V) )).

%----Inl_iff (direction:Inl(?a) = Inl(?b) <-> ?a = ?b)
cnf(clause5,axiom,
    ( U != V
    | inl(U) = inl(V) )).

%----InlI (disjsum is "+")
cnf(clause6,axiom,
    ( ~ member(U,V)
    | member(inl(U),disjsum(V,W)) )).

%----InrI (disjsum is "+")
cnf(clause7,axiom,
    ( ~ member(U,V)
    | member(inr(U),disjsum(W,V)) )).

%----singleton_eq_iff (direction: {?a} = {?b} <- ?a = ?b
cnf(clause11,axiom,
    ( U != V
    | cons(U,eptset) = cons(V,eptset) )).

%----two clauses for succCI
cnf(clause12,axiom,
    ( ~ member(U,V)
    | member(U,succ(V)) )).

cnf(clause13,axiom,
    ( U != V
    | member(U,succ(V)) )).

%----singletonI
cnf(clause14,axiom,
    ( member(U,cons(U,eptset)) )).

%----two clauses for consCI
cnf(clause15,axiom,
    ( ~ member(U,V)
    | member(U,cons(W,V)) )).

cnf(clause16,axiom,
    ( U != V
    | member(U,cons(V,W)) )).

%----DiffI
cnf(clause17,axiom,
    ( ~ member(U,V)
    | member(U,W)
    | member(U,diff(V,W)) )).

%----IntI
cnf(clause18,axiom,
    ( ~ member(U,V)
    | ~ member(U,W)
    | member(U,int(V,W)) )).

%----two clauses for UnCI
cnf(clause19,axiom,
    ( ~ member(U,V)
    | member(U,un(W,V)) )).

cnf(clause20,axiom,
    ( ~ member(U,V)
    | member(U,un(V,W)) )).

%----two clauses for PowI
cnf(clause21,axiom,
    ( member(powI_sk1(U,V),U)
    | member(U,pow(V)) )).

cnf(clause22,axiom,
    ( ~ member(powI_sk1(U,V),V)
    | member(U,pow(V)) )).

%----two clauses for InterI
cnf(clause23,axiom,
    ( ~ member(U,V)
    | member(interI_sk1(W,V),V)
    | member(W,inter(V)) )).

cnf(clause24,axiom,
    ( ~ member(U,interI_sk1(U,V))
    | ~ member(W,V)
    | member(U,inter(V)) )).

%----intro:
%----two clauses for Card_Union
cnf(clause25,axiom,
    ( member(card_Union_sk1(U),U)
    | card(union(U)) )).

cnf(clause26,axiom,
    ( ~ card(card_Union_sk1(U))
    | card(union(U)) )).

%----Fin_IntI1 (fin is Fin in Isabelle)
cnf(clause27,axiom,
    ( ~ member(U,fin(V))
    | member(int(U,W),fin(V)) )).

%----Fin_IntI2
cnf(clause28,axiom,
    ( ~ member(U,fin(V))
    | member(int(W,U),fin(V)) )).

%----two clauses for Ord_Inter
cnf(clause29,axiom,
    ( member(order_Inter_sk1(U),U)
    | ord(inter(U)) )).

cnf(clause30,axiom,
    ( ~ ord(order_Inter_sk1(U))
    | ord(inter(U)) )).

%----two axioms for Ord_Union
cnf(clause31,axiom,
    ( member(order_Union_sk1(U),U)
    | ord(union(U)) )).

cnf(clause32,axiom,
    ( ~ ord(order_Union_sk1(U))
    | ord(union(U)) )).

%----Ord_Un
cnf(clause33,axiom,
    ( ~ ord(U)
    | ~ ord(V)
    | ord(un(U,V)) )).

%----compI (comp is "O")
cnf(clause34,axiom,
    ( ~ member(pair(U,V),W)
    | ~ member(pair(V,X),Y)
    | member(pair(U,X),comp(Y,W)) )).

%----vimageI (vimage is "-``")
cnf(clause35,axiom,
    ( ~ member(pair(U,V),W)
    | ~ member(V,X)
    | member(U,vimage(W,X)) )).

%----imageI (image is "``")
cnf(clause36,axiom,
    ( ~ member(pair(U,V),W)
    | ~ member(U,X)
    | member(V,image(W,X)) )).

%----elim!
%----QInr_QInl_iff
cnf(clause37,axiom,
    (  qInr(U) != qInl(V) )).

%----QInl_QInr_iff
cnf(clause38,axiom,
    (  qInl(U) != qInr(V) )).

%----QInr_inject
cnf(clause39,axiom,
    ( qInr(U) != qInr(V)
    | U = V )).

%----QInl_inject
cnf(clause40,axiom,
    ( qInl(U) != qInl(V)
    | U = V )).

%----four clauses for axiom qsumE (qsum is "<+>")
cnf(clause41,axiom,
    ( ~ member(U,qsum(V,W))
    | member(qsumE_sk1(U,V,W),V)
    | member(qsumE_sk2(U,V,W),W) )).

cnf(clause42,axiom,
    ( ~ member(U,qsum(V,W))
    | member(qsumE_sk1(U,V,W),V)
    | U = qInr(qsumE_sk2(U,V,W)) )).

cnf(clause43,axiom,
    ( ~ member(U,qsum(V,W))
    | U = qInl(qsumE_sk1(U,V,W))
    | member(qsumE_sk2(U,V,W),W) )).

cnf(clause44,axiom,
    ( ~ member(U,qsum(V,W))
    | U = qInl(qsumE_sk1(U,V,W))
    | U = qInr(qsumE_sk2(U,V,W)) )).

%----two clauses for qconverseE (qPair is "<-; ->")
cnf(clause45,axiom,
    ( ~ member(U,qconverse(V))
    | U = qPair(qconverseE_sk2(U,V),qconverseE_sk1(U,V)) )).

cnf(clause46,axiom,
    ( ~ member(U,qconverse(V))
    | member(qPair(qconverseE_sk1(U,V),qconverseE_sk2(U,V)),V) )).

%----qconverseD
cnf(clause47,axiom,
    ( ~ member(qPair(U,V),qconverse(W))
    | member(qPair(V,U),W) )).

%----QPair_inject1
cnf(clause48,axiom,
    ( qPair(U,V) != qPair(W,X)
    | U = W )).

%----QPair_inject2
cnf(clause49,axiom,
    ( qPair(U,V) != qPair(W,X)
    | V = X )).

%----succ_natD
cnf(clause50,axiom,
    ( ~ member(succ(U),nat)
    | member(U,nat) )).

%----11 clauses for rmultE
cnf(clause51,axiom,
    ( ~ member(pair(pair(U,V),pair(W,X)),rmult(Y,Z,X1,X2))
    | rmultE_c1(U,V,W,X,Y,Z,X1,X2)
    | rmultE_c2(U,V,W,X,Y,Z,X1,X2) )).

cnf(clause52,axiom,
    ( ~ rmultE_c1(U,V,W,X,Y,Z,X1,X2)
    | member(pair(U,W),Z) )).

cnf(clause53,axiom,
    ( ~ rmultE_c1(U,V,W,X,Y,Z,X1,X2)
    | member(U,Y) )).

cnf(clause54,axiom,
    ( ~ rmultE_c1(U,V,W,X,Y,Z,X1,X2)
    | member(W,Y) )).

cnf(clause55,axiom,
    ( ~ rmultE_c1(U,V,W,X,Y,Z,X1,X2)
    | member(V,X1) )).

cnf(clause56,axiom,
    ( ~ rmultE_c1(U,V,W,X,Y,Z,X1,X2)
    | member(X,X1) )).

cnf(clause57,axiom,
    ( ~ rmultE_c2(U,V,W,X,Y,Z,X1,X2)
    | member(pair(V,X),X2) )).

cnf(clause58,axiom,
    ( ~ rmultE_c2(U,V,W,X,Y,Z,X1,X2)
    | member(W,Y) )).

cnf(clause59,axiom,
    ( ~ rmultE_c2(U,V,W,X,Y,Z,X1,X2)
    | U = W )).

cnf(clause60,axiom,
    ( ~ rmultE_c2(U,V,W,X,Y,Z,X1,X2)
    | member(V,X1) )).

cnf(clause61,axiom,
    ( ~ rmultE_c2(U,V,W,X,Y,Z,X1,X2)
    | member(X,X1) )).

%----radd_Inr_Inl_iff
cnf(clause62,axiom,
    ( ~ member(pair(inr(U),inl(V)),radd(W,X,Y,Z)) )).

%----three clauses for radd_Inr_iff (direction: LHS->RHS)
cnf(clause63,axiom,
    ( ~ member(pair(inr(U),inr(V)),radd(W,X,Y,Z))
    | member(U,Y) )).

cnf(clause64,axiom,
    ( ~ member(pair(inr(U),inr(V)),radd(W,X,Y,Z))
    | member(V,Y) )).

cnf(clause65,axiom,
    ( ~ member(pair(inr(U),inr(V)),radd(W,X,Y,Z))
    | member(pair(U,V),Z) )).

%----three clauses for radd_Inl_iff (direction: LHS->RHS)
cnf(clause66,axiom,
    ( ~ member(pair(inl(U),inl(V)),radd(W,X,Y,Z))
    | member(U,W) )).

cnf(clause67,axiom,
    ( ~ member(pair(inl(U),inl(V)),radd(W,X,Y,Z))
    | member(V,W) )).

cnf(clause68,axiom,
    ( ~ member(pair(inl(U),inl(V)),radd(W,X,Y,Z))
    | member(pair(U,V),X) )).

%----two clauses for radd_Inl_Inr_iff (direction: lHS->RHS)
cnf(clause69,axiom,
    ( ~ member(pair(inl(U),inr(V)),radd(W,X,Y,Z))
    | member(U,W) )).

cnf(clause70,axiom,
    ( ~ member(pair(inl(U),inr(V)),radd(W,X,Y,Z))
    | member(V,Y) )).

%----succ_leE (le is "<=", lt is "<")
cnf(clause71,axiom,
    ( ~ le(succ(U),V)
    | lt(U,V) )).

%----zero_le_succ_iff (direction: LHS->RHS),(zero is represented as eptset here)
cnf(clause72,axiom,
    ( ~ le(eptset,succ(U))
    | ord(U) )).

%----three clauses for MemrelE
cnf(clause73,axiom,
    ( ~ member(pair(U,V),memrel(W))
    | member(U,W) )).

cnf(clause74,axiom,
    ( ~ member(pair(U,V),memrel(W))
    | member(V,W) )).

cnf(clause75,axiom,
    ( ~ member(pair(U,V),memrel(W))
    | member(U,V) )).

%----le0D (zero is represented as eptset)
cnf(clause76,axiom,
    ( ~ le(U,eptset)
    | U = eptset )).

%----le_refl_iff (direction: LHS->RHS)
cnf(clause77,axiom,
    ( ~ le(U,U)
    | ord(U) )).

%----Ord_succ_iff (direction: LHS->RHS)
cnf(clause78,axiom,
    ( ~ ord(succ(U))
    | ord(U) )).

%----three clauses for compE
cnf(clause79,axiom,
    ( ~ member(U,comp(V,W))
    | U = pair(compE_sk1(U,V,W),compE_sk3(U,V,W)) )).

cnf(clause80,axiom,
    ( ~ member(U,comp(V,W))
    | member(pair(compE_sk1(U,V,W),compE_sk2(U,V,W)),W) )).

cnf(clause81,axiom,
    ( ~ member(U,comp(V,W))
    | member(pair(compE_sk2(U,V,W),compE_sk3(U,V,W)),V) )).

%----two clauses for idE
cnf(clause82,axiom,
    ( ~ member(U,id(V))
    | member(idE_sk1(U,V),V) )).

cnf(clause83,axiom,
    ( ~ member(U,id(V))
    | U = pair(idE_sk1(U,V),idE_sk1(U,V)) )).

%----Inr_Inl_iff
cnf(clause84,axiom,
    (  inr(U) != inl(V) )).

%----Inl_Inr_iff
cnf(clause85,axiom,
    (  inl(U) != inr(V) )).

%----Inr_iff (direction: LHS->RHS)
cnf(clause86,axiom,
    ( inr(U) != inr(V)
    | U = V )).

%----Inl_iff
cnf(clause87,axiom,
    ( inl(U) != inl(V)
    | U = V )).

%----four clauses for sumE (disjsum is "+")
cnf(clause88,axiom,
    ( ~ member(U,disjsum(V,W))
    | member(sumE_sk1(U,V,W),V)
    | member(sumE_sk2(U,V,W),W) )).

cnf(clause89,axiom,
    ( ~ member(U,disjsum(V,W))
    | member(sumE_sk1(U,V,W),V)
    | U = inr(sumE_sk2(U,V,W)) )).

cnf(clause90,axiom,
    ( ~ member(U,disjsum(V,W))
    | U = inl(sumE_sk1(U,V,W))
    | member(sumE_sk2(U,V,W),W) )).

cnf(clause91,axiom,
    ( ~ member(U,disjsum(V,W))
    | U = inl(sumE_sk1(U,V,W))
    | U = inr(sumE_sk2(U,V,W)) )).

%----Pair_inject1
cnf(clause106,axiom,
    ( pair(U,V) != pair(W,X)
    | U = W )).

%----Pair_inject2
cnf(clause107,axiom,
    ( pair(U,V) != pair(W,X)
    | V = X )).

%----singleton_eq_iff (direction: LHS->RHS)
cnf(clause108,axiom,
    ( cons(U,eptset) != cons(V,eptset)
    | U = V )).

%----succ_inject
cnf(clause109,axiom,
    ( succ(U) != succ(V)
    | U = V )).

%----succE
cnf(clause110,axiom,
    ( ~ member(U,succ(V))
    | U = V
    | member(U,V) )).

%----singletonE
cnf(clause111,axiom,
    ( ~ member(U,cons(V,eptset))
    | U = V )).

%----consE
cnf(clause112,axiom,
    ( ~ member(U,cons(V,W))
    | U = V
    | member(U,W) )).

%----DiffD1
cnf(clause113,axiom,
    ( ~ member(U,diff(V,W))
    | member(U,V) )).

%----DiffD2
cnf(clause114,axiom,
    ( ~ member(U,diff(V,W))
    | ~ member(U,W) )).

%----IntD1
cnf(clause115,axiom,
    ( ~ member(U,int(V,W))
    | member(U,V) )).

%----IntD2
cnf(clause116,axiom,
    ( ~ member(U,int(V,W))
    | member(U,W) )).

%----UnE
cnf(clause117,axiom,
    ( ~ member(U,un(V,W))
    | member(U,V)
    | member(U,W) )).

%----PowD
cnf(clause118,axiom,
    ( ~ member(U,pow(V))
    | ~ member(W,U)
    | member(W,V) )).

%----two clauses for UnionE
cnf(clause119,axiom,
    ( ~ member(U,union(V))
    | member(U,unionE_sk1(U,V)) )).

cnf(clause120,axiom,
    ( ~ member(U,union(V))
    | member(unionE_sk1(U,V),V) )).

%----elim
%----equals0D
cnf(clause121,axiom,
    ( U != eptset
    | ~ member(V,U) )).

%----InterD
cnf(clause122,axiom,
    ( ~ member(U,inter(V))
    | ~ member(W,V)
    | member(U,W) )).

%----two clauses for subsetD
%----subset relation is represented by membership relation
cnf(clause123,axiom,
    ( ~ member(U,V)
    | member(subsetD_sk1(V,W,U),V)
    | member(U,W) )).

cnf(clause124,axiom,
    ( ~ member(subsetD_sk1(U,V,W),V)
    | ~ member(W,U)
    | member(W,V) )).

%----another version of subsetD
cnf(subsetD,axiom,
    ( ~ subset(A,B)
    | ~ member(C,A)
    | member(C,B) )).

%----two clauses for fieldCI
cnf(clause125,axiom,
    ( ~ member(pair(C,A),R)
    | member(A,field(R)) )).

cnf(clause126,axiom,
    ( ~ member(pair(A,B),R)
    | member(A,field(R)) )).

%----Pair_neq_0
cnf(clause127,axiom,
    (  pair(A,B) != eptset )).

%----Pair_neq_fst
cnf(clause128,axiom,
    (  pair(A,B) != A )).

%----Pair_neq_snd
cnf(clause129,axiom,
    (  pair(A,B) != B )).

%----Pair_iff (RHS-->LHS)
cnf(clause130,axiom,
    ( A != C
    | B != D
    | pair(A,B) = pair(C,D) )).

%----ABOUT SUBSET RELATION.
%----two clauses for subsetI
cnf(clause131,axiom,
    ( member(subsetI_sk1(A,B),A)
    | subset(A,B) )).

cnf(clause132,axiom,
    ( ~ member(subsetI_sk1(A,B),B)
    | subset(A,B) )).

%----subset_refl
cnf(clause133,axiom,
    ( subset(A,A) )).

%----subset_trans
cnf(clause134,axiom,
    ( ~ subset(A,B)
    | ~ subset(B,C)
    | subset(A,C) )).

%----empty_subsetI
cnf(clause135,axiom,
    ( ~ member(X,eptset)
    | member(X,A) )).

%----another version of empty_subsetI
cnf(clause136,axiom,
    ( subset(eptset,A) )).

%----subsetD
cnf(clause137,axiom,
    ( ~ subset(A,B)
    | ~ member(C,A)
    | member(C,B) )).

%----UpairI1
cnf(clause138,axiom,
    ( member(A,upair(A,B)) )).

%----UpairI2
cnf(clause139,axiom,
    ( member(B,upair(A,B)) )).

%----UpairE
cnf(clause140,axiom,
    ( ~ member(A,upair(B,C))
    | A = B
    | A = C )).

%----succI1
cnf(clause141,axiom,
    ( member(I,succ(I)) )).

%----succI2
cnf(clause142,axiom,
    ( ~ member(I,J)
    | member(I,succ(J)) )).

%----UnionI
cnf(clause143,axiom,
    ( ~ member(B,C)
    | ~ member(A,B)
    | member(A,union(C)) )).

%----some new axioms
%----new version of SigmaE, three clauses.
%----as we should have B(x), but B is a var, so use apply(B,x) instead.
cnf(clause144,axiom,
    ( ~ member(C,sigma(A,B))
    | member(sigmaE_sk1x(A,B,C),A) )).

cnf(clause145,axiom,
    ( ~ member(C,sigma(A,B))
    | member(sigmaE_sk1y(A,B,C),apply(B,sigmaE_sk1x(A,B,C))) )).

cnf(clause147,axiom,
    ( ~ member(C,sigma(A,B))
    | C = pair(sigmaE_sk1x(A,B,C),sigmaE_sk1y(A,B,C)) )).

%----equalityI
cnf(clause148,axiom,
    ( ~ subset(A,B)
    | ~ subset(B,A)
    | A = B )).

%----equalityD1
cnf(clause149,axiom,
    ( A != B
    | subset(A,B) )).

%----equalityD2
cnf(clause150,axiom,
    ( A != B
    | subset(B,A) )).

%----Pow_bottom
cnf(clause151,axiom,
    ( member(eptset,pow(B)) )).

%----Pow_top
cnf(clause152,axiom,
    ( member(A,pow(A)) )).

%----SigmaI
%----NOTE: not ordinary translation.
cnf(clause153,axiom,
    ( ~ member(V_a,A)
    | ~ member(V_b,apply(B,V_a))
    | member(pair(V_a,V_b),sigma(A,B)) )).

%----fst_type
cnf(clause154,axiom,
    ( ~ member(P,sigma(A,B))
    | member(fst(P),A) )).

%----snd_type
cnf(clause155,axiom,
    ( ~ member(P,sigma(A,B))
    | member(snd(P),apply(B,fst(P))) )).

%----fst_conv
cnf(clause156,axiom,
    ( fst(pair(A,B)) = A )).

%----snd_conv
cnf(clause157,axiom,
    ( snd(pair(A,B)) = B )).

%----emptyE
cnf(clause158,axiom,
    ( ~ member(X,eptset) )).

%----UnI1
cnf(unI1,axiom,
    ( ~ member(C,A)
    | member(C,un(A,B)) )).

%----UnI2
cnf(unI2,axiom,
    ( ~ member(C,B)
    | member(C,un(A,B)) )).

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

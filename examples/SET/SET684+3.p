%------------------------------------------------------------------------------
% File     : SET684+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Relations)
% Problem  : <x,z> in P(DtoE) o R(EtoF) iff ?y in E:<x,y> in P & <y,z> in R
% Version  : [Wor90] axioms : Reduced > Incomplete.
% English  : Let P be a relation from D to E, R a relation from E to F, x an
%            element of D, and z in F. Then <x,z> is in P composed with R if
%            and only if there exists an element y in E such that <x,y> is in
%            P and <y,z> is in R.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Wor90] Woronowicz (1990), Relations Defined on Sets
% Source   : [ILF]
% Names    : RELSET_1 (51) [Wor90]

% Status   : Theorem
% Rating   : 0.64 v6.1.0, 0.77 v6.0.0, 0.65 v5.5.0, 0.78 v5.4.0, 0.75 v5.3.0, 0.74 v5.2.0, 0.65 v5.1.0, 0.62 v5.0.0, 0.67 v4.1.0, 0.65 v4.0.1, 0.70 v4.0.0, 0.71 v3.7.0, 0.70 v3.5.0, 0.74 v3.3.0, 0.64 v3.1.0, 0.78 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 1.00 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   30 (   2 unit)
%            Number of atoms       :  134 (   9 equality)
%            Maximal formula depth :   19 (   7 average)
%            Number of connectives :  111 (   7 ~  ;   0  |;  16  &)
%                                         (  11 <=>;  77 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :   12 (   2 constant; 0-5 arity)
%            Number of variables   :   82 (   0 singleton;  74 !;   8 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%---- line(relat_1 - th(43),1918466)
fof(p1,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,binary_relation_type)
               => ! [E] :
                    ( ilf_type(E,binary_relation_type)
                   => ( member(ordered_pair(B,C),compose(D,E))
                    <=> ? [F] :
                          ( ilf_type(F,set_type)
                          & member(ordered_pair(B,F),D)
                          & member(ordered_pair(F,C),E) ) ) ) ) ) ) )).

%---- line(relset_1 - th(7),1916125)
fof(p2,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,set_type)
                   => ! [F] :
                        ( ilf_type(F,relation_type(B,C))
                       => ( member(ordered_pair(D,E),F)
                         => ( member(D,B)
                            & member(E,C) ) ) ) ) ) ) ) )).

%---- line(tarski - df(5),1832760)
fof(p3,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,set_type)
                   => ! [F] :
                        ( ilf_type(F,set_type)
                       => ( F = ordered_pair(D,E)
                        <=> F = unordered_pair(unordered_pair(D,E),singleton(D)) ) ) ) ) ) ) )).

%---- declaration(line(tarski - df(5),1832760))
fof(p4,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(ordered_pair(B,C),set_type) ) ) )).

%---- line(relset_1 - df(1),1916080)
fof(p5,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ! [D] :
                  ( ilf_type(D,subset_type(cross_product(B,C)))
                 => ilf_type(D,relation_type(B,C)) )
              & ! [E] :
                  ( ilf_type(E,relation_type(B,C))
                 => ilf_type(E,subset_type(cross_product(B,C))) ) ) ) ) )).

%---- type_nonempty(line(relset_1 - df(1),1916080))
fof(p6,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ? [D] : ilf_type(D,relation_type(C,B)) ) ) )).

%---- line(hidden - axiom671,1832640)
fof(p7,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ( ~ empty(C)
              & ilf_type(C,set_type) )
           => ( ilf_type(B,member_type(C))
            <=> member(B,C) ) ) ) )).

%---- type_nonempty(line(hidden - axiom671,1832640))
fof(p8,axiom,
    ( ! [B] :
        ( ( ~ empty(B)
          & ilf_type(B,set_type) )
       => ? [C] : ilf_type(C,member_type(B)) ) )).

%---- line(hidden - axiom673,1832628)
fof(p9,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( empty(B)
        <=> ! [C] :
              ( ilf_type(C,set_type)
             => ~ member(C,B) ) ) ) )).

%---- declaration(op(singleton,1,function))
fof(p10,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ilf_type(singleton(B),set_type) ) )).

%---- declaration(op(cross_product,2,function))
fof(p11,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(cross_product(B,C),set_type) ) ) )).

%---- declaration(op(unordered_pair,2,function))
fof(p12,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(unordered_pair(B,C),set_type) ) ) )).

%---- property(commutativity,op(unordered_pair,2,function))
fof(p13,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => unordered_pair(B,C) = unordered_pair(C,B) ) ) )).

%---- declaration(op(compose,2,function))
fof(p14,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ! [C] :
            ( ilf_type(C,binary_relation_type)
           => ilf_type(compose(B,C),binary_relation_type) ) ) )).

%---- line(relat_1 - axiom674,1917641)
fof(p15,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ilf_type(B,binary_relation_type)
        <=> ( relation_like(B)
            & ilf_type(B,set_type) ) ) ) )).

%---- type_nonempty(line(relat_1 - axiom674,1917641))
fof(p16,axiom,
    ( ? [B] : ilf_type(B,binary_relation_type) )).

%---- line(hidden - axiom675,1832648)
fof(p17,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ilf_type(C,subset_type(B))
            <=> ilf_type(C,member_type(power_set(B))) ) ) ) )).

%---- type_nonempty(line(hidden - axiom675,1832648))
fof(p18,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ? [C] : ilf_type(C,subset_type(B)) ) )).

%---- line(hidden - axiom676,1832615)
fof(p19,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( B = C
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                  <=> member(D,C) ) ) ) ) ) )).

%---- property(symmetry,op(=,2,predicate))
fof(p20,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ! [C] :
            ( ilf_type(C,binary_relation_type)
           => ( B = C
             => C = B ) ) ) )).

%---- property(reflexivity,op(=,2,predicate))
fof(p21,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => B = B ) )).

%---- line(hidden - axiom678,1832644)
fof(p22,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( member(B,power_set(C))
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                   => member(D,C) ) ) ) ) ) )).

%---- declaration(line(hidden - axiom678,1832644))
fof(p23,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ~ empty(power_set(B))
          & ilf_type(power_set(B),set_type) ) ) )).

%---- line(relat_1 - df(1),1917627)
fof(p24,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( relation_like(B)
        <=> ! [C] :
              ( ilf_type(C,set_type)
             => ( member(C,B)
               => ? [D] :
                    ( ilf_type(D,set_type)
                    & ? [E] :
                        ( ilf_type(E,set_type)
                        & C = ordered_pair(D,E) ) ) ) ) ) ) )).

%---- conditional_cluster(axiom679,relation_like)
fof(p25,axiom,
    ( ! [B] :
        ( ( empty(B)
          & ilf_type(B,set_type) )
       => relation_like(B) ) )).

%---- conditional_cluster(axiom680,relation_like)
fof(p26,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,subset_type(cross_product(B,C)))
               => relation_like(D) ) ) ) )).

%---- line(relset_1 - axiom687,1916444)
fof(p27,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,relation_type(B,C))
                   => ! [F] :
                        ( ilf_type(F,relation_type(C,D))
                       => compose5(B,C,D,E,F) = compose(E,F) ) ) ) ) ) )).

%---- declaration(line(relset_1 - axiom687,1916444))
fof(p28,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,relation_type(B,C))
                   => ! [F] :
                        ( ilf_type(F,relation_type(C,D))
                       => ilf_type(compose5(B,C,D,E,F),relation_type(B,D)) ) ) ) ) ) )).

%---- declaration(set)
fof(p29,axiom,
    ( ! [B] : ilf_type(B,set_type) )).

%---- line(relset_1 - th(51),1916968)
fof(prove_relset_1_51,conjecture,
    ( ! [B] :
        ( ( ~ empty(B)
          & ilf_type(B,set_type) )
       => ! [C] :
            ( ( ~ empty(C)
              & ilf_type(C,set_type) )
           => ! [D] :
                ( ( ~ empty(D)
                  & ilf_type(D,set_type) )
               => ! [E] :
                    ( ilf_type(E,relation_type(B,C))
                   => ! [F] :
                        ( ilf_type(F,relation_type(C,D))
                       => ! [G] :
                            ( ilf_type(G,member_type(B))
                           => ! [H] :
                                ( ilf_type(H,member_type(D))
                               => ( member(ordered_pair(G,H),compose5(B,C,D,E,F))
                                <=> ? [I] :
                                      ( ilf_type(I,member_type(C))
                                      & member(ordered_pair(G,I),E)
                                      & member(ordered_pair(I,H),F) ) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

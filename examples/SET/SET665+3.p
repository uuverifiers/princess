%--------------------------------------------------------------------------
% File     : SET665+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Relations)
% Problem  : The identity relation on X is a subset of X x X
% Version  : [Wor90] axioms : Reduced > Incomplete.
% English  :

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Wor90] Woronowicz (1990), Relations Defined on Sets
% Source   : [ILF]
% Names    : RELSET_1 (28) [Wor90]

% Status   : Theorem
% Rating   : 0.56 v6.1.0, 0.63 v6.0.0, 0.57 v5.5.0, 0.74 v5.4.0, 0.75 v5.3.0, 0.81 v5.2.0, 0.65 v5.1.0, 0.67 v5.0.0, 0.71 v4.1.0, 0.65 v4.0.1, 0.70 v4.0.0, 0.62 v3.7.0, 0.70 v3.5.0, 0.63 v3.4.0, 0.58 v3.3.0, 0.57 v3.2.0, 0.64 v3.1.0, 0.67 v2.6.0, 0.86 v2.5.0, 0.75 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   28 (   2 unit)
%            Number of atoms       :  114 (   4 equality)
%            Maximal formula depth :   14 (   6 average)
%            Number of connectives :   90 (   4 ~  ;   0  |;  15  &)
%                                         (  12 <=>;  59 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :    9 (   2 constant; 0-2 arity)
%            Number of variables   :   64 (   0 singleton;  56 !;   8 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(relat_1 - df(3),1917829)
fof(p1,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ! [C] :
            ( ilf_type(C,binary_relation_type)
           => ( subset(B,C)
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ! [E] :
                      ( ilf_type(E,set_type)
                     => ( member(ordered_pair(D,E),B)
                       => member(ordered_pair(D,E),C) ) ) ) ) ) ) )).

%---- line(relat_1 - th(69),1918879)
fof(p2,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ( member(ordered_pair(C,D),identity_relation_of(B))
                <=> ( member(C,B)
                    & C = D ) ) ) ) ) )).

%---- line(zfmisc_1 - th(106),1905180)
fof(p3,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,set_type)
                   => ( member(ordered_pair(B,C),cross_product(D,E))
                    <=> ( member(B,D)
                        & member(C,E) ) ) ) ) ) ) )).

%---- line(relset_1 - th(5),1916109)
fof(p4,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(cross_product(B,C),relation_type(B,C)) ) ) )).

%---- line(zfmisc_1 - df(1),1903822)
fof(p5,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ( member(D,cross_product(B,C))
                <=> ? [E] :
                      ( ilf_type(E,set_type)
                      & ? [F] :
                          ( ilf_type(F,set_type)
                          & member(E,B)
                          & member(F,C)
                          & D = ordered_pair(E,F) ) ) ) ) ) ) )).

%---- declaration(line(zfmisc_1 - df(1),1903822))
fof(p6,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(cross_product(B,C),set_type) ) ) )).

%---- line(relat_1 - df(10),1918876)
fof(p7,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ( member(ordered_pair(C,D),identity_relation_of(B))
                <=> ( member(C,B)
                    & C = D ) ) ) ) ) )).

%---- declaration(line(relat_1 - df(10),1918876))
fof(p8,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ilf_type(identity_relation_of(B),binary_relation_type) ) )).

%---- line(tarski - df(3),1832749)
fof(p9,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( subset(B,C)
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                   => member(D,C) ) ) ) ) ) )).

%---- declaration(op(ordered_pair,2,function))
fof(p10,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(ordered_pair(B,C),set_type) ) ) )).

%---- line(relat_1 - axiom283,1917641)
fof(p11,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ilf_type(B,binary_relation_type)
        <=> ( relation_like(B)
            & ilf_type(B,set_type) ) ) ) )).

%---- type_nonempty(line(relat_1 - axiom283,1917641))
fof(p12,axiom,
    ( ? [B] : ilf_type(B,binary_relation_type) )).

%---- line(relset_1 - df(1),1916080)
fof(p13,axiom,
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
fof(p14,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ? [D] : ilf_type(D,relation_type(C,B)) ) ) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(p15,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => subset(B,B) ) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(p16,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => subset(B,B) ) )).

%---- line(hidden - axiom285,1832648)
fof(p17,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ilf_type(C,subset_type(B))
            <=> ilf_type(C,member_type(power_set(B))) ) ) ) )).

%---- type_nonempty(line(hidden - axiom285,1832648))
fof(p18,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ? [C] : ilf_type(C,subset_type(B)) ) )).

%---- line(relat_1 - df(1),1917627)
fof(p19,axiom,
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

%---- conditional_cluster(axiom287,relation_like)
fof(p20,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,subset_type(cross_product(B,C)))
               => relation_like(D) ) ) ) )).

%---- line(hidden - axiom288,1832644)
fof(p21,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( member(B,power_set(C))
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                   => member(D,C) ) ) ) ) ) )).

%---- declaration(line(hidden - axiom288,1832644))
fof(p22,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ~ empty(power_set(B))
          & ilf_type(power_set(B),set_type) ) ) )).

%---- line(hidden - axiom289,1832640)
fof(p23,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ( ~ empty(C)
              & ilf_type(C,set_type) )
           => ( ilf_type(B,member_type(C))
            <=> member(B,C) ) ) ) )).

%---- type_nonempty(line(hidden - axiom289,1832640))
fof(p24,axiom,
    ( ! [B] :
        ( ( ~ empty(B)
          & ilf_type(B,set_type) )
       => ? [C] : ilf_type(C,member_type(B)) ) )).

%---- line(hidden - axiom290,1832628)
fof(p25,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( empty(B)
        <=> ! [C] :
              ( ilf_type(C,set_type)
             => ~ member(C,B) ) ) ) )).

%---- conditional_cluster(axiom291,empty)
fof(p26,axiom,
    ( ! [B] :
        ( ( empty(B)
          & ilf_type(B,set_type) )
       => relation_like(B) ) )).

%---- declaration(set)
fof(p27,axiom,
    ( ! [B] : ilf_type(B,set_type) )).

%---- line(relset_1 - th(28),1916537)
fof(prove_relset_1_28,conjecture,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => subset(identity_relation_of(B),cross_product(B,B)) ) )).

%--------------------------------------------------------------------------

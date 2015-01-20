%--------------------------------------------------------------------------
% File     : SET668+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Relations)
% Problem  : Id on X subset of R  => X is domain R & X subset of range R
% Version  : [Wor90] axioms : Reduced > Incomplete.
% English  : If the identity relation on X is a subset of a relation R from
%            X to Y then X is the domain of R and X is a subset of the range
%            of R.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Wor90] Woronowicz (1990), Relations Defined on Sets
% Source   : [ILF]
% Names    : RELSET_1 (31) [Wor90]

% Status   : Theorem
% Rating   : 0.44 v6.1.0, 0.50 v6.0.0, 0.57 v5.5.0, 0.59 v5.4.0, 0.61 v5.3.0, 0.59 v5.2.0, 0.50 v5.1.0, 0.48 v5.0.0, 0.50 v4.1.0, 0.57 v4.0.0, 0.54 v3.7.0, 0.55 v3.5.0, 0.53 v3.4.0, 0.37 v3.3.0, 0.36 v3.2.0, 0.27 v3.1.0, 0.22 v2.7.0, 0.17 v2.6.0, 0.14 v2.5.0, 0.12 v2.4.0, 0.25 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :   33 (   2 unit)
%            Number of atoms       :  130 (   7 equality)
%            Maximal formula depth :   11 (   6 average)
%            Number of connectives :  101 (   4 ~  ;   0  |;  13  &)
%                                         (  10 <=>;  74 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   13 (   2 constant; 0-3 arity)
%            Number of variables   :   74 (   0 singleton;  68 !;   6 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - th(28),1909410)
fof(p1,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ( subset(B,C)
                & subset(C,B) )
             => B = C ) ) ) )).

%---- line(relset_1 - th(30),1916572)
fof(p2,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,relation_type(B,C))
                   => ( subset(identity_relation_of(D),E)
                     => ( subset(D,domain(B,C,E))
                        & subset(D,range(B,C,E)) ) ) ) ) ) ) )).

%---- line(relat_1 - df(10),1918876)
fof(p3,axiom,
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
fof(p4,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ilf_type(identity_relation_of(B),binary_relation_type) ) )).

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

%---- line(tarski - df(3),1832749)
fof(p7,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( subset(B,C)
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                   => member(D,C) ) ) ) ) ) )).

%---- line(relat_1 - df(3),1917829)
fof(p8,axiom,
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

%---- line(boole - df(8),1909359)
fof(p9,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( B = C
            <=> ( subset(B,C)
                & subset(C,B) ) ) ) ) )).

%---- declaration(op(domain_of,1,function))
fof(p10,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ilf_type(domain_of(B),set_type) ) )).

%---- declaration(op(cross_product,2,function))
fof(p11,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(cross_product(B,C),set_type) ) ) )).

%---- declaration(op(range_of,1,function))
fof(p12,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ilf_type(range_of(B),set_type) ) )).

%---- declaration(op(ordered_pair,2,function))
fof(p13,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(ordered_pair(B,C),set_type) ) ) )).

%---- line(relat_1 - axiom336,1917641)
fof(p14,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ilf_type(B,binary_relation_type)
        <=> ( relation_like(B)
            & ilf_type(B,set_type) ) ) ) )).

%---- type_nonempty(line(relat_1 - axiom336,1917641))
fof(p15,axiom,
    ( ? [B] : ilf_type(B,binary_relation_type) )).

%---- line(hidden - axiom337,1832648)
fof(p16,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ilf_type(C,subset_type(B))
            <=> ilf_type(C,member_type(power_set(B))) ) ) ) )).

%---- type_nonempty(line(hidden - axiom337,1832648))
fof(p17,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ? [C] : ilf_type(C,subset_type(B)) ) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(p18,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => subset(B,B) ) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(p19,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => subset(B,B) ) )).

%---- line(hidden - axiom339,1832644)
fof(p20,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( member(B,power_set(C))
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                   => member(D,C) ) ) ) ) ) )).

%---- declaration(line(hidden - axiom339,1832644))
fof(p21,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ~ empty(power_set(B))
          & ilf_type(power_set(B),set_type) ) ) )).

%---- line(hidden - axiom340,1832640)
fof(p22,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ( ~ empty(C)
              & ilf_type(C,set_type) )
           => ( ilf_type(B,member_type(C))
            <=> member(B,C) ) ) ) )).

%---- type_nonempty(line(hidden - axiom340,1832640))
fof(p23,axiom,
    ( ! [B] :
        ( ( ~ empty(B)
          & ilf_type(B,set_type) )
       => ? [C] : ilf_type(C,member_type(B)) ) )).

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

%---- conditional_cluster(axiom342,relation_like)
fof(p25,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,subset_type(cross_product(B,C)))
               => relation_like(D) ) ) ) )).

%---- line(hidden - axiom343,1832628)
fof(p26,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( empty(B)
        <=> ! [C] :
              ( ilf_type(C,set_type)
             => ~ member(C,B) ) ) ) )).

%---- conditional_cluster(axiom344,empty)
fof(p27,axiom,
    ( ! [B] :
        ( ( empty(B)
          & ilf_type(B,set_type) )
       => relation_like(B) ) )).

%---- line(relset_1 - axiom348,1916330)
fof(p28,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => domain(B,C,D) = domain_of(D) ) ) ) )).

%---- declaration(line(relset_1 - axiom348,1916330))
fof(p29,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => ilf_type(domain(B,C,D),subset_type(B)) ) ) ) )).

%---- line(relset_1 - axiom349,1916334)
fof(p30,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => range(B,C,D) = range_of(D) ) ) ) )).

%---- declaration(line(relset_1 - axiom349,1916334))
fof(p31,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => ilf_type(range(B,C,D),subset_type(C)) ) ) ) )).

%---- declaration(set)
fof(p32,axiom,
    ( ! [B] : ilf_type(B,set_type) )).

%---- line(relset_1 - th(31),1916588)
fof(prove_relset_1_31,conjecture,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(C,B))
               => ( subset(identity_relation_of(C),D)
                 => ( C = domain(C,B,D)
                    & subset(C,range(C,B,D)) ) ) ) ) ) )).

%--------------------------------------------------------------------------

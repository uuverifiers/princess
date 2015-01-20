%------------------------------------------------------------------------------
% File     : SET673+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Relations)
% Problem  : Y a subset of Y1 => Y1 restricted to R (X to Y) is R
% Version  : [Wor90] axioms : Reduced > Incomplete.
% English  : If Y is a subset of Y1 then Y1 restricted to a relation R from
%            X to Y is R.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Wor90] Woronowicz (1990), Relations Defined on Sets
% Source   : [ILF]
% Names    : RELSET_1 (36) [Wor90]

% Status   : Theorem
% Rating   : 0.80 v6.1.0, 0.90 v6.0.0, 0.83 v5.5.0, 0.89 v5.3.0, 0.81 v5.2.0, 0.75 v5.1.0, 0.76 v5.0.0, 0.79 v4.1.0, 0.83 v4.0.0, 0.79 v3.7.0, 0.80 v3.5.0, 0.84 v3.3.0, 0.71 v3.2.0, 0.82 v3.1.0, 0.78 v2.7.0, 0.83 v2.6.0, 0.71 v2.5.0, 0.75 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   28 (   2 unit)
%            Number of atoms       :  117 (   7 equality)
%            Maximal formula depth :   13 (   7 average)
%            Number of connectives :   93 (   4 ~  ;   0  |;  10  &)
%                                         (  10 <=>;  69 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   10 (   2 constant; 0-4 arity)
%            Number of variables   :   70 (   0 singleton;  64 !;   6 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%---- line(relat_1 - df(2),1917780)
fof(p1,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ! [C] :
            ( ilf_type(C,binary_relation_type)
           => ( B = C
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ! [E] :
                      ( ilf_type(E,set_type)
                     => ( member(ordered_pair(D,E),B)
                      <=> member(ordered_pair(D,E),C) ) ) ) ) ) ) )).

%---- line(relat_1 - th(114),1919569)
fof(p2,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,binary_relation_type)
                   => ( member(ordered_pair(C,D),restrict(B,E))
                    <=> ( member(D,B)
                        & member(ordered_pair(C,D),E) ) ) ) ) ) ) )).

%---- line(relset_1 - th(7),1916125)
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
                        ( ilf_type(F,relation_type(B,C))
                       => ( member(ordered_pair(D,E),F)
                         => ( member(D,B)
                            & member(E,C) ) ) ) ) ) ) ) )).

%---- line(relset_1 - df(1),1916080)
fof(p4,axiom,
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
fof(p5,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ? [D] : ilf_type(D,relation_type(C,B)) ) ) )).

%---- line(tarski - df(3),1832749)
fof(p6,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( subset(B,C)
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                   => member(D,C) ) ) ) ) ) )).

%---- declaration(op(cross_product,2,function))
fof(p7,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(cross_product(B,C),set_type) ) ) )).

%---- declaration(op(ordered_pair,2,function))
fof(p8,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(ordered_pair(B,C),set_type) ) ) )).

%---- declaration(op(restrict,2,function))
fof(p9,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,binary_relation_type)
           => ilf_type(restrict(B,C),binary_relation_type) ) ) )).

%---- line(relat_1 - axiom428,1917641)
fof(p10,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ilf_type(B,binary_relation_type)
        <=> ( relation_like(B)
            & ilf_type(B,set_type) ) ) ) )).

%---- type_nonempty(line(relat_1 - axiom428,1917641))
fof(p11,axiom,
    ( ? [B] : ilf_type(B,binary_relation_type) )).

%---- line(hidden - axiom429,1832648)
fof(p12,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ilf_type(C,subset_type(B))
            <=> ilf_type(C,member_type(power_set(B))) ) ) ) )).

%---- type_nonempty(line(hidden - axiom429,1832648))
fof(p13,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ? [C] : ilf_type(C,subset_type(B)) ) )).

%---- property(symmetry,op(=,2,predicate))
fof(p14,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ! [C] :
            ( ilf_type(C,binary_relation_type)
           => ( B = C
             => C = B ) ) ) )).

%---- property(reflexivity,op(=,2,predicate))
fof(p15,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => B = B ) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(p16,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => subset(B,B) ) )).

%---- line(hidden - axiom431,1832644)
fof(p17,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( member(B,power_set(C))
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                   => member(D,C) ) ) ) ) ) )).

%---- declaration(line(hidden - axiom431,1832644))
fof(p18,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ~ empty(power_set(B))
          & ilf_type(power_set(B),set_type) ) ) )).

%---- line(hidden - axiom432,1832640)
fof(p19,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ( ~ empty(C)
              & ilf_type(C,set_type) )
           => ( ilf_type(B,member_type(C))
            <=> member(B,C) ) ) ) )).

%---- type_nonempty(line(hidden - axiom432,1832640))
fof(p20,axiom,
    ( ! [B] :
        ( ( ~ empty(B)
          & ilf_type(B,set_type) )
       => ? [C] : ilf_type(C,member_type(B)) ) )).

%---- line(relat_1 - df(1),1917627)
fof(p21,axiom,
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

%---- conditional_cluster(axiom434,relation_like)
fof(p22,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,subset_type(cross_product(B,C)))
               => relation_like(D) ) ) ) )).

%---- line(hidden - axiom435,1832628)
fof(p23,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( empty(B)
        <=> ! [C] :
              ( ilf_type(C,set_type)
             => ~ member(C,B) ) ) ) )).

%---- conditional_cluster(axiom436,empty)
fof(p24,axiom,
    ( ! [B] :
        ( ( empty(B)
          & ilf_type(B,set_type) )
       => relation_like(B) ) )).

%---- line(relset_1 - axiom445,1916652)
fof(p25,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,relation_type(B,C))
                   => restrict4(B,C,D,E) = restrict(D,E) ) ) ) ) )).

%---- declaration(line(relset_1 - axiom445,1916652))
fof(p26,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,relation_type(B,C))
                   => ilf_type(restrict4(B,C,D,E),relation_type(B,C)) ) ) ) ) )).

%---- declaration(set)
fof(p27,axiom,
    ( ! [B] : ilf_type(B,set_type) )).

%---- line(relset_1 - th(36),1916736)
fof(prove_relset_1_36,conjecture,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,relation_type(B,C))
                   => ( subset(C,D)
                     => restrict4(B,C,D,E) = E ) ) ) ) ) )).

%------------------------------------------------------------------------------

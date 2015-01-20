%--------------------------------------------------------------------------
% File     : SET655+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Relations)
% Problem  : X a subset of X1 & Y a subset of Y1 => R (X to Y) is (X1 to Y1)
% Version  : [Wor90] axioms : Reduced > Incomplete.
% English  : If X is a subset of X1 and Y is a subset of Y1 then a relation
%            R from X to Y is a relation from X1 to Y1.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Wor90] Woronowicz (1990), Relations Defined on Sets
% Source   : [ILF]
% Names    : RELSET_1 (17) [Wor90]

% Status   : Theorem
% Rating   : 0.48 v6.1.0, 0.53 v6.0.0, 0.61 v5.5.0, 0.63 v5.4.0, 0.64 v5.3.0, 0.59 v5.2.0, 0.50 v5.1.0, 0.52 v5.0.0, 0.50 v4.1.0, 0.52 v4.0.0, 0.50 v3.7.0, 0.45 v3.5.0, 0.47 v3.4.0, 0.37 v3.3.0, 0.29 v3.2.0, 0.36 v3.1.0, 0.22 v2.7.0, 0.33 v2.6.0, 0.29 v2.5.0, 0.38 v2.4.0, 0.50 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   20 (   1 unit)
%            Number of atoms       :   86 (   1 equality)
%            Maximal formula depth :   13 (   7 average)
%            Number of connectives :   70 (   4 ~  ;   0  |;  10  &)
%                                         (   6 <=>;  50 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :    7 (   1 constant; 0-2 arity)
%            Number of variables   :   50 (   0 singleton;  45 !;   5 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - th(29),1909428)
fof(p1,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ( ( subset(B,C)
                    & subset(C,D) )
                 => subset(B,D) ) ) ) ) )).

%---- line(zfmisc_1 - th(119),1905457)
fof(p2,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,set_type)
                   => ( ( subset(B,C)
                        & subset(D,E) )
                     => subset(cross_product(B,D),cross_product(C,E)) ) ) ) ) ) )).

%---- line(relset_1 - df(1),1916080)
fof(p3,axiom,
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
fof(p4,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ? [D] : ilf_type(D,relation_type(C,B)) ) ) )).

%---- line(tarski - df(3),1832749)
fof(p5,axiom,
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
fof(p6,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(cross_product(B,C),set_type) ) ) )).

%---- line(hidden - axiom131,1832648)
fof(p7,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ilf_type(C,subset_type(B))
            <=> ilf_type(C,member_type(power_set(B))) ) ) ) )).

%---- type_nonempty(line(hidden - axiom131,1832648))
fof(p8,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ? [C] : ilf_type(C,subset_type(B)) ) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(p9,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => subset(B,B) ) )).

%---- line(hidden - axiom133,1832644)
fof(p10,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( member(B,power_set(C))
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                   => member(D,C) ) ) ) ) ) )).

%---- declaration(line(hidden - axiom133,1832644))
fof(p11,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ~ empty(power_set(B))
          & ilf_type(power_set(B),set_type) ) ) )).

%---- line(hidden - axiom134,1832640)
fof(p12,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ( ~ empty(C)
              & ilf_type(C,set_type) )
           => ( ilf_type(B,member_type(C))
            <=> member(B,C) ) ) ) )).

%---- type_nonempty(line(hidden - axiom134,1832640))
fof(p13,axiom,
    ( ! [B] :
        ( ( ~ empty(B)
          & ilf_type(B,set_type) )
       => ? [C] : ilf_type(C,member_type(B)) ) )).

%---- line(hidden - axiom135,1832628)
fof(p14,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( empty(B)
        <=> ! [C] :
              ( ilf_type(C,set_type)
             => ~ member(C,B) ) ) ) )).

%---- line(relat_1 - df(1),1917627)
fof(p15,axiom,
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

%---- conditional_cluster(axiom137,relation_like)
fof(p16,axiom,
    ( ! [B] :
        ( ( empty(B)
          & ilf_type(B,set_type) )
       => relation_like(B) ) )).

%---- conditional_cluster(axiom138,relation_like)
fof(p17,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,subset_type(cross_product(B,C)))
               => relation_like(D) ) ) ) )).

%---- declaration(op(ordered_pair,2,function))
fof(p18,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(ordered_pair(B,C),set_type) ) ) )).

%---- declaration(set)
fof(p19,axiom,
    ( ! [B] : ilf_type(B,set_type) )).

%---- line(relset_1 - th(17),1916284)
fof(prove_relset_1_17,conjecture,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,set_type)
                   => ! [F] :
                        ( ilf_type(F,relation_type(B,D))
                       => ( ( subset(B,C)
                            & subset(D,E) )
                         => ilf_type(F,relation_type(C,E)) ) ) ) ) ) ) )).

%--------------------------------------------------------------------------

%--------------------------------------------------------------------------
% File     : SET666+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Relations)
% Problem  : The identity relation on X is a relation from X to X
% Version  : [Wor90] axioms : Reduced > Incomplete.
% English  :

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Wor90] Woronowicz (1990), Relations Defined on Sets
% Source   : [ILF]
% Names    : RELSET_1 (29) [Wor90]

% Status   : Theorem
% Rating   : 0.28 v6.1.0, 0.30 v6.0.0, 0.26 v5.5.0, 0.30 v5.4.0, 0.29 v5.3.0, 0.37 v5.2.0, 0.25 v5.1.0, 0.29 v4.1.0, 0.35 v4.0.1, 0.39 v4.0.0, 0.38 v3.7.0, 0.35 v3.5.0, 0.37 v3.4.0, 0.26 v3.3.0, 0.29 v3.2.0, 0.36 v3.1.0, 0.33 v2.6.0, 0.29 v2.5.0, 0.25 v2.4.0, 0.50 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :   25 (   2 unit)
%            Number of atoms       :   88 (   2 equality)
%            Maximal formula depth :   11 (   6 average)
%            Number of connectives :   67 (   4 ~  ;   0  |;   9  &)
%                                         (   9 <=>;  45 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   10 (   2 constant; 0-2 arity)
%            Number of variables   :   50 (   0 singleton;  43 !;   7 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(relset_1 - df(1),1916080)
fof(p1,axiom,
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
fof(p2,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ? [D] : ilf_type(D,relation_type(C,B)) ) ) )).

%---- line(relset_1 - th(28),1916537)
fof(p3,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => subset(identity_relation_of(B),cross_product(B,B)) ) )).

%---- line(relat_1 - df(10),1918876)
fof(p4,axiom,
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
fof(p5,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ilf_type(identity_relation_of(B),binary_relation_type) ) )).

%---- line(relset_1 - axiom299,1916837)
fof(p6,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ilf_type(C,identity_relation_of_type(B))
            <=> ilf_type(C,relation_type(B,B)) ) ) ) )).

%---- type_nonempty(line(relset_1 - axiom299,1916837))
fof(p7,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ? [C] : ilf_type(C,identity_relation_of_type(B)) ) )).

%---- declaration(op(cross_product,2,function))
fof(p8,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(cross_product(B,C),set_type) ) ) )).

%---- declaration(op(ordered_pair,2,function))
fof(p9,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(ordered_pair(B,C),set_type) ) ) )).

%---- line(relat_1 - axiom300,1917641)
fof(p10,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ilf_type(B,binary_relation_type)
        <=> ( relation_like(B)
            & ilf_type(B,set_type) ) ) ) )).

%---- type_nonempty(line(relat_1 - axiom300,1917641))
fof(p11,axiom,
    ( ? [B] : ilf_type(B,binary_relation_type) )).

%---- line(hidden - axiom301,1832648)
fof(p12,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ilf_type(C,subset_type(B))
            <=> ilf_type(C,member_type(power_set(B))) ) ) ) )).

%---- type_nonempty(line(hidden - axiom301,1832648))
fof(p13,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ? [C] : ilf_type(C,subset_type(B)) ) )).

%---- line(tarski - df(3),1832749)
fof(p14,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( subset(B,C)
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                   => member(D,C) ) ) ) ) ) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(p15,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => subset(B,B) ) )).

%---- line(hidden - axiom303,1832644)
fof(p16,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( member(B,power_set(C))
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                   => member(D,C) ) ) ) ) ) )).

%---- declaration(line(hidden - axiom303,1832644))
fof(p17,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ~ empty(power_set(B))
          & ilf_type(power_set(B),set_type) ) ) )).

%---- line(hidden - axiom304,1832640)
fof(p18,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ( ~ empty(C)
              & ilf_type(C,set_type) )
           => ( ilf_type(B,member_type(C))
            <=> member(B,C) ) ) ) )).

%---- type_nonempty(line(hidden - axiom304,1832640))
fof(p19,axiom,
    ( ! [B] :
        ( ( ~ empty(B)
          & ilf_type(B,set_type) )
       => ? [C] : ilf_type(C,member_type(B)) ) )).

%---- line(relat_1 - df(1),1917627)
fof(p20,axiom,
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

%---- conditional_cluster(axiom306,relation_like)
fof(p21,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,subset_type(cross_product(B,C)))
               => relation_like(D) ) ) ) )).

%---- line(hidden - axiom307,1832628)
fof(p22,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( empty(B)
        <=> ! [C] :
              ( ilf_type(C,set_type)
             => ~ member(C,B) ) ) ) )).

%---- conditional_cluster(axiom308,empty)
fof(p23,axiom,
    ( ! [B] :
        ( ( empty(B)
          & ilf_type(B,set_type) )
       => relation_like(B) ) )).

%---- declaration(set)
fof(p24,axiom,
    ( ! [B] : ilf_type(B,set_type) )).

%---- line(relset_1 - th(29),1916543)
fof(prove_relset_1_29,conjecture,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ilf_type(identity_relation_of(B),identity_relation_of_type(B)) ) )).

%--------------------------------------------------------------------------

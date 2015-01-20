%--------------------------------------------------------------------------
% File     : SET678+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Relations)
% Problem  : R o Id on X is R & Id on X o R is R
% Version  : [Wor90] axioms : Reduced > Incomplete.
% English  : A relation R from X to Y composed with the identity relation on
%            X is R; and the identity relation on X composed with R is R.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Wor90] Woronowicz (1990), Relations Defined on Sets
% Source   : [ILF]
% Names    : RELSET_1 (45) [Wor90]

% Status   : Theorem
% Rating   : 0.64 v6.1.0, 0.70 v5.5.0, 0.74 v5.4.0, 0.79 v5.3.0, 0.81 v5.2.0, 0.65 v5.1.0, 0.67 v5.0.0, 0.71 v4.1.0, 0.70 v4.0.0, 0.67 v3.7.0, 0.70 v3.5.0, 0.63 v3.3.0, 0.57 v3.2.0, 0.55 v3.1.0, 0.67 v2.7.0, 0.50 v2.6.0, 0.57 v2.5.0, 0.62 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   39 (   2 unit)
%            Number of atoms       :  152 (  13 equality)
%            Maximal formula depth :   13 (   6 average)
%            Number of connectives :  117 (   4 ~  ;   0  |;  12  &)
%                                         (  12 <=>;  89 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   16 (   2 constant; 0-5 arity)
%            Number of variables   :   92 (   0 singleton;  84 !;   8 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(relat_1 - th(77),1919048)
fof(p1,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,binary_relation_type)
           => ( subset(domain_of(C),B)
             => compose(identity_relation_of(B),C) = C ) ) ) )).

%---- line(relat_1 - th(79),1919070)
fof(p2,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,binary_relation_type)
           => ( subset(range_of(C),B)
             => compose(C,identity_relation_of(B)) = C ) ) ) )).

%---- line(relat_1 - df(8),1918463)
fof(p3,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ! [C] :
            ( ilf_type(C,binary_relation_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ! [E] :
                    ( ilf_type(E,set_type)
                   => ( member(ordered_pair(D,E),compose(B,C))
                    <=> ? [F] :
                          ( ilf_type(F,set_type)
                          & member(ordered_pair(D,F),B)
                          & member(ordered_pair(F,E),C) ) ) ) ) ) ) )).

%---- declaration(line(relat_1 - df(8),1918463))
fof(p4,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ! [C] :
            ( ilf_type(C,binary_relation_type)
           => ilf_type(compose(B,C),binary_relation_type) ) ) )).

%---- line(relat_1 - df(10),1918876)
fof(p5,axiom,
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
fof(p6,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ilf_type(identity_relation_of(B),binary_relation_type) ) )).

%---- line(relset_1 - axiom538,1916837)
fof(p7,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ilf_type(C,identity_relation_of_type(B))
            <=> ilf_type(C,relation_type(B,B)) ) ) ) )).

%---- type_nonempty(line(relset_1 - axiom538,1916837))
fof(p8,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ? [C] : ilf_type(C,identity_relation_of_type(B)) ) )).

%---- line(relat_1 - df(2),1917780)
fof(p9,axiom,
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

%---- declaration(op(domain_of,1,function))
fof(p10,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ilf_type(domain_of(B),set_type) ) )).

%---- declaration(op(range_of,1,function))
fof(p11,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ilf_type(range_of(B),set_type) ) )).

%---- declaration(op(ordered_pair,2,function))
fof(p12,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(ordered_pair(B,C),set_type) ) ) )).

%---- line(relat_1 - axiom539,1917641)
fof(p13,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ilf_type(B,binary_relation_type)
        <=> ( relation_like(B)
            & ilf_type(B,set_type) ) ) ) )).

%---- type_nonempty(line(relat_1 - axiom539,1917641))
fof(p14,axiom,
    ( ? [B] : ilf_type(B,binary_relation_type) )).

%---- line(relset_1 - df(1),1916080)
fof(p15,axiom,
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
fof(p16,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ? [D] : ilf_type(D,relation_type(C,B)) ) ) )).

%---- property(symmetry,op(=,2,predicate))
fof(p17,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ! [C] :
            ( ilf_type(C,binary_relation_type)
           => ( B = C
             => C = B ) ) ) )).

%---- property(reflexivity,op(=,2,predicate))
fof(p18,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => B = B ) )).

%---- line(tarski - df(3),1832749)
fof(p19,axiom,
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
fof(p20,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => subset(B,B) ) )).

%---- declaration(op(cross_product,2,function))
fof(p21,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(cross_product(B,C),set_type) ) ) )).

%---- line(hidden - axiom541,1832648)
fof(p22,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ilf_type(C,subset_type(B))
            <=> ilf_type(C,member_type(power_set(B))) ) ) ) )).

%---- type_nonempty(line(hidden - axiom541,1832648))
fof(p23,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ? [C] : ilf_type(C,subset_type(B)) ) )).

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

%---- conditional_cluster(axiom543,relation_like)
fof(p25,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,subset_type(cross_product(B,C)))
               => relation_like(D) ) ) ) )).

%---- line(hidden - axiom544,1832644)
fof(p26,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( member(B,power_set(C))
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                   => member(D,C) ) ) ) ) ) )).

%---- declaration(line(hidden - axiom544,1832644))
fof(p27,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ~ empty(power_set(B))
          & ilf_type(power_set(B),set_type) ) ) )).

%---- line(hidden - axiom545,1832640)
fof(p28,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ( ~ empty(C)
              & ilf_type(C,set_type) )
           => ( ilf_type(B,member_type(C))
            <=> member(B,C) ) ) ) )).

%---- type_nonempty(line(hidden - axiom545,1832640))
fof(p29,axiom,
    ( ! [B] :
        ( ( ~ empty(B)
          & ilf_type(B,set_type) )
       => ? [C] : ilf_type(C,member_type(B)) ) )).

%---- line(hidden - axiom546,1832628)
fof(p30,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( empty(B)
        <=> ! [C] :
              ( ilf_type(C,set_type)
             => ~ member(C,B) ) ) ) )).

%---- conditional_cluster(axiom547,empty)
fof(p31,axiom,
    ( ! [B] :
        ( ( empty(B)
          & ilf_type(B,set_type) )
       => relation_like(B) ) )).

%---- line(relset_1 - axiom551,1916330)
fof(p32,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => domain(B,C,D) = domain_of(D) ) ) ) )).

%---- declaration(line(relset_1 - axiom551,1916330))
fof(p33,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => ilf_type(domain(B,C,D),subset_type(B)) ) ) ) )).

%---- line(relset_1 - axiom552,1916334)
fof(p34,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => range(B,C,D) = range_of(D) ) ) ) )).

%---- declaration(line(relset_1 - axiom552,1916334))
fof(p35,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => ilf_type(range(B,C,D),subset_type(C)) ) ) ) )).

%---- line(relset_1 - axiom554,1916444)
fof(p36,axiom,
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

%---- declaration(line(relset_1 - axiom554,1916444))
fof(p37,axiom,
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
fof(p38,axiom,
    ( ! [B] : ilf_type(B,set_type) )).

%---- line(relset_1 - th(45),1916849)
fof(prove_relset_1_45,conjecture,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,identity_relation_of_type(B))
           => ( compose(C,identity_relation_of(B)) = C
              & compose(identity_relation_of(B),C) = C ) ) ) )).

%--------------------------------------------------------------------------

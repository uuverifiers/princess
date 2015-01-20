%--------------------------------------------------------------------------
% File     : SET686+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Relations)
% Problem  : x in R^-1(D2) iff ?y in E : <x,y> in R (X to Y) & y in D2
% Version  : [Wor89] axioms : Reduced > Incomplete.
% English  : x is in the inverse of a relation R from X to Y applied to D2
%            iff there exists an element y in E such that <x,y> is in a
%            relation R from X to Y and y is in D2.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Wor89] Woronowicz (1989), Relations Defined on Sets
% Source   : [ILF]
% Names    : RELSET_1 (53) [Wor89]

% Status   : Theorem
% Rating   : 0.56 v6.1.0, 0.57 v5.5.0, 0.67 v5.4.0, 0.68 v5.3.0, 0.70 v5.2.0, 0.55 v5.1.0, 0.57 v5.0.0, 0.54 v4.1.0, 0.48 v4.0.0, 0.46 v3.7.0, 0.50 v3.5.0, 0.53 v3.4.0, 0.58 v3.3.0, 0.50 v3.2.0, 0.45 v3.1.0, 0.56 v2.7.0, 0.50 v2.6.0, 0.43 v2.5.0, 0.50 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :   28 (   2 unit)
%            Number of atoms       :  122 (   5 equality)
%            Maximal formula depth :   15 (   7 average)
%            Number of connectives :  101 (   7 ~  ;   0  |;  16  &)
%                                         (  11 <=>;  67 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :   12 (   2 constant; 0-4 arity)
%            Number of variables   :   74 (   0 singleton;  66 !;   8 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(relat_1 - th(165),1920359)
fof(p1,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,binary_relation_type)
               => ( member(C,inverse2(D,B))
                <=> ? [E] :
                      ( ilf_type(E,set_type)
                      & member(ordered_pair(C,E),D)
                      & member(E,B) ) ) ) ) ) )).

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

%---- line(hidden - axiom715,1832640)
fof(p7,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ( ~ empty(C)
              & ilf_type(C,set_type) )
           => ( ilf_type(B,member_type(C))
            <=> member(B,C) ) ) ) )).

%---- type_nonempty(line(hidden - axiom715,1832640))
fof(p8,axiom,
    ( ! [B] :
        ( ( ~ empty(B)
          & ilf_type(B,set_type) )
       => ? [C] : ilf_type(C,member_type(B)) ) )).

%---- line(hidden - axiom717,1832628)
fof(p9,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( empty(B)
        <=> ! [C] :
              ( ilf_type(C,set_type)
             => ~ member(C,B) ) ) ) )).

%---- declaration(op(inverse2,2,function))
fof(p10,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(inverse2(B,C),set_type) ) ) )).

%---- declaration(op(singleton,1,function))
fof(p11,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ilf_type(singleton(B),set_type) ) )).

%---- declaration(op(cross_product,2,function))
fof(p12,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(cross_product(B,C),set_type) ) ) )).

%---- declaration(op(unordered_pair,2,function))
fof(p13,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(unordered_pair(B,C),set_type) ) ) )).

%---- property(commutativity,op(unordered_pair,2,function))
fof(p14,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] : ilf_type(C,set_type) ) )).

%---- line(relat_1 - axiom718,1917641)
fof(p15,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ilf_type(B,binary_relation_type)
        <=> ( relation_like(B)
            & ilf_type(B,set_type) ) ) ) )).

%---- type_nonempty(line(relat_1 - axiom718,1917641))
fof(p16,axiom,
    ( ? [B] : ilf_type(B,binary_relation_type) )).

%---- line(hidden - axiom719,1832648)
fof(p17,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ilf_type(C,subset_type(B))
            <=> ilf_type(C,member_type(power_set(B))) ) ) ) )).

%---- type_nonempty(line(hidden - axiom719,1832648))
fof(p18,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ? [C] : ilf_type(C,subset_type(B)) ) )).

%---- line(hidden - axiom720,1832615)
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

%---- line(hidden - axiom722,1832644)
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

%---- declaration(line(hidden - axiom722,1832644))
fof(p21,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ~ empty(power_set(B))
          & ilf_type(power_set(B),set_type) ) ) )).

%---- line(relat_1 - df(1),1917627)
fof(p22,axiom,
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

%---- conditional_cluster(axiom723,relation_like)
fof(p23,axiom,
    ( ! [B] :
        ( ( empty(B)
          & ilf_type(B,set_type) )
       => relation_like(B) ) )).

%---- conditional_cluster(axiom724,relation_like)
fof(p24,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,subset_type(cross_product(B,C)))
               => relation_like(D) ) ) ) )).

%---- line(relset_1 - axiom735,1916768)
fof(p25,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => ! [E] :
                    ( ilf_type(E,set_type)
                   => inverse4(B,C,D,E) = inverse2(D,E) ) ) ) ) )).

%---- declaration(line(relset_1 - axiom735,1916768))
fof(p26,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => ! [E] :
                    ( ilf_type(E,set_type)
                   => ilf_type(inverse4(B,C,D,E),subset_type(B)) ) ) ) ) )).

%---- declaration(set)
fof(p27,axiom,
    ( ! [B] : ilf_type(B,set_type) )).

%---- line(relset_1 - th(53),1917018)
fof(prove_relset_1_53,conjecture,
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
                    ( ilf_type(E,relation_type(B,D))
                   => ! [F] :
                        ( ilf_type(F,member_type(B))
                       => ( member(F,inverse4(B,D,E,C))
                        <=> ? [G] :
                              ( ilf_type(G,member_type(D))
                              & member(ordered_pair(F,G),E)
                              & member(G,C) ) ) ) ) ) ) ) )).

%--------------------------------------------------------------------------

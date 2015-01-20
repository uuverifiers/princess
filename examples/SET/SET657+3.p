%------------------------------------------------------------------------------
% File     : SET657+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Relations)
% Problem  : The field of a relation R from X to Y is a subset of X union Y
% Version  : [Wor90] axioms : Reduced > Incomplete.
% English  :

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Wor90] Woronowicz (1990), Relations Defined on Sets
% Source   : [ILF]
% Names    : RELSET_1 (19) [Wor90]

% Status   : Theorem
% Rating   : 0.52 v6.1.0, 0.60 v6.0.0, 0.52 v5.5.0, 0.63 v5.4.0, 0.64 v5.3.0, 0.70 v5.2.0, 0.60 v5.1.0, 0.57 v5.0.0, 0.67 v4.1.0, 0.74 v4.0.1, 0.70 v4.0.0, 0.71 v3.7.0, 0.70 v3.5.0, 0.68 v3.4.0, 0.63 v3.3.0, 0.57 v3.2.0, 0.55 v3.1.0, 0.67 v2.7.0, 0.50 v2.6.0, 0.43 v2.5.0, 0.50 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   38 (   2 unit)
%            Number of atoms       :  141 (  11 equality)
%            Maximal formula depth :   11 (   6 average)
%            Number of connectives :  107 (   4 ~  ;   1  |;   9  &)
%                                         (  10 <=>;  83 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   15 (   2 constant; 0-4 arity)
%            Number of variables   :   85 (   0 singleton;  79 !;   6 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%---- line(boole - th(34),1909498)
fof(p1,axiom,
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
                     => subset(union(B,D),union(C,E)) ) ) ) ) ) )).

%---- line(relat_1 - th(29),1918207)
fof(p2,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => field_of(B) = union(domain_of(B),range_of(B)) ) )).

%---- line(boole - df(2),1909298)
fof(p3,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,set_type)
               => ( member(D,union(B,C))
                <=> ( member(D,B)
                    | member(D,C) ) ) ) ) ) )).

%---- declaration(line(boole - df(2),1909298))
fof(p4,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(union(B,C),set_type) ) ) )).

%---- line(relat_1 - df(6),1918204)
fof(p5,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => field_of(B) = union(domain_of(B),range_of(B)) ) )).

%---- declaration(line(relat_1 - df(6),1918204))
fof(p6,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ilf_type(field_of(B),set_type) ) )).

%---- line(relset_1 - df(1),1916080)
fof(p7,axiom,
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
fof(p8,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ? [D] : ilf_type(D,relation_type(C,B)) ) ) )).

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

%---- property(commutativity,op(union,2,function))
fof(p10,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => union(B,C) = union(C,B) ) ) )).

%---- declaration(op(domain_of,1,function))
fof(p11,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ilf_type(domain_of(B),set_type) ) )).

%---- declaration(op(cross_product,2,function))
fof(p12,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(cross_product(B,C),set_type) ) ) )).

%---- declaration(op(range_of,1,function))
fof(p13,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ilf_type(range_of(B),set_type) ) )).

%---- line(relat_1 - axiom152,1917641)
fof(p14,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ilf_type(B,binary_relation_type)
        <=> ( relation_like(B)
            & ilf_type(B,set_type) ) ) ) )).

%---- type_nonempty(line(relat_1 - axiom152,1917641))
fof(p15,axiom,
    ( ? [B] : ilf_type(B,binary_relation_type) )).

%---- line(hidden - axiom153,1832648)
fof(p16,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( ilf_type(C,subset_type(B))
            <=> ilf_type(C,member_type(power_set(B))) ) ) ) )).

%---- type_nonempty(line(hidden - axiom153,1832648))
fof(p17,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ? [C] : ilf_type(C,subset_type(B)) ) )).

%---- property(symmetry,op(=,2,predicate))
fof(p18,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => ! [C] :
            ( ilf_type(C,binary_relation_type)
           => ( B = C
             => C = B ) ) ) )).

%---- property(reflexivity,op(=,2,predicate))
fof(p19,axiom,
    ( ! [B] :
        ( ilf_type(B,binary_relation_type)
       => B = B ) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(p20,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => subset(B,B) ) )).

%---- line(hidden - axiom155,1832644)
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

%---- declaration(line(hidden - axiom155,1832644))
fof(p22,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( ~ empty(power_set(B))
          & ilf_type(power_set(B),set_type) ) ) )).

%---- line(hidden - axiom156,1832640)
fof(p23,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ( ~ empty(C)
              & ilf_type(C,set_type) )
           => ( ilf_type(B,member_type(C))
            <=> member(B,C) ) ) ) )).

%---- type_nonempty(line(hidden - axiom156,1832640))
fof(p24,axiom,
    ( ! [B] :
        ( ( ~ empty(B)
          & ilf_type(B,set_type) )
       => ? [C] : ilf_type(C,member_type(B)) ) )).

%---- line(hidden - axiom157,1832615)
fof(p25,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ( B = C
            <=> ! [D] :
                  ( ilf_type(D,set_type)
                 => ( member(D,B)
                  <=> member(D,C) ) ) ) ) ) )).

%---- line(relat_1 - df(1),1917627)
fof(p26,axiom,
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

%---- conditional_cluster(axiom159,relation_like)
fof(p27,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,subset_type(cross_product(B,C)))
               => relation_like(D) ) ) ) )).

%---- declaration(op(ordered_pair,2,function))
fof(p28,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ilf_type(ordered_pair(B,C),set_type) ) ) )).

%---- line(hidden - axiom160,1832628)
fof(p29,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ( empty(B)
        <=> ! [C] :
              ( ilf_type(C,set_type)
             => ~ member(C,B) ) ) ) )).

%---- conditional_cluster(axiom161,empty)
fof(p30,axiom,
    ( ! [B] :
        ( ( empty(B)
          & ilf_type(B,set_type) )
       => relation_like(B) ) )).

%---- line(relset_1 - axiom162,1916314)
fof(p31,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => ! [E] :
                    ( ilf_type(E,relation_type(B,C))
                   => union4(B,C,D,E) = union(D,E) ) ) ) ) )).

%---- declaration(line(relset_1 - axiom162,1916314))
fof(p32,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => ! [E] :
                    ( ilf_type(E,relation_type(B,C))
                   => ilf_type(union4(B,C,D,E),relation_type(B,C)) ) ) ) ) )).

%---- line(relset_1 - axiom165,1916330)
fof(p33,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => domain(B,C,D) = domain_of(D) ) ) ) )).

%---- declaration(line(relset_1 - axiom165,1916330))
fof(p34,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => ilf_type(domain(B,C,D),subset_type(B)) ) ) ) )).

%---- line(relset_1 - axiom166,1916334)
fof(p35,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => range(B,C,D) = range_of(D) ) ) ) )).

%---- declaration(line(relset_1 - axiom166,1916334))
fof(p36,axiom,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => ilf_type(range(B,C,D),subset_type(C)) ) ) ) )).

%---- declaration(set)
fof(p37,axiom,
    ( ! [B] : ilf_type(B,set_type) )).

%---- line(relset_1 - th(19),1916346)
fof(prove_relset_1_19,conjecture,
    ( ! [B] :
        ( ilf_type(B,set_type)
       => ! [C] :
            ( ilf_type(C,set_type)
           => ! [D] :
                ( ilf_type(D,relation_type(B,C))
               => subset(field_of(D),union(B,C)) ) ) ) )).

%------------------------------------------------------------------------------

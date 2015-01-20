%--------------------------------------------------------------------------
% File     : SET770+4 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Equivalence relations)
% Problem  : Two equivalence classes are equal or disjoint
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.60 v6.1.0, 0.70 v5.5.0, 0.78 v5.4.0, 0.89 v5.2.0, 0.90 v5.1.0, 0.95 v5.0.0, 0.88 v4.1.0, 0.87 v4.0.0, 0.88 v3.7.0, 0.85 v3.5.0, 0.84 v3.4.0, 0.89 v3.3.0, 0.79 v3.2.0, 0.82 v3.1.0, 0.89 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.88 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   17 (   1 unit)
%            Number of atoms       :   73 (   4 equality)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   59 (   3 ~  ;   3  |;  23  &)
%                                         (  15 <=>;  15 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    9 (   0 propositional; 2-3 arity)
%            Number of functors    :   10 (   1 constant; 0-3 arity)
%            Number of variables   :   61 (   0 singleton;  57 !;   4 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include equivalence relation axioms
include('Axioms/SET006+2.ax').
%--------------------------------------------------------------------------
fof(thIII06,conjecture,
    ( ! [E,R,A,B] :
        ( ( equivalence(R,E)
          & member(A,E)
          & member(B,E) )
       => ( equal_set(equivalence_class(A,E,R),equivalence_class(B,E,R))
          | disjoint(equivalence_class(A,E,R),equivalence_class(B,E,R)) ) ) )).

%--------------------------------------------------------------------------

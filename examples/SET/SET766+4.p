%--------------------------------------------------------------------------
% File     : SET766+4 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Equivalence relations)
% Problem  : A member belongs to its equivalence class
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.10 v6.0.0, 0.13 v5.5.0, 0.07 v5.3.0, 0.15 v5.2.0, 0.10 v5.0.0, 0.12 v4.1.0, 0.13 v4.0.0, 0.17 v3.7.0, 0.20 v3.5.0, 0.16 v3.4.0, 0.11 v3.3.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :   17 (   1 unit)
%            Number of atoms       :   71 (   4 equality)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   57 (   3 ~  ;   2  |;  22  &)
%                                         (  15 <=>;  15 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    9 (   0 propositional; 2-3 arity)
%            Number of functors    :   10 (   1 constant; 0-3 arity)
%            Number of variables   :   60 (   0 singleton;  56 !;   4 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include equivalence relation axioms
include('Axioms/SET006+2.ax').
%--------------------------------------------------------------------------
fof(thIII02,conjecture,
    ( ! [E,R,A] :
        ( ( equivalence(R,E)
          & member(A,E) )
       => member(A,equivalence_class(A,E,R)) ) )).

%--------------------------------------------------------------------------

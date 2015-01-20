%------------------------------------------------------------------------------
% File     : SET793+4 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory (Order relations)
% Problem  : If the order is total, a maximal element is the greatest element
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Theorem
% Rating   : 0.08 v6.1.0, 0.07 v6.0.0, 0.04 v5.5.0, 0.00 v5.3.0, 0.07 v5.2.0, 0.05 v5.0.0, 0.04 v3.7.0, 0.00 v3.2.0
% Syntax   : Number of formulae    :   11 (   0 unit)
%            Number of atoms       :   59 (   3 equality)
%            Maximal formula depth :   12 (   9 average)
%            Number of connectives :   48 (   0 ~  ;   1  |;  22  &)
%                                         (  10 <=>;  15 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   13 (   0 propositional; 2-4 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :   49 (   0 singleton;  49 !;   0 ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%----Include order relation axioms
include('Axioms/SET006+3.ax').
%------------------------------------------------------------------------------
fof(thIV5,conjecture,(
    ! [R,E,M] :
      ( ( total_order(R,E)
        & max(M,R,E) )
     => greatest(M,R,E) ) )).

%------------------------------------------------------------------------------

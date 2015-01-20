%------------------------------------------------------------------------------
% File     : SET796+4 : TPTP v6.1.0. Bugfixed v4.0.0.
% Domain   : Set Theory (Order relations)
% Problem  : If R(a,b) then a is the greatest lower bound of unordered_pair(a,b)
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Theorem
% Rating   : 0.60 v6.1.0, 0.67 v6.0.0, 0.70 v5.4.0, 0.79 v5.3.0, 0.81 v5.2.0, 0.80 v5.1.0, 0.81 v5.0.0, 0.79 v4.1.0, 0.78 v4.0.1, 0.83 v4.0.0
% Syntax   : Number of formulae    :   22 (   1 unit)
%            Number of atoms       :   90 (   6 equality)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   70 (   2   ~;   3   |;  28   &)
%                                         (  20 <=>;  17  =>;   0  <=)
%                                         (   0 <~>;   0  ~|;   0  ~&)
%            Number of predicates  :   15 (   0 propositional; 2-4 arity)
%            Number of functors    :    9 (   1 constant; 0-2 arity)
%            Number of variables   :   78 (   0 sgn;  77   !;   1   ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixes : v4.0.0 - removed duplicate include of SET006+3.ax
%------------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include order relation axioms
include('Axioms/SET006+3.ax').
%------------------------------------------------------------------------------
fof(thIV8,conjecture,(
    ! [R,E,A,B] :
      ( ( order(R,E)
        & member(A,E)
        & member(B,E)
        & apply(R,A,B) )
     => greatest_lower_bound(A,unordered_pair(A,B),R,E) ) )).

%------------------------------------------------------------------------------

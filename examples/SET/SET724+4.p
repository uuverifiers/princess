%------------------------------------------------------------------------------
% File     : SET724+4 : TPTP v6.1.0. Bugfixed v2.2.1.
% Domain   : Set Theory (Mappings)
% Problem  : If GoF = HoF and F is surjective, then G = H
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.76 v6.1.0, 0.77 v6.0.0, 0.74 v5.5.0, 0.78 v5.4.0, 0.86 v5.3.0, 0.85 v5.2.0, 0.75 v5.1.0, 0.81 v5.0.0, 0.79 v4.1.0, 0.78 v4.0.1, 0.83 v3.7.0, 0.90 v3.5.0, 0.89 v3.4.0, 0.95 v3.3.0, 0.86 v3.2.0, 0.82 v3.1.0, 0.89 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.88 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   29 (   1 unit)
%            Number of atoms       :  134 (   6 equality)
%            Maximal formula depth :   19 (   9 average)
%            Number of connectives :  107 (   2 ~  ;   2  |;  54  &)
%                                         (  30 <=>;  19 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   16 (   0 propositional; 2-6 arity)
%            Number of functors    :   15 (   1 constant; 0-5 arity)
%            Number of variables   :  139 (   0 singleton; 130 !;   9 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixes : v2.2.1 - Bugfixes in SET006+1.ax.
%------------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include mappings axioms
include('Axioms/SET006+1.ax').
%------------------------------------------------------------------------------
fof(thII15,conjecture,
    ( ! [F,G,H,A,B,C] :
        ( ( maps(F,A,B)
          & maps(G,B,C)
          & maps(H,B,C)
          & surjective(F,A,B)
          & equal_maps(compose_function(G,F,A,B,C),compose_function(H,F,A,B,C),A,C) )
       => equal_maps(G,H,B,C) ) )).

%------------------------------------------------------------------------------

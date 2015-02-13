%--------------------------------------------------------------------------
% File     : SET710+4 : TPTP v6.1.0. Bugfixed v2.2.1.
% Domain   : Set Theory (Mappings)
% Problem  : Associativity of composition
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.72 v6.1.0, 0.77 v6.0.0, 0.83 v5.5.0, 0.85 v5.4.0, 0.93 v5.2.0, 0.95 v5.0.0, 0.92 v4.1.0, 0.96 v3.7.0, 0.95 v3.3.0, 0.93 v3.2.0, 0.91 v3.1.0, 0.89 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.88 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   29 (   1 unit)
%            Number of atoms       :  132 (   6 equality)
%            Maximal formula depth :   19 (   9 average)
%            Number of connectives :  105 (   2 ~  ;   2  |;  52  &)
%                                         (  30 <=>;  19 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   16 (   0 propositional; 2-6 arity)
%            Number of functors    :   15 (   1 constant; 0-5 arity)
%            Number of variables   :  140 (   0 singleton; 131 !;   9 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixes : v2.2.1 - Bugfixes in SET006+1.ax.
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include mappings axioms
include('Axioms/SET006+1.ax').
%--------------------------------------------------------------------------
fof(thII02,conjecture,
    ( ! [F,G,H,A,B,C,D] :
        ( ( maps(F,A,B)
          & maps(G,B,C)
          & maps(H,C,D) )
       => equal_maps(compose_function(H,compose_function(G,F,A,B,C),A,C,D),compose_function(compose_function(H,G,B,C,D),F,A,B,D),A,D) ) )).

%--------------------------------------------------------------------------
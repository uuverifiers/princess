%--------------------------------------------------------------------------
% File     : SET727+4 : TPTP v6.1.0. Bugfixed v2.2.1.
% Domain   : Set Theory (Mappings)
% Problem  : If GoF and FoH are identities, then inverse(F) = H
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.68 v6.1.0, 0.77 v6.0.0, 0.78 v5.5.0, 0.81 v5.4.0, 0.89 v5.2.0, 0.85 v5.1.0, 0.86 v5.0.0, 0.92 v4.1.0, 0.96 v3.7.0, 0.95 v3.3.0, 0.93 v3.2.0, 0.91 v3.1.0, 0.89 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.88 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   29 (   1 unit)
%            Number of atoms       :  134 (   6 equality)
%            Maximal formula depth :   19 (   9 average)
%            Number of connectives :  107 (   2 ~  ;   2  |;  54  &)
%                                         (  30 <=>;  19 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   16 (   0 propositional; 2-6 arity)
%            Number of functors    :   15 (   1 constant; 0-5 arity)
%            Number of variables   :  138 (   0 singleton; 129 !;   9 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixes : v2.2.1 - Bugfixes in SET006+1.ax.
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include mappings axioms
include('Axioms/SET006+1.ax').
%--------------------------------------------------------------------------
fof(thII18,conjecture,
    ( ! [F,G,H,A,B] :
        ( ( maps(F,A,B)
          & maps(G,B,A)
          & maps(H,B,A)
          & identity(compose_function(G,F,A,B,A),A)
          & identity(compose_function(F,H,B,A,B),B) )
       => equal_maps(inverse_function(F,A,B),H,B,A) ) )).

%--------------------------------------------------------------------------

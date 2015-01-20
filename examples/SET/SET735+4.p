%--------------------------------------------------------------------------
% File     : SET735+4 : TPTP v6.1.0. Bugfixed v2.2.1.
% Domain   : Set Theory (Mappings)
% Problem  : Property of mappings
% Version  : [Pas99] axioms.
% English  : If GoF1 and GoF2 are identities,and the images of A by F1
%            and F2 are equal, then F1 and F2 are equal.

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.92 v6.1.0, 0.97 v6.0.0, 0.96 v5.2.0, 0.95 v5.0.0, 0.96 v3.7.0, 0.95 v3.3.0, 0.93 v3.2.0, 0.91 v3.1.0, 0.89 v2.7.0, 0.67 v2.6.0, 0.71 v2.5.0, 0.88 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   29 (   1 unit)
%            Number of atoms       :  135 (   6 equality)
%            Maximal formula depth :   19 (   9 average)
%            Number of connectives :  108 (   2 ~  ;   2  |;  55  &)
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
fof(thII26,conjecture,
    ( ! [F1,F2,G,A,B] :
        ( ( maps(F1,A,B)
          & maps(F2,A,B)
          & maps(G,B,A)
          & identity(compose_function(G,F1,A,B,A),A)
          & identity(compose_function(G,F2,A,B,A),A)
          & equal_set(image3(F1,A,B),image3(F2,A,B)) )
       => equal_maps(F1,F2,A,B) ) )).

%--------------------------------------------------------------------------

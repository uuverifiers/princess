%--------------------------------------------------------------------------
% File     : SET762+4 : TPTP v6.1.0. Bugfixed v2.2.1.
% Domain   : Set Theory (Mappings)
% Problem  : The image of empty set is empty
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.16 v6.1.0, 0.27 v6.0.0, 0.30 v5.5.0, 0.41 v5.4.0, 0.43 v5.3.0, 0.44 v5.2.0, 0.35 v5.1.0, 0.38 v5.0.0, 0.42 v4.1.0, 0.39 v4.0.0, 0.42 v3.7.0, 0.45 v3.5.0, 0.42 v3.4.0, 0.47 v3.3.0, 0.43 v3.2.0, 0.45 v3.1.0, 0.56 v2.7.0, 0.33 v2.6.0, 0.43 v2.5.0, 0.50 v2.4.0, 0.50 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :   29 (   1 unit)
%            Number of atoms       :  130 (   6 equality)
%            Maximal formula depth :   19 (   9 average)
%            Number of connectives :  103 (   2 ~  ;   2  |;  50  &)
%                                         (  30 <=>;  19 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   16 (   0 propositional; 2-6 arity)
%            Number of functors    :   15 (   1 constant; 0-5 arity)
%            Number of variables   :  136 (   0 singleton; 127 !;   9 ?)
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
fof(thIIa12,conjecture,
    ( ! [F,A,B] :
        ( maps(F,A,B)
       => equal_set(image2(F,empty_set),empty_set) ) )).

%--------------------------------------------------------------------------

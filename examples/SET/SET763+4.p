%--------------------------------------------------------------------------
% File     : SET763+4 : TPTP v6.1.0. Bugfixed v2.2.1.
% Domain   : Set Theory (Mappings)
% Problem  : If the image of X is empty then X is empty
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.52 v6.1.0, 0.60 v6.0.0, 0.70 v5.5.0, 0.59 v5.4.0, 0.57 v5.3.0, 0.59 v5.2.0, 0.50 v5.1.0, 0.52 v5.0.0, 0.54 v4.1.0, 0.52 v4.0.1, 0.48 v4.0.0, 0.46 v3.7.0, 0.50 v3.5.0, 0.53 v3.4.0, 0.58 v3.3.0, 0.50 v3.2.0, 0.64 v3.1.0, 0.56 v2.7.0, 0.50 v2.6.0, 0.57 v2.5.0, 0.62 v2.4.0, 0.50 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :   29 (   1 unit)
%            Number of atoms       :  132 (   6 equality)
%            Maximal formula depth :   19 (   9 average)
%            Number of connectives :  105 (   2 ~  ;   2  |;  52  &)
%                                         (  30 <=>;  19 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   16 (   0 propositional; 2-6 arity)
%            Number of functors    :   15 (   1 constant; 0-5 arity)
%            Number of variables   :  137 (   0 singleton; 128 !;   9 ?)
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
fof(thIIa13,conjecture,
    ( ! [F,A,B,X] :
        ( ( maps(F,A,B)
          & subset(X,A)
          & equal_set(image2(F,X),empty_set) )
       => equal_set(X,empty_set) ) )).

%--------------------------------------------------------------------------
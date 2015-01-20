%--------------------------------------------------------------------------
% File     : SET746+4 : TPTP v6.1.0. Bugfixed v2.2.1.
% Domain   : Set Theory (Mappings)
% Problem  : If F and G and increasing, then GoF is increasing
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.72 v6.1.0, 0.80 v6.0.0, 0.83 v5.5.0, 0.85 v5.4.0, 0.93 v5.2.0, 0.90 v5.0.0, 0.92 v4.1.0, 0.91 v4.0.1, 0.96 v3.7.0, 0.95 v3.3.0, 0.93 v3.2.0, 0.91 v3.1.0, 0.89 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.88 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   29 (   1 unit)
%            Number of atoms       :  133 (   6 equality)
%            Maximal formula depth :   19 (   9 average)
%            Number of connectives :  106 (   2 ~  ;   2  |;  53  &)
%                                         (  30 <=>;  19 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   16 (   0 propositional; 2-6 arity)
%            Number of functors    :   15 (   1 constant; 0-5 arity)
%            Number of variables   :  141 (   0 singleton; 132 !;   9 ?)
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
fof(thII37,conjecture,
    ( ! [F,G,A,B,C,R,S,T] :
        ( ( maps(F,A,B)
          & maps(G,B,C)
          & increasing(F,A,R,B,S)
          & increasing(G,B,S,C,T) )
       => increasing(compose_function(G,F,A,B,C),A,R,C,T) ) )).

%--------------------------------------------------------------------------

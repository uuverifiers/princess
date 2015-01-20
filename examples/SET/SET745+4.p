%--------------------------------------------------------------------------
% File     : SET745+4 : TPTP v6.1.0. Bugfixed v2.2.1.
% Domain   : Set Theory (Mappings)
% Problem  : Problem on composition of mappings 10
% Version  : [Pas99] axioms.
% English  : Consider three mappings F1 from A1 to B,F2 from A2 to B,
%            F which is equal to F1 on A1 and to F2 on A2, then F is a
%            mapping from union(A1,A2) to B if and only if F1 and F2 are
%            equal on the intersection of A1 and A2.

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.84 v6.1.0, 0.83 v6.0.0, 0.87 v5.5.0, 0.89 v5.4.0, 0.93 v5.2.0, 0.95 v5.0.0, 0.96 v3.7.0, 0.95 v3.3.0, 0.93 v3.2.0, 0.91 v3.1.0, 0.89 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.88 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   29 (   1 unit)
%            Number of atoms       :  145 (   7 equality)
%            Maximal formula depth :   19 (   9 average)
%            Number of connectives :  118 (   2 ~  ;   3  |;  60  &)
%                                         (  32 <=>;  21 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   16 (   0 propositional; 2-6 arity)
%            Number of functors    :   15 (   1 constant; 0-5 arity)
%            Number of variables   :  144 (   0 singleton; 135 !;   9 ?)
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
fof(thII36,conjecture,
    ( ! [F1,F2,F,A1,A2,B] :
        ( ( maps(F1,A1,B)
          & maps(F2,A2,B)
          & ! [X,Y] :
              ( ( member(X,union(A1,A2))
                & member(Y,B) )
             => ( apply(F,X,Y)
              <=> ( ( member(X,A1)
                    & apply(F1,X,Y) )
                  | ( member(X,A2)
                    & apply(F2,X,Y) ) ) ) ) )
       => ( maps(F,union(A1,A2),B)
        <=> ! [X,Y1,Y2] :
              ( ( member(X,A1)
                & member(X,A2)
                & member(Y1,B)
                & member(Y2,B)
                & apply(F1,X,Y1)
                & apply(F2,X,Y2) )
             => Y1 = Y2 ) ) ) )).

%--------------------------------------------------------------------------

%--------------------------------------------------------------------------
% File     : SET788+1 : TPTP v6.1.0. Released v3.1.0.
% Domain   : Set theory
% Problem  : Symmetry of equality from set membership
% Version  : Especial.
% English  :

% Refs     : [Shu04] Shults (2004), Email to G. Sutcliffe
% Source   : [Shu04]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v5.3.0, 0.09 v5.2.0, 0.00 v4.0.0, 0.05 v3.7.0, 0.00 v3.3.0, 0.11 v3.2.0, 0.33 v3.1.0, 0.00 v2.5.0
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :    5 (   0 equality)
%            Maximal formula depth :    7 (   7 average)
%            Number of connectives :    4 (   0 ~  ;   0  |;   0  &)
%                                         (   3 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    5 (   0 singleton;   5 !;   0 ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
fof(prove_this,conjecture,
    ( ! [X,Y] :
        ( equalish(X,Y)
      <=> ! [Z] :
            ( a_member_of(Z,X)
          <=> a_member_of(Z,Y) ) )
   => ! [X,Y] :
        ( equalish(X,Y)
      <=> equalish(Y,X) ) )).
%--------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File     : KRS026+1 : TPTP v5.3.0. Released v3.1.0.
% Domain   : Knowledge Representation (Semantic Web)
% Problem  : The extension of OWL Thing may be a singleton in OWL DL
% Version  : Especial.
% English  :

% Refs     : [Bec03] Bechhofer (2003), Email to G. Sutcliffe
%          : [TR+04] Tsarkov et al. (2004), Using Vampire to Reason with OW
% Source   : [Bec03]
% Names    : consistent_Thing-Manifest004 [Bec03]

% Status   : Satisfiable

%----Thing and Nothing
tff(thing_type,type,(
    thing: $tType )).

tff(cowlThing_type,type,(
    cowlThing: thing > $o )).

tff(cowlNothing_type,type,(
    cowlNothing: thing > $o )).

tff(is_type,type,(
    is: thing )).

tff(axiom_0,axiom,
    ( ! [X: thing] :
        ( cowlThing(X)
        & ~ cowlNothing(X) ) )).

%----Enumeration cowlThing
tff(axiom_2,axiom,
    ( ! [X: thing] :
        ( cowlThing(X)
      <=> X = is ) )).

%------------------------------------------------------------------------------

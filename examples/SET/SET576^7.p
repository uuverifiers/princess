%------------------------------------------------------------------------------
% File     : SET576^7 : TPTP v6.1.0. Released v5.5.0.
% Domain   : Set Theory
% Problem  : Trybulec's 17th Boolean property of sets
% Version  : [Ben12] axioms.
% English  :

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
%          : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : s4-cumul-SET576+3 [Ben12]

% Status   : Theorem
% Rating   : 0.14 v5.5.0
% Syntax   : Number of formulae    :   79 (   1 unit;  39 type;  32 defn)
%            Number of atoms       :  470 (  36 equality; 163 variable)
%            Maximal formula depth :   14 (   6 average)
%            Number of connectives :  194 (   5   ~;   5   |;   9   &; 165   @)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  189 ( 189   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   44 (  39   :)
%            Number of variables   :  100 (   2 sgn;  34   !;   7   ?;  59   ^)
%                                         ( 100   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Include axioms for Modal logic S4 under cumulative domains
include('Axioms/LCL015^0.ax').
include('Axioms/LCL013^5.ax').
include('Axioms/LCL015^1.ax').
%------------------------------------------------------------------------------
thf(intersect_type,type,(
    intersect: mu > mu > $i > $o )).

thf(disjoint_type,type,(
    disjoint: mu > mu > $i > $o )).

thf(member_type,type,(
    member: mu > mu > $i > $o )).

thf(intersect_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [B: mu] :
          ( mforall_ind
          @ ^ [C: mu] :
              ( mequiv @ ( intersect @ B @ C )
              @ ( mexists_ind
                @ ^ [D: mu] :
                    ( mand @ ( member @ D @ B ) @ ( member @ D @ C ) ) ) ) ) ) )).

thf(disjoint_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [B: mu] :
          ( mforall_ind
          @ ^ [C: mu] :
              ( mequiv @ ( disjoint @ B @ C ) @ ( mnot @ ( intersect @ B @ C ) ) ) ) ) )).

thf(symmetry_of_intersect,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [B: mu] :
          ( mforall_ind
          @ ^ [C: mu] :
              ( mimplies @ ( intersect @ B @ C ) @ ( intersect @ C @ B ) ) ) ) )).

thf(prove_th17,conjecture,
    ( mvalid
    @ ( mforall_ind
      @ ^ [B: mu] :
          ( mforall_ind
          @ ^ [C: mu] :
              ( mimplies
              @ ( mforall_ind
                @ ^ [D: mu] :
                    ( mimplies @ ( member @ D @ B ) @ ( mnot @ ( member @ D @ C ) ) ) )
              @ ( disjoint @ B @ C ) ) ) ) )).

%------------------------------------------------------------------------------

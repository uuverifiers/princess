%------------------------------------------------------------------------------
% File     : SET027^7 : TPTP v6.1.0. Released v5.5.0.
% Domain   : Set Theory
% Problem  : Transitivity of subset
% Version  : [Ben12] axioms.
% English  :

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
%          : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : s4-cumul-SET027+3 [Ben12]

% Status   : Theorem
% Rating   : 0.43 v5.5.0
% Syntax   : Number of formulae    :   77 (   1 unit;  38 type;  32 defn)
%            Number of atoms       :  449 (  36 equality; 157 variable)
%            Maximal formula depth :   14 (   6 average)
%            Number of connectives :  178 (   5   ~;   5   |;   9   &; 149   @)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  186 ( 186   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   43 (  38   :)
%            Number of variables   :   97 (   2 sgn;  34   !;   7   ?;  56   ^)
%                                         (  97   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Include axioms for Modal logic S4 under cumulative domains
include('Axioms/LCL015^0.ax').
include('Axioms/LCL013^5.ax').
include('Axioms/LCL015^1.ax').
%------------------------------------------------------------------------------
thf(member_type,type,(
    member: mu > mu > $i > $o )).

thf(subset_type,type,(
    subset: mu > mu > $i > $o )).

thf(subset_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [B: mu] :
          ( mforall_ind
          @ ^ [C: mu] :
              ( mequiv @ ( subset @ B @ C )
              @ ( mforall_ind
                @ ^ [D: mu] :
                    ( mimplies @ ( member @ D @ B ) @ ( member @ D @ C ) ) ) ) ) ) )).

thf(reflexivity_of_subset,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [B: mu] :
          ( subset @ B @ B ) ) )).

thf(prove_transitivity_of_subset,conjecture,
    ( mvalid
    @ ( mforall_ind
      @ ^ [B: mu] :
          ( mforall_ind
          @ ^ [C: mu] :
              ( mforall_ind
              @ ^ [D: mu] :
                  ( mimplies @ ( mand @ ( subset @ B @ C ) @ ( subset @ C @ D ) ) @ ( subset @ B @ D ) ) ) ) ) )).

%------------------------------------------------------------------------------

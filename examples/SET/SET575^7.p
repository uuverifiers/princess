%------------------------------------------------------------------------------
% File     : SET575^7 : TPTP v6.1.0. Released v5.5.0.
% Domain   : Set Theory
% Problem  : Trybulec's 15th Boolean property of sets
% Version  : [Ben12] axioms.
% English  :

% Refs     : [Goe69] Goedel (1969), An Interpretation of the Intuitionistic
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : s4-cumul-GSE575+3 [Ben12]

% Status   : Theorem
% Rating   : 0.43 v5.5.0
% Syntax   : Number of formulae    :   77 (   1 unit;  38 type;  32 defn)
%            Number of atoms       :  488 (  36 equality; 165 variable)
%            Maximal formula depth :   19 (   6 average)
%            Number of connectives :  217 (   5   ~;   5   |;   9   &; 188   @)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  186 ( 186   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   43 (  38   :)
%            Number of variables   :   99 (   2 sgn;  34   !;   7   ?;  58   ^)
%                                         (  99   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : Goedel translation of SET575+3
%------------------------------------------------------------------------------
%----Include axioms for Modal logic S4 under cumulative domains
include('Axioms/LCL015^0.ax').
include('Axioms/LCL013^5.ax').
include('Axioms/LCL015^1.ax').
%------------------------------------------------------------------------------
thf(member_type,type,(
    member: mu > mu > $i > $o )).

thf(intersect_type,type,(
    intersect: mu > mu > $i > $o )).

thf(intersect_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [B: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [C: mu] :
                  ( mand
                  @ ( mbox_s4
                    @ ( mimplies @ ( mbox_s4 @ ( intersect @ B @ C ) )
                      @ ( mexists_ind
                        @ ^ [D: mu] :
                            ( mand @ ( mbox_s4 @ ( member @ D @ B ) ) @ ( mbox_s4 @ ( member @ D @ C ) ) ) ) ) )
                  @ ( mbox_s4
                    @ ( mimplies
                      @ ( mexists_ind
                        @ ^ [D: mu] :
                            ( mand @ ( mbox_s4 @ ( member @ D @ B ) ) @ ( mbox_s4 @ ( member @ D @ C ) ) ) )
                      @ ( mbox_s4 @ ( intersect @ B @ C ) ) ) ) ) ) ) ) ) )).

thf(symmetry_of_intersect,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [B: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [C: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( intersect @ B @ C ) ) @ ( mbox_s4 @ ( intersect @ C @ B ) ) ) ) ) ) ) ) )).

thf(prove_th15,conjecture,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [B: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [C: mu] :
                  ( mbox_s4
                  @ ( mimplies @ ( mbox_s4 @ ( intersect @ B @ C ) )
                    @ ( mexists_ind
                      @ ^ [D: mu] :
                          ( mand @ ( mbox_s4 @ ( member @ D @ B ) ) @ ( mbox_s4 @ ( member @ D @ C ) ) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------

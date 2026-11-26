import Checker

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Automorphism
open PEqualNP.Outside.L_meta_6581

def fastCoordinate (j : Fin 10) : Word :=
  Extended.pins.getD (([7,9,6,8,5,2,4,1,3,0] : List Nat).getD j.val 0) Extended.zero

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma fastCoordinate_eq : ∀ j : Fin 10, fastCoordinate j = coordinate j := by
  decide +kernel

def fastSwapMove (i j : Fin 10) : Move :=
  let lo := if i.val ≤ j.val then i else j
  let hi := if i.val ≤ j.val then j else i
  (fastCoordinate lo &&& ~~~fastCoordinate hi, fastCoordinate hi &&& ~~~fastCoordinate lo,
    Fin.ofNat 1024 (2^hi.val-2^lo.val))

lemma fastSwapMove_eq (i j : Fin 10) : fastSwapMove i j = swapMove i j := by
  simp only [fastSwapMove,swapMove,fastCoordinate_eq]

def fastSwapWords (swaps : List (Fin 10 × Fin 10)) : List Move :=
  swaps.map fun s => fastSwapMove s.1 s.2

lemma fastSwapWords_eq (swaps : List (Fin 10 × Fin 10)) : fastSwapWords swaps = swapWords swaps := by
  simp only [fastSwapWords,swapWords,fastSwapMove_eq]

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Automorphism

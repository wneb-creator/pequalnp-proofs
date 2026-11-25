import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590

def petersen (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def row (k : ℕ) (i : Fin 10) : Bool := k.testBit i.val

def swapTriple (i : Fin 10) : Fin 10 :=
  ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6] i

lemma swapTriple_involutive : Function.Involutive swapTriple := by
  change ∀ i : Fin 10, swapTriple (swapTriple i) = i
  decide

lemma swapTriple_zero : swapTriple 0 = 0 := rfl

set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
lemma petersen_swapTriple : ∀ x : Fin 10 → Bool,
    petersen (x ∘ swapTriple) = petersen x := by
  decide

lemma swapTriple_row772 : row 772 ∘ swapTriple = row 200 := by
  decide

lemma swapTriple_row200 : row 200 ∘ swapTriple = row 772 := by
  decide

end PEqualNP.Outside.L_meta_2590

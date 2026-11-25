import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

def gePetersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 0 && x 4 || x 0 && x 5 || x 1 && x 2 || x 1 && x 6 || x 2 && x 3 || x 2 && x 7 || x 3 && x 4 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 5 && x 8 || x 6 && x 8 || x 6 && x 9 || x 7 && x 9

def geMasks : List Nat :=
  [0, 0, 16, 2, 2, 20, 2, 10, 2, 16, 2, 32, 2, 80, 2, 130, 2, 258, 2, 514, 4, 1, 0, 0, 1, 4, 1, 9, 1, 20, 1, 36, 1, 64, 1, 129, 1, 257, 1, 513, 2, 9, 8, 2, 0, 0, 2, 8, 2, 18, 2, 34, 2, 72, 2, 128, 2, 258, 2, 514, 4, 5, 4, 18, 16, 4, 0, 0, 4, 16, 4, 36, 4, 68, 4, 144, 4, 256, 4, 516, 8, 1, 1, 10, 1, 5, 1, 8, 0, 0, 1, 40, 1, 65, 1, 129, 1, 257, 1, 512, 128, 1, 1, 130, 1, 5, 1, 9, 1, 144, 0, 0, 1, 65, 1, 128, 1, 256, 1, 513, 2, 257, 256, 2, 2, 260, 2, 10, 2, 18, 2, 34, 0, 0, 2, 130, 2, 256, 2, 512, 4, 5, 4, 34, 32, 4, 4, 40, 4, 20, 4, 32, 4, 68, 0, 0, 4, 260, 4, 512, 8, 9, 8, 10, 8, 36, 32, 8, 8, 48, 8, 32, 8, 64, 8, 136, 0, 0, 8, 520, 16, 65, 16, 18, 16, 20, 16, 72, 64, 16, 16, 48, 16, 64, 16, 128, 16, 272, 0, 0]

def geWitness (i j : Fin 10) (b : Bool) (v : Fin 10) : Bool :=
  (geMasks.getD (i.val * 20 + j.val * 2 + if b then 1 else 0) 0).testBit v.val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma ge_witness_checked : ∀ (i j : Fin 10) (b : Bool), i ≠ j →
    geWitness i j b i = false ∧ geWitness i j b j = b ∧
    gePetersen (geWitness i j b) = false ∧
    gePetersen (Function.update (geWitness i j b) i true) = true := by
  decide +kernel

lemma ge_depends_after_cofactor (i j : Fin 10) (h : i ≠ j) (b : Bool) :
    ∃ x : Fin 10 → Bool, x j = b ∧
      gePetersen (Function.update x i false) ≠ gePetersen (Function.update x i true) := by
  obtain ⟨hi, hj, hf, ht⟩ := ge_witness_checked i j b h
  refine ⟨geWitness i j b, hj, ?_⟩
  have hu : Function.update (geWitness i j b) i false = geWitness i j b := by
    rw [← hi, Function.update_eq_self]
  rw [hu, hf, ht]
  decide

end PEqualNP.Outside.L_meta_2592

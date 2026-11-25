import Mathlib

namespace PEqualNP.Outside.L_meta_2373

def edge (x : Fin 10 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5


def pairInput (a c : Fin 10) (i : Fin 10) : Bool := decide (i = a ∨ i = c)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma separator_exists : ∀ a b : Fin 10, a ≠ b → ∃ c : Fin 10,
    c ≠ a ∧ c ≠ b ∧ edge (pairInput a c) = true ∧ edge (pairInput b c) = false := by
  decide +kernel

lemma no_or_identification : ∀ a b : Fin 10, a ≠ b →
    ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ a → i ≠ b → x i = y i) ∧
      (x a || x b) = (y a || y b) ∧ edge x ≠ edge y := by
  intro a b hab
  obtain ⟨c, hca, hcb, ha, hb⟩ := separator_exists a b hab
  refine ⟨pairInput a c, pairInput b c, ?_, ?_, ?_⟩
  · intro i hia hib
    simp [pairInput, hia, hib]
  · simp [pairInput]
  · simp [ha, hb]

end PEqualNP.Outside.L_meta_2373

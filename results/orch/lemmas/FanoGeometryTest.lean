import Mathlib

namespace PEqualNP.Outside.L_meta_2583_aux.FanoGeometryTest

def edges : Finset (Fin 7 × Fin 7) :=
  Finset.univ.filter fun e => e.1 = e.2 ∨ e.1 = e.2 + 1 ∨ e.1 = e.2 + 3

lemma simple_exists : ∃ a : Fin 7, a = 0 := by decide +kernel

lemma unique : ∀ p p' : Fin 7, p ≠ p' →
    ∃ l : Fin 7, (p,l) ∈ edges ∧ (p',l) ∈ edges ∧
      ∀ k : Fin 7, (p,k) ∈ edges → (p',k) ∈ edges → k = l := by
  decide +kernel

end PEqualNP.Outside.L_meta_2583_aux.FanoGeometryTest

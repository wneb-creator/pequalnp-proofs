import Mathlib

namespace PEqualNP.Outside.L_lib_123_Audit

lemma exact_stack_summary_injective {b : ℕ} {S : Type}
    (summary : (Fin b → Bool) → S)
    (close : S → (Fin b → Bool) → Prop)
    (correct : ∀ u v, close (summary u) v ↔ u = v) :
    Function.Injective summary := by
  intro u v huv
  have h := (correct u u).mpr rfl
  rw [huv] at h
  exact ((correct v u).mp h).symm

lemma exact_stack_summary_cardinality {b : ℕ} {S : Type} [Fintype S]
    (summary : (Fin b → Bool) → S)
    (close : S → (Fin b → Bool) → Prop)
    (correct : ∀ u v, close (summary u) v ↔ u = v) :
    2 ^ b ≤ Fintype.card S := by
  have h := Fintype.card_le_of_injective summary
    (exact_stack_summary_injective summary close correct)
  simpa using h

lemma exact_stack_summary_bits {b c : ℕ}
    (summary : (Fin b → Bool) → (Fin c → Bool))
    (close : (Fin c → Bool) → (Fin b → Bool) → Prop)
    (correct : ∀ u v, close (summary u) v ↔ u = v) :
    b ≤ c := by
  have hcard : 2 ^ b ≤ 2 ^ c := by
    simpa using exact_stack_summary_cardinality summary close correct
  by_contra h
  have hcb : c < b := by omega
  have hpow : (2 : ℕ) ^ c < 2 ^ b := Nat.pow_lt_pow_right (by decide) hcb
  omega

end PEqualNP.Outside.L_lib_123_Audit

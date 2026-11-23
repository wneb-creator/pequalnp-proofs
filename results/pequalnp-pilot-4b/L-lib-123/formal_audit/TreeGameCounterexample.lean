import Mathlib

namespace PEqualNP.Outside.L_lib_123_Audit

lemma unqueried_leaf_can_change_parity (n : ℕ) (Q : Finset (Fin n))
    (hQ : Q ≠ Finset.univ) :
    ∃ f : Fin n → ZMod 2, (∀ i ∈ Q, f i = 0) ∧ ∑ i, f i = 1 := by
  classical
  have hmissing : ∃ k : Fin n, k ∉ Q := by
    by_contra h
    push_neg at h
    exact hQ (Finset.eq_univ_of_forall h)
  obtain ⟨k, hk⟩ := hmissing
  refine ⟨fun i => if i = k then 1 else 0, ?_, ?_⟩
  · intro i hi
    have hik : i ≠ k := by
      rintro rfl
      exact hk hi
    simp [hik]
  · simp

lemma adaptive_parity_claim_passes (n : ℕ) :
    ∀ Q : Finset (Fin n), Q ≠ Finset.univ →
      ∃ f : Fin n → ZMod 2, (∀ i ∈ Q, f i = 0) ∧ ∑ i, f i = 1 :=
  fun Q hQ => unqueried_leaf_can_change_parity n Q hQ

lemma actual_zero_leaf_parity (n : ℕ) :
    (∑ _ : Fin n, (0 : ZMod 2)) ≠ 1 := by
  simp

end PEqualNP.Outside.L_lib_123_Audit

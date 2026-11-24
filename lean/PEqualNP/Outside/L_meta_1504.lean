import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1504 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (t : Fin N → (Fin N → Bool) → Bool), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → (∀ l0 : Fin N, Monotone (t l0)) → (∀ (x y : Fin N → Bool), (∀ l1 : Fin N, (Finset.univ.filter (fun p1 : Fin N => I p1 l1 ∧ x p1 = true)).card ≤ 2) → (∃ l2 : Fin N, y l2 = true ∧ t l2 x = true) → ∃ p3 l3 : Fin N, I p3 l3 ∧ x p3 = true ∧ y l3 = true) → (∀ p4 l4 : Fin N, I p4 l4 → ∃ l5 : Fin N, decide (l5 = l4) = true ∧ t l5 (fun k4 : Fin N => decide (k4 = p4)) = true) → ∀ (l6 : Fin N) (z : Fin N → Bool), (∀ l7 : Fin N, (Finset.univ.filter (fun p7 : Fin N => I p7 l7 ∧ z p7 = true)).card ≤ 2) → (t l6 z = true ↔ ∃ p8 : Fin N, I p8 l6 ∧ z p8 = true) := by
  intro N I _ t _ hMono hBelow hTrue l6 z hz
  constructor
  · intro h
    obtain ⟨p3, l3, hI, hx, hy⟩ := hBelow z (fun k => decide (k = l6)) hz ⟨l6, by simp, h⟩
    have : l3 = l6 := by simpa using hy
    subst this
    exact ⟨p3, hI, hx⟩
  · rintro ⟨p8, hI, hzp⟩
    obtain ⟨l5, hl5, ht⟩ := hTrue p8 l6 hI
    have : l5 = l6 := by simpa using hl5
    subst this
    have hle : (fun k : Fin N => decide (k = p8)) ≤ z := by
      intro k
      by_cases hk : k = p8
      · subst hk
        simp [hzp]
      · simp [hk]
    have h2 := hMono l5 hle
    rw [ht] at h2
    revert h2
    cases t l5 z <;> simp

import Mathlib.Data.Finset.Basic

namespace PEqualNP.Outside.L_meta_2602_aux.PureClause

def BitMonotone {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

lemma and_clause (n : ℕ) (A : Finset (Fin n)) (f g : (Fin n → Bool) → Bool)
    (hf : BitMonotone f) (hg : BitMonotone g)
    (hspec : ∀ x, (f x && g x) = true ↔ ∃ i ∈ A, x i = true) :
    (∀ x, f x = true ↔ ∃ i ∈ A, x i = true) ∨
      (∀ x, g x = true ↔ ∃ i ∈ A, x i = true) := by
  let z : Fin n → Bool := fun i => decide (i ∉ A)
  have hz : ¬∃ i ∈ A, z i = true := by simp [z]
  have recover (h : (Fin n → Bool) → Bool) (hm : BitMonotone h)
      (hlow : ∀ x, (∃ i ∈ A, x i = true) → h x = true)
      (hzero : h z = false) : ∀ x, h x = true ↔ ∃ i ∈ A, x i = true := by
    intro x
    constructor
    · intro hh
      by_contra hno
      have hle : ∀ i, x i = true → z i = true := by
        intro i hi
        simp only [z, decide_eq_true_eq]
        intro hiA
        exact hno ⟨i, hiA, hi⟩
      have ht := hm x z hle hh
      rw [hzero] at ht
      contradiction
    · exact hlow x
  have hlowf : ∀ x, (∃ i ∈ A, x i = true) → f x = true := by
    intro x hx
    exact (Bool.and_eq_true_iff.mp ((hspec x).2 hx)).1
  have hlowg : ∀ x, (∃ i ∈ A, x i = true) → g x = true := by
    intro x hx
    exact (Bool.and_eq_true_iff.mp ((hspec x).2 hx)).2
  cases hF : f z
  · exact Or.inl (recover f hf hlowf hF)
  · have hG : g z = false := by
      cases hG : g z
      · rfl
      · exact False.elim (hz ((hspec z).1 (by simp [hF, hG])))
    exact Or.inr (recover g hg hlowg hG)

end PEqualNP.Outside.L_meta_2602_aux.PureClause

import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17902 : ∀ (x1 x2 x3 : (Fin (10 : ℕ) → Bool) → Bool), (∀ (x4 : Fin (10 : ℕ) → Bool), x1 x4 = Bool.false → x2 x4 = Bool.false ∧ x3 x4 = Bool.false) → (¬∃ (x5 : Fin (10 : ℕ) → Bool), x1 x5 = Bool.true ∧ x2 x5 = Bool.false ∧ x3 x5 = Bool.false) → ∀ (x6 : Fin (10 : ℕ) → Bool), x1 x6 = (x2 x6 || x3 x6) := by
  intro x1 x2 x3 h1 h2 x6
  have h3 := h1 x6
  have h4 : ¬ (x1 x6 = true ∧ x2 x6 = false ∧ x3 x6 = false) := fun h => h2 ⟨x6, h⟩
  cases ha : x1 x6 <;> cases hb : x2 x6 <;> cases hc : x3 x6 <;> simp_all

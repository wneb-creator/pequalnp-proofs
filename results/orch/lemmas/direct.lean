import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_meta_2592

lemma oneNot_join_obligation {n : ℕ}
    (A B G F : (Fin n → Bool) → Bool)
    (monoF : Monotone F) (monoG : Monotone G)
    (formula : ∀ x, F x = (B x || (A x && !G x)))
    (x y : Fin n → Bool)
    (fx : F x = true) (by0 : B x = false)
    (ay : A y = true) (fy : F y = false) :
    A x = true ∧ G x = false ∧ G y = true ∧ B (x ⊔ y) = true := by
  have hx := formula x
  rw [fx, by0] at hx
  have ax : A x = true := by
    cases ha : A x
    · simp only [ha, Bool.false_and, Bool.false_or] at hx
      cases hx
    · rfl
  have gx : G x = false := by
    cases hg : G x
    · rfl
    · simp only [hg, Bool.not_true, Bool.and_false, Bool.false_or] at hx
      cases hx
  have hy := formula y
  rw [fy, ay] at hy
  have gy : G y = true := by
    cases hg : G y
    · simp only [hg, Bool.not_false, Bool.true_and, Bool.or_true] at hy
      cases hy
    · rfl
  have fjoin : F (x ⊔ y) = true := by
    have h := monoF (show x ≤ x ⊔ y from le_sup_left)
    rw [fx] at h
    cases hf : F (x ⊔ y)
    · rw [hf] at h
      exact False.elim ((by decide : ¬ (true : Bool) ≤ false) h)
    · rfl
  have gjoin : G (x ⊔ y) = true := by
    have h := monoG (show y ≤ x ⊔ y from le_sup_right)
    rw [gy] at h
    cases hg : G (x ⊔ y)
    · rw [hg] at h
      exact False.elim ((by decide : ¬ (true : Bool) ≤ false) h)
    · rfl
  have hjoin := formula (x ⊔ y)
  rw [fjoin, gjoin] at hjoin
  have bjoin : B (x ⊔ y) = true := by
    simpa only [Bool.not_true, Bool.and_false, Bool.or_false] using hjoin.symm
  exact ⟨ax, gx, gy, bjoin⟩

end PEqualNP.Outside.L_meta_2592

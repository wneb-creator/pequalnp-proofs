import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Basic

namespace PEqualNP.Outside.L_meta_2685

lemma and_below_linear {α : Type*} (A : Finset α)
    (f g : (α → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x && g x) = true → ∃ a ∈ A, x a = true) :
    (∀ x, f x = true → ∃ a ∈ A, x a = true) ∨
      (∀ x, g x = true → ∃ a ∈ A, x a = true) := by
  classical
  by_cases hfA : ∀ x, f x = true → ∃ a ∈ A, x a = true
  · exact Or.inl hfA
  right
  intro y hgy
  by_contra hy
  obtain ⟨x, hx⟩ := not_forall.mp hfA
  obtain ⟨hfx, hx⟩ := not_imp.mp hx
  let z : α → Bool := fun a => x a || y a
  have hxz : x ≤ z := by
    intro a
    change x a ≤ (x a || y a)
    cases x a <;> cases y a <;> decide
  have hyz : y ≤ z := by
    intro a
    change y a ≤ (x a || y a)
    cases x a <;> cases y a <;> decide
  have hfz : f z = true := le_antisymm le_top (hfx ▸ hf hxz)
  have hgz : g z = true := le_antisymm le_top (hgy ▸ hg hyz)
  obtain ⟨a, ha, hza⟩ := h z (by simp only [hfz, hgz, Bool.and_self])
  have hxa : x a = false := by
    cases hxa : x a
    · rfl
    · exact False.elim (hx ⟨a, ha, hxa⟩)
  have hya : y a = false := by
    cases hya : y a
    · rfl
    · exact False.elim (hy ⟨a, ha, hya⟩)
  simp only [z, hxa, hya, Bool.or_self, Bool.false_eq_true] at hza

end PEqualNP.Outside.L_meta_2685

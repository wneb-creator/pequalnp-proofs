import Mathlib.Data.Bool.Basic
import Mathlib.Order.Monotone.Basic

namespace PEqualNP.Outside.L_meta_2592.ComparableNot

lemma replace_by_true {α : Type*} (G : α → Bool → Bool) (h f : α → Bool)
    (mono : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (below : h ≤ f) : ∀ x, G x true = f x := by
  intro x
  have order := mono x (show false ≤ true from by decide)
  have computes := correct x
  have compare := below x
  cases hh : h x <;> cases hf : f x <;>
    cases ht : G x true <;> cases hz : G x false <;>
    simp_all [Bool.le_iff_imp]

lemma replace_by_false {α : Type*} (G : α → Bool → Bool) (h f : α → Bool)
    (mono : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (above : f ≤ h) : ∀ x, G x false = f x := by
  intro x
  have order := mono x (show false ≤ true from by decide)
  have computes := correct x
  have compare := above x
  cases hh : h x <;> cases hf : f x <;>
    cases ht : G x true <;> cases hz : G x false <;>
    simp_all [Bool.le_iff_imp]

end PEqualNP.Outside.L_meta_2592.ComparableNot

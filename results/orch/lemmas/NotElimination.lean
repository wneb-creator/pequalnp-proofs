import Mathlib

namespace PEqualNP.Outside.L_meta_2592.NotElimination

lemma replace_not_by_true {α : Type} (G : α → Bool → Bool) (h f : α → Bool)
    (compute : ∀ x, f x = G x (!(h x)))
    (mono : ∀ x, G x false = true → G x true = true)
    (implicant : ∀ x, h x = true → f x = true) :
    ∀ x, G x true = f x := by
  intro x
  have hc := compute x
  have hm := mono x
  have hi := implicant x
  cases hh : h x <;> cases hg0 : G x false <;> cases hg1 : G x true <;> simp_all

lemma replace_not_by_false {α : Type} (G : α → Bool → Bool) (h f : α → Bool)
    (compute : ∀ x, f x = G x (!(h x)))
    (mono : ∀ x, G x false = true → G x true = true)
    (upper : ∀ x, f x = true → h x = true) :
    ∀ x, G x false = f x := by
  intro x
  have hc := compute x
  have hm := mono x
  have hu := upper x
  cases hh : h x <;> cases hg0 : G x false <;> cases hg1 : G x true <;> simp_all

end PEqualNP.Outside.L_meta_2592.NotElimination

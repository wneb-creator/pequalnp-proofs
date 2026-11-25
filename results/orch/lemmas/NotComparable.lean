import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

lemma replace_not_true_of_operand_le {α : Type} (f h : α → Bool)
    (G : α → Bool → Bool) (mono : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x) (bound : ∀ x, h x ≤ f x) :
    ∀ x, G x true = f x := by
  intro x
  have hle := bound x
  have hm := mono x (show false ≤ true by decide)
  have hc := correct x
  cases hh : h x <;> cases hf : f x <;>
    cases hzero : G x false <;> cases hone : G x true <;> simp_all
  all_goals first
    | exact (by decide : ¬ ((true : Bool) ≤ false)) hle
    | exact (by decide : ¬ ((true : Bool) ≤ false)) hm

lemma replace_not_false_of_target_le {α : Type} (f h : α → Bool)
    (G : α → Bool → Bool) (mono : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x) (bound : ∀ x, f x ≤ h x) :
    ∀ x, G x false = f x := by
  intro x
  have hle := bound x
  have hm := mono x (show false ≤ true by decide)
  have hc := correct x
  cases hh : h x <;> cases hf : f x <;>
    cases hzero : G x false <;> cases hone : G x true <;> simp_all
  all_goals first
    | exact (by decide : ¬ ((true : Bool) ≤ false)) hle
    | exact (by decide : ¬ ((true : Bool) ≤ false)) hm

end PEqualNP.Outside.L_meta_2592_aux

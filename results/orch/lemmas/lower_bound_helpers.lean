import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

lemma erase_last_not_true {α : Type*} (f h : α → Bool) (G : α → Bool → Bool)
    (correct : ∀ x, G x (!h x) = f x)
    (mono : ∀ x, Monotone (G x))
    (contained : ∀ x, h x = true → f x = true) :
    ∀ x, G x true = f x := by
  intro x
  cases hh : h x with
  | false => simpa only [hh, Bool.not_false] using correct x
  | true =>
    have hc : G x false = true := by
      simpa only [hh, Bool.not_true, contained x hh] using correct x
    have hm := mono x (show false ≤ true by decide)
    rw [hc] at hm
    rw [contained x hh]
    cases hg : G x true <;> simp_all
    exact (by decide : ¬ ((true : Bool) ≤ false)) hm

lemma erase_last_not_false {α : Type*} (f h : α → Bool) (G : α → Bool → Bool)
    (correct : ∀ x, G x (!h x) = f x)
    (mono : ∀ x, Monotone (G x))
    (contained : ∀ x, f x = true → h x = true) :
    ∀ x, G x false = f x := by
  intro x
  cases hh : h x with
  | true => simpa only [hh, Bool.not_true] using correct x
  | false =>
    have hf : f x = false := by
      cases hfx : f x <;> simp_all
    have hc : G x true = false := by
      simpa only [hh, Bool.not_false, hf] using correct x
    have hm := mono x (show false ≤ true by decide)
    rw [hc] at hm
    rw [hf]
    cases hg : G x false <;> simp_all
    exact (by decide : ¬ ((true : Bool) ≤ false)) hm

end PEqualNP.Outside.L_meta_2592_aux

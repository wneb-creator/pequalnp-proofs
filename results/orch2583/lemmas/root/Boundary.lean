import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux

lemma eq_of_minimal_true_maximal_false {α : Type*} [Preorder α] [Finite α]
    (f g : α → Bool) (hg : Monotone g)
    (hp : ∀ x, Minimal (fun y => f y = true) x → g x = true)
    (hn : ∀ x, Maximal (fun y => f y = false) x → g x = false) : f = g := by
  classical
  funext x
  cases hx : f x with
  | false =>
    obtain ⟨y, hxy, hy⟩ := (Set.toFinite {y | f y = false}).exists_le_maximal hx
    have hm := hg hxy
    have hh := hn y hy
    cases hgx : g x <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) hm
  | true =>
    obtain ⟨y, hyx, hy⟩ := (Set.toFinite {y : OrderDual α | f y = true}).exists_le_maximal hx
    have hm := hg hyx
    have hh := hp y hy
    cases hgx : g x <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) hm

end PEqualNP.Outside.L_meta_2583_aux

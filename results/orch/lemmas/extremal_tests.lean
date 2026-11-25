import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.ExtremalTests

lemma eq_of_extremal_tests {α : Type*} [Fintype α] [PartialOrder α]
    (f g : α → Bool) (hf : Monotone f)
    (hpos : ∀ x, Minimal (fun y => g y = true) x → f x = true)
    (hneg : ∀ x, Maximal (fun y => g y = false) x → f x = false) :
    f = g := by
  classical
  funext x
  cases hx : g x with
  | false =>
      let s : Finset α := Finset.univ.filter fun y => g y = false
      have hxs : x ∈ s := by simp [s, hx]
      obtain ⟨y, hxy, hy⟩ := s.exists_le_maximal hxs
      have hmax : Maximal (fun z => g z = false) y := by
        simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hy
      have hfy := hneg y hmax
      have h := hf hxy
      cases hfx : f x with
      | false => rfl
      | true =>
          exact False.elim ((by decide : ¬ ((true : Bool) ≤ false))
            (by simpa only [hfx, hfy] using h))
  | true =>
      let s : Finset α := Finset.univ.filter fun y => g y = true
      have hxs : x ∈ s := by simp [s, hx]
      obtain ⟨y, hyx, hy⟩ := s.exists_le_minimal hxs
      have hmin : Minimal (fun z => g z = true) y := by
        simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hy
      have hfy := hpos y hmin
      have h := hf hyx
      cases hfx : f x with
      | false =>
          exact False.elim ((by decide : ¬ ((true : Bool) ≤ false))
            (by simpa only [hfx, hfy] using h))
      | true => rfl

end PEqualNP.Outside.L_meta_2583.ExtremalTests

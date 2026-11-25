import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux.Bracket

lemma low_replacement_of_generators {α : Type*} [Preorder α]
    (f h : α → Bool) (G : α → Bool → Bool) (E : Finset α)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (generators : ∀ x, f x = true → ∃ e ∈ E, e ≤ x ∧ f e = true)
    (allH : ∀ e ∈ E, h e = true) :
    ∀ x, G x false = f x := by
  intro x
  have below : G x false ≤ f x := by
    rw [← correct x]
    apply monoZ x
    cases h x <;> decide
  cases hx : f x with
  | false =>
    rw [hx] at below
    cases hg : G x false with
    | false => rfl
    | true => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa [hg] using below))
  | true =>
    obtain ⟨e, he, hex, hfe⟩ := generators x hx
    have hge : G e false = true := by simpa [allH e he, hfe] using correct e
    have le : G e false ≤ G x false := monoX false hex
    rw [hge] at le
    cases hg : G x false with
    | false => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa [hg] using le))
    | true => rfl

lemma high_replacement_of_cogenerators {α : Type*} [Preorder α]
    (f h : α → Bool) (G : α → Bool → Bool) (M : Finset α)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (cogenerators : ∀ x, f x = false → ∃ m ∈ M, x ≤ m ∧ f m = false)
    (allH : ∀ m ∈ M, h m = false) :
    ∀ x, G x true = f x := by
  intro x
  have above : f x ≤ G x true := by
    rw [← correct x]
    apply monoZ x
    cases h x <;> decide
  cases hx : f x with
  | false =>
    obtain ⟨m, hm, hxm, hfm⟩ := cogenerators x hx
    have hgm : G m true = false := by simpa [allH m hm, hfm] using correct m
    have le : G x true ≤ G m true := monoX true hxm
    rw [hgm] at le
    cases hg : G x true with
    | false => rfl
    | true => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa [hg] using le))
  | true =>
    rw [hx] at above
    cases hg : G x true with
    | false => exact False.elim ((by decide : ¬ (true ≤ false)) (by simpa [hg] using above))
    | true => rfl

lemma critical_generator {α : Type*} [Preorder α]
    (f h : α → Bool) (G : α → Bool → Bool) (E : Finset α)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (generators : ∀ x, f x = true → ∃ e ∈ E, e ≤ x ∧ f e = true)
    (changed : ∃ x, G x false ≠ f x) :
    ∃ e ∈ E, h e = false := by
  classical
  by_contra! no
  have allH : ∀ e ∈ E, h e = true := by
    intro e he
    have ne := no e he
    cases hh : h e <;> simp_all
  obtain ⟨x, hx⟩ := changed
  exact hx (low_replacement_of_generators f h G E monoX monoZ correct generators allH x)

lemma critical_cogenerator {α : Type*} [Preorder α]
    (f h : α → Bool) (G : α → Bool → Bool) (M : Finset α)
    (monoX : ∀ z, Monotone (fun x => G x z))
    (monoZ : ∀ x, Monotone (G x))
    (correct : ∀ x, G x (!(h x)) = f x)
    (cogenerators : ∀ x, f x = false → ∃ m ∈ M, x ≤ m ∧ f m = false)
    (changed : ∃ x, G x true ≠ f x) :
    ∃ m ∈ M, h m = true := by
  classical
  by_contra! no
  have allH : ∀ m ∈ M, h m = false := by
    intro m hm
    have ne := no m hm
    cases hh : h m <;> simp_all
  obtain ⟨x, hx⟩ := changed
  exact hx (high_replacement_of_cogenerators f h G M monoX monoZ correct cogenerators allH x)

end PEqualNP.Outside.L_meta_2592_aux.Bracket

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.PureOrAbsorption

variable {α : Type} [DecidableEq α]

def Increasing (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def Hits (S : Finset α) (x : α → Bool) : Prop := ∃ i ∈ S, x i = true

theorem and_below_or {f g : (α → Bool) → Bool} (hf : Increasing f) (hg : Increasing g)
    (S : Finset α) (below : ∀ x, (f x && g x) = true → Hits S x) :
    (∀ x, f x = true → Hits S x) ∨ (∀ x, g x = true → Hits S x) := by
  classical
  let z : α → Bool := fun i => decide (i ∉ S)
  have nz : ¬ Hits S z := by
    rintro ⟨i, hi, hx⟩
    simp [z, hi] at hx
  have drop (h : (α → Bool) → Bool) (hm : Increasing h) (hz : h z = false) :
      ∀ x, h x = true → Hits S x := by
    intro x hx
    by_contra hn
    have le : ∀ i, x i = true → z i = true := by
      intro i hi
      have ni : i ∉ S := fun mem => hn ⟨i, mem, hi⟩
      simp [z, ni]
    have bad := hm x z le hx
    rw [hz] at bad
    contradiction
  cases ef : f z with
  | false => exact Or.inl (drop f hf ef)
  | true =>
    have eg : g z = false := by
      cases he : g z with
      | false => rfl
      | true => exact (nz (below z (by simp [ef, he]))).elim
    exact Or.inr (drop g hg eg)

theorem and_pure_or_alias {f g : (α → Bool) → Bool} (hf : Increasing f) (hg : Increasing g)
    (S : Finset α) (exactOr : ∀ x, (f x && g x) = true ↔ Hits S x) :
    (∀ x, f x = true ↔ Hits S x) ∨ (∀ x, g x = true ↔ Hits S x) := by
  rcases and_below_or hf hg S (fun x => (exactOr x).mp) with left | right
  · refine Or.inl (fun x => ⟨left x, ?_⟩)
    intro hx
    have h := (exactOr x).mpr hx
    cases ef : f x <;> cases eg : g x <;> simp_all
  · refine Or.inr (fun x => ⟨right x, ?_⟩)
    intro hx
    have h := (exactOr x).mpr hx
    cases ef : f x <;> cases eg : g x <;> simp_all

end PEqualNP.Outside.L_meta_4970_aux.PureOrAbsorption

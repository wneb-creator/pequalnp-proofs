import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451

theorem ocFilterSplit {α : Type*} (xs : List α) (A B : α → Bool) (x y : Bool)
    (hx : x = true → ∀ i ∈ xs, A i = true)
    (hy : y = true → ∀ i ∈ xs, B i = true) :
    ((x || y) && xs.any (fun i => A i && B i)) =
      ((x && xs.any B) || (y && xs.any A)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨hxy, i, hi, hAi, hBi⟩
    rcases hxy with hxt | hyt
    · exact Or.inl ⟨hxt, i, hi, hBi⟩
    · exact Or.inr ⟨hyt, i, hi, hAi⟩
  · rintro (⟨hxt, i, hi, hBi⟩ | ⟨hyt, i, hi, hAi⟩)
    · exact ⟨Or.inl hxt, i, hi, hx hxt i hi, hBi⟩
    · exact ⟨Or.inr hyt, i, hi, hAi, hy hyt i hi⟩

theorem ocFilterCollapse {α : Type*} (xs : List α) (A B : α → Bool) (x y : Bool)
    (hx : x = true → ∀ i ∈ xs, A i = true)
    (hy : y = true → ∀ i ∈ xs, B i = true) :
    ((x || y) && xs.any (fun i => A i && B i)) =
      (((x || y) && xs.any A) && xs.any B) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨hxy, i, hi, hAi, hBi⟩
    exact ⟨⟨hxy, i, hi, hAi⟩, i, hi, hBi⟩
  · rintro ⟨⟨hxy, hA⟩, hB⟩
    rcases hxy with hxt | hyt
    · obtain ⟨i, hi, hBi⟩ := hB
      exact ⟨Or.inl hxt, i, hi, hx hxt i hi, hBi⟩
    · obtain ⟨i, hi, hAi⟩ := hA
      exact ⟨Or.inr hyt, i, hi, hAi, hy hyt i hi⟩

end PEqualNP.Outside.L_meta_3451

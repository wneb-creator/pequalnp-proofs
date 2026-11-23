import Mathlib

namespace PriorRoutes.Meta952

/-- On a face where the desired output has exactly one zero, a single negative
input can be frozen to its value at that zero. This is a semantic restriction
lemma, not a global gate-count inequality. -/
theorem freeze_negation_on_unique_zero_face {α : Type} [PartialOrder α]
    (F : α → Bool → Bool) (h target : α → Bool) (z : α)
    (hmono : ∀ x, z ≤ x → h z = true → h x = true)
    (Fmono : ∀ x, F x false = true → F x true = true)
    (correct : ∀ x, F x (!h x) = target x)
    (unique_zero : ∀ x, z ≤ x → target x = false → x = z) :
    ∀ x, z ≤ x → F x (!h z) = target x := by
  intro x hx
  cases hz : h z with
  | false =>
    simp only [Bool.not_false]
    cases ht : target x with
    | false =>
      have hh : h x = false := by rw [unique_zero x hx ht]; exact hz
      simpa [hh, ht] using correct x
    | true =>
      have hc := correct x
      rw [ht] at hc
      cases hh : h x with
      | false => simpa [hh] using hc
      | true => exact Fmono x (by simpa [hh] using hc)
  | true =>
    have hh := hmono x hx hz
    simpa [hz, hh] using correct x

end PriorRoutes.Meta952

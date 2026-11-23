import Mathlib

namespace PriorRoutes.Meta921

theorem small_context_misses_line {α : Type} [DecidableEq α]
    (S R B C : Finset α) (hS : S.card = 4)
    (hSR : (S ∩ R).card ≤ 1) (hB : B ⊆ R) (hC : C.card ≤ 2) :
    ¬ S ⊆ B ∪ C := by
  intro cover
  have sub : S ⊆ (S ∩ R) ∪ C := by
    intro p hp
    rcases Finset.mem_union.mp (cover hp) with hb | hc
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hp, hB hb⟩)
    · exact Finset.mem_union_right _ hc
  have h1 := Finset.card_le_card sub
  have h2 := Finset.card_union_le (S ∩ R) C
  omega

/-- A wire that forces a promised line-AND together with at most two fixed
context points cannot have a certificate of at most three points on another line. -/
theorem proper_certificate_ownership {α : Type} [DecidableEq α]
    (S R C : Finset α) (wire output : Finset α → Prop)
    (hS : S.card = 4) (hSR : (S ∩ R).card ≤ 1) (hC : C.card ≤ 2)
    (mono : Monotone wire)
    (context : ∀ X, C ⊆ X → wire X → output X)
    (correct : ∀ X, X.card ≤ 5 → output X → S ⊆ X) :
    ∀ B ⊆ R, B.card ≤ 3 → ¬ wire B := by
  intro B hB hsize hw
  have hu : (B ∪ C).card ≤ 5 := by
    have := Finset.card_union_le B C
    omega
  have hout : output (B ∪ C) :=
    context (B ∪ C) Finset.subset_union_right (mono Finset.subset_union_left hw)
  exact small_context_misses_line S R B C hS hSR hB hC (correct _ hu hout)

end PriorRoutes.Meta921

import Mathlib

namespace PriorRoutes

/-- A universal seed can reject all adaptively chosen certificates if each fixed
certificate passes on few seeds and the seed universe dominates their union. -/
theorem seed_rejects_all {Seed Certificate : Type}
    [Fintype Seed] [Fintype Certificate]
    (passes : Seed → Certificate → Prop) [DecidableRel passes] (D : ℕ)
    (per_certificate : ∀ c, (Finset.univ.filter fun r => passes r c).card ≤ D)
    (large_field : Fintype.card Certificate * D < Fintype.card Seed) :
    ∃ r, ∀ c, ¬ passes r c := by
  classical
  let bad : Certificate → Finset Seed := fun c => Finset.univ.filter fun r => passes r c
  have union_bound : (Finset.univ.biUnion bad).card ≤ Fintype.card Certificate * D := by
    exact Finset.card_biUnion_le_card_mul Finset.univ bad D (by
      intro c _
      exact per_certificate c)
  by_contra h
  have covered : Finset.univ ⊆ Finset.univ.biUnion bad := by
    intro r _
    have : ∃ c, passes r c := by
      by_contra hn
      apply h
      exact ⟨r, fun c hc => hn ⟨c, hc⟩⟩
    obtain ⟨c, hc⟩ := this
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, by simp [bad, hc]⟩
  have := Finset.card_le_card covered
  simpa using (not_lt_of_ge (this.trans union_bound) large_field)

end PriorRoutes

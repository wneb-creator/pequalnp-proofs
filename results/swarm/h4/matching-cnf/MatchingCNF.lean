import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373_aux.MatchingCNF

lemma fewer_clauses_than_endpoint_choices (n : ℕ) (κ : Type*) [Fintype κ]
    (S : κ → Fin n → Bool → Bool)
    (covers : ∀ c j, S c j false = true ∨ S c j true = true)
    (few : Fintype.card κ < 2 ^ n) :
    ∃ x : Fin n → Bool, ∀ c, ∃ j, S c j (x j) = true := by
  classical
  let forbidden : κ → Fin n → Bool := fun c j => S c j false
  have not_surjective : ¬ Function.Surjective forbidden := by
    intro surj
    have hc := Fintype.card_le_of_surjective forbidden surj
    have he : Fintype.card (Fin n → Bool) = 2 ^ n := by simp
    rw [he] at hc
    omega
  obtain ⟨x, hx⟩ : ∃ x, ∀ c, forbidden c ≠ x := by
    simpa only [Function.Surjective, not_forall, not_exists] using not_surjective
  refine ⟨x, ?_⟩
  intro c
  have diff : ∃ j, forbidden c j ≠ x j := by
    by_contra! same
    exact hx c (funext same)
  obtain ⟨j, hj⟩ := diff
  refine ⟨j, ?_⟩
  have cover := covers c j
  change S c j false ≠ x j at hj
  cases h0 : S c j false <;> cases h1 : S c j true <;>
    cases hval : x j <;> simp_all

#print axioms fewer_clauses_than_endpoint_choices
end PEqualNP.Outside.L_meta_2373_aux.MatchingCNF

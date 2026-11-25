
namespace PEqualNP.Outside.L_meta_2583_aux.SingleOrSparse

/-- If every accepting sibling input has a certificate using at most q points,
  then the sibling is already below incidence when p is absent. -/
theorem sibling_below_of_small_certificates {P L q : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (unique : ∀ a b : Fin P, a ≠ b → ∃! l : Fin L, I a l ∧ I b l)
    (p : Fin P) (degree : (Finset.univ.filter (I p)).card = q + 1)
    (h : Finset (Fin P) → Finset (Fin L) → Bool)
    (K : Finset (Fin P) → Finset (Fin L) → Bool → Bool)
    (context_mono : ∀ A A' B B' t, A ⊆ A' → B ⊆ B' →
      K A B t = true → K A' B' t = true)
    (sibling_mono : ∀ A B B', B ⊆ B' → h A B = true → h A B' = true)
    (spec : ∀ A B, Incidence I A B ↔
      K (A.erase p) B (decide (p ∈ A) || h (A.erase p) B) = true)
    (small : ∀ A B, h A B = true →
      ∃ A' ⊆ A, A'.card ≤ q ∧ h A' B = true)
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (absent : p ∉ A) (sibling : h A B = true) : Incidence I A B := by
  by_contra negative
  obtain ⟨A', subset, bound, accepted⟩ := small A B sibling
  have absent' : p ∉ A' := fun hp => absent (subset hp)
  have negative' : ¬ Incidence I A' B := by
    rintro ⟨a, ha, l, hl, hal⟩
    exact negative ⟨a, subset ha, l, hl, hal⟩
  have lower := sibling_false_card I unique p degree h K context_mono sibling_mono
    spec A' B absent' negative' accepted
  omega

/-- In particular, a sibling depending on at most q point inputs is below
  incidence when p is absent. Its dependence on line inputs is unrestricted. -/
theorem sibling_below_of_small_support {P L q : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (unique : ∀ a b : Fin P, a ≠ b → ∃! l : Fin L, I a l ∧ I b l)
    (p : Fin P) (degree : (Finset.univ.filter (I p)).card = q + 1)
    (h : Finset (Fin P) → Finset (Fin L) → Bool)
    (K : Finset (Fin P) → Finset (Fin L) → Bool → Bool)
    (context_mono : ∀ A A' B B' t, A ⊆ A' → B ⊆ B' →
      K A B t = true → K A' B' t = true)
    (sibling_mono : ∀ A B B', B ⊆ B' → h A B = true → h A B' = true)
    (spec : ∀ A B, Incidence I A B ↔
      K (A.erase p) B (decide (p ∈ A) || h (A.erase p) B) = true)
    (T : Finset (Fin P)) (bound : T.card ≤ q)
    (support : ∀ A B, h (A ∩ T) B = h A B)
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (absent : p ∉ A) (sibling : h A B = true) : Incidence I A B := by
  apply sibling_below_of_small_certificates I unique p degree h K context_mono
    sibling_mono spec ?_ A B absent sibling
  intro A B accepted
  exact ⟨A ∩ T, Finset.inter_subset_left,
    (Finset.card_le_card Finset.inter_subset_right).trans bound,
    (support A B).trans accepted⟩

end PEqualNP.Outside.L_meta_2583_aux.SingleOrSparse

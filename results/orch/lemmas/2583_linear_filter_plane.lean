namespace PEqualNP.Outside.L_meta_2583

lemma plane_opposite_neighborhoods_not_vertex_cover (q N : Nat)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p l : Fin N) (S T : Finset (Fin N))
    (hS : ∀ s ∈ S, I s l) (hT : ∀ t ∈ T, I p t) :
    ¬ (∀ a b, I a b → a ∈ S ∨ b ∈ T) := by
  classical
  obtain ⟨σ, hσ⟩ := PlaneMatching.plane_perfect_matching q N I (by omega) hN hl hu
  have hp : (Finset.univ.filter (fun b => I p b)).card ≤ q + 1 := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      PlaneMatching.plane_point_degree_le q N
        (fun b => Finset.univ.filter (fun a => I a b)) (by omega) hN hl
        (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hu) p
  exact small_opposite_neighborhoods_not_cover I hq hN σ hσ p l
    (le_of_eq (hl l)) hp S T hS hT

lemma plane_one_extra_edge_linear_filter_impossible (q N : Nat)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p l : Fin N) (nonincident : ¬ I p l) (S T : Finset (Fin N)) :
    ¬ (∀ X Y : Finset (Fin N),
      (((∃ a ∈ X, ∃ b ∈ Y, I a b) ∨ (p ∈ X ∧ l ∈ Y)) ∧
        ((X ∩ S).Nonempty ∨ (Y ∩ T).Nonempty)) ↔
      (∃ a ∈ X, ∃ b ∈ Y, I a b)) := by
  intro repair
  obtain ⟨cover, hs, ht⟩ := one_extra_edge_filter_constraints I p l nonincident S T repair
  exact plane_opposite_neighborhoods_not_vertex_cover q N I hq hN hl hu p l S T hs ht cover

end PEqualNP.Outside.L_meta_2583

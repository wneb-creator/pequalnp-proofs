import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602.GraphSearch

abbrev plane : SimpleGraph (Fin 26) :=
  SimpleGraph.fromRel fun a b : Fin 26 =>
    a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + 26 - b.val) % 13 ∈ [0, 1, 3, 9]

theorem incidence_pair : ∀ p l : Fin 13,
    plane.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 l) ↔
      p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9 := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem edge_count : plane.edgeFinset.card = 52 := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem no_four_cycle : PEqualNP.TopForm.NoFourCycle plane := by
  decide

theorem diagonal_edge (p : Fin 13) :
    plane.Adj (Fin.castAdd 13 p) (Fin.natAdd 13 p) :=
  (incidence_pair p p).mpr (Or.inl rfl)

theorem cover_at_least_thirteen (T : Finset (Fin 26))
    (cover : ∀ u v : Fin 26, plane.Adj u v → u ∈ T ∨ v ∈ T) :
    13 ≤ T.card := by
  let f : Fin 13 → Fin 26 := fun p =>
    if Fin.castAdd 13 p ∈ T then Fin.castAdd 13 p else Fin.natAdd 13 p
  have mem (p : Fin 13) : f p ∈ T := by
    dsimp only [f]
    split_ifs with h
    · exact h
    · exact (cover _ _ (diagonal_edge p)).resolve_left h
  have inj : Function.Injective f := by
    intro p q eq
    dsimp only [f] at eq
    split_ifs at eq with hp hq
    · exact Fin.ext (congrArg Fin.val eq)
    · have vals := congrArg Fin.val eq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at vals
      have := p.isLt
      omega
    · have vals := congrArg Fin.val eq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at vals
      have := q.isLt
      omega
    · apply Fin.ext
      have vals := congrArg Fin.val eq
      simp only [Fin.val_natAdd] at vals
      omega
  have sub : Finset.univ.image f ⊆ T := by
    intro v hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
    exact mem p
  have bound := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin] at bound
  exact bound

theorem sixty_four_of_edge_cover_bound (s : ℕ)
    (bound : ∃ T : Finset (Fin 26),
      (∀ u v : Fin 26, plane.Adj u v → u ∈ T ∨ v ∈ T) ∧
      plane.edgeFinset.card + T.card ≤ s + 1) : 64 ≤ s := by
  obtain ⟨T, cover, bound⟩ := bound
  have lower := cover_at_least_thirteen T cover
  rw [edge_count] at bound
  omega

end PEqualNP.Outside.L_meta_2602.GraphSearch

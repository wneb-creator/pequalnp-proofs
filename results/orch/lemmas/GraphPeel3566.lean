import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.MetaComplexity.CoverPromise

theorem cut_adj {n : ℕ} (G : SimpleGraph (Fin n)) (z u v : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj u v ↔ G.Adj u v ∧ u ≠ z ∧ v ≠ z := by
  exact SimpleGraph.deleteIncidenceSet_adj

theorem exists_positive_cut_edge (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧
      ∃ u v : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj u v := by
  classical
  obtain ⟨e, he, f, hf, hne⟩ := Finset.one_lt_card.mp (show 1 < G.edgeFinset.card by omega)
  induction e using Sym2.inductionOn with
  | hf a b =>
    induction f using Sym2.inductionOn with
    | hf c d =>
      have hab : G.Adj a b := by simpa using he
      have hcd : G.Adj c d := by simpa using hf
      have hab' : a ≠ b := G.ne_of_adj hab
      have hout : (a ≠ c ∧ a ≠ d) ∨ (b ≠ c ∧ b ≠ d) := by
        by_cases hac : a = c <;> by_cases had : a = d <;>
          by_cases hbc : b = c <;> by_cases hbd : b = d <;>
          simp_all
      rcases hout with ⟨hac, had⟩ | ⟨hbc, hbd⟩
      · exact ⟨a, (G.degree_pos_iff_exists_adj a).mpr ⟨b, hab⟩, c, d,
          (cut_adj G a c d).mpr ⟨hcd, hac.symm, had.symm⟩⟩
      · exact ⟨b, (G.degree_pos_iff_exists_adj b).mpr ⟨a, hab.symm⟩, c, d,
          (cut_adj G b c d).mpr ⟨hcd, hbc.symm, hbd.symm⟩⟩

theorem exists_positive_cut_nonempty (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧
      (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty := by
  classical
  obtain ⟨z, hz, u, v, huv⟩ := exists_positive_cut_edge n G h
  exact ⟨z, hz, s(u, v), by simpa using huv⟩

theorem cut_edge_card (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (z : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).edgeFinset.card + G.degree z = G.edgeFinset.card := by
  classical
  change (G.deleteIncidenceSet z).edgeFinset.card + G.degree z = G.edgeFinset.card
  rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset z)

theorem exists_min_cover (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ S : Finset (Fin n), IsVertexCover G S ∧
      ∀ T : Finset (Fin n), IsVertexCover G T → S.card ≤ T.card := by
  classical
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n), IsVertexCover G S ∧ S.card = k :=
    ⟨Finset.univ.card, Finset.univ, by intro u v h; simp, rfl⟩
  obtain ⟨S, hS, hSk⟩ := Nat.find_spec hex
  refine ⟨S, hS, ?_⟩
  intro T hT
  have := Nat.find_min' hex (show ∃ S : Finset (Fin n), IsVertexCover G S ∧ S.card = T.card
    from ⟨T, hT, rfl⟩)
  omega

theorem cut_cover_of_cover {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S : Finset (Fin n)) (hS : IsVertexCover G S) :
    IsVertexCover (G.deleteEdges (G.incidenceSet z)) S := by
  intro u v h
  exact hS u v ((cut_adj G z u v).mp h).1

theorem cover_insert_of_cut_cover {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S : Finset (Fin n)) (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S) :
    IsVertexCover G (insert z S) := by
  intro u v h
  by_cases hu : u = z
  · exact Or.inl (by simp [hu])
  by_cases hv : v = z
  · exact Or.inr (by simp [hv])
  rcases hS u v ((cut_adj G z u v).mpr ⟨h, hu, hv⟩) with h | h
  · exact Or.inl (Finset.mem_insert_of_mem h)
  · exact Or.inr (Finset.mem_insert_of_mem h)

theorem cut_cover_erase {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S : Finset (Fin n)) (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S) :
    IsVertexCover (G.deleteEdges (G.incidenceSet z)) (S.erase z) := by
  intro u v h
  have hne := (cut_adj G z u v).mp h
  rcases hS u v h with hu | hv
  · exact Or.inl (Finset.mem_erase.mpr ⟨hne.2.1, hu⟩)
  · exact Or.inr (Finset.mem_erase.mpr ⟨hne.2.2, hv⟩)

theorem min_cover_cut_bounds {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S T : Finset (Fin n))
    (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S)
    (hSm : ∀ U : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) U →
      S.card ≤ U.card)
    (hT : IsVertexCover G T)
    (hTm : ∀ U : Finset (Fin n), IsVertexCover G U → T.card ≤ U.card) :
    S.card ≤ T.card ∧ T.card ≤ S.card + 1 := by
  refine ⟨hSm T (cut_cover_of_cover G z T hT), ?_⟩
  exact (hTm (insert z S) (cover_insert_of_cut_cover G z S hS)).trans
    (Finset.card_insert_le z S)

theorem cut_cover_drop_iff {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S T : Finset (Fin n))
    (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S)
    (hSm : ∀ U : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) U →
      S.card ≤ U.card)
    (hT : IsVertexCover G T)
    (hTm : ∀ U : Finset (Fin n), IsVertexCover G U → T.card ≤ U.card) :
    (∃ U : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) U ∧
      ∀ V : Finset (Fin n), IsVertexCover G V → U.card < V.card) ↔
      S.card + 1 = T.card := by
  have hb := min_cover_cut_bounds G z S T hS hSm hT hTm
  constructor
  · rintro ⟨U, hU, hUmin⟩
    have h1 := hSm U hU
    have h2 := hUmin T hT
    omega
  · intro h
    refine ⟨S, hS, ?_⟩
    intro V hV
    have := hTm V hV
    omega

end PEqualNP.Outside.L_meta_3566

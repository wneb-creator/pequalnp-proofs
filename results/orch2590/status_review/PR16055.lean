import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

-- Route through the top-form theory. Normalise to a least top-form circuit (h1), read off the
-- star sides and the junk behind every uncovered edge (h2) and the gate count (h3). With at most
-- one uncovered edge the count already gives 20 gates, since every vertex cover of the Petersen
-- graph minus one edge has 6 vertices. The case of two or more uncovered edges is h4.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.R_meta_2590_2
    (h1 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.edgeFinset.Nonempty → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x8 ∧ PEqualNP.TopForm.TopForm x2 x8 ∧ x8.size ≤ x4.size)
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
        (∀ a ∈ PEqualNP.TopForm.tops G C,
          Disjoint (PEqualNP.TopForm.side (n := n) C a 0) (PEqualNP.TopForm.side (n := n) C a 1) ∧
          (∀ u ∈ PEqualNP.TopForm.side (n := n) C a 0, ∀ v ∈ PEqualNP.TopForm.side (n := n) C a 1, G.Adj u v) ∧
          ((PEqualNP.TopForm.side (n := n) C a 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C a 1).card ≤ 1)) ∧
        ∀ u v : Fin n, s(u, v) ∈ PEqualNP.TopForm.Ustar G C →
          ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, ∃ h ∈ PEqualNP.TopForm.junk G C,
            PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
            PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h ∧
            PEqualNP.EdgeOwnership.gateVal n C h (PEqualNP.EdgeOwnership.pairInput u v) = true)
    (h3 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
        G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
            2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
            (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
          C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
        ∀ K : Finset (Fin n),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
          K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card)
    (h4 : ∀ (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
       G = PEqualNP.EdgeOwnership.edgeGraph 10 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] →
       PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
       let T : Finset ℕ := PEqualNP.TopForm.tops G D
       let C0 : Finset ℕ := PEqualNP.TopForm.centreless G D
       let J : Finset ℕ := PEqualNP.TopForm.junk G D
       let U : Finset (Sym2 (Fin 10)) := PEqualNP.TopForm.Ustar G D
       (∀ a ∈ T,
         let S : Fin 2 → Finset (Fin 10) := PEqualNP.TopForm.side D a
         Disjoint (S 0) (S 1) ∧ (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
       (∀ u v : Fin 10, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J, PEqualNP.EdgeOwnership.gateVal 10 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 10 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 10 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) →
       15 + (T \ C0).card + 2 * C0.card + J.card + (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ D.size + U.card + 1 →
       (∀ K : Finset (Fin 10), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ C0).card) →
       2 ≤ U.card → 20 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → ¬∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C hm hs he
  set P := PEqualNP.EdgeOwnership.edgeGraph 10 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] with hP
  have hnf : PEqualNP.TopForm.NoFourCycle P := by decide
  have hne : P.edgeFinset.Nonempty := by decide
  have hecard : P.edgeFinset.card = 15 := by decide
  have htable : ∀ x : Fin 10 → Bool, (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) = graphFun P ∅ x := by
    decide +kernel
  have hfun : PEqualNP.MetaComplexity.circuitFun 10 C = graphFun P ∅ := by
    funext x
    exact (he x).trans (htable x)
  -- every vertex cover of the Petersen graph minus at most one listed edge has 6 vertices
  have tau_dec : ∀ (T : Finset (Fin 10)) (i : Fin 16), ¬ (T.card ≤ 5 ∧
      ∀ k : Fin 15, k.val ≠ i.val → (((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).1 ∈ T ∨
        ((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).2 ∈ T)) := by
    decide +kernel
  have hadj : ∀ k : Fin 15, P.Adj ((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).1
      ((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).2 := by
    decide
  have hdist : ∀ k k' : Fin 15, k ≠ k' →
      s(((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).1, ((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).2) ≠
      s(((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k').1, ((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k').2) := by
    decide
  obtain ⟨D, hL, hT, hDs⟩ := h1 10 P C hne hm hfun
  obtain ⟨hstar, hoff⟩ := h2 10 P D hnf hne hL hT
  obtain ⟨hcnt, hcov⟩ := h3 10 P D hnf hne hL hT
  rw [hecard] at hcnt
  by_cases hu : 2 ≤ (PEqualNP.TopForm.Ustar P D).card
  · have h20 := h4 P D rfl hL hT hstar hoff hcnt hcov hu
    omega
  · classical
    set U := PEqualNP.TopForm.Ustar P D with hU
    have hU1 : U.card ≤ 1 := by omega
    have hcover6 : ∀ K : Finset (Fin 10), (P.deleteEdges ↑U).IsVertexCover (↑K : Set (Fin 10)) →
        6 ≤ K.card := by
      intro K hK
      have hcov' : ∀ k : Fin 15,
          s(((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).1, ((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).2) ∉ U →
          ((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).1 ∈ K ∨ ((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).2 ∈ K := by
        intro k hk
        have hd : (P.deleteEdges ↑U).Adj ((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).1
            ((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).2 :=
          SimpleGraph.deleteEdges_adj.mpr ⟨hadj k, fun h => hk (Finset.mem_coe.mp h)⟩
        exact hK hd
      by_contra hsmall
      by_cases hex : ∃ k : Fin 15,
          s(((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).1, ((![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : Fin 15 → Fin 10 × Fin 10) k).2) ∈ U
      · obtain ⟨k, hk⟩ := hex
        apply tau_dec K ⟨k.val, by have := k.isLt; omega⟩
        refine ⟨by omega, fun k' hne' => hcov' k' fun hk' => ?_⟩
        have hkk : k' ≠ k := fun h => hne' (congrArg Fin.val h)
        exact hdist k' k hkk (Finset.card_le_one.mp hU1 _ hk' _ hk)
      · apply tau_dec K (Fin.last 15)
        exact ⟨by omega, fun k' _ => hcov' k' fun hk' => hex ⟨k', hk'⟩⟩
    obtain ⟨K, hK, hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter fun T : Finset (Fin 10) => (P.deleteEdges ↑U).IsVertexCover (↑T : Set (Fin 10)))
      Finset.card ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        intro v w _
        exact Or.inl (Finset.mem_coe.mpr (Finset.mem_univ v))⟩⟩
    have hKmin : PEqualNP.MetaComplexity.NestedCover.IsMinCover (P.deleteEdges ↑U) K :=
      ⟨(Finset.mem_filter.mp hK).2, fun T' hT' => hmin T' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)⟩
    have h6 := hcover6 K (Finset.mem_filter.mp hK).2
    have ht := hcov K hKmin
    by_cases hu0 : U.card = 0
    · omega
    · have hj : 1 ≤ (PEqualNP.TopForm.junk P D).card := by
        obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
        induction e using Sym2.ind with
        | h u v =>
          obtain ⟨a, _, b, h, hh, _⟩ := hoff u v he
          have hpos := Finset.card_pos.mpr ⟨h, hh⟩
          omega
      omega

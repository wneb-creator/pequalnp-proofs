import PEqualNP.Defs

-- The profile bounds the loss of vertex-cover size after deleting u edges.
-- The circuit needs a charge only for u at least two; the first two entries vanish.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5968_71
    (profile : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj], G = PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      ∀ U ⊆ G.edgeFinset, ∀ S : Finset (Fin 11),
        (G.deleteEdges (U : Set (Sym2 (Fin 11)))).IsVertexCover (S : Set (Fin 11)) →
        5 + U.card ≤ S.card + ([0,0,2,4,5,7,8,9,11,12,13,14,16,17,18,19,21] : List ℕ).getD U.card 0)
    (charge : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj], G = PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → C.size < 22 →
        PEqualNP.TopForm.junk G C = {a,b} →
        let w := PEqualNP.TopForm.wmax G C
        let e := PEqualNP.TopForm.gammaE G C
        let v := PEqualNP.EdgeOwnership.gateVal 11 C
        let stars := fun j : ℕ => (e j).filter (fun t => ∃ z ∈ w j, z ∈ t)
        let inter := e a ∩ e b
        let good := ∀ x, v a x = true → v b x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true
        let U := PEqualNP.TopForm.Ustar G C
        (stars a).card ≤ 7 ∧ (stars b).card ≤ 7 ∧ (good → inter.card ≤ 8) ∧
          (good ∨ (w a ∩ w b).Nonempty) →
        (∀ t ∈ U, t ∈ stars a ∨ t ∈ stars b ∨ good ∧ t ∈ inter) →
        2 ≤ U.card →
        ([0,0,2,4,5,7,8,9,11,12,13,14,16,17,18,19,21] : List ℕ).getD U.card 0 ≤ 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           PEqualNP.TopForm.junk x1 x3 = {x4, x5} →             have x11 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x11 : ℕ) => {x12 ∈ PEqualNP.TopForm.gammaE x1 x3 x11 | ∃ x13 ∈ PEqualNP.TopForm.wmax x1 x3 x11, x13 ∈ x12};             have x12 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.gammaE x1 x3 x4 ∩ PEqualNP.TopForm.gammaE x1 x3 x5;             have x13 : Prop := ∀ (x13 : Fin (11 : ℕ) → Bool), PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x4 x13 = Bool.true → PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x5 x13 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x13 = Bool.true;             have x14 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             (x11 x4).card ≤ (7 : ℕ) ∧ (x11 x5).card ≤ (7 : ℕ) ∧ (x13 → x12.card ≤ (8 : ℕ)) ∧ (x13 ∨ (PEqualNP.TopForm.wmax x1 x3 x4 ∩ PEqualNP.TopForm.wmax x1 x3 x5).Nonempty) → (∀ x16 ∈ x14, x16 ∈ x11 x4 ∨ x16 ∈ x11 x5 ∨ x13 ∧ x16 ∈ x12) → ∃ (x17 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x14) x17 ∧ (5 : ℕ) + x14.card ≤ x17.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  classical
  intro G inst C a b hG hleast htop hsize hj
  have hcharge := charge G hG C a b hleast htop hsize hj
  dsimp only at hcharge ⊢
  intro hb hc
  let U := PEqualNP.TopForm.Ustar G C
  let K := G.deleteEdges (U : Set (Sym2 (Fin 11)))
  let covers := Finset.univ.filter (fun S : Finset (Fin 11) => K.IsVertexCover (S : Set (Fin 11)))
  have hall : (Finset.univ : Finset (Fin 11)) ∈ covers := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by intro u v huv; exact Or.inl (Finset.mem_univ _)⟩
  obtain ⟨S,hS,hmin⟩ := covers.exists_min_image Finset.card ⟨_, hall⟩
  have hcov := (Finset.mem_filter.mp hS).2
  refine ⟨S, ⟨hcov, fun R hR => hmin R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR⟩)⟩, ?_⟩
  have hs : U ⊆ _ := Finset.sdiff_subset
  have hp := profile G hG U hs S hcov
  by_cases ht : 2 ≤ U.card
  · have := hcharge hb hc ht
    change 5 + U.card ≤ _ 
    dsimp only [U] at hp ⊢
    omega
  · have hsmall : U.card = 0 ∨ U.card = 1 := by omega
    rcases hsmall with h | h <;> rw [h] at hp <;> norm_num [List.getD] at hp <;>
      change 5 + U.card ≤ _ <;> omega

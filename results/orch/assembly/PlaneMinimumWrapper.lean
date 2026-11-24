namespace PEqualNP.Outside.L_meta_1477.TwoProductCentreless

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma plane_minimum_junk_two_product_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hTF : TopForm planeGraph C)
    (hminjunk : ∀ D : Circuit, IsLeastAO planeGraph D → (junk planeGraph C).card ≤ (junk planeGraph D).card)
    (hjcard : 2 ≤ (junk planeGraph C).card)
    (g : Fin 2 → ℕ) (hgj : ∀ i, g i ∈ junk planeGraph C)
    (honto : ∀ j ∈ junk planeGraph C, ∃ i, g i = j)
    (hpure : ∀ i, ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR 42 C (opnd C (g i) b) (42+k))
    (hdis : ∀ i, Disjoint (side (n := 42) C (g i) 0) (side C (g i) 1))
    (hA : ∀ i, 2 ≤ (side (n := 42) C (g i) 0).card)
    (hB : ∀ i, 2 ≤ (side (n := 42) C (g i) 1).card)
    (hnojoint : ∀ j ∈ junk planeGraph C, ∀ k ∈ junk planeGraph C, j ≠ k → ∀ u v : Fin 42,
      gateVal 42 C j (pairInput u v) = true → gateVal 42 C k (pairInput u v) = true →
      ¬ GeneralDirtyPairs.JointClean planeGraph C j k) :
    125 ≤ C.size := by
  have hAO := P2.ao_of 42 C hL.1
  have hpureAll : ∀ j ∈ junk planeGraph C, ∀ b : Fin 2, ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and → ¬ P2.OrR 42 C (opnd C j b) (42+k) := by
    intro j hj
    obtain ⟨i,rfl⟩ := honto j hj
    exact hpure i
  have htwo : ∀ i, (cleanCenters planeGraph (side (n := 42) C (g i) 0) (side C (g i) 1)).card = 2 := by
    intro i
    have hg := (P1.junk_iff planeGraph C (g i)).mp (hgj i)
    have heff := FirstLayerEffective.minimum_junk_two_effective_centers planeGraph C hL hTF hminjunk
      (g i) (hgj i) hpureAll (hnojoint (g i) (hgj i)) (hdis i)
    exact ActualCleanCenters.two_clean_centers_of_effective planeGraph plane_no_four C hAO
      (g i) hg.1 hg.2.1 (hpure i) (hdis i) (hA i) (hB i) heff
  exact plane_two_product_size C hL hTF hjcard g hgj honto hpure hdis hA hB htwo hnojoint

end PEqualNP.Outside.L_meta_1477.TwoProductCentreless

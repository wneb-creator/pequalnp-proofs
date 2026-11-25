namespace PEqualNP.Outside.L_meta_4675.TopFormNormalization

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

theorem normalize_with_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (colour : ℕ → Bool) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C colour = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      tCount n D colour = 0 ∧ D.size ≤ C.size ∧
      (junk G D).card ≤ (junk G C).card ∧ TopForm G D := by
  classical
  let Good (D : Circuit) : Prop := IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
    tCount n D colour = 0 ∧ D.size ≤ C.size ∧ (junk G D).card ≤ (junk G C).card
  have hex : ∃ k : ℕ, ∃ D : Circuit, Good D ∧ andPairs n D = k :=
    ⟨andPairs n C, C, ⟨hAO, hfun, hz, le_rfl, le_rfl⟩, rfl⟩
  obtain ⟨D, hD, hk⟩ := Nat.find_spec hex
  obtain ⟨hAO_D, hfun_D, hz_D, hsize, hjunk⟩ := hD
  refine ⟨D, hAO_D, hfun_D, hz_D, hsize, hjunk, ?_⟩
  by_contra hnot
  obtain ⟨D', hAO_D', hfun_D', hz_D', hsize', hless, hjunk'⟩ :=
    PEqualNP.Outside.L_meta_4675.ProductiveStepWithJunk.improve
      n G D colour hAO_D hfun_D hz_D hnot
  have hGood : Good D' :=
    ⟨hAO_D', hfun_D', hz_D', hsize'.trans hsize, hjunk'.trans hjunk⟩
  have hle : andPairs n D ≤ andPairs n D' := by
    rw [hk]
    exact Nat.find_min' hex ⟨D', hGood, rfl⟩
  omega

end PEqualNP.Outside.L_meta_4675.TopFormNormalization

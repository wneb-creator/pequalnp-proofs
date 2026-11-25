namespace PEqualNP.Outside.L_meta_4675.TopFormNormalization

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

theorem normalize (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (colour : ℕ → Bool) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C colour = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      tCount n D colour = 0 ∧ D.size ≤ C.size ∧ TopForm G D := by
  classical
  obtain ⟨D, hD, hfunD, hzD, hsize, hmin⟩ :=
    PEqualNP.Outside.L_meta_4675.TopFormMinimization.exists_min_andPairs
      n C colour (graphFun G ∅) hAO hfun hz
  refine ⟨D, hD, hfunD, hzD, hsize, ?_⟩
  by_contra hnot
  obtain ⟨D', hD', hfunD', hzD', hsize', hless⟩ :=
    PEqualNP.Outside.L_meta_4675.ProductiveStep.improve n G D colour hD hfunD hzD hnot
  have hle := hmin D' hD' hfunD' hzD' (hsize'.trans hsize)
  omega

end PEqualNP.Outside.L_meta_4675.TopFormNormalization

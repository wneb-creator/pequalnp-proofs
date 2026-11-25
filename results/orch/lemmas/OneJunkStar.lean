namespace PEqualNP.Outside.L_meta_2448_aux.oneJunkStar

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma star_replacement_of_one_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (hE : G.edgeFinset.Nonempty) (h4 : NoFourCycle G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hg : junk G C = {g}) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      HasStarProfile n G D ∧ D.size ≤ C.size := by
  obtain ⟨K, hK, hbudget⟩ :=
    PEqualNP.Outside.L_meta_2448_aux.oneJunk.one_junk_cover_all G C g h4 htri hL hT hg
  obtain ⟨D, hD, hDf, hDs, hsize⟩ :=
    PEqualNP.Outside.L_meta_2448.StarCoverPrototype.star_cover_witness G hE K hK
  refine ⟨D, hD, hDf, hDs, ?_⟩
  omega

lemma mono_of_AO2 {n : ℕ} {C : Circuit} (h : IsAO2 n C) : Monotone2 C := by
  intro g hg
  constructor
  · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1 g hg
  · rw [h.2.2 g hg]

lemma posted_conclusion_of_one_junk_minimum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (hE : G.edgeFinset.Nonempty) (h4 : NoFourCycle G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hmin : IsMinimalMonoCircuit n C) (hT : TopForm G C) (hg : junk G C = {g}) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → D.size ≤ E.size) ∧
      HasStarProfile n G D := by
  have hL : IsLeastAO G C := ⟨hAO, hfun,
    fun E hE hEf => hmin.2 E (mono_of_AO2 hE) (hEf.trans hfun.symm)⟩
  obtain ⟨D, hD, hDf, hDs, hsize⟩ := star_replacement_of_one_junk G C g hE h4 htri hL hT hg
  exact ⟨D, hD, hDf, fun E hE hEf => hsize.trans (hmin.2 E hE (hEf.trans hfun.symm)), hDs⟩

end PEqualNP.Outside.L_meta_2448_aux.oneJunkStar

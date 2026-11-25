namespace PEqualNP.Outside.L_meta_2448_aux.oneJunkStar

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma star_of_no_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h4 : NoFourCycle G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hmono : Monotone2 C) (hzero : (junk G C).card = 0) : HasStarProfile n G C := by
  classical
  apply PEqualNP.Outside.L_meta_2448.cross.star_of_proper_pair_sound n G C htri h4 hmono
  intro j hj hop u v _ hval
  by_contra huv
  have hfalse : graphFun G ∅ (pairInput u v) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    exact huv ((PEqualNP.Outside.L_meta_3760.M1528.P1.S90.graphFun_pair G u v).mp ht)
  have hmem : j ∈ junk G C := by
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hop, hj, pairInput u v, hval, hfalse⟩
  rw [Finset.card_eq_zero.mp hzero] at hmem
  exact Finset.notMem_empty _ hmem

lemma empty_graph_star_minimum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hempty : G.edgeFinset = ∅) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → D.size ≤ E.size) ∧
      HasStarProfile n G D := by
  let D : Circuit := ⟨[], n⟩
  have hno : ∀ u v : Fin n, ¬ G.Adj u v := by
    intro u v huv
    have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  have hfun : circuitFun n D = graphFun G ∅ := by
    funext x
    simp [D, circuitFun, Circuit.eval, Circuit.wires, graphFun, hno,
      List.getD_eq_getElem?_getD]
  refine ⟨D, ?_, hfun, ?_, ?_⟩
  · intro g hg
    cases hg
  · intro E _ _
    exact Nat.zero_le _
  · intro j hj
    exact (Nat.not_lt_zero j hj).elim

lemma posted_conclusion_of_at_most_one_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h4 : NoFourCycle G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hmin : IsMinimalMonoCircuit n C) (hjunk : (junk G C).card ≤ 1) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → D.size ≤ E.size) ∧
      HasStarProfile n G D := by
  classical
  by_cases hzero : (junk G C).card = 0
  · exact ⟨C, hmin.1, hfun, fun E hE hEf => hmin.2 E hE (hEf.trans hfun.symm),
      star_of_no_junk G C h4 htri hmin.1 hzero⟩
  by_cases hE : G.edgeFinset.Nonempty
  · have hL : IsLeastAO G C := ⟨hAO, hfun,
      fun E hE hEf => hmin.2 E (mono_of_AO2 hE) (hEf.trans hfun.symm)⟩
    have hjunk1 : (junk G C).card = 1 := by omega
    obtain ⟨K, hK, hbudget⟩ :=
      PEqualNP.Outside.L_meta_2448_aux.oneJunk.least_single_junk_cover G C h4 htri hL hjunk1
    obtain ⟨D, hD, hDf, hDs, hsize⟩ :=
      PEqualNP.Outside.L_meta_2448.StarCoverPrototype.star_cover_witness G hE K hK
    have hsz : D.size ≤ C.size := by omega
    exact ⟨D, hD, hDf, fun E hE hEf => hsz.trans (hmin.2 E hE (hEf.trans hfun.symm)), hDs⟩
  · exact empty_graph_star_minimum G (Finset.not_nonempty_iff_eq_empty.mp hE)

end PEqualNP.Outside.L_meta_2448_aux.oneJunkStar

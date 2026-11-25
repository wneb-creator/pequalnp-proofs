import PEqualNP.Outside.L_meta_3760

namespace PEqualNP.Outside.L_meta_2448_aux.oneJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3760 PEqualNP.Outside.L_meta_3760.Close
open PEqualNP.Outside.L_meta_3760.M1528.P1.S98 (W AO AO_of_IsAO2 W_and)
open PEqualNP.Outside.L_meta_3760.M1528.P2 (OrR mem_orIn orR_mono opnd_eq graphFun_pair)

lemma cover_of_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (X0 : Finset (Fin n))
    (hXcov : ∀ e ∈ Ustar G C, ∃ v ∈ K ∪ X0, v ∈ e)
    (hbudget : (Ustar G C).card + (X0 \ K).card ≤
      (pen G C g K).card + (mixing G C).card + 2 * (centreless G C).card +
        (coneGates G C g).card + 1) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hfull : ∀ e ∈ G.edgeFinset, ∃ v ∈ K ∪ (X0 \ K), v ∈ e := by
    intro e he
    by_cases hS : e ∈ starEdges G C
    · obtain ⟨v, hv, hve⟩ := hKcov e hS
      exact ⟨v, Finset.mem_union_left _ hv, hve⟩
    · have hU : e ∈ Ustar G C := Finset.mem_sdiff.mpr ⟨he, hS⟩
      obtain ⟨v, hv, hve⟩ := hXcov e hU
      have hv' : v ∈ K ∪ (X0 \ K) := by
        rcases Finset.mem_union.mp hv with hvK | hvX
        · exact Finset.mem_union_left _ hvK
        · by_cases h : v ∈ K
          · exact Finset.mem_union_left _ h
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvX, h⟩)
      exact ⟨v, hv', hve⟩
  refine ⟨K ∪ (X0 \ K), hfull, ?_⟩
  have hcard : (K ∪ (X0 \ K)).card = K.card + (X0 \ K).card :=
    Finset.card_union_of_disjoint Finset.disjoint_sdiff
  omega

lemma one_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hg : junk G C = {g})
    (hUne : (Ustar G C).Nonempty)
    (hdisj : side (n := n) C g 0 ∩ side (n := n) C g 1 = ∅)
    (b : Fin 2) (zstar : Fin n) (hz_side : zstar ∈ side (n := n) C g b)
    (hU_inc : ∀ e ∈ Ustar G C, zstar ∈ e) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  let PU := (side (n := n) C g (1 - b)).filter fun p => s(p, zstar) ∈ Ustar G C
  have hU_eq : Ustar G C = PU.image (fun p => s(p, zstar)) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Finset.mem_image, PU, Finset.mem_filter]
      constructor
      · intro hU
        have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1
        have hz_in := hU_inc s(u, v) hU
        obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv hU
        obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg u v hgtrue
        have h1b : u ∈ side (n := n) C g (1 - b) ∨ v ∈ side (n := n) C g (1 - b) := by
          fin_cases b <;> [exact h1; exact h0]
        have hz_not_1b : zstar ∉ side (n := n) C g (1 - b) := by
          intro hmem
          have : zstar ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := by
            fin_cases b
            · exact Finset.mem_inter.mpr ⟨hz_side, hmem⟩
            · exact Finset.mem_inter.mpr ⟨hmem, hz_side⟩
          rw [hdisj] at this; exact Finset.notMem_empty _ this
        rcases Sym2.mem_iff.mp hz_in with rfl | rfl
        · rcases h1b with hu | hv
          · exact absurd hu hz_not_1b
          · exact ⟨v, ⟨hv, by rw [Sym2.eq_swap]; exact hU⟩, Sym2.eq_swap⟩
        · rcases h1b with hu | hv
          · exact ⟨u, ⟨hu, hU⟩, rfl⟩
          · exact absurd hv hz_not_1b
      · rintro ⟨p, ⟨_, hU⟩, heq⟩; rwa [← heq]
  have hPU_adj : ∀ p ∈ PU, G.Adj zstar p := by
    intro p hp
    exact (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).2).1).symm
  have hU_card : (Ustar G C).card = PU.card := by
    rw [hU_eq, Finset.card_image_of_injOn]
    intro p1 hp1 p2 hp2 heq
    have hadj := hPU_adj p1 hp1
    rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hadj.ne'
  have hPU_notStar : ∀ p ∈ PU, s(zstar, p) ∉ starEdges G C := fun p hp => by
    rw [Sym2.eq_swap]; exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).2).2
  let Cg1b := (coneGates G C g).filter fun h => OrR n C (opnd C g (1 - b)) (n + h)
  have hCg_le : Cg1b.card ≤ (coneGates G C g).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hlamPU : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ PU).card ≤ 1 :=
    lam_card_le_one_of_common_nbr G h4 C hL zstar PU hPU_adj (fun a _ ha _ _ => Or.inl (hPU_notStar a ha))
  have hcg1b : PU.card ≤ 1 + Cg1b.card :=
    g_cone_gate_count G C hL hT g hg (1 - b) PU (Finset.filter_subset _ _) hlamPU
  have hXcov : ∀ e ∈ Ustar G C, ∃ v ∈ K ∪ {zstar}, v ∈ e :=
    fun e he => ⟨zstar, Finset.mem_union_right _ (Finset.mem_singleton_self _), hU_inc e he⟩
  have hmixcl := ustar_ne_implies_mix_or_cl G C h4 hE hL hT g hg hUne
  have hxcard : (({zstar} : Finset (Fin n)) \ K).card ≤ 1 :=
    (Finset.card_le_card Finset.sdiff_subset).trans (by simp)
  apply cover_of_budget G C g K hKcov h1528 {zstar} hXcov
  omega

lemma two_centers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hg : junk G C = {g})
    (hUne : (Ustar G C).Nonempty)
    (hdisj : side (n := n) C g 0 ∩ side (n := n) C g 1 = ∅)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hP2 : 2 ≤ (side (n := n) C g 0).card) (hQ2 : 2 ≤ (side (n := n) C g 1).card)
    (pstar qstar : Fin n)
    (hpW : pstar ∈ wmax G C g) (hpP : pstar ∈ side (n := n) C g 0)
    (hqW : qstar ∈ wmax G C g) (hqQ : qstar ∈ side (n := n) C g 1)
    (hp1_ex : ∃ p1 ∈ side (n := n) C g 0, p1 ≠ pstar ∧ s(p1, qstar) ∈ Ustar G C)
    (hq1_ex : ∃ q1 ∈ side (n := n) C g 1, q1 ≠ qstar ∧ s(pstar, q1) ∈ Ustar G C) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hg_lt := (junk_single_props G C hL hT g hg).1
  obtain ⟨_, _, _, hW_iff, pb, hpbP, qb, hqbQ, hbad_nadj⟩ := g_semantics G C hL hT g hg
  have h1529 := thm_1529 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have h1530 := thm_1530 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have hp_adj_Q : ∀ q ∈ side (n := n) C g 1, G.Adj pstar q := (h1529.1 pstar hpW hpP).2
  have hq_adj_P : ∀ p ∈ side (n := n) C g 0, G.Adj qstar p := (h1529.2.1 qstar hqW hqQ).2
  have hpq_adj : G.Adj pstar qstar := hp_adj_Q qstar hqQ
  have hWP_eq : wmax G C g ∩ side (n := n) C g 0 = {pstar} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_inter.mpr ⟨hpW, hpP⟩, fun x hx =>
      Finset.card_le_one.mp (h1530.1 hQ2) x hx pstar (Finset.mem_inter.mpr ⟨hpW, hpP⟩)⟩
  have hWQ_eq : wmax G C g ∩ side (n := n) C g 1 = {qstar} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_inter.mpr ⟨hqW, hqQ⟩, fun x hx =>
      Finset.card_le_one.mp (h1530.2.1 hP2) x hx qstar (Finset.mem_inter.mpr ⟨hqW, hqQ⟩)⟩
  have hP_notW : ∀ p ∈ side (n := n) C g 0, p ≠ pstar → p ∉ wmax G C g := by
    intro p hpP' hne hpW'
    have : p ∈ wmax G C g ∩ side (n := n) C g 0 := Finset.mem_inter.mpr ⟨hpW', hpP'⟩
    rw [hWP_eq, Finset.mem_singleton] at this; exact hne this
  have hQ_notW : ∀ q ∈ side (n := n) C g 1, q ≠ qstar → q ∉ wmax G C g := by
    intro q hqQ' hne hqW'
    have : q ∈ wmax G C g ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hqW', hqQ'⟩
    rw [hWQ_eq, Finset.mem_singleton] at this; exact hne this
  let PU' := (side (n := n) C g 0).filter fun p => p ≠ pstar ∧ s(p, qstar) ∈ Ustar G C
  let QU' := (side (n := n) C g 1).filter fun q => q ≠ qstar ∧ s(pstar, q) ∈ Ustar G C
  have hU_class : ∀ e ∈ Ustar G C, e = s(pstar, qstar) ∨
      (∃ p ∈ PU', e = s(p, qstar)) ∨ (∃ q ∈ QU', e = s(pstar, q)) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
      obtain ⟨hgtrue, huvW, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
      obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg u v hgtrue
      have hPQ : (u ∈ side (n := n) C g 0 ∧ v ∈ side (n := n) C g 1) ∨
                 (v ∈ side (n := n) C g 0 ∧ u ∈ side (n := n) C g 1) := by
        rcases h0 with hu0 | hv0 <;> rcases h1 with hu1 | hv1
        · exfalso; have : u ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hu0, hu1⟩
          rw [hdisj] at this; exact Finset.notMem_empty _ this
        · exact Or.inl ⟨hu0, hv1⟩
        · exact Or.inr ⟨hv0, hu1⟩
        · exfalso; have : v ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hv0, hv1⟩
          rw [hdisj] at this; exact Finset.notMem_empty _ this
      rcases hPQ with ⟨huP, hvQ⟩ | ⟨hvP, huQ⟩
      · rcases huvW with huW | hvW
        · have hup : u = pstar := by
            have : u ∈ wmax G C g ∩ side (n := n) C g 0 := Finset.mem_inter.mpr ⟨huW, huP⟩
            rwa [hWP_eq, Finset.mem_singleton] at this
          subst hup
          by_cases hvq : v = qstar
          · subst hvq; exact Or.inl rfl
          · exact Or.inr (Or.inr ⟨v, Finset.mem_filter.mpr ⟨hvQ, hvq, he⟩, rfl⟩)
        · have hvq : v = qstar := by
            have : v ∈ wmax G C g ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hvW, hvQ⟩
            rwa [hWQ_eq, Finset.mem_singleton] at this
          subst hvq
          by_cases hup : u = pstar
          · subst hup; exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨u, Finset.mem_filter.mpr ⟨huP, hup, he⟩, rfl⟩)
      · rcases huvW with huW | hvW
        · have huq : u = qstar := by
            have : u ∈ wmax G C g ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨huW, huQ⟩
            rwa [hWQ_eq, Finset.mem_singleton] at this
          subst huq
          by_cases hvp : v = pstar
          · subst hvp; exact Or.inl Sym2.eq_swap
          · exact Or.inr (Or.inl ⟨v, Finset.mem_filter.mpr ⟨hvP, hvp, by rw [Sym2.eq_swap]; exact he⟩, Sym2.eq_swap⟩)
        · have hvp : v = pstar := by
            have : v ∈ wmax G C g ∩ side (n := n) C g 0 := Finset.mem_inter.mpr ⟨hvW, hvP⟩
            rwa [hWP_eq, Finset.mem_singleton] at this
          subst hvp
          by_cases huq : u = qstar
          · subst huq; exact Or.inl Sym2.eq_swap
          · exact Or.inr (Or.inr ⟨u, Finset.mem_filter.mpr ⟨huQ, huq, by rw [Sym2.eq_swap]; exact he⟩, Sym2.eq_swap⟩)
  let EP := PU'.image (fun p => s(p, qstar))
  let EQ := QU'.image (fun q => s(pstar, q))
  have hEP_card : EP.card = PU'.card := by
    rw [Finset.card_image_of_injOn]
    intro p1 hp1 p2 hp2 heq
    have hadj := hq_adj_P p1 (Finset.mem_filter.mp hp1).1
    rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hadj.ne'
  have hEQ_card : EQ.card = QU'.card := by
    rw [Finset.card_image_of_injOn]
    intro q1 hq1 q2 hq2 heq
    have hadj := hp_adj_Q q1 (Finset.mem_filter.mp hq1).1
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · exact absurd h.symm hadj.ne
  have hEP_EQ_disj : Disjoint EP EQ := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp h2
    have hp_ne := (Finset.mem_filter.mp hp).2.1
    have hq_ne := (Finset.mem_filter.mp hq).2.1
    rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨_, h⟩
    · exact hp_ne h.symm
    · exact hp_ne (by
        have : p ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 :=
          Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, h ▸ (Finset.mem_filter.mp hq).1⟩
        rw [hdisj] at this; exact (Finset.notMem_empty _ this).elim)
  have hspq_notEP : s(pstar, qstar) ∉ EP := by
    intro h
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
    have hp_ne := (Finset.mem_filter.mp hp).2.1
    rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hp_ne h1
    · have : p ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 :=
        Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, h1 ▸ hqQ⟩
      rw [hdisj] at this; exact Finset.notMem_empty _ this
  have hspq_notEQ : s(pstar, qstar) ∉ EQ := by
    intro h
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp h
    have hq_ne := (Finset.mem_filter.mp hq).2.1
    rcases Sym2.eq_iff.mp heq with ⟨_, h1⟩ | ⟨_, h1⟩
    · exact hq_ne h1
    · have : q ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 :=
        Finset.mem_inter.mpr ⟨h1 ▸ hpP, (Finset.mem_filter.mp hq).1⟩
      rw [hdisj] at this; exact Finset.notMem_empty _ this
  let Cg0 := (coneGates G C g).filter fun h => OrR n C (opnd C g 0) (n + h)
  let Cg1 := (coneGates G C g).filter fun h => OrR n C (opnd C g 1) (n + h)
  have hCg_disj : Disjoint Cg0 Cg1 := g_cones_disjoint G C hL hT g hg hdisj
  have hCg_sum : Cg0.card + Cg1.card ≤ (coneGates G C g).card := by
    rw [← Finset.card_union_of_disjoint hCg_disj]
    exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hCg0_lb : PU'.card ≤ Cg0.card := by
    let TP := insert pstar PU'
    have hp_not : pstar ∉ PU' := fun h => (Finset.mem_filter.mp h).2.1 rfl
    have hTP_sub : TP ⊆ side (n := n) C g 0 := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · exact hpP
      · exact (Finset.mem_filter.mp hp').1
    have hlamTP : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ TP).card ≤ 1 := by
      refine lam_card_le_one_of_common_nbr G h4 C hL qstar TP (fun p hp => hq_adj_P p (hTP_sub hp)) ?_
      intro u v hu hv huv
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact absurd rfl huv
        · exact Or.inr (by rw [Sym2.eq_swap]; exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv').2.2).2)
      · exact Or.inl (by rw [Sym2.eq_swap]; exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu').2.2).2)
    have h : TP.card ≤ 1 + Cg0.card := g_cone_gate_count G C hL hT g hg 0 TP hTP_sub hlamTP
    rw [Finset.card_insert_of_notMem hp_not] at h
    omega
  have hCg1_lb : QU'.card ≤ Cg1.card := by
    let TQ := insert qstar QU'
    have hq_not : qstar ∉ QU' := fun h => (Finset.mem_filter.mp h).2.1 rfl
    have hTQ_sub : TQ ⊆ side (n := n) C g 1 := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq'
      · exact hqQ
      · exact (Finset.mem_filter.mp hq').1
    have hlamTQ : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ TQ).card ≤ 1 := by
      refine lam_card_le_one_of_common_nbr G h4 C hL pstar TQ (fun q hq => hp_adj_Q q (hTQ_sub hq)) ?_
      intro u v hu hv huv
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact absurd rfl huv
        · exact Or.inr (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv').2.2).2
      · exact Or.inl (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu').2.2).2
    have h : TQ.card ≤ 1 + Cg1.card := g_cone_gate_count G C hL hT g hg 1 TQ hTQ_sub hlamTQ
    rw [Finset.card_insert_of_notMem hq_not] at h
    omega
  have hXcov : ∀ e ∈ Ustar G C, ∃ v ∈ K ∪ {pstar, qstar}, v ∈ e := by
    intro e he
    rcases hU_class e he with rfl | ⟨p, _, rfl⟩ | ⟨q, _, rfl⟩
    · exact ⟨pstar, Finset.mem_union_right _ (by simp), Sym2.mem_mk_left _ _⟩
    · exact ⟨qstar, Finset.mem_union_right _ (by simp), Sym2.mem_mk_right _ _⟩
    · exact ⟨pstar, Finset.mem_union_right _ (by simp), Sym2.mem_mk_left _ _⟩
  have hxcard : (({pstar, qstar} : Finset (Fin n)) \ K).card ≤ 2 :=
    (Finset.card_le_card Finset.sdiff_subset).trans Finset.card_le_two
  have hmixcl := ustar_ne_implies_mix_or_cl G C h4 hE hL hT g hg hUne
  apply cover_of_budget G C g K hKcov h1528 {pstar, qstar} hXcov
  by_cases hspqU : s(pstar, qstar) ∈ Ustar G C
  ·
    have hU_eq : Ustar G C = insert s(pstar, qstar) (EP ∪ EQ) := by
      ext e
      simp only [Finset.mem_insert, Finset.mem_union, EP, EQ, Finset.mem_image]
      constructor
      · intro he
        rcases hU_class e he with h | ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨p, hp, rfl⟩)
        · exact Or.inr (Or.inr ⟨q, hq, rfl⟩)
      · rintro (rfl | ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩)
        · exact hspqU
        · exact (Finset.mem_filter.mp hp).2.2
        · exact (Finset.mem_filter.mp hq).2.2
    have hU_card : (Ustar G C).card = PU'.card + QU'.card + 1 := by
      rw [hU_eq, Finset.card_insert_of_notMem (by simp [hspq_notEP, hspq_notEQ]),
        Finset.card_union_of_disjoint hEP_EQ_disj, hEP_card, hEQ_card]
    have hweight : 2 ≤ (mixing G C).card + 2 * (centreless G C).card := by
      by_cases hcl : 0 < (centreless G C).card
      · omega
      have hCL0 : (centreless G C).card = 0 := by omega
      obtain ⟨p1, hp1P, hp1_ne, hp1U⟩ := hp1_ex
      obtain ⟨q1, hq1Q, hq1_ne, hq1U⟩ := hq1_ex
      obtain ⟨_, _, htri_p⟩ := ustar_edge_structure G C h4 hE hL hT g hg p1 qstar
        (hq_adj_P p1 hp1P).symm hp1U
      rcases htri_p with ⟨a, haCL, _⟩ | ⟨a_p, ha_p_top, _, ba_p, _, m_p, hm_p_mix, hm_p_reach, hgm_p,
          y_p, hy_p_in, hy_p_ne, um_p, hum_p_y, _, _, z_p, hz_pW, hum_pz, hz_peq, hqstar_side, hformU_p, hformZ_p⟩
      · have := Finset.card_pos.mpr ⟨a, haCL⟩; omega
      have hzp_eq : z_p = qstar := by
        rcases hz_peq with h1 | h2
        · exact absurd (h1 ▸ hz_pW) (hP_notW p1 hp1P hp1_ne)
        · exact h2
      subst z_p
      obtain ⟨_, _, htri_q⟩ := ustar_edge_structure G C h4 hE hL hT g hg pstar q1
        (hp_adj_Q q1 hq1Q) hq1U
      rcases htri_q with ⟨a, haCL, _⟩ | ⟨a_q, ha_q_top, _, ba_q, _, m_q, hm_q_mix, hm_q_reach, hgm_q,
          y_q, hy_q_in, hy_q_ne, um_q, hum_q_y, _, _, z_q, hz_qW, hum_qz, hz_qeq, _, hformU_q, hformZ_q⟩
      · have := Finset.card_pos.mpr ⟨a, haCL⟩; omega
      have hzq_eq : z_q = pstar := by
        rcases hz_qeq with h1 | h2
        · exact h1
        · exact absurd (h2 ▸ hz_qW) (hQ_notW q1 hq1Q hq1_ne)
      subst z_q
      have hmq_ne_mp : m_q ≠ m_p := by
        intro heq; subst heq
        have hm_lt : m_q < C.gates.length := by
          simp only [mixing, orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hm_q_mix; exact hm_q_mix.1.1
        have hy_eq : y_q = y_p := by
          obtain ⟨_, i0, i1, hin, _, _⟩ := hA m_q hm_lt
          rw [hin] at hgm_q hy_q_in hy_p_in
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm_q hy_q_in hy_p_in
          rcases hgm_q with rfl | rfl <;> rcases hy_q_in with rfl | rfl <;> rcases hy_p_in with rfl | rfl <;>
            first | rfl | exact absurd rfl hy_q_ne | exact absurd rfl hy_p_ne
        subst hy_eq
        have humq_side_ap : um_q ∈ side (n := n) C a_p ba_p :=
          ((thm_1506 n G C h4 hE hL hT g hg m_q hm_q_mix hgm_q y_q hy_q_in hy_q_ne).2
            um_q hum_q_y a_p ha_p_top ba_p hm_p_reach).1
        simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha_p_top
        have hW0 := orR_mono n C hA (pairInput um_q qstar) (opnd C a_p ba_p) um_q.val
          ((mem_orIn n C hA _ (by have := opnd_lt' hA a_p ha_p_top.1 ba_p; omega) um_q).mp humq_side_ap)
          (by rw [M1528.P2.W_input n C _ um_q.val um_q.isLt]; simp [pairInput])
        have hW1 := orR_mono n C hA (pairInput um_q qstar) (opnd C a_p (1 - ba_p)) qstar.val
          ((mem_orIn n C hA _ (by have := opnd_lt' hA a_p ha_p_top.1 (1 - ba_p); omega) qstar).mp hqstar_side)
          (by rw [M1528.P2.W_input n C _ qstar.val qstar.isLt]; simp [pairInput])
        have hWa : W n C (pairInput um_q qstar) (n + a_p) = true := by
          rw [W_and n C _ a_p ha_p_top.1 ha_p_top.2.1 (opnd C a_p 0) (opnd C a_p 1) (opnd_eq n C hA a_p ha_p_top.1)
            (opnd_lt' hA a_p ha_p_top.1 0) (opnd_lt' hA a_p ha_p_top.1 1), Bool.and_eq_true]
          fin_cases ba_p <;> [exact ⟨hW0, hW1⟩; exact ⟨hW1, hW0⟩]
        have humq_adj_qstar : G.Adj um_q qstar := by
          have hF := ha_p_top.2.2 (pairInput um_q qstar) hWa; rwa [graphFun_pair] at hF
        exact htri pstar qstar um_q hpq_adj humq_adj_qstar.symm hum_qz
      have hmix2 : 2 ≤ (mixing G C).card := by
        have hsub : ({m_p, m_q} : Finset ℕ) ⊆ mixing G C := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have hcard := Finset.card_le_card hsub
        rwa [Finset.card_pair hmq_ne_mp.symm] at hcard
      omega
    omega
  ·
    have hU_eq : Ustar G C = EP ∪ EQ := by
      ext e
      simp only [Finset.mem_union, EP, EQ, Finset.mem_image]
      constructor
      · intro he
        rcases hU_class e he with rfl | ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩
        · exact absurd he hspqU
        · exact Or.inl ⟨p, hp, rfl⟩
        · exact Or.inr ⟨q, hq, rfl⟩
      · rintro (⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩)
        · exact (Finset.mem_filter.mp hp).2.2
        · exact (Finset.mem_filter.mp hq).2.2
    have hU_card : (Ustar G C).card = PU'.card + QU'.card := by
      rw [hU_eq, Finset.card_union_of_disjoint hEP_EQ_disj, hEP_card, hEQ_card]
    omega

lemma cover_no_singletons {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hg : junk G C = {g})
    (hUne : (Ustar G C).Nonempty)
    (hdisj : side (n := n) C g 0 ∩ side (n := n) C g 1 = ∅)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
 :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hsing (b : Fin 2) (z : Fin n) (hs : side (n := n) C g b = {z}) :
      ∀ e ∈ Ustar G C, z ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
      obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
      obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg u v hgtrue
      have hb : u ∈ side (n := n) C g b ∨ v ∈ side (n := n) C g b := by
        fin_cases b
        · exact h0
        · exact h1
      rw [hs] at hb
      simp only [Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact Sym2.mem_mk_left _ _
      · exact Sym2.mem_mk_right _ _
  obtain ⟨hPne, hQne, _, hW_iff, _, _, _, _, _⟩ := g_semantics G C hL hT g hg
  by_cases hP1 : (side (n := n) C g 0).card ≤ 1
  · obtain ⟨p0, hp0⟩ := Finset.card_eq_one.mp (le_antisymm hP1 (Finset.card_pos.mpr hPne))
    exact one_center G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj 0 p0
      (by rw [hp0]; simp) (hsing 0 p0 hp0)
  by_cases hQ1 : (side (n := n) C g 1).card ≤ 1
  · obtain ⟨q0, hq0⟩ := Finset.card_eq_one.mp (le_antisymm hQ1 (Finset.card_pos.mpr hQne))
    exact one_center G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj 1 q0
      (by rw [hq0]; simp) (hsing 1 q0 hq0)
  have hP2 : 2 ≤ (side (n := n) C g 0).card := by omega
  have hQ2 : 2 ≤ (side (n := n) C g 1).card := by omega
  have h1530 := thm_1530 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have hU_in_WPQ : ∀ e ∈ Ustar G C, ∃ z ∈ (wmax G C g ∩ side (n := n) C g 0) ∪
      (wmax G C g ∩ side (n := n) C g 1), z ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
      obtain ⟨hgtrue, huvW, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
      obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg u v hgtrue
      rcases huvW with huW | hvW
      · rcases h0 with hu0 | hv0
        · exact ⟨u, Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨huW, hu0⟩), Sym2.mem_mk_left _ _⟩
        · rcases h1 with hu1 | hv1
          · exact ⟨u, Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨huW, hu1⟩), Sym2.mem_mk_left _ _⟩
          · exfalso; have : v ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hv0, hv1⟩
            rw [hdisj] at this; exact Finset.notMem_empty _ this
      · rcases h0 with hu0 | hv0
        · rcases h1 with hu1 | hv1
          · exfalso; have : u ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hu0, hu1⟩
            rw [hdisj] at this; exact Finset.notMem_empty _ this
          · exact ⟨v, Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvW, hv1⟩), Sym2.mem_mk_right _ _⟩
        · exact ⟨v, Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvW, hv0⟩), Sym2.mem_mk_right _ _⟩
  by_cases hWP : (wmax G C g ∩ side (n := n) C g 0).Nonempty
  · obtain ⟨pstar, hpstar⟩ := Finset.card_eq_one.mp (le_antisymm (h1530.1 hQ2) (Finset.card_pos.mpr hWP))
    have hpW : pstar ∈ wmax G C g := (Finset.mem_inter.mp (by rw [hpstar]; simp)).1
    have hpP : pstar ∈ side (n := n) C g 0 := (Finset.mem_inter.mp (by rw [hpstar]; simp)).2
    by_cases hWQ : (wmax G C g ∩ side (n := n) C g 1).Nonempty
    · obtain ⟨qstar, hqstar⟩ := Finset.card_eq_one.mp (le_antisymm (h1530.2.1 hP2) (Finset.card_pos.mpr hWQ))
      have hqW : qstar ∈ wmax G C g := (Finset.mem_inter.mp (by rw [hqstar]; simp)).1
      have hqQ : qstar ∈ side (n := n) C g 1 := (Finset.mem_inter.mp (by rw [hqstar]; simp)).2
      by_cases hp1 : ∃ p1 ∈ side (n := n) C g 0, p1 ≠ pstar ∧ s(p1, qstar) ∈ Ustar G C
      · by_cases hq1 : ∃ q1 ∈ side (n := n) C g 1, q1 ≠ qstar ∧ s(pstar, q1) ∈ Ustar G C
        · exact two_centers G C g K hKcov h1528 h4 hE hL hT hg hUne
            hdisj htri hP2 hQ2 pstar qstar hpW hpP hqW hqQ hp1 hq1
        ·
          refine one_center G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj 1 qstar hqQ ?_
          intro e he
          obtain ⟨z, hz, hze⟩ := hU_in_WPQ e he
          rw [hpstar, hqstar] at hz
          simp only [Finset.mem_union, Finset.mem_singleton] at hz
          rcases hz with hz | hz
          · subst z
            induction e using Sym2.ind with
            | _ u v =>
              have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
              obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
              obtain ⟨_, h1⟩ := g_pair_sides G C hL hT g hg u v hgtrue
              have hp_notQ : pstar ∉ side (n := n) C g 1 := fun h => by
                have : pstar ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hpP, h⟩
                rw [hdisj] at this; exact Finset.notMem_empty _ this
              rcases Sym2.mem_iff.mp hze with hu | hv
              · subst u
                have hvQ : v ∈ side (n := n) C g 1 := h1.resolve_left hp_notQ
                by_cases hvq : v = qstar
                · subst v; exact Sym2.mem_mk_right _ _
                · exact absurd ⟨v, hvQ, hvq, he⟩ hq1
              · subst v
                have huQ : u ∈ side (n := n) C g 1 := h1.resolve_right hp_notQ
                by_cases huq : u = qstar
                · subst u; exact Sym2.mem_mk_left _ _
                · exact absurd ⟨u, huQ, huq, by rw [Sym2.eq_swap]; exact he⟩ hq1
          · subst z; exact hze
      ·
        refine one_center G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj 0 pstar hpP ?_
        intro e he
        obtain ⟨z, hz, hze⟩ := hU_in_WPQ e he
        rw [hpstar, hqstar] at hz
        simp only [Finset.mem_union, Finset.mem_singleton] at hz
        rcases hz with hz | hz
        · subst z; exact hze
        · subst z
          induction e using Sym2.ind with
          | _ u v =>
            have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
            obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
            obtain ⟨h0, _⟩ := g_pair_sides G C hL hT g hg u v hgtrue
            have hq_notP : qstar ∉ side (n := n) C g 0 := fun h => by
              have : qstar ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨h, hqQ⟩
              rw [hdisj] at this; exact Finset.notMem_empty _ this
            rcases Sym2.mem_iff.mp hze with hu | hv
            · subst u
              have hvP : v ∈ side (n := n) C g 0 := h0.resolve_left hq_notP
              by_cases hvp : v = pstar
              · subst v; exact Sym2.mem_mk_right _ _
              · exact absurd ⟨v, hvP, hvp, by rw [Sym2.eq_swap]; exact he⟩ hp1
            · subst v
              have huP : u ∈ side (n := n) C g 0 := h0.resolve_right hq_notP
              by_cases hup : u = pstar
              · subst u; exact Sym2.mem_mk_left _ _
              · exact absurd ⟨u, huP, hup, he⟩ hp1
    ·
      rw [Finset.not_nonempty_iff_eq_empty] at hWQ
      refine one_center G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj 0 pstar hpP ?_
      intro e he
      obtain ⟨z, hz, hze⟩ := hU_in_WPQ e he
      rw [hpstar, hWQ] at hz
      simp only [Finset.union_empty, Finset.mem_singleton] at hz
      rwa [← hz]
  ·
    rw [Finset.not_nonempty_iff_eq_empty] at hWP
    have hWQ : (wmax G C g ∩ side (n := n) C g 1).Nonempty := by
      obtain ⟨e, he⟩ := hUne
      obtain ⟨z, hz, _⟩ := hU_in_WPQ e he
      rw [hWP, Finset.empty_union] at hz
      exact ⟨z, hz⟩
    obtain ⟨qstar, hqstar⟩ := Finset.card_eq_one.mp (le_antisymm (h1530.2.1 hP2) (Finset.card_pos.mpr hWQ))
    have hqW : qstar ∈ wmax G C g := (Finset.mem_inter.mp (by rw [hqstar]; simp)).1
    have hqQ : qstar ∈ side (n := n) C g 1 := (Finset.mem_inter.mp (by rw [hqstar]; simp)).2
    refine one_center G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj 1 qstar hqQ ?_
    intro e he
    obtain ⟨z, hz, hze⟩ := hU_in_WPQ e he
    rw [hWP, hqstar] at hz
    simp only [Finset.empty_union, Finset.mem_singleton] at hz
    rwa [← hz]

lemma one_junk_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (h4 : NoFourCycle G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hg : junk G C = {g})
    (hsil : ∀ u : Fin n, gateVal n C g (pairInput u u) = false) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  by_cases hE : G.edgeFinset.Nonempty
  · obtain ⟨K, hKcov, _, _, h1528⟩ := thm_1528 n G C h4 hE hL hT g hg
    by_cases hUne : (Ustar G C).Nonempty
    · have hdisj : side (n := n) C g 0 ∩ side (n := n) C g 1 = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        obtain ⟨hu0, hu1⟩ := Finset.mem_inter.mp hu
        have hf := ((g_semantics G C hL hT g hg).2.2.1 (pairInput u u)).mpr
          ⟨⟨u, hu0, by simp [pairInput]⟩, ⟨u, hu1, by simp [pairInput]⟩⟩
        rw [W_eq_gateVal, hsil u] at hf
        contradiction
      exact cover_no_singletons G C g K hKcov h1528 h4 hE hL hT hg hUne hdisj htri
    · have hU0 : Ustar G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUne
      refine ⟨K, ?_, ?_⟩
      · intro e he
        apply hKcov e
        by_contra hs
        have hu : e ∈ Ustar G C := Finset.mem_sdiff.mpr ⟨he, hs⟩
        rw [hU0] at hu
        exact Finset.notMem_empty _ hu
      · rw [hU0, Finset.card_empty] at h1528
        omega
  · have hE0 : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    refine ⟨∅, ?_, ?_⟩
    · intro e he
      rw [hE0] at he
      exact (Finset.notMem_empty _ he).elim
    · rw [hE0]
      simp

end PEqualNP.Outside.L_meta_2448_aux.oneJunk

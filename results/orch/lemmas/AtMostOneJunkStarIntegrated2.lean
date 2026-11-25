import PEqualNP.Outside.L_meta_3760
import PEqualNP.Outside.L_meta_2448


namespace PEqualNP.Outside.L_meta_2448_aux.oneJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3760 PEqualNP.Outside.L_meta_3760.Close
open PEqualNP.Outside.L_meta_3760.M1528.P1.S98 (W AO AO_of_IsAO2 W_and W_input)
open PEqualNP.Outside.L_meta_3760.M1528.P2 (OrR mem_orIn orR_mono opnd_eq graphFun_pair orR_orReaches orR_le orR_cone pairInput_true)

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

lemma cover_inter_ge_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (hUne : (Ustar G C).Nonempty)
    (hI2 : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hg_lt := (junk_single_props G C hL hT g hg).1
  obtain ⟨_, _, hgeval, hW_iff, _, _, _, _, _⟩ := g_semantics G C hL hT g hg
  have h1529 := thm_1529 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have h1530 := thm_1530 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have hWle1 : (wmax G C g).card ≤ 1 := h1529.2.2.2.2 hI2
  have hWne : (wmax G C g).Nonempty := by
    obtain ⟨e, he⟩ := hUne
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
      obtain ⟨_, huvW, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv he
      rcases huvW with hu | hv <;> [exact ⟨u, hu⟩; exact ⟨v, hv⟩]
  obtain ⟨w0, hw0_eq⟩ := Finset.card_eq_one.mp (le_antisymm hWle1 (Finset.card_pos.mpr hWne))
  have hw0W : w0 ∈ wmax G C g := by rw [hw0_eq]; simp
  obtain ⟨h0_lt, h0_no⟩ := no_and_in_g_opnd G C hL hT g hg 0
  obtain ⟨h1_lt, h1_no⟩ := no_and_in_g_opnd G C hL hT g hg 1
  by_cases hQall : ∀ q ∈ side (n := n) C g 1, G.Adj w0 q
  · exfalso
    refine replace_gate_by_wire G C hE hL hT g hg (opnd C g 1) h1_lt ?_ (Or.inr ⟨w0, hw0_eq, ?_⟩)
    · intro u v huv hU
      obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv hU
      rw [← W_eq_gateVal, hgeval] at hgtrue
      exact (pure_or_wire_eval C hA (opnd C g 1) (by omega) h1_no).2 (pairInput u v) |>.mpr hgtrue.2
    · intro x hxw0 hW1
      obtain ⟨q, hqQ, hxq⟩ := (pure_or_wire_eval C hA (opnd C g 1) (by omega) h1_no).2 x |>.mp hW1
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨w0, q, hQall q hqQ, hxw0, hxq⟩
  by_cases hPall : ∀ p ∈ side (n := n) C g 0, G.Adj w0 p
  · exfalso
    refine replace_gate_by_wire G C hE hL hT g hg (opnd C g 0) h0_lt ?_ (Or.inr ⟨w0, hw0_eq, ?_⟩)
    · intro u v huv hU
      obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv hU
      rw [← W_eq_gateVal, hgeval] at hgtrue
      exact (pure_or_wire_eval C hA (opnd C g 0) (by omega) h0_no).2 (pairInput u v) |>.mpr hgtrue.1
    · intro x hxw0 hW0
      obtain ⟨p, hpP, hxp⟩ := (pure_or_wire_eval C hA (opnd C g 0) (by omega) h0_no).2 x |>.mp hW0
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨w0, p, hPall p hpP, hxw0, hxp⟩
  have hw0_notP : w0 ∉ side (n := n) C g 0 := fun h => hQall (h1529.1 w0 hw0W h).2
  have hw0_notQ : w0 ∉ side (n := n) C g 1 := fun h => hPall (h1529.2.1 w0 hw0W h).2
  push Not at hQall hPall
  obtain ⟨q', hq'Q, hq'nadj⟩ := hQall
  obtain ⟨p', hp'P, hp'nadj⟩ := hPall
  have hp'q' : G.Adj p' q' := by
    rcases (hW_iff w0).mp hw0W p' hp'P q' hq'Q with h | h | h
    · exact h
    · exact absurd h.symm hp'nadj
    · exact absurd h.symm hq'nadj
  let IU := (side (n := n) C g 0 ∩ side (n := n) C g 1).filter fun b => s(w0, b) ∈ Ustar G C
  have hU_eq : Ustar G C = IU.image (fun b => s(w0, b)) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Finset.mem_image, IU, Finset.mem_filter]
      constructor
      · intro hU
        have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1
        obtain ⟨hgtrue, huvW, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg u v huv hU
        obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg u v hgtrue
        rcases huvW with huW | hvW
        · have hu0 : u = w0 := by rw [hw0_eq, Finset.mem_singleton] at huW; exact huW
          subst u
          have hvI := (h1530.2.2.1 w0 v huv h0 h1 hw0W).2.2 hw0_notP hw0_notQ
          exact ⟨v, ⟨hvI, hU⟩, rfl⟩
        · have hv0 : v = w0 := by rw [hw0_eq, Finset.mem_singleton] at hvW; exact hvW
          subst v
          have huI := (h1530.2.2.1 w0 u huv.symm h0.symm h1.symm hw0W).2.2 hw0_notP hw0_notQ
          exact ⟨u, ⟨huI, by rw [Sym2.eq_swap]; exact hU⟩, Sym2.eq_swap⟩
      · rintro ⟨b, ⟨_, hU⟩, heq⟩; rwa [← heq]
  have hIU_adj : ∀ b ∈ IU, G.Adj w0 b := fun b hb =>
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).2).1
  have hIU_notStar : ∀ b ∈ IU, s(w0, b) ∉ starEdges G C := fun b hb =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).2).2
  have hU_card : (Ustar G C).card = IU.card := by
    rw [hU_eq, Finset.card_image_of_injOn]
    intro b1 hb1 b2 hb2 heq
    have hadj := hIU_adj b1 hb1
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · exact absurd h.symm hadj.ne
  have hlamIU : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ IU).card ≤ 1 :=
    lam_card_le_one_of_common_nbr G h4 C hL w0 IU hIU_adj
      (fun a _ ha _ _ => Or.inl (hIU_notStar a ha))
  have hIU_sub : IU ⊆ side (n := n) C g 0 := by
    intro x hx
    exact (Finset.mem_inter.mp (Finset.mem_filter.mp hx).1).1
  have hcg := g_cone_gate_count G C hL hT g hg 0 IU hIU_sub hlamIU
  have hcg_le : ((coneGates G C g).filter fun h => OrR n C (opnd C g 0) (n + h)).card ≤
      (coneGates G C g).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hXcov : ∀ e ∈ Ustar G C, ∃ v ∈ K ∪ {w0}, v ∈ e := by
    intro e he
    rw [hU_eq, Finset.mem_image] at he
    obtain ⟨b, _, rfl⟩ := he
    exact ⟨w0, Finset.mem_union_right _ (Finset.mem_singleton_self _), Sym2.mem_mk_left _ _⟩
  have hmixcl := ustar_ne_implies_mix_or_cl G C h4 hE hL hT g hg hUne
  have hxcard : (({w0} : Finset (Fin n)) \ K).card ≤ 1 :=
    (Finset.card_le_card Finset.sdiff_subset).trans (by simp)
  apply cover_of_budget G C g K hKcov h1528 {w0} hXcov
  omega

lemma cover_inter_one_side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (hformU : formU G C g ⊆ K) (hformZ : formZ G C g ⊆ K)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (v : Fin n) (hInter : side (n := n) C g 0 ∩ side (n := n) C g 1 = {v})
    (b : Fin 2) (wP : Fin n)
    (hWb : wmax G C g ∩ side (n := n) C g b = {wP})
    (hW1b : wmax G C g ∩ side (n := n) C g (1 - b) = ∅) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hg_lt := (junk_single_props G C hL hT g hg).1
  obtain ⟨_, _, hgeval, hW_iff, _, _, _, _, _⟩ := g_semantics G C hL hT g hg
  have h1529 := thm_1529 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have h1530 := thm_1530 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have hv_mem_inter : v ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := by rw [hInter]; simp
  have hv0 : v ∈ side (n := n) C g 0 := (Finset.mem_inter.mp hv_mem_inter).1
  have hv1 : v ∈ side (n := n) C g 1 := (Finset.mem_inter.mp hv_mem_inter).2
  have hv_b : v ∈ side (n := n) C g b := by rcases fin2_cases b with rfl | rfl <;> assumption
  have hv_1b : v ∈ side (n := n) C g (1 - b) := by rcases fin2_cases b with rfl | rfl <;> assumption
  have hv_notW : v ∉ wmax G C g := h1529.2.2.2.1 v hv_mem_inter
  have hv_adj_W : ∀ w ∈ wmax G C g, G.Adj v w := h1529.2.2.1 v hv_mem_inter
  have hwP_W : wP ∈ wmax G C g := (Finset.mem_inter.mp (by rw [hWb]; simp)).1
  have hwP_b : wP ∈ side (n := n) C g b := (Finset.mem_inter.mp (by rw [hWb]; simp)).2
  have hwP_not1b : wP ∉ side (n := n) C g (1 - b) := by
    intro hmem
    have : wP ∈ wmax G C g ∩ side (n := n) C g (1 - b) := Finset.mem_inter.mpr ⟨hwP_W, hmem⟩
    rw [hW1b] at this; exact Finset.notMem_empty _ this
  have hwP_adj_1b : ∀ q ∈ side (n := n) C g (1 - b), G.Adj wP q := by
    rcases fin2_cases b with rfl | rfl
    · exact (h1529.1 wP hwP_W hwP_b).2
    · exact (h1529.2.1 wP hwP_W hwP_b).2
  have hvwP_adj : G.Adj v wP := hv_adj_W wP hwP_W
  have hW_clause4 : ∀ u : Fin n, u ≠ v → ((Finset.univ.filter fun w => G.Adj u w) ∩ wmax G C g).card ≤ 1 :=
    h1530.2.2.2 v hInter
  let QU := (side (n := n) C g (1 - b)).filter fun q => q ≠ v ∧ s(wP, q) ∈ Ustar G C
  let WU := (wmax G C g).filter fun w => s(w, v) ∈ Ustar G C
  let EQ := QU.image (fun q => s(wP, q))
  let EW := WU.image (fun w => s(w, v))
  have hU_eq : Ustar G C = EQ ∪ EW := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_union, EQ, EW, Finset.mem_image, QU, WU, Finset.mem_filter]
      constructor
      · intro hU
        have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1
        obtain ⟨hgtrue, hxyW, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg x y hxy hU
        obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg x y hgtrue
        have hclassify : ∀ a c : Fin n, G.Adj a c → (a ∈ side (n := n) C g 0 ∨ c ∈ side (n := n) C g 0) →
            (a ∈ side (n := n) C g 1 ∨ c ∈ side (n := n) C g 1) → a ∈ wmax G C g →
            s(a, c) ∈ Ustar G C →
            (∃ q, (q ∈ side (n := n) C g (1 - b) ∧ q ≠ v ∧ s(wP, q) ∈ Ustar G C) ∧ s(wP, q) = s(a, c)) ∨
            (∃ w, (w ∈ wmax G C g ∧ s(w, v) ∈ Ustar G C) ∧ s(w, v) = s(a, c)) := by
          intro a c hac h0' h1' haW haU
          have hc3 := h1530.2.2.1 a c hac h0' h1' haW
          by_cases hab : a ∈ side (n := n) C g b
          · have haw : a = wP := by
              have : a ∈ wmax G C g ∩ side (n := n) C g b := Finset.mem_inter.mpr ⟨haW, hab⟩
              rwa [hWb, Finset.mem_singleton] at this
            subst a
            have hc1b : c ∈ side (n := n) C g (1 - b) := by
              rcases fin2_cases b with rfl | rfl
              · exact hc3.1 hab
              · exact hc3.2.1 hab
            by_cases hcv : c = v
            · subst c; exact Or.inr ⟨wP, ⟨haW, haU⟩, rfl⟩
            · exact Or.inl ⟨c, ⟨hc1b, hcv, haU⟩, rfl⟩
          · have ha1b : a ∉ side (n := n) C g (1 - b) := fun h => by
              have : a ∈ wmax G C g ∩ side (n := n) C g (1 - b) := Finset.mem_inter.mpr ⟨haW, h⟩
              rw [hW1b] at this; exact Finset.notMem_empty _ this
            have hcI : c ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := by
              rcases fin2_cases b with rfl | rfl
              · exact hc3.2.2 hab ha1b
              · exact hc3.2.2 ha1b hab
            rw [hInter, Finset.mem_singleton] at hcI
            subst c
            exact Or.inr ⟨a, ⟨haW, haU⟩, rfl⟩
        rcases hxyW with hxW | hyW
        · exact hclassify x y hxy h0 h1 hxW hU
        · rcases hclassify y x hxy.symm h0.symm h1.symm hyW (by rw [Sym2.eq_swap]; exact hU) with
            ⟨q, hq, heq⟩ | ⟨w, hw, heq⟩
          · exact Or.inl ⟨q, hq, heq.trans Sym2.eq_swap⟩
          · exact Or.inr ⟨w, hw, heq.trans Sym2.eq_swap⟩
      · rintro (⟨q, ⟨_, _, hU⟩, heq⟩ | ⟨w, ⟨_, hU⟩, heq⟩) <;> rwa [← heq]
  have hEQ_EW_disj : Disjoint EQ EW := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp h2
    have hq_nev := (Finset.mem_filter.mp hq).2.1
    rcases Sym2.eq_iff.mp heq with ⟨_, hqv⟩ | ⟨_, hwv⟩
    · exact hq_nev hqv.symm
    · exact hvwP_adj.ne hwv
  have hEQ_card : EQ.card = QU.card := by
    rw [Finset.card_image_of_injOn]
    intro q1 hq1 q2 hq2 heq
    have hadj := hwP_adj_1b q1 (Finset.mem_filter.mp hq1).1
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · exact absurd h.symm hadj.ne
  have hEW_card : EW.card = WU.card := by
    rw [Finset.card_image_of_injOn]
    intro w1 hw1 w2 hw2 heq
    have hadj := hv_adj_W w1 (Finset.mem_filter.mp hw1).1
    rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hadj.ne'
  have hU_card : (Ustar G C).card = QU.card + WU.card := by
    rw [hU_eq, Finset.card_union_of_disjoint hEQ_EW_disj, hEQ_card, hEW_card]
  by_cases hQUempty : QU = ∅
  · exfalso
    refine replace_gate_by_wire G C hE hL hT g hg v.val (by have := v.isLt; omega) ?_ (Or.inl ?_)
    · intro x y _ hU
      rw [hU_eq, show EQ = ∅ by simp [EQ, hQUempty], Finset.empty_union, Finset.mem_image] at hU
      obtain ⟨w, _, heq⟩ := hU
      rw [W_input n C _ v.val v.isLt, pairInput_true]
      rcases Sym2.eq_iff.mp heq with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl rfl
    · intro x hxv
      rw [W_input n C x v.val v.isLt] at hxv
      rw [hgeval]
      exact ⟨⟨v, hv0, hxv⟩, ⟨v, hv1, hxv⟩⟩
  have hQU_ne : QU.Nonempty := Finset.nonempty_iff_ne_empty.mpr hQUempty
  let Cg1b := (coneGates G C g).filter fun h => OrR n C (opnd C g (1 - b)) (n + h)
  have hCg1b_lb : QU.card ≤ Cg1b.card := by
    let T := insert v QU
    have hv_notQU : v ∉ QU := fun h => (Finset.mem_filter.mp h).2.1 rfl
    have hT_sub : T ⊆ side (n := n) C g (1 - b) := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq'
      · exact hv_1b
      · exact (Finset.mem_filter.mp hq').1
    have hlamT : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ T).card ≤ 1 := by
      refine lam_card_le_one_of_common_nbr G h4 C hL wP T (fun q hq => hwP_adj_1b q (hT_sub hq)) ?_
      intro x y hx hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact absurd rfl hxy
        · exact Or.inr (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy').2.2).2
      · exact Or.inl (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx').2.2).2
    have h : T.card ≤ 1 + Cg1b.card := g_cone_gate_count G C hL hT g hg (1 - b) T hT_sub hlamT
    rw [Finset.card_insert_of_notMem hv_notQU] at h
    omega
  obtain ⟨hb_lt, hb_noAnd⟩ := no_and_in_g_opnd G C hL hT g hg b
  have hroot_b : ∃ hb, opnd C g b = n + hb ∧ hb < C.gates.length ∧ (gateAt C hb).op = GateOp.or := by
    by_cases hwn : opnd C g b < n
    · exfalso
      have hv_eq : v.val = opnd C g b := by
        have hr := (mem_orIn n C hA _ (by omega) v).mp hv_b
        rcases Relation.ReflTransGen.cases_head hr with heq | ⟨_, ⟨k, hk, _⟩, _⟩
        · exact heq.symm
        · omega
      have hw_eq : wP.val = opnd C g b := by
        have hr := (mem_orIn n C hA _ (by omega) wP).mp hwP_b
        rcases Relation.ReflTransGen.cases_head hr with heq | ⟨_, ⟨k, hk, _⟩, _⟩
        · exact heq.symm
        · omega
      exact hvwP_adj.ne (Fin.ext (hv_eq.trans hw_eq.symm))
    · refine ⟨opnd C g b - n, by omega, by omega, ?_⟩
      rcases (hA (opnd C g b - n) (by omega)).1 with hop | hop
      · exact absurd (show OrR n C (opnd C g b) (n + (opnd C g b - n)) by
          rw [show n + (opnd C g b - n) = opnd C g b by omega]; exact Relation.ReflTransGen.refl)
          (hb_noAnd _ (by omega) hop)
      · exact hop
  obtain ⟨hb, hhb_eq, hhb_lt, hhb_op⟩ := hroot_b
  have hhb_notLam : hb ∉ lam G C := by
    intro hlam
    obtain ⟨c, hc⟩ := lam_has_center G C hL hb hlam
    have hcv := (hc v (by
      change v ∈ orIn n C (opnd C g b) at hv_b
      rwa [hhb_eq] at hv_b)).1
    have hcw := (hc wP (by
      change wP ∈ orIn n C (opnd C g b) at hwP_b
      rwa [hhb_eq] at hwP_b)).1
    exact htri c v wP hcv hvwP_adj hcw.symm
  obtain ⟨hhb_orN, hhb_notMix⟩ := pure_or_gate_in_orN_not_mixing G C hL (opnd C g b) (by omega)
    hb_noAnd hb hhb_lt hhb_op (by rw [hhb_eq]; exact Relation.ReflTransGen.refl)
  have hhb_cg : hb ∈ coneGates G C g := by
    simp only [coneGates, Finset.mem_filter, Finset.mem_sdiff]
    refine ⟨⟨⟨hhb_orN, hhb_notLam⟩, hhb_notMix⟩, ?_⟩
    have hre := orR_orReaches n C hA hb hhb_lt (opnd C g b) (by omega)
      (by rw [hhb_eq]; exact Relation.ReflTransGen.refl)
    rcases fin2_cases b with rfl | rfl
    · exact Or.inl hre
    · exact Or.inr (Or.inl hre)
  have hhb_not_Cg1b : hb ∉ Cg1b := by
    intro hmem
    have hr1b := (Finset.mem_filter.mp hmem).2
    have hwP_orR := (mem_orIn n C hA (n + hb) (by omega) wP).mp
      (by change wP ∈ orIn n C (opnd C g b) at hwP_b; rwa [hhb_eq] at hwP_b)
    have hwP_in1b : wP ∈ side (n := n) C g (1 - b) :=
      (mem_orIn n C hA (opnd C g (1 - b)) (by have := opnd_lt' hA g hg_lt (1 - b); omega) wP).mpr
        (hr1b.trans hwP_orR)
    exact hwP_not1b hwP_in1b
  let Wcl := WU.filter fun w =>
    ∃ a ∈ centreless G C, ∃ ba : Fin 2, opnd C a ba = n + g ∧ w ∈ side (n := n) C a (1 - ba)
  let Wmix := WU \ Wcl
  have hWU_split : Wcl.card + Wmix.card = WU.card := by
    have h1 : Wcl ∪ Wmix = WU := Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
    rw [← h1, Finset.card_union_of_disjoint Finset.disjoint_sdiff]
  let Rcl := (centreless G C).biUnion fun a =>
    (Finset.univ : Finset (Fin 2)).filter (fun ba => opnd C a ba = n + g) |>.image fun ba => opnd C a (1 - ba)
  have hRcl_card : Rcl.card ≤ (centreless G C).card := by
    calc Rcl.card ≤ ∑ a ∈ centreless G C,
          (((Finset.univ : Finset (Fin 2)).filter fun ba => opnd C a ba = n + g).image fun ba => opnd C a (1 - ba)).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ centreless G C, 1 := by
            refine Finset.sum_le_sum fun a ha => ?_
            refine Finset.card_le_one.mpr fun r1 hr1 r2 hr2 => ?_
            obtain ⟨b1, hb1, rfl⟩ := Finset.mem_image.mp hr1
            obtain ⟨b2, hb2, rfl⟩ := Finset.mem_image.mp hr2
            have h1 := (Finset.mem_filter.mp hb1).2
            have h2 := (Finset.mem_filter.mp hb2).2
            have hb_eq : b1 = b2 := by
              by_contra hne
              have h01 : opnd C a 0 = n + g ∧ opnd C a 1 = n + g := by
                rcases fin2_cases b1 with rfl | rfl <;> rcases fin2_cases b2 with rfl | rfl
                · exact absurd rfl hne
                · exact ⟨h1, h2⟩
                · exact ⟨h2, h1⟩
                · exact absurd rfl hne
              have ha_top : a ∈ tops G C := (Finset.mem_filter.mp ha).1
              simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha_top
              exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx => ha_top.2.2 x (by
                rw [← W_eq_gateVal, W_and n C x a ha_top.1 ha_top.2.1 (opnd C a 0) (opnd C a 1)
                  (opnd_eq n C hA a ha_top.1) (opnd_lt' hA a ha_top.1 0) (opnd_lt' hA a ha_top.1 1),
                  h01.1, h01.2, Bool.and_self]; exact hx))
            rw [hb_eq]
      _ = (centreless G C).card := by simp
  have hRcl_props : ∀ r ∈ Rcl, r < n + C.gates.length ∧
      orIn n C r ⊆ wmax G C g ∧
      (∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C r (n + h)) ∧
      ∃ a ∈ centreless G C, ∃ ba : Fin 2, opnd C a ba = n + g ∧ r = opnd C a (1 - ba) := by
    intro r hr
    obtain ⟨a, haCL, hr'⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨ba, hba_f, rfl⟩ := Finset.mem_image.mp hr'
    have hba_g : opnd C a ba = n + g := (Finset.mem_filter.mp hba_f).2
    have ha_top : a ∈ tops G C := (Finset.mem_filter.mp haCL).1
    have ha_lt : a < C.gates.length := by
      simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha_top; exact ha_top.1
    have hlt := opnd_lt' hA a ha_lt (1 - ba)
    obtain ⟨ba0, hba0_g, _, hba0_subW, _⟩ := thm_1503 n G C hE hL hT g hg a haCL
    have hba_eq : ba = ba0 := by
      by_contra hne
      have h01 : opnd C a 0 = n + g ∧ opnd C a 1 = n + g := by
        rcases fin2_cases ba with rfl | rfl <;> rcases fin2_cases ba0 with rfl | rfl
        · exact absurd rfl hne
        · exact ⟨hba_g, hba0_g⟩
        · exact ⟨hba0_g, hba_g⟩
        · exact absurd rfl hne
      simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha_top
      exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx => ha_top.2.2 x (by
        rw [← W_eq_gateVal, W_and n C x a ha_top.1 ha_top.2.1 (opnd C a 0) (opnd C a 1)
          (opnd_eq n C hA a ha_top.1) (opnd_lt' hA a ha_top.1 0) (opnd_lt' hA a ha_top.1 1),
          h01.1, h01.2, Bool.and_self]; exact hx))
    subst ba
    refine ⟨by omega, hba0_subW, ?_, a, haCL, ba0, hba0_g, rfl⟩
    intro h hh hop hr_and
    have hmem : opnd C a (1 - ba0) ∈ (gateAt C a).inputs := by
      have := opnd_eq n C hA a ha_lt; rcases fin2_cases ba0 with rfl | rfl <;> rw [this] <;> simp
    have hic : InCone n C h a := by
      by_cases h1 : opnd C a (1 - ba0) < n
      · have := orR_le n C hA _ _ hr_and; omega
      · obtain ⟨k, hkeq⟩ : ∃ k, opnd C a (1 - ba0) = n + k := ⟨opnd C a (1 - ba0) - n, by omega⟩
        rcases orR_cone n C hA h (opnd C a (1 - ba0)) hr_and k hkeq (by omega) with rfl | hc
        · exact M1528.P2.inCone_c1 n C hA h a ha_lt (hkeq ▸ hmem)
        · exact M1528.P2.inCone_c2 n C hA h k a ha_lt hc (hkeq ▸ hmem)
    have hhg := (junk_single_props G C hL hT g hg).2.2.2.2.2 a ha_top h hh hop hic
    rw [hhg] at hr_and
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha_top
    exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx => ha_top.2.2 x (by
      have h0 : W n C x (opnd C a ba0) = true := by rw [hba0_g]; exact hx
      have h1 : W n C x (opnd C a (1 - ba0)) = true := orR_mono n C hA x _ _ hr_and hx
      rw [← W_eq_gateVal, W_and n C x a ha_top.1 ha_top.2.1 (opnd C a 0) (opnd C a 1)
        (opnd_eq n C hA a ha_top.1) (opnd_lt' hA a ha_top.1 0) (opnd_lt' hA a ha_top.1 1),
        Bool.and_eq_true]
      rcases fin2_cases ba0 with rfl | rfl <;> [exact ⟨h0, h1⟩; exact ⟨h1, h0⟩]))
  let Cgcl := (coneGates G C g).filter fun h => ∃ r ∈ Rcl, OrR n C r (n + h)
  have hWcl_lb : Wcl.card ≤ (centreless G C).card + Cgcl.card := by
    have hlamWcl : ∀ h ∈ lam G C, ((orIn n C (n + h)) ∩ Wcl).card ≤ 1 := by
      refine lam_card_le_one_of_common_nbr G h4 C hL v Wcl ?_ ?_
      · intro w hw; exact hv_adj_W w (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
      · intro x _ hx _ _
        exact Or.inl (by rw [Sym2.eq_swap]; exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2).2)
    have hbound := or_dag_leaf_bound C hA Wcl (lam G C) hlamWcl Rcl
      (fun r hr => (hRcl_props r hr).1) (fun r hr => (hRcl_props r hr).2.2.1)
    have hsubWcl : Wcl ⊆ Rcl.biUnion (fun r => orIn n C r) := by
      intro w hw
      obtain ⟨_, a, haCL, ba, hbag, hw_side⟩ := Finset.mem_filter.mp hw
      refine Finset.mem_biUnion.mpr ⟨opnd C a (1 - ba), ?_, hw_side⟩
      refine Finset.mem_biUnion.mpr ⟨a, haCL, Finset.mem_image.mpr ⟨ba, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbag⟩, rfl⟩⟩
    have hlhs : (Rcl.biUnion (fun r => orIn n C r) ∩ Wcl) = Wcl := Finset.inter_eq_right.mpr hsubWcl
    rw [hlhs] at hbound
    have hF_sub : ((Finset.range C.gates.length).filter fun h =>
        (gateAt C h).op = GateOp.or ∧ h ∉ lam G C ∧ ∃ r ∈ Rcl, OrR n C r (n + h)) ⊆ Cgcl := by
      intro h hh
      obtain ⟨hrng, hop, hnotLam, r, hrR, hrh⟩ := Finset.mem_filter.mp hh
      have hh_lt := Finset.mem_range.mp hrng
      obtain ⟨hr_lt, _, hr_noAnd, a, haCL, ba, hbag, rfl⟩ := hRcl_props r hrR
      obtain ⟨horN, hnotMix⟩ := pure_or_gate_in_orN_not_mixing G C hL _ hr_lt hr_noAnd h hh_lt hop hrh
      refine Finset.mem_filter.mpr ⟨?_, opnd C a (1 - ba), hrR, hrh⟩
      simp only [coneGates, Finset.mem_filter, Finset.mem_sdiff]
      exact ⟨⟨⟨horN, hnotLam⟩, hnotMix⟩, Or.inr (Or.inr ⟨a, haCL, ba, hbag,
        orR_orReaches n C hA h hh_lt _ hr_lt hrh⟩)⟩
    have hF_le := Finset.card_le_card hF_sub
    omega
  have hCgcl_subW : ∀ h ∈ Cgcl, (orIn n C (n + h)).Nonempty ∧ orIn n C (n + h) ⊆ wmax G C g := by
    intro h hh
    obtain ⟨_, r, hrR, hrh⟩ := Finset.mem_filter.mp hh
    obtain ⟨hr_lt, hr_subW, hr_noAnd, _⟩ := hRcl_props r hrR
    have hh_lt : h < C.gates.length := by have := orR_le n C hA _ _ hrh; omega
    have hne := (pure_or_wire_eval C hA (n + h) (by omega)
      (fun k hk hop hrk => hr_noAnd k hk hop (hrh.trans hrk))).1
    refine ⟨hne, fun u hu => hr_subW ?_⟩
    exact (mem_orIn n C hA r hr_lt u).mpr (hrh.trans ((mem_orIn n C hA (n + h) (by omega) u).mp hu))
  have hCgcl_disj_Cg1b : Disjoint Cgcl Cg1b := by
    rw [Finset.disjoint_left]
    intro h h1 h2
    obtain ⟨⟨u, hu⟩, hsubW⟩ := hCgcl_subW h h1
    have hr1b := (Finset.mem_filter.mp h2).2
    have hh_lt : h < C.gates.length := by have := orR_le n C hA _ _ hr1b; have := opnd_lt' hA g hg_lt (1 - b); omega
    have hu1b : u ∈ side (n := n) C g (1 - b) :=
      (mem_orIn n C hA (opnd C g (1 - b)) (by have := opnd_lt' hA g hg_lt (1 - b); omega) u).mpr
        (hr1b.trans ((mem_orIn n C hA (n + h) (by omega) u).mp hu))
    have : u ∈ wmax G C g ∩ side (n := n) C g (1 - b) := Finset.mem_inter.mpr ⟨hsubW hu, hu1b⟩
    rw [hW1b] at this; exact Finset.notMem_empty _ this
  have hhb_not_Cgcl : hb ∉ Cgcl := by
    intro hmem
    have hsubW := (hCgcl_subW hb hmem).2
    exact hv_notW (hsubW (by change v ∈ orIn n C (opnd C g b) at hv_b; rwa [hhb_eq] at hv_b))
  have hcg_total : Cg1b.card + 1 + Cgcl.card ≤ (coneGates G C g).card := by
    have hsub : insert hb (Cg1b ∪ Cgcl) ⊆ coneGates G C g :=
      Finset.insert_subset hhb_cg (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hhb_not_Cg1b, hhb_not_Cgcl]),
      Finset.card_union_of_disjoint hCgcl_disj_Cg1b.symm] at hcard
    omega
  have hmix_witness_uniq : ∀ (m : ℕ), m ∈ mixing G C → n + g ∈ (gateAt C m).inputs →
      ∀ (a1 a2 : ℕ) (b1 b2 : Fin 2) (w1 w2 : Fin n),
      a1 ∈ tops G C → OrReaches n C (opnd C a1 b1) m → w1 ∈ side (n := n) C a1 (1 - b1) → w1 ∈ wmax G C g →
      a2 ∈ tops G C → OrReaches n C (opnd C a2 b2) m → w2 ∈ side (n := n) C a2 (1 - b2) → w2 ∈ wmax G C g →
      w1 = w2 := by
    intro m hm hgm a1 a2 b1 b2 w1 w2 ha1 hr1 hw1s hw1W ha2 hr2 hw2s hw2W
    have hm_lt : m < C.gates.length := by
      simp only [mixing, orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hm; exact hm.1.1
    obtain ⟨_, y0, y1, hmin, _, _⟩ := hA m hm_lt
    have hex_y : ∃ y ∈ (gateAt C m).inputs, y ≠ n + g := by
      have hm_xor : (orIn n C (opnd C m 0) = ∅) ≠ (orIn n C (opnd C m 1) = ∅) := (Finset.mem_filter.mp hm).2
      have h0eq : opnd C m 0 = y0 := by simp [opnd, hmin]
      have h1eq : opnd C m 1 = y1 := by simp [opnd, hmin]
      rw [h0eq, h1eq] at hm_xor
      rw [hmin] at hgm ⊢
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm ⊢
      rcases hgm with rfl | rfl
      · refine ⟨y1, Or.inr rfl, fun heq => hm_xor (by rw [heq])⟩
      · refine ⟨y0, Or.inl rfl, fun heq => hm_xor (by rw [heq])⟩
    obtain ⟨y, hy_in, hy_ne⟩ := hex_y
    obtain ⟨⟨um, hum_y, hum_g⟩, hrest⟩ := thm_1506 n G C h4 hE hL hT g hg m hm hgm y hy_in hy_ne
    have hum_nev : um ≠ v := by
      intro heq; subst um
      have hgv : gateVal n C g (pairInput v v) = true := by
        rw [← W_eq_gateVal, hgeval]
        exact ⟨⟨v, hv0, by simp [pairInput]⟩, ⟨v, hv1, by simp [pairInput]⟩⟩
      rw [hgv] at hum_g; exact Bool.noConfusion hum_g
    have hadj_of_sides : ∀ a ∈ tops G C, ∀ t : Fin 2, ∀ x ∈ side (n := n) C a t, ∀ z ∈ side (n := n) C a (1 - t),
        G.Adj x z := by
      intro a ha t x hx z hz
      simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
      have hW0 := orR_mono n C hA (pairInput x z) (opnd C a t) x.val
        ((mem_orIn n C hA _ (by have := opnd_lt' hA a ha.1 t; omega) x).mp hx)
        (by rw [M1528.P2.W_input n C _ x.val x.isLt]; simp [pairInput])
      have hW1 := orR_mono n C hA (pairInput x z) (opnd C a (1 - t)) z.val
        ((mem_orIn n C hA _ (by have := opnd_lt' hA a ha.1 (1 - t); omega) z).mp hz)
        (by rw [M1528.P2.W_input n C _ z.val z.isLt]; simp [pairInput])
      have hWa : W n C (pairInput x z) (n + a) = true := by
        rw [W_and n C _ a ha.1 ha.2.1 (opnd C a 0) (opnd C a 1) (opnd_eq n C hA a ha.1)
          (opnd_lt' hA a ha.1 0) (opnd_lt' hA a ha.1 1), Bool.and_eq_true]
        rcases fin2_cases t with rfl | rfl <;> [exact ⟨hW0, hW1⟩; exact ⟨hW1, hW0⟩]
      have hF := ha.2.2 (pairInput x z) hWa
      rwa [graphFun_pair] at hF
    have hum1 := (hrest um hum_y a1 ha1 b1 hr1).1
    have hum2 := (hrest um hum_y a2 ha2 b2 hr2).1
    have h1 := hadj_of_sides a1 ha1 b1 um hum1 w1 hw1s
    have h2 := hadj_of_sides a2 ha2 b2 um hum2 w2 hw2s
    exact Finset.card_le_one.mp (hW_clause4 um hum_nev) w1
      (Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩, hw1W⟩)
      w2
      (Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩, hw2W⟩)
  have hwmix_ex : ∀ w ∈ Wmix, ∃ m ∈ mixing G C, n + g ∈ (gateAt C m).inputs ∧
      ∃ a ∈ tops G C, ∃ ba : Fin 2, OrReaches n C (opnd C a ba) m ∧ w ∈ side (n := n) C a (1 - ba) := by
    intro w hw
    obtain ⟨hwU, hw_notCL⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨hwW, hw_ustar⟩ := Finset.mem_filter.mp hwU
    have hwv : G.Adj w v := (hv_adj_W w hwW).symm
    obtain ⟨_, _, htri⟩ := ustar_edge_structure G C h4 hE hL hT g hg w v hwv hw_ustar
    rcases htri with ⟨a, haCL, ba, hbag, hsubW, hwv_side⟩ | ⟨a, ha_top, _, ba, _, m, hm, hm_reach, hgm,
        _, _, _, _, _, _, _, z, hzW, _, hz_eq, hz_side, _, _⟩
    · exfalso
      apply hw_notCL
      refine Finset.mem_filter.mpr ⟨hwU, a, haCL, ba, hbag, ?_⟩
      rcases hwv_side with h | h
      · exact h
      · exact absurd (hsubW h) hv_notW
    · have hzw : z = w := by
        rcases hz_eq with h | h
        · exact h
        · exact absurd (h ▸ hzW) hv_notW
      subst z
      exact ⟨m, hm, hgm, a, ha_top, ba, hm_reach, hz_side⟩
  let fmix : Fin n → ℕ := fun w => if h : w ∈ Wmix then (hwmix_ex w h).choose else 0
  have hfmix_mem : ∀ w ∈ Wmix, fmix w ∈ mixing G C := fun w hw => by
    simp only [fmix, hw, ↓reduceDIte]; exact (hwmix_ex w hw).choose_spec.1
  have hfmix_inj : Set.InjOn fmix Wmix := by
    intro w1 hw1 w2 hw2 heq
    have h1 := (hwmix_ex w1 hw1).choose_spec
    have h2 := (hwmix_ex w2 hw2).choose_spec
    have hm1eq : fmix w1 = (hwmix_ex w1 hw1).choose := by dsimp only [fmix]; split_ifs <;> first | rfl | contradiction
    have hm2eq : fmix w2 = (hwmix_ex w2 hw2).choose := by dsimp only [fmix]; split_ifs <;> first | rfl | contradiction
    have hmeq : (hwmix_ex w1 hw1).choose = (hwmix_ex w2 hw2).choose := by rw [← hm1eq, ← hm2eq, heq]
    obtain ⟨hm1, hgm1, a1, ha1, b1, hr1, hs1⟩ := h1
    obtain ⟨hm2, hgm2, a2, ha2, b2, hr2, hs2⟩ := h2
    rw [← hmeq] at hr2
    have hw1W : w1 ∈ wmax G C g := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hw1).1).1
    have hw2W : w2 ∈ wmax G C g := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hw2).1).1
    exact hmix_witness_uniq _ hm1 hgm1 a1 a2 b1 b2 w1 w2 ha1 hr1 hs1 hw1W ha2 hr2 hs2 hw2W
  have hWmix_le : Wmix.card ≤ (mixing G C).card := by
    have hsub : Wmix.image fmix ⊆ mixing G C := by
      intro m hm; obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hm; exact hfmix_mem w hw
    rw [← Finset.card_image_of_injOn hfmix_inj]
    exact Finset.card_le_card hsub
  have hXcov : ∀ e ∈ Ustar G C, ∃ z ∈ K ∪ {v, wP}, z ∈ e := by
    intro e he
    rw [hU_eq, Finset.mem_union] at he
    rcases he with h1 | h2
    · obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp h1
      exact ⟨wP, Finset.mem_union_right _ (by simp), Sym2.mem_mk_left _ _⟩
    · obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp h2
      exact ⟨v, Finset.mem_union_right _ (by simp), Sym2.mem_mk_right _ _⟩
  have hxcard : (({v, wP} : Finset (Fin n)) \ K).card ≤ 2 :=
    (Finset.card_le_card Finset.sdiff_subset).trans Finset.card_le_two
  apply cover_of_budget G C g K hKcov h1528 {v, wP} hXcov
  omega

lemma cover_with_singletons {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (K : Finset (Fin n))
    (hKcov : ∀ e ∈ starEdges G C, ∃ v ∈ K, v ∈ e)
    (hformU : formU G C g ⊆ K) (hformZ : formZ G C g ⊆ K)
    (h1528 : G.edgeFinset.card + K.card + (pen G C g K).card + 1 +
      (mixing G C).card + 2 * (centreless G C).card + (coneGates G C g).card ≤
      C.size + (Ustar G C).card + 1)
    (hUne : (Ustar G C).Nonempty)
    (hIne : (side (n := n) C g 0 ∩ side (n := n) C g 1).Nonempty) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  obtain ⟨hPne, hQne, hgeval, hW_iff, _, _, _, _, _⟩ := g_semantics G C hL hT g hg
  by_cases hP1 : (side (n := n) C g 0).card ≤ 1
  · obtain ⟨v, hvI⟩ := hIne
    have hv0 : v ∈ side (n := n) C g 0 := (Finset.mem_inter.mp hvI).1
    have hv1 : v ∈ side (n := n) C g 1 := (Finset.mem_inter.mp hvI).2
    have hPeq : side (n := n) C g 0 = {v} := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (le_antisymm hP1 (Finset.card_pos.mpr hPne))
      have : v = x := by rw [hx, Finset.mem_singleton] at hv0; exact hv0
      rw [hx, this]
    exfalso
    refine replace_gate_by_wire G C hE hL hT g hg v.val (by have := v.isLt; omega) ?_ (Or.inl ?_)
    · intro x y huv hU
      obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg x y huv hU
      rw [← W_eq_gateVal, hgeval, hPeq] at hgtrue
      obtain ⟨⟨p, hp, hpx⟩, _⟩ := hgtrue
      rw [Finset.mem_singleton] at hp; subst p
      rw [W_input n C _ v.val v.isLt]; exact hpx
    · intro x hxv
      rw [W_input n C x v.val v.isLt] at hxv
      rw [hgeval]; exact ⟨⟨v, hv0, hxv⟩, ⟨v, hv1, hxv⟩⟩
  by_cases hQ1 : (side (n := n) C g 1).card ≤ 1
  · obtain ⟨v, hvI⟩ := hIne
    have hv0 : v ∈ side (n := n) C g 0 := (Finset.mem_inter.mp hvI).1
    have hv1 : v ∈ side (n := n) C g 1 := (Finset.mem_inter.mp hvI).2
    have hQeq : side (n := n) C g 1 = {v} := by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (le_antisymm hQ1 (Finset.card_pos.mpr hQne))
      have : v = x := by rw [hx, Finset.mem_singleton] at hv1; exact hv1
      rw [hx, this]
    exfalso
    refine replace_gate_by_wire G C hE hL hT g hg v.val (by have := v.isLt; omega) ?_ (Or.inl ?_)
    · intro x y huv hU
      obtain ⟨hgtrue, _, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg x y huv hU
      rw [← W_eq_gateVal, hgeval, hQeq] at hgtrue
      obtain ⟨_, ⟨q, hq, hqx⟩⟩ := hgtrue
      rw [Finset.mem_singleton] at hq; subst q
      rw [W_input n C _ v.val v.isLt]; exact hqx
    · intro x hxv
      rw [W_input n C x v.val v.isLt] at hxv
      rw [hgeval]; exact ⟨⟨v, hv0, hxv⟩, ⟨v, hv1, hxv⟩⟩
  have hP2 : 2 ≤ (side (n := n) C g 0).card := by omega
  have hQ2 : 2 ≤ (side (n := n) C g 1).card := by omega
  by_cases hI2 : 2 ≤ (side (n := n) C g 0 ∩ side (n := n) C g 1).card
  · exact cover_inter_ge_two G h4 hE C hL hT g hg K hKcov h1528 hUne hI2
  have hI1 : (side (n := n) C g 0 ∩ side (n := n) C g 1).card = 1 :=
    le_antisymm (by omega) (Finset.card_pos.mpr hIne)
  obtain ⟨v, hInter⟩ := Finset.card_eq_one.mp hI1
  have h1529 := thm_1529 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have h1530 := thm_1530 n G h4 (side (n := n) C g 0) (side (n := n) C g 1) (wmax G C g) hW_iff
  have hv_mem : v ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := by rw [hInter]; simp
  by_cases hWP : (wmax G C g ∩ side (n := n) C g 0).Nonempty
  · obtain ⟨wP, hwP_eq⟩ := Finset.card_eq_one.mp (le_antisymm (h1530.1 hQ2) (Finset.card_pos.mpr hWP))
    have hwPW : wP ∈ wmax G C g := (Finset.mem_inter.mp (by rw [hwP_eq]; simp)).1
    have hwPP : wP ∈ side (n := n) C g 0 := (Finset.mem_inter.mp (by rw [hwP_eq]; simp)).2
    have hWQ_empty : wmax G C g ∩ side (n := n) C g 1 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro wQ hwQ
      obtain ⟨hwQW, hwQQ⟩ := Finset.mem_inter.mp hwQ
      have hadj := (h1529.1 wP hwPW hwPP).2 wQ hwQQ
      exact htri v wP wQ (h1529.2.2.1 v hv_mem wP hwPW) hadj
        (h1529.2.2.1 v hv_mem wQ hwQW).symm
    exact cover_inter_one_side G htri h4 hE C hL hT g hg K hKcov hformU hformZ h1528
      v hInter 0 wP hwP_eq hWQ_empty
  · rw [Finset.not_nonempty_iff_eq_empty] at hWP
    by_cases hWQ : (wmax G C g ∩ side (n := n) C g 1).Nonempty
    · obtain ⟨wQ, hwQ_eq⟩ := Finset.card_eq_one.mp (le_antisymm (h1530.2.1 hP2) (Finset.card_pos.mpr hWQ))
      exact cover_inter_one_side G htri h4 hE C hL hT g hg K hKcov hformU hformZ h1528
        v hInter 1 wQ hwQ_eq hWP
    · rw [Finset.not_nonempty_iff_eq_empty] at hWQ
      exfalso
      refine replace_gate_by_wire G C hE hL hT g hg v.val (by have := v.isLt; omega) ?_ (Or.inl ?_)
      · intro x y hxy hU
        obtain ⟨hgtrue, hxyW, _⟩ := ustar_edge_structure G C h4 hE hL hT g hg x y hxy hU
        obtain ⟨h0, h1⟩ := g_pair_sides G C hL hT g hg x y hgtrue
        have hv_xy : x = v ∨ y = v := by
          rcases hxyW with hxW | hyW
          · have hx_notP : x ∉ side (n := n) C g 0 := fun h => by
              have : x ∈ wmax G C g ∩ side (n := n) C g 0 := Finset.mem_inter.mpr ⟨hxW, h⟩
              rw [hWP] at this; exact Finset.notMem_empty _ this
            have hx_notQ : x ∉ side (n := n) C g 1 := fun h => by
              have : x ∈ wmax G C g ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hxW, h⟩
              rw [hWQ] at this; exact Finset.notMem_empty _ this
            have hyI := (h1530.2.2.1 x y hxy h0 h1 hxW).2.2 hx_notP hx_notQ
            rw [hInter, Finset.mem_singleton] at hyI
            exact Or.inr hyI
          · have hy_notP : y ∉ side (n := n) C g 0 := fun h => by
              have : y ∈ wmax G C g ∩ side (n := n) C g 0 := Finset.mem_inter.mpr ⟨hyW, h⟩
              rw [hWP] at this; exact Finset.notMem_empty _ this
            have hy_notQ : y ∉ side (n := n) C g 1 := fun h => by
              have : y ∈ wmax G C g ∩ side (n := n) C g 1 := Finset.mem_inter.mpr ⟨hyW, h⟩
              rw [hWQ] at this; exact Finset.notMem_empty _ this
            have hxI := (h1530.2.2.1 y x hxy.symm h0.symm h1.symm hyW).2.2 hy_notP hy_notQ
            rw [hInter, Finset.mem_singleton] at hxI
            exact Or.inl hxI
        rw [W_input n C _ v.val v.isLt, pairInput_true]
        rcases hv_xy with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
      · intro x hxv
        rw [W_input n C x v.val v.isLt] at hxv
        rw [hgeval]
        exact ⟨⟨v, (Finset.mem_inter.mp hv_mem).1, hxv⟩, ⟨v, (Finset.mem_inter.mp hv_mem).2, hxv⟩⟩
lemma one_junk_cover_all {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (h4 : NoFourCycle G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hg : junk G C = {g}) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  by_cases hsil : ∀ u : Fin n, gateVal n C g (pairInput u u) = false
  · exact one_junk_cover G C g h4 htri hL hT hg hsil
  have hIne : (side (n := n) C g 0 ∩ side (n := n) C g 1).Nonempty := by
    push Not at hsil
    obtain ⟨u, hu⟩ := hsil
    have hu' : gateVal n C g (pairInput u u) = true := by
      cases h : gateVal n C g (pairInput u u) <;> simp_all
    rw [← W_eq_gateVal] at hu'
    obtain ⟨⟨v, hv, hvu⟩, ⟨w, hw, hwu⟩⟩ :=
      ((g_semantics G C hL hT g hg).2.2.1 (pairInput u u)).mp hu'
    have hv_eq : v = u := by simpa [pairInput] using hvu
    have hw_eq : w = u := by simpa [pairInput] using hwu
    subst v
    subst w
    exact ⟨u, Finset.mem_inter.mpr ⟨hv, hw⟩⟩
  by_cases hE : G.edgeFinset.Nonempty
  · obtain ⟨K, hKcov, hformU, hformZ, h1528⟩ := thm_1528 n G C h4 hE hL hT g hg
    by_cases hUne : (Ustar G C).Nonempty
    · exact cover_with_singletons G htri h4 hE C hL hT g hg K hKcov hformU hformZ h1528 hUne hIne
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

lemma least_single_junk_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h4 : NoFourCycle G)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hL : IsLeastAO G C) (hg : (junk G C).card = 1) :
    ∃ T : Finset (Fin n), (∀ e ∈ G.edgeFinset, ∃ v ∈ T, v ∈ e) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  by_cases hE : G.edgeFinset.Nonempty
  · obtain ⟨D, hLD, hsz, hJ, hTD⟩ := thm_1501 n G C hE hL
    obtain ⟨g, hgj⟩ := Finset.card_eq_one.mp (hJ.trans hg)
    obtain ⟨T, hTc, hTs⟩ := one_junk_cover_all G D g h4 htri hLD hTD hgj
    exact ⟨T, hTc, by rwa [hsz] at hTs⟩
  · have hE0 : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    refine ⟨∅, ?_, ?_⟩
    · intro e he
      rw [hE0] at he
      exact (Finset.notMem_empty _ he).elim
    · rw [hE0]
      simp

end PEqualNP.Outside.L_meta_2448_aux.oneJunk


-- Scratch prototype using outside modules; these are not approved final dependencies.
namespace PEqualNP.Outside.L_meta_2448.StarCoverPrototype
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3760
open PEqualNP.Outside.L_meta_3760.Close
open PEqualNP.Outside.L_meta_3760.M1528.P1.S98

lemma orTree_all_or (base : ℕ) (ws : List ℕ) :
    ∀ g ∈ (orTreeGates base ws).1, g.op = GateOp.or := by
  induction ws with
  | nil => simp [orTreeGates]
  | cons w ws ih =>
    cases ws with
    | nil => simp [orTreeGates]
    | cons u us =>
      intro g hg
      simp only [orTreeGates, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact ih g hg
      · rfl

theorem star_cover_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hE : G.edgeFinset.Nonempty)
    (K0 : Finset (Fin n)) (hcov : ∀ e ∈ G.edgeFinset, ∃ v ∈ K0, v ∈ e) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      HasStarProfile n G D ∧ D.size + 1 ≤ G.edgeFinset.card + K0.card := by
  classical
  let owner : Sym2 (Fin n) → Fin n := fun e =>
    if h : e ∈ G.edgeFinset then (hcov e h).choose else (hE.choose.out).1
  have howner_mem : ∀ e (he : e ∈ G.edgeFinset), owner e ∈ K0 ∧ owner e ∈ e := by
    intro e he
    simp only [owner, dite_eq_left, he]
    exact (hcov e he).choose_spec
  let L : Fin n → Finset (Fin n) := fun v =>
    Finset.univ.filter fun u => ∃ h : s(v, u) ∈ G.edgeFinset, owner s(v, u) = v
  have hL_adj : ∀ v u, u ∈ L v → G.Adj v u := by
    intro v u hu
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact SimpleGraph.mem_edgeFinset.mp hu.1
  have hL_edge_iff : ∀ u v, G.Adj u v → (v ∈ L u ∨ u ∈ L v) ∧ (u ∈ K0 ∧ v ∈ L u ∨ v ∈ K0 ∧ u ∈ L v) := by
    intro u v huv
    have he : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    obtain ⟨hK, hmem⟩ := howner_mem s(u, v) he
    rcases Sym2.mem_iff.mp hmem with h | h
    · have hu : v ∈ L u := by
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨he, h⟩
      exact ⟨Or.inl hu, Or.inl ⟨h ▸ hK, hu⟩⟩
    · have hv : u ∈ L v := by
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        have he' : s(v, u) ∈ G.edgeFinset := by rw [Sym2.eq_swap]; exact he
        exact ⟨he', by rw [Sym2.eq_swap]; exact h⟩
      exact ⟨Or.inr hv, Or.inr ⟨h ▸ hK, hv⟩⟩
  have hsum : (∑ v ∈ K0, (L v).card) = G.edgeFinset.card := by
    have hbij : (K0.sigma L).card = G.edgeFinset.card := by
      refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_sigma] at hp
        exact SimpleGraph.mem_edgeFinset.mpr (hL_adj p.1 p.2 hp.2)
      · intro p1 hp1 p2 hp2 heq
        simp only [Finset.mem_sigma, L, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
        have h1 : p1.1 = p2.1 := by
          rw [← hp1.2.2, heq, hp2.2.2]
        have h2 : p1.2 = p2.2 := by
          have : s(p1.1, p1.2) = s(p1.1, p2.2) := by rw [← h1] at heq; exact heq
          rcases Sym2.eq_iff.mp this with ⟨_, hb⟩ | ⟨_, hb⟩
          · exact hb
          · have hadj : G.Adj p1.1 p1.2 := SimpleGraph.mem_edgeFinset.mp hp1.2.1
            rw [hb] at hadj
            exact (G.irrefl hadj).elim
        exact Sigma.ext h1 (heq_of_eq h2)
      · intro e he
        induction e using Sym2.ind with
        | _ u v =>
          have huv := SimpleGraph.mem_edgeFinset.mp he
          rcases (hL_edge_iff u v huv).2 with ⟨huK, hvL⟩ | ⟨hvK, huL⟩
          · exact ⟨⟨u, v⟩, Finset.mem_sigma.mpr ⟨huK, hvL⟩, rfl⟩
          · exact ⟨⟨v, u⟩, Finset.mem_sigma.mpr ⟨hvK, huL⟩, Sym2.eq_swap⟩
    rw [Finset.card_sigma] at hbij
    exact hbij
  let M := K0.filter fun v => (L v).Nonempty
  have hM_sub : M ⊆ K0 := Finset.filter_subset _ _
  have hM_ne : M.Nonempty := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ u v =>
      rcases (hL_edge_iff u v (SimpleGraph.mem_edgeFinset.mp he)).2 with ⟨huK, hvL⟩ | ⟨hvK, huL⟩
      · exact ⟨u, Finset.mem_filter.mpr ⟨huK, ⟨v, hvL⟩⟩⟩
      · exact ⟨v, Finset.mem_filter.mpr ⟨hvK, ⟨u, huL⟩⟩⟩
  have hsumM : (∑ v ∈ M, (L v).card) = G.edgeFinset.card := by
    rw [← hsum]
    refine Finset.sum_subset hM_sub ?_
    intro v hv hnotM
    simp only [M, Finset.mem_filter, not_and, Finset.not_nonempty_iff_eq_empty] at hnotM
    rw [hnotM hv, Finset.card_empty]
  let buildStars : List (Fin n) → List Gate × List ℕ :=
    List.foldl (fun (acc : List Gate × List ℕ) (v : Fin n) =>
      let ws := (L v).toList.map Fin.val
      let (gs, out) := orTreeGates (n + acc.1.length) ws
      let andGate : Gate := ⟨GateOp.and, [v.val, out]⟩
      let andWire := n + acc.1.length + gs.length
      (acc.1 ++ gs ++ [andGate], acc.2 ++ [andWire])) ([], [])
  have hbuild_aux : ∀ (vs : List (Fin n)), (∀ v ∈ vs, (L v).Nonempty) →
      let res := buildStars vs
      res.1.length = (vs.map fun v => (L v).card).sum ∧
      res.2.length = vs.length ∧
      (∀ w ∈ res.2, w < n + res.1.length) ∧
      AO n ⟨res.1, 0⟩ ∧
      (∀ x : Fin n → Bool, ∀ w ∈ res.2, W n ⟨res.1, 0⟩ x w = true →
        ∃ v ∈ vs, x v = true ∧ ∃ u ∈ L v, x u = true) ∧
      (∀ x : Fin n → Bool, ∀ v ∈ vs, x v = true → (∃ u ∈ L v, x u = true) →
        ∃ w ∈ res.2, W n ⟨res.1, 0⟩ x w = true) := by
    intro vs
    induction vs using List.reverseRecOn with
    | nil =>
      intro _
      simp [buildStars, AO]
    | append_singleton vs v ih =>
      intro hne
      have hne_vs : ∀ u ∈ vs, (L u).Nonempty := fun u hu => hne u (by simp [hu])
      have hne_v : (L v).Nonempty := hne v (by simp)
      obtain ⟨hlen, hlen2, hlt, hAO, hsound, hcomp⟩ := ih hne_vs
      set acc := buildStars vs
      set ws := (L v).toList.map Fin.val
      have hws_ne : ws ≠ [] := by
        simp only [ws, ne_eq, List.map_eq_nil_iff, Finset.toList_eq_nil]
        exact Finset.nonempty_iff_ne_empty.mp hne_v
      have hws_lt : ∀ w ∈ ws, w < n + acc.1.length := by
        intro w hw
        simp only [ws, List.mem_map] at hw
        obtain ⟨u, _, rfl⟩ := hw
        have := u.isLt; omega
      set ot := orTreeGates (n + acc.1.length) ws
      have hot_len : ot.1.length + 1 = (L v).card := by
        have := orTreeGates_length (n + acc.1.length) ws hws_ne
        simpa [ot, ws] using this
      have hot_out_lt : ot.2 < n + acc.1.length + ot.1.length :=
        orTreeGates_out_lt (n + acc.1.length) ws hws_ne hws_lt
      let andGate : Gate := ⟨GateOp.and, [v.val, ot.2]⟩
      let andWire := n + acc.1.length + ot.1.length
      let newGs := acc.1 ++ ot.1 ++ [andGate]
      have hbuild_eq : buildStars (vs ++ [v]) = (newGs, acc.2 ++ [andWire]) := by
        simp [buildStars, List.foldl_append, acc, newGs, ot, ws, andGate, andWire]
      rw [hbuild_eq]
      have hnewLen : newGs.length = acc.1.length + (L v).card := by
        simp only [newGs, List.length_append, List.length_singleton]
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hnewLen, hlen]
      · simp [hlen2]
      · intro w hw
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · have h1 := hlt w hw
          have h2 : newGs.length = acc.1.length + (L v).card := hnewLen
          change w < n + newGs.length
          omega
        · simp only [andWire, newGs, List.length_append, List.length_singleton]; omega
      · intro k hk
        have hAO_ot := (orTreeGates_eval n acc.1 ws hws_ne hws_lt (fun _ => false)).1
        by_cases hk1 : k < acc.1.length
        · have hg : gateAt ⟨newGs, 0⟩ k = gateAt ⟨acc.1, 0⟩ k := by
            rw [gateAt_eq ⟨newGs, 0⟩ k hk, gateAt_eq ⟨acc.1, 0⟩ k hk1]
            simp only [newGs, List.append_assoc]
            exact List.getElem_append_left hk1
          rw [hg]; exact hAO k hk1
        · by_cases hk2 : k < acc.1.length + ot.1.length
          · have hidx : k - acc.1.length < ot.1.length := by omega
            have hg : gateAt ⟨newGs, 0⟩ k = ot.1[k - acc.1.length]'hidx := by
              rw [gateAt_eq ⟨newGs, 0⟩ k hk]
              simp only [newGs]
              rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
            rw [hg]
            obtain ⟨hop, a, b, hin, ha, hb⟩ := hAO_ot (k - acc.1.length) hidx
            exact ⟨Or.inr hop, a, b, hin, by omega, by omega⟩
          · have hkeq : k = acc.1.length + ot.1.length := by
              simp only [newGs, List.length_append, List.length_singleton] at hk; omega
            subst hkeq
            have hg : gateAt ⟨newGs, 0⟩ (acc.1.length + ot.1.length) = andGate := by
              rw [gateAt_eq ⟨newGs, 0⟩ _ hk]
              simp [newGs]
            rw [hg]
            exact ⟨Or.inl rfl, v.val, ot.2, rfl, by have := v.isLt; omega, by omega⟩
      · intro x w hw hW
        have hpre_eq : ∀ u, u < n + acc.1.length → W n ⟨newGs, 0⟩ x u = W n ⟨acc.1, 0⟩ x u := by
          intro u hu
          have := prefix_W n acc.1 (ot.1 ++ [andGate]) [] 0 0 x u hu
          simpa [newGs, List.append_assoc] using this
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · rw [hpre_eq w (hlt w hw)] at hW
          obtain ⟨u0, hu0, hxu0, z, hzL, hxz⟩ := hsound x w hw hW
          exact ⟨u0, by simp [hu0], hxu0, z, hzL, hxz⟩
        · have hk : acc.1.length + ot.1.length < newGs.length := by
            simp [newGs]
          have hg : gateAt ⟨newGs, 0⟩ (acc.1.length + ot.1.length) = andGate := by
            rw [gateAt_eq ⟨newGs, 0⟩ _ hk]; simp [newGs]
          have hadd : andWire = n + (acc.1.length + ot.1.length) := by simp [andWire]; omega
          rw [hadd, W_and n ⟨newGs, 0⟩ x _ hk (by rw [hg]) v.val ot.2 (by rw [hg])
            (by have := v.isLt; omega) (by omega), Bool.and_eq_true] at hW
          rw [W_input n ⟨newGs, 0⟩ x v.val v.isLt] at hW
          have hot_eq : W n ⟨newGs, 0⟩ x ot.2 = W n ⟨acc.1 ++ ot.1, ot.2⟩ x ot.2 := by
            have := prefix_W n (acc.1 ++ ot.1) [andGate] [] 0 ot.2 x ot.2
              (by simp; omega)
            simpa [newGs] using this
          rw [hot_eq, (orTreeGates_eval n acc.1 ws hws_ne hws_lt x).2] at hW
          obtain ⟨uval, huval, hWu⟩ := hW.2
          simp only [ws, List.mem_map, Finset.mem_toList] at huval
          obtain ⟨u, huL, rfl⟩ := huval
          rw [W_input n ⟨acc.1, 0⟩ x u.val u.isLt] at hWu
          exact ⟨v, by simp, hW.1, u, huL, hWu⟩
      · intro x v0 hv0 hxv0 ⟨u, huL, hxu⟩
        have hpre_eq : ∀ u', u' < n + acc.1.length → W n ⟨newGs, 0⟩ x u' = W n ⟨acc.1, 0⟩ x u' := by
          intro u' hu'
          have := prefix_W n acc.1 (ot.1 ++ [andGate]) [] 0 0 x u' hu'
          simpa [newGs, List.append_assoc] using this
        simp only [List.mem_append, List.mem_singleton] at hv0
        rcases hv0 with hv0 | rfl
        · obtain ⟨w, hw, hW⟩ := hcomp x v0 hv0 hxv0 ⟨u, huL, hxu⟩
          exact ⟨w, by simp [hw], by rw [hpre_eq w (hlt w hw)]; exact hW⟩
        · refine ⟨andWire, by simp, ?_⟩
          have hk : acc.1.length + ot.1.length < newGs.length := by simp [newGs]
          have hg : gateAt ⟨newGs, 0⟩ (acc.1.length + ot.1.length) = andGate := by
            rw [gateAt_eq ⟨newGs, 0⟩ _ hk]; simp [newGs]
          have hadd : andWire = n + (acc.1.length + ot.1.length) := by simp [andWire]; omega
          rw [hadd, W_and n ⟨newGs, 0⟩ x _ hk (by rw [hg]) v0.val ot.2 (by rw [hg])
            (by have := v0.isLt; omega) (by omega), Bool.and_eq_true,
            W_input n ⟨newGs, 0⟩ x v0.val v0.isLt]
          refine ⟨hxv0, ?_⟩
          have hot_eq : W n ⟨newGs, 0⟩ x ot.2 = W n ⟨acc.1 ++ ot.1, ot.2⟩ x ot.2 := by
            have := prefix_W n (acc.1 ++ ot.1) [andGate] [] 0 ot.2 x ot.2
              (by simp; omega)
            simpa [newGs] using this
          rw [hot_eq, (orTreeGates_eval n acc.1 ws hws_ne hws_lt x).2]
          refine ⟨u.val, List.mem_map.mpr ⟨u, Finset.mem_toList.mpr huL, rfl⟩, ?_⟩
          rw [W_input n ⟨acc.1, 0⟩ x u.val u.isLt]
          exact hxu
  let vs := M.toList
  have hvs_ne : ∀ v ∈ vs, (L v).Nonempty := by
    intro v hv
    simp only [vs, Finset.mem_toList, M, Finset.mem_filter] at hv
    exact hv.2
  obtain ⟨hlen1, hlen2, hlt, hAO1, hsound1, hcomp1⟩ := hbuild_aux vs hvs_ne
  set bs := buildStars vs
  have hbs2_ne : bs.2 ≠ [] := by
    intro h
    have h1 : vs.length = 0 := by rw [← hlen2, h]; rfl
    have : M = ∅ := by
      rw [← Finset.card_eq_zero, ← Finset.length_toList, h1]
    exact Finset.nonempty_iff_ne_empty.mp hM_ne this
  set top := orTreeGates (n + bs.1.length) bs.2
  let D : Circuit := ⟨bs.1 ++ top.1, top.2⟩
  have hD_AO : AO n D := by
    intro k hk
    have hAO_top := (orTreeGates_eval n bs.1 bs.2 hbs2_ne hlt (fun _ => false)).1
    by_cases hk1 : k < bs.1.length
    · have hg : gateAt D k = gateAt ⟨bs.1, 0⟩ k := by
        rw [gateAt_eq D k hk, gateAt_eq ⟨bs.1, 0⟩ k hk1]
        exact List.getElem_append_left hk1
      rw [hg]; exact hAO1 k hk1
    · have hidx : k - bs.1.length < top.1.length := by simp [D] at hk; omega
      have hg : gateAt D k = top.1[k - bs.1.length]'hidx := by
        rw [gateAt_eq D k hk]
        exact List.getElem_append_right (by omega)
      rw [hg]
      obtain ⟨hop, a, b, hin, ha, hb⟩ := hAO_top (k - bs.1.length) hidx
      exact ⟨Or.inr hop, a, b, hin, by omega, by omega⟩
  have hD_fun : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [Bool.eq_iff_iff]
    have hDeval : circuitFun n D x = W n D x top.2 := rfl
    rw [hDeval, (orTreeGates_eval n bs.1 bs.2 hbs2_ne hlt x).2]
    constructor
    · rintro ⟨w, hw, hW⟩
      obtain ⟨v, hv, hxv, u, huL, hxu⟩ := hsound1 x w hw hW
      have hadj : G.Adj v u := hL_adj v u huL
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨v, u, hadj, hxv, hxu⟩
    · intro hG
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] at hG
      obtain ⟨u, v, hadj, hxu, hxv⟩ := hG
      rcases (hL_edge_iff u v hadj).2 with ⟨huK, hvL⟩ | ⟨hvK, huL⟩
      · have huM : u ∈ vs := by
          simp only [vs, Finset.mem_toList, M, Finset.mem_filter]
          exact ⟨huK, ⟨v, hvL⟩⟩
        exact hcomp1 x u huM hxu ⟨v, hvL, hxv⟩
      · have hvM : v ∈ vs := by
          simp only [vs, Finset.mem_toList, M, Finset.mem_filter]
          exact ⟨hvK, ⟨u, huL⟩⟩
        exact hcomp1 x v hvM hxv ⟨u, huL, hxu⟩
  have hD_size : D.size + 1 = G.edgeFinset.card + M.card := by
    have htop_len : top.1.length + 1 = bs.2.length :=
      orTreeGates_length (n + bs.1.length) bs.2 hbs2_ne
    have hsum_vs : (vs.map fun v => (L v).card).sum = G.edgeFinset.card := by
      rw [← hsumM]
      simp [vs]
    have hvs_len : vs.length = M.card := Finset.length_toList M
    have h1 : bs.1.length = G.edgeFinset.card := by rw [hlen1, hsum_vs]
    have h2 : bs.2.length = M.card := by rw [hlen2, hvs_len]
    simp only [Circuit.size, D, List.length_append]
    omega
  have hbuild_primary : ∀ vs, ∀ g ∈ (buildStars vs).1, g.op = GateOp.and →
      ∃ a : Fin n, a.val ∈ g.inputs := by
    intro vs
    induction vs using List.reverseRecOn with
    | nil => simp [buildStars]
    | append_singleton vs v ih =>
      intro g hg hop
      simp only [buildStars, List.foldl_append, List.foldl_cons, List.foldl_nil] at hg
      change g ∈ ((buildStars vs).1 ++
        (orTreeGates (n + (buildStars vs).1.length) ((L v).toList.map Fin.val)).1 ++
        [⟨GateOp.and, [v.val,
          (orTreeGates (n + (buildStars vs).1.length) ((L v).toList.map Fin.val)).2]⟩]) at hg
      rcases List.mem_append.mp hg with hg | hg
      · rcases List.mem_append.mp hg with hg | hg
        · exact ih g hg hop
        · have hor := orTree_all_or _ _ g hg
          rw [hop] at hor
          cases hor
      · simp only [List.mem_singleton] at hg
        subst g
        exact ⟨v, by simp⟩
  have hD_primary : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ∃ a : Fin n, a.val ∈ (gateAt D j).inputs := by
    intro j hj hop
    have hmem : gateAt D j ∈ D.gates := by
      rw [gateAt_eq D j hj]
      exact List.getElem_mem hj
    change gateAt D j ∈ bs.1 ++ top.1 at hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hbuild_primary vs _ hmem hop
    · have hor := orTree_all_or _ _ (gateAt D j) hmem
      rw [hop] at hor
      cases hor
  have hD_mono : Monotone2 D := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have h := hD_AO j hj
    rw [gateAt_eq D j hj] at h
    obtain ⟨hop, a, b, hin, _, _⟩ := h
    constructor
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
    · simp [hin]
  refine ⟨D, hD_mono, hD_fun,
    PEqualNP.Outside.L_meta_2448.cross.star_of_primary_operands G D hD_primary, ?_⟩
  have hM_le : M.card ≤ K0.card := Finset.card_le_card hM_sub
  omega

end PEqualNP.Outside.L_meta_2448.StarCoverPrototype

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

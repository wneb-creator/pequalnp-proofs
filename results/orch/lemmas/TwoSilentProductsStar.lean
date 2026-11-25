import PEqualNP.Outside.L_meta_2448
import PEqualNP.Outside.L_meta_2074

namespace PEqualNP.Outside.L_meta_2448_aux.twoSilentProducts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def Cross {n : ℕ} (L R : Finset (Fin n)) (u v : Fin n) : Prop :=
  (u ∈ L ∧ v ∈ R) ∨ (v ∈ L ∧ u ∈ R)

lemma cross_mem {n : ℕ} {L R : Finset (Fin n)} {u v : Fin n}
    (h : Cross L R u v) : u ∈ L ∪ R ∧ v ∈ L ∪ R := by
  unfold Cross at h
  simp only [Finset.mem_union]
  tauto

lemma star_forest_cover_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (K : Finset (Fin n))
    (hc : ∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K)
    (hi : ∀ u ∈ K, ∀ v ∈ K, ¬ G.Adj u v)
    (hl : ∀ u, u ∉ K → ∀ v w, G.Adj u v → G.Adj u w → v = w)
    (ha : ∀ u ∈ K, u ∈ G.support) :
    G.edgeFinset.card + K.card ≤ G.support.ncard := by
  classical
  have hex : ∀ e ∈ G.edgeFinset, ∃ u, ∃ v,
      u ∉ K ∧ v ∈ K ∧ G.Adj u v ∧ e = s(u, v) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      rcases hc u v huv with hu | hv
      · exact ⟨v, u, fun hv => hi u hu v hv huv, hu, huv.symm, Sym2.eq_swap⟩
      · exact ⟨u, v, fun hu => hi u hu v hv huv, hv, huv, rfl⟩
  let leaf : {e // e ∈ G.edgeFinset} → Fin n := fun e => (hex e.val e.property).choose
  have hp : ∀ e : {e // e ∈ G.edgeFinset}, ∃ v,
      leaf e ∉ K ∧ v ∈ K ∧ G.Adj (leaf e) v ∧ e.val = s(leaf e, v) := by
    intro e
    exact (hex e.val e.property).choose_spec
  have hinj : Set.InjOn leaf (G.edgeFinset.attach : Set {e // e ∈ G.edgeFinset}) := by
    intro e1 _ e2 _ he
    obtain ⟨v1, h1, _, ha1, hv1⟩ := hp e1
    obtain ⟨v2, _, _, ha2, hv2⟩ := hp e2
    have hv : v1 = v2 := hl (leaf e1) h1 v1 v2 ha1 (he ▸ ha2)
    apply Subtype.ext
    rw [hv1, hv2, he, hv]
  let L := G.edgeFinset.attach.image leaf
  have hcard : L.card = G.edgeFinset.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_attach]
  have hd : Disjoint K L := by
    apply Finset.disjoint_left.mpr
    intro u hu hL
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hL
    exact (hp e).choose_spec.1 hu
  have hs : ((K ∪ L : Finset (Fin n)) : Set (Fin n)) ⊆ G.support := by
    intro u hu
    rcases Finset.mem_union.mp hu with huK | huL
    · exact ha u huK
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp huL
      obtain ⟨v, _, _, huv, _⟩ := hp e
      exact huv.mem_support_left
  have hn := Set.ncard_le_ncard hs (Set.toFinite G.support)
  rw [Set.ncard_coe_finset, Finset.card_union_of_disjoint hd, hcard] at hn
  omega

lemma biclique_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (L R : Finset (Fin n))
    (hedge : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v) :
    ∃ K : Finset (Fin n), K ⊆ L ∪ R ∧ K.card ≤ 1 ∧
      (∀ u ∈ K, u ∈ G.support) ∧
      ∀ u v, Cross L R u v → u ∈ K ∨ v ∈ K := by
  classical
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · have hsmall : L.card ≤ 1 ∨ R.card ≤ 1 := by
        by_contra! h
        obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h.1
        have hs : R ⊆ Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w) := by
          intro w hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge u hu w hw, hedge v hv w hw⟩
        have hcard := Finset.card_le_card hs
        have hfour := h4 u v huv
        omega
      rcases hsmall with hsmall | hsmall
      · obtain ⟨u, hLu⟩ := Finset.card_eq_one.mp (le_antisymm hsmall (Finset.card_pos.mpr hL))
        obtain ⟨v, hv⟩ := hR
        refine ⟨{u}, ?_, by simp, ?_, ?_⟩
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          apply Finset.mem_union_left
          rw [hLu]
          simp
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          exact (hedge u (by rw [hLu]; simp) v hv).mem_support_left
        · intro a b hab
          simp only [Cross, hLu, Finset.mem_singleton] at hab ⊢
          tauto
      · obtain ⟨v, hRv⟩ := Finset.card_eq_one.mp (le_antisymm hsmall (Finset.card_pos.mpr hR))
        obtain ⟨u, hu⟩ := hL
        refine ⟨{v}, ?_, by simp, ?_, ?_⟩
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          apply Finset.mem_union_right
          rw [hRv]
          simp
        · intro w hw
          rw [Finset.mem_singleton] at hw
          subst w
          exact (hedge u hu v (by rw [hRv]; simp)).mem_support_right
        · intro a b hab
          simp only [Cross, hRv, Finset.mem_singleton] at hab ⊢
          tauto
    · refine ⟨∅, by simp, by simp, by simp, ?_⟩
      have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
      simp [Cross, he]
  · refine ⟨∅, by simp, by simp, by simp, ?_⟩
    have he : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    simp [Cross, he]

lemma two_disjoint_bicliques_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A B C D : Finset (Fin n))
    (hd : Disjoint (A ∪ B) (C ∪ D))
    (hedge : ∀ u v, G.Adj u v ↔ Cross A B u v ∨ Cross C D u v) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card + K.card ≤ G.support.ncard := by
  classical
  obtain ⟨K1, hs1, hc1, ha1, he1⟩ := biclique_cover G h4 A B
    (fun u hu v hv => (hedge u v).mpr (Or.inl (Or.inl ⟨hu, hv⟩)))
  obtain ⟨K2, hs2, hc2, ha2, he2⟩ := biclique_cover G h4 C D
    (fun u hu v hv => (hedge u v).mpr (Or.inr (Or.inl ⟨hu, hv⟩)))
  have sep : ∀ u, u ∈ A ∪ B → u ∈ C ∪ D → False := Finset.disjoint_left.mp hd
  have k1 (u : Fin n) (hu : u ∈ A ∪ B) (hk : u ∈ K1 ∪ K2) : u ∈ K1 := by
    rcases Finset.mem_union.mp hk with hk | hk
    · exact hk
    · exact (sep u hu (hs2 hk)).elim
  have k2 (u : Fin n) (hu : u ∈ C ∪ D) (hk : u ∈ K1 ∪ K2) : u ∈ K2 := by
    rcases Finset.mem_union.mp hk with hk | hk
    · exact (sep u (hs1 hk) hu).elim
    · exact hk
  have hcov : ∀ u v, G.Adj u v → u ∈ K1 ∪ K2 ∨ v ∈ K1 ∪ K2 := by
    intro u v huv
    rcases (hedge u v).mp huv with h | h
    · rcases he1 u v h with h | h
      · exact Or.inl (Finset.mem_union_left _ h)
      · exact Or.inr (Finset.mem_union_left _ h)
    · rcases he2 u v h with h | h
      · exact Or.inl (Finset.mem_union_right _ h)
      · exact Or.inr (Finset.mem_union_right _ h)
  refine ⟨K1 ∪ K2, hcov, star_forest_cover_budget G (K1 ∪ K2) hcov ?_ ?_ ?_⟩
  · intro u hu v hv huv
    have heq : u = v := by
      rcases (hedge u v).mp huv with h | h
      · exact Finset.card_le_one.mp hc1 u (k1 u (cross_mem h).1 hu) v (k1 v (cross_mem h).2 hv)
      · exact Finset.card_le_one.mp hc2 u (k2 u (cross_mem h).1 hu) v (k2 v (cross_mem h).2 hv)
    exact huv.ne heq
  · intro u hu v w huv huw
    have hv : v ∈ K1 ∪ K2 := (hcov u v huv).resolve_left hu
    have hw : w ∈ K1 ∪ K2 := (hcov u w huw).resolve_left hu
    rcases (hedge u v).mp huv with h1 | h1
    · rcases (hedge u w).mp huw with h2 | h2
      · exact Finset.card_le_one.mp hc1 v (k1 v (cross_mem h1).2 hv) w (k1 w (cross_mem h2).2 hw)
      · exact (sep u (cross_mem h1).1 (cross_mem h2).1).elim
    · rcases (hedge u w).mp huw with h2 | h2
      · exact (sep u (cross_mem h2).1 (cross_mem h1).1).elim
      · exact Finset.card_le_one.mp hc2 v (k2 v (cross_mem h1).2 hv) w (k2 w (cross_mem h2).2 hw)
  · intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact ha1 u h
    · exact ha2 u h

set_option maxHeartbeats 4000000 in
lemma four_sides_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (P Q R S : Finset (Fin n))
    (hPQ : Disjoint P Q) (hRS : Disjoint R S)
    (hedge : ∀ u v, G.Adj u v ↔
      (u ∈ P ∨ v ∈ P) ∧ (u ∈ Q ∨ v ∈ Q) ∧ (u ∈ R ∨ v ∈ R) ∧ (u ∈ S ∨ v ∈ S)) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card + K.card ≤ G.support.ncard := by
  have hpq : ∀ u, u ∈ P → u ∈ Q → False := Finset.disjoint_left.mp hPQ
  have hrs : ∀ u, u ∈ R → u ∈ S → False := Finset.disjoint_left.mp hRS
  apply two_disjoint_bicliques_budget G h4 (P ∩ R) (Q ∩ S) (P ∩ S) (Q ∩ R)
  · apply Finset.disjoint_left.mpr
    intro u h1 h2
    simp only [Finset.mem_union, Finset.mem_inter] at h1 h2
    have hPQu := hpq u
    have hRSu := hrs u
    tauto
  · intro u v
    rw [hedge]
    simp only [Cross, Finset.mem_inter]
    have hPQu := hpq u
    have hPQv := hpq v
    have hRSu := hrs u
    have hRSv := hrs v
    tauto

lemma pair_hits {n : ℕ} (P : Finset (Fin n)) (u v : Fin n) :
    (∃ a ∈ P, pairInput u v a = true) ↔ u ∈ P ∨ v ∈ P := by
  constructor
  · rintro ⟨a, ha, hx⟩
    simp only [pairInput, decide_eq_true_eq] at hx
    rcases hx with rfl | rfl
    · exact Or.inl ha
    · exact Or.inr ha
  · rintro (hu | hv)
    · exact ⟨u, hu, by simp [pairInput]⟩
    · exact ⟨v, hv, by simp [pairInput]⟩

lemma posted_conclusion_of_two_silent_products {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) (hmin : IsMinimalMonoCircuit n C)
    (P Q R S : Finset (Fin n)) (hPQ : Disjoint P Q) (hRS : Disjoint R S)
    (hsem : ∀ x : Fin n → Bool, circuitFun n C x = true ↔
      (∃ u ∈ P, x u = true) ∧ (∃ u ∈ Q, x u = true) ∧
      (∃ u ∈ R, x u = true) ∧ (∃ u ∈ S, x u = true)) :
    ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ E : Circuit, Monotone2 E → circuitFun n E = graphFun G ∅ → D.size ≤ E.size) ∧
      HasStarProfile n G D := by
  classical
  have hpairs : ∀ u v, G.Adj u v ↔
      (u ∈ P ∨ v ∈ P) ∧ (u ∈ Q ∨ v ∈ Q) ∧ (u ∈ R ∨ v ∈ R) ∧ (u ∈ S ∨ v ∈ S) := by
    intro u v
    have h := hsem (pairInput u v)
    rw [hfun, PEqualNP.Outside.L_meta_2448_aux.foundation.M1528.P1.S90.graphFun_pair] at h
    simpa only [pair_hits] using h
  obtain ⟨K, hK, hbudget⟩ := four_sides_budget G h4 P Q R S hPQ hRS hpairs
  by_cases hE : G.edgeFinset.Nonempty
  · have hcover : ∀ e ∈ G.edgeFinset, ∃ u ∈ K, u ∈ e := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        rcases hK u v (SimpleGraph.mem_edgeFinset.mp he) with hu | hv
        · exact ⟨u, hu, Sym2.mem_mk_left _ _⟩
        · exact ⟨v, hv, Sym2.mem_mk_right _ _⟩
    obtain ⟨D, hD, hDf, hDs, hDsize⟩ :=
      PEqualNP.Outside.L_meta_2448.StarCoverPrototype.star_cover_witness G hE K hcover
    have hsupport := PEqualNP.Outside.L_meta_2074.main n G C hAO.2.2 hfun
    have hsz : D.size ≤ C.size := by omega
    exact ⟨D, hD, hDf,
      fun E hE hEf => hsz.trans (hmin.2 E hE (hEf.trans hfun.symm)), hDs⟩
  · exact PEqualNP.Outside.L_meta_2448_aux.oneJunkStar.empty_graph_star_minimum G
      (Finset.not_nonempty_iff_eq_empty.mp hE)

end PEqualNP.Outside.L_meta_2448_aux.twoSilentProducts

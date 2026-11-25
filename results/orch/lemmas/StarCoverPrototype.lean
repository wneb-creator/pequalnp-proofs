import PEqualNP.Outside.L_meta_3760
import PEqualNP.Outside.L_meta_2448

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

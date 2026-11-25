import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.AndBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma output_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma output_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [output_gateAt_eq hj]; exact List.getElem_mem hj

open PEqualNP.CleanedNonEdge

lemma output_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma output_orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [output_orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma output_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := output_orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma output_tail_step (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w, OrReaches n C w g → g ≠ w - n →
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        n + g ∈ (gateAt C k).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h hne
    have hnw : n ≤ w := h.1
    obtain ⟨k0, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (output_orReaches_iff n C k0 g).mp h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · exact (hne (by omega)).elim
    · have hself : OrReaches n C (n + k0) k0 :=
        (output_orReaches_iff n C k0 k0).mpr ⟨hk, Or.inl rfl⟩
      by_cases hg : g = i - n
      · refine ⟨k0, hk, hself, hop, ?_⟩
        have hni : n ≤ i := hr.1
        have e : n + g = i := by omega
        rw [e]
        exact hi
      · obtain ⟨k, hkl, hrk, hopk, hin⟩ := ih i hlt hr hg
        exact ⟨k, hkl,
          (output_orReaches_iff n C k0 k).mpr ⟨hk, Or.inr ⟨hop, i, hi, hlt, hrk⟩⟩, hopk, hin⟩

def output_par (n : ℕ) (C : Circuit) (O : Finset ℕ) : Finset ℕ :=
  O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))

lemma output_par_card (n : ℕ) (C : Circuit) (O : Finset ℕ)
    (h : ∀ k ∈ O, (gateAt C k).inputs.length = 2) : (output_par n C O).card ≤ O.card * 2 := by
  unfold output_par
  calc (O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))).card
      ≤ ∑ k ∈ O, (((gateAt C k).inputs.toFinset).image (fun w => w - n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ O, 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.card_image_le.trans
          ((List.toFinset_card_le _).trans (le_of_eq (h k hk)))
    _ = O.card * 2 := by rw [Finset.sum_const, smul_eq_mul]

lemma output_or_bound : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hC hF
  obtain ⟨_, _, hlen⟩ := hC
  obtain ⟨O, hO⟩ : ∃ O : Finset ℕ, ∀ i, i ∈ O ↔ (i < C.gates.length ∧
      (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i) :=
      by
    have hfin : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i}.Finite := by
      apply (Finset.finite_toSet (Finset.range C.gates.length)).subset
      intro i hi
      have hi2 : i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
          OrReaches n C C.output i := Eq.mp Set.mem_setOf_eq hi
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hi2.1)
    refine ⟨hfin.toFinset, fun i => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} = (↑O : Set ℕ) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.mem_coe, hO]
  rw [hset, Set.ncard_coe_finset]
  have hdisj : Disjoint F O := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h1 := (hF a ha).2.1
    have h2 := ((hO a).mp hb).2.1
    rw [h1] at h2
    exact GateOp.noConfusion h2
  have hsub : F ∪ O ⊆ insert (C.output - n) (output_par n C O) := by
    intro g hg
    have hr : OrReaches n C C.output g := by
      rcases Finset.mem_union.mp hg with h | h
      · exact (hF g h).2.2
      · exact ((hO g).mp h).2.2
    by_cases hgo : g = C.output - n
    · exact Finset.mem_insert.mpr (Or.inl hgo)
    · obtain ⟨k, hk, hrk, hop, hin⟩ := output_tail_step n C g C.output hr hgo
      refine Finset.mem_insert.mpr (Or.inr ?_)
      unfold output_par
      exact Finset.mem_biUnion.mpr ⟨k, (hO k).mpr ⟨hk, hop, hrk⟩,
        Finset.mem_image.mpr ⟨n + g, List.mem_toFinset.mpr hin, by omega⟩⟩
  have hcard := output_par_card n C O (fun k hk => hlen _ (output_gateAt_mem ((hO k).mp hk).1))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 := Finset.card_insert_le (C.output - n) (output_par n C O)
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def boundary_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma boundary_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl boundary_stepWire x := rfl

lemma boundary_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl boundary_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [boundary_stepWire]
    omega

lemma boundary_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl boundary_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (boundary_stepWire w g).length := by simp [boundary_stepWire]; omega
    rw [ih (boundary_stepWire w g) hlt]
    simp [boundary_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma boundary_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma boundary_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [boundary_wires_eq_foldl, boundary_foldl_stepWire_length, List.length_ofFn]

lemma boundary_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def boundary_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma boundary_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma boundary_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    boundary_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then boundary_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := boundary_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [boundary_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl boundary_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, boundary_foldl_stepWire_length, hpre_len]
  have hCj : boundary_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [boundary_W]
    rw [boundary_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [boundary_foldl_stepWire_getD_lt post (boundary_stepWire w0 gj) (n + k) (by simp [boundary_stepWire]; omega)]
    simp [boundary_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [boundary_W]
    rw [boundary_wires_eq_foldl, hgs, List.foldl_append]
    exact (boundary_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact boundary_getD_ge_length w0 i (by omega)

lemma boundary_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    boundary_W n C x u = x ⟨u, hu⟩ := by
  simp only [boundary_W]
  rw [boundary_wires_eq_foldl, boundary_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in

lemma boundary_W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ)
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (i : ℕ) (hi : i ∈ (gateAt C r).inputs) (hlt : i < n + r)
    (hv : boundary_W n C x i = true) : boundary_W n C x (n + r) = true := by
  rw [boundary_W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [if_pos hlt]; exact hv⟩

lemma boundary_reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : boundary_W n C x (n + g) = true) :
    ∀ w, OrReaches n C w g → boundary_W n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hn : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    rcases (output_orReaches_iff n C k g).mp hr with ⟨hk, rfl | ⟨hop, i, hi, hlt, hir⟩⟩
    · exact hv
    · exact boundary_W_or n C x k hk hop i hi hlt (ih i hlt hir)

lemma boundary_orIn_up (n : ℕ) (C : Circuit) (k i : ℕ) (a : Fin n)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or)
    (hi : i ∈ (gateAt C k).inputs) (hlt : i < n + k)
    (ha : a ∈ PEqualNP.TopForm.orIn n C i) :
    a ∈ PEqualNP.TopForm.orIn n C (n + k) := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  unfold PEqualNP.TopForm.orIn at ha ⊢
  have ha' := (@Finset.mem_filter _ _ _ _ _).mp ha
  apply (@Finset.mem_filter _ _ _ _ _).mpr
  refine ⟨Finset.mem_univ _, Or.inr ?_⟩
  rcases ha'.2 with h | ⟨j, hj, hr, hjor, haj⟩
  · exact ⟨k, hk, (output_orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩,
      hop, h ▸ hi⟩
  · exact ⟨j, hj, (output_orReaches_iff n C k j).mpr
      ⟨hk, Or.inr ⟨hop, i, hi, hlt, hr⟩⟩, hjor, haj⟩

lemma boundary_orIn_true (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (a : Fin n) (ha : a ∈ PEqualNP.TopForm.orIn n C w) (hx : x a = true) :
    boundary_W n C x w = true := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  unfold PEqualNP.TopForm.orIn at ha
  have ha' := (@Finset.mem_filter _ _ _ _ _).mp ha
  rcases ha'.2 with h | ⟨k, hk, hr, hop, hin⟩
  · rw [← h, boundary_W_input n C x a.val a.isLt]
    exact hx
  · apply boundary_reach_up n C x k _ w hr
    apply boundary_W_or n C x k hk hop a.val hin (by have := a.isLt; omega)
    rw [boundary_W_input n C x a.val a.isLt]
    exact hx

lemma boundary_true_witness (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n → Bool) : ∀ w, boundary_W n C x w = true →
      (∃ a ∈ PEqualNP.TopForm.orIn n C w, x a = true) ∨
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
        OrReaches n C w j ∧ boundary_W n C x (n + j) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · left
      refine ⟨⟨w, hw⟩, ?_, ?_⟩
      · simp [PEqualNP.TopForm.orIn]
      · rw [boundary_W_input n C x w hw] at hv
        exact hv
    · have hn : n ≤ w := by omega
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by
        by_contra h
        have he : boundary_W n C x (n + k) = false := by
          apply boundary_getD_ge_length
          rw [boundary_wires_length]
          omega
        rw [he] at hv
        contradiction
      have hm := output_gateAt_mem hk
      rcases hAO.1 _ hm with hop | hop
      · right
        exact ⟨k, hk, hop, (output_orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hv⟩
      · have hv' := hv
        rw [boundary_W_gate n C x k hk, hop] at hv'
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv'
        obtain ⟨i, hi, hiv⟩ := hv'
        have hlt : i < n + k := hAO.2.1 k hk i hi
        rw [if_pos hlt] at hiv
        rcases ih i hlt hiv with ⟨a, ha, hax⟩ | ⟨j, hj, hja, hr, hjv⟩
        · exact Or.inl ⟨a, boundary_orIn_up n C k i a hk hop hi hlt ha, hax⟩
        · exact Or.inr ⟨j, hj, hja, (output_orReaches_iff n C k j).mpr
            ⟨hk, Or.inr ⟨hop, i, hi, hlt, hr⟩⟩, hjv⟩

lemma boundary_output_and (n : ℕ) (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hsingle : ∀ a : Fin n, PEqualNP.MetaComplexity.circuitFun n C
      (fun i => decide (i = a)) = false) (x : Fin n → Bool)
    (hx : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧ boundary_W n C x (n + j) = true := by
  have hval : boundary_W n C x C.output = true := hx
  rcases boundary_true_witness n C hAO x C.output hval with ⟨a, ha, _⟩ | h
  · have hbad := boundary_orIn_true n C (fun i => decide (i = a)) C.output a ha (by simp)
    have hz : boundary_W n C (fun i => decide (i = a)) C.output = false := hsingle a
    rw [hz] at hbad
    contradiction
  · exact h

def branching_and (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => decide (2 ≤ g.inputs.length)
  | _ => false

def and_count (C : Circuit) (k : ℕ) : ℕ :=
  (C.gates.take k).countP branching_and

lemma and_count_succ (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    and_count C (k + 1) = and_count C k + (if branching_and (gateAt C k) then 1 else 0) := by
  unfold and_count
  rw [List.take_succ, List.countP_append, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.countP_singleton, output_gateAt_eq hk]

lemma true_gate_frontier (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    (hb : ∀ i ∈ (gateAt C k).inputs, i < n + k)
    (hl : (gateAt C k).inputs.length ≤ 2)
    (hv : boundary_W n C x (n + k) = true) :
    ∃ J : Finset ℕ,
      J.card ≤ (if branching_and (gateAt C k) then 1 else 0) + 1 ∧
      (∀ i ∈ J, i < n + k) ∧ (∀ i ∈ J, boundary_W n C x i = true) ∧
      ∀ y : Fin n → Bool, (∀ i ∈ J, boundary_W n C y i = true) →
        boundary_W n C y (n + k) = true := by
  rcases hop with ha | ho
  · refine ⟨(gateAt C k).inputs.toFinset, ?_, ?_, ?_, ?_⟩
    · by_cases htwo : 2 ≤ (gateAt C k).inputs.length
      · simpa [branching_and, ha, htwo] using (List.toFinset_card_le _).trans hl
      · have hsmall : (gateAt C k).inputs.length ≤ 1 := by omega
        simpa [branching_and, ha, htwo] using (List.toFinset_card_le _).trans hsmall
    · intro i hi
      exact hb i (List.mem_toFinset.mp hi)
    · rw [boundary_W_gate n C x k hk, ha] at hv
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hv
      intro i hi
      have hit := List.mem_toFinset.mp hi
      simpa [hb i hit] using hv i hit
    · intro y hy
      rw [boundary_W_gate n C y k hk, ha]
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
      intro i hi
      simpa [hb i hi] using hy i (List.mem_toFinset.mpr hi)
  · rw [boundary_W_gate n C x k hk, ho] at hv
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv
    obtain ⟨i, hi, hv⟩ := hv
    have hiv : boundary_W n C x i = true := by simpa [hb i hi] using hv
    refine ⟨{i}, by simp [branching_and, ho], ?_, ?_, ?_⟩
    · intro j hj
      simpa using (Finset.mem_singleton.mp hj ▸ hb i hi)
    · intro j hj
      simpa using (Finset.mem_singleton.mp hj ▸ hiv)
    · intro y hy
      exact boundary_W_or n C y k hk ho i hi (hb i hi) (hy i (by simp))

lemma true_frontier_certificate (n : ℕ) (C : Circuit)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (hback : ReadsBack n C)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (x : Fin n → Bool) :
    ∀ k, k ≤ C.gates.length → ∀ R : Finset ℕ,
      (∀ w ∈ R, w < n + k) → (∀ w ∈ R, boundary_W n C x w = true) →
      ∃ S : Finset (Fin n), (∀ i ∈ S, x i = true) ∧
        (∀ y : Fin n → Bool, (∀ i ∈ S, y i = true) →
          ∀ w ∈ R, boundary_W n C y w = true) ∧
        S.card ≤ and_count C k + R.card := by
  intro k
  induction k with
  | zero =>
    intro _ R hR ht
    let S : Finset (Fin n) := Finset.univ.filter fun i => i.val ∈ R
    refine ⟨S, ?_, ?_, ?_⟩
    · intro i hi
      have hv := ht i.val ((Finset.mem_filter.mp hi).2)
      rw [boundary_W_input n C x i.val i.isLt] at hv
      exact hv
    · intro y hy w hw
      have hwn : w < n := by simpa using hR w hw
      rw [boundary_W_input n C y w hwn]
      apply hy ⟨w, hwn⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
    · have hsub : S.image Fin.val ⊆ R := by
        intro w hw
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp hi).2
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective S Fin.val_injective] at hc
      simpa [and_count] using hc
  | succ k ih =>
    intro hk R hR ht
    have hkl : k < C.gates.length := by omega
    have hcount := and_count_succ C k hkl
    by_cases hm : n + k ∈ R
    · have hgmem := output_gateAt_mem hkl
      obtain ⟨J, hJc, hJb, hJt, hJforce⟩ := true_gate_frontier n C x k hkl
        (hAO _ hgmem) (hback k hkl) (hfanin _ hgmem) (ht (n + k) hm)
      let R' : Finset ℕ := J ∪ R.erase (n + k)
      have hR'b : ∀ w ∈ R', w < n + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with h | h
        · exact hJb w h
        · have hwR := Finset.mem_of_mem_erase h
          have hne := Finset.ne_of_mem_erase h
          have hb := hR w hwR
          omega
      have hR't : ∀ w ∈ R', boundary_W n C x w = true := by
        intro w hw
        rcases Finset.mem_union.mp hw with h | h
        · exact hJt w h
        · exact ht w (Finset.mem_of_mem_erase h)
      obtain ⟨S, hSt, hSf, hSc⟩ := ih (by omega) R' hR'b hR't
      refine ⟨S, hSt, ?_, ?_⟩
      · intro y hy w hw
        by_cases hwm : w = n + k
        · subst w
          apply hJforce y
          intro i hi
          exact hSf y hy i (Finset.mem_union.mpr (Or.inl hi))
        · exact hSf y hy w (Finset.mem_union.mpr
            (Or.inr (Finset.mem_erase.mpr ⟨hwm, hw⟩)))
      · have hR'c : R'.card ≤ J.card + (R.erase (n + k)).card := Finset.card_union_le _ _
        have hRc := Finset.card_erase_add_one hm
        omega
    · have hR0 : ∀ w ∈ R, w < n + k := by
        intro w hw
        have hb := hR w hw
        have hne : w ≠ n + k := by intro h; exact hm (h ▸ hw)
        omega
      obtain ⟨S, hSt, hSf, hSc⟩ := ih (by omega) R hR0 ht
      exact ⟨S, hSt, hSf, by omega⟩

lemma true_input_certificate (n : ℕ) (C : Circuit)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (hback : ReadsBack n C)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (x : Fin n → Bool)
    (hx : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    ∃ S : Finset (Fin n), (∀ i ∈ S, x i = true) ∧
      (∀ y : Fin n → Bool, (∀ i ∈ S, y i = true) →
        PEqualNP.MetaComplexity.circuitFun n C y = true) ∧
      S.card ≤ C.gates.countP branching_and + 1 := by
  have hval : boundary_W n C x C.output = true := hx
  have hout : C.output < n + C.gates.length := by
    by_contra h
    have hz : boundary_W n C x C.output = false := by
      apply boundary_getD_ge_length
      rw [boundary_wires_length]
      omega
    rw [hz] at hval
    contradiction
  obtain ⟨S, hS, hforce, hcard⟩ := true_frontier_certificate n C hAO hback hfanin x
    C.gates.length le_rfl {C.output} (by simpa using hout) (by simpa using hval)
  refine ⟨S, hS, ?_, ?_⟩
  · intro y hy
    exact hforce y hy C.output (by simp)
  · simpa [and_count] using hcard

end PEqualNP.Outside.L_meta_4970.AndBudget

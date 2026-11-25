import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.Surgery

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma card_sdiff_eq {α : Type} [DecidableEq α] {A B : Finset α} (h : A ⊆ B) :
    (B \ A).card = B.card - A.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]

-- Section 1: Basic wire, cone, OrReaches, orIn, and side lemmas

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wval_input C _ w hwn]
    · have hj : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      rw [hw_eq]
      have hop := hAO.1 _ (gateAt_mem hj)
      have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hj 0; omega
      have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hj 1; omega
      have hv0 := ih _ h0 (by omega)
      have hv1 := ih _ h1 (by omega)
      rcases hop with hand | hor
      · rw [wval_gate_and hAO _ hj hand, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hor, hv0, hv1]; rfl

lemma wval_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwx
    by_cases hwn : w < n
    · rw [wval_input C x w hwn] at hwx
      rw [wval_input C y w hwn]
      exact hxy ⟨w, hwn⟩ hwx
    · by_cases hwlen : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have hw_eq : w = n + (w - n) := by omega
        rw [hw_eq] at hwx ⊢
        have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hj 0; omega
        have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hj 1; omega
        rcases hAO.1 _ (gateAt_mem hj) with hand | hor
        · rw [wval_gate_and hAO x hj hand, Bool.and_eq_true] at hwx
          rw [wval_gate_and hAO y hj hand, Bool.and_eq_true]
          exact ⟨ih _ h0 hwx.1, ih _ h1 hwx.2⟩
        · rw [wval_gate_or hAO x hj hor, Bool.or_eq_true] at hwx
          rw [wval_gate_or hAO y hj hor, Bool.or_eq_true]
          exact hwx.imp (ih _ h0) (ih _ h1)
      · rw [wval_ge_len C x (by omega)] at hwx; cases hwx

-- Cone characterization

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hnw, hwnj, rfl | hsub⟩
    · omega
    · have := ih (w - n) (by omega) hsub; omega

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩

-- OrReaches and orIn characterization

lemma foldl_orSets_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (orStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, orStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_orSets_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (orStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (orStep n acc g).length := by
      simp only [orStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  unfold orSets; rw [foldl_orSets_len]; simp

lemma foldl_orSets_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (orStep n) acc).getD (acc.length + j) [] =
      (acc.length + j) :: (match gs[j].op with
        | GateOp.or =>
          (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
            (fun w => (gs.foldl (orStep n) acc).getD (w - n) [])
        | _ => []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := orStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', orStep, List.length_append, List.length_singleton]; omega
      rw [foldl_orSets_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          acc.length :: (match g.op with
            | GateOp.or =>
              (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
                (fun w => acc.getD (w - n) [])
            | _ => []) := by
        simp only [acc', orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        cases g.op <;> rfl
      rw [hlhs]
      congr 1
      cases g.op
      · rfl
      · apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have hwn : w - n < acc.length := by omega
        have hwn' : w - n < acc'.length := by omega
        rw [foldl_orSets_getD_lt n gs acc' (w - n) hwn']
        simp only [acc', orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
      · rfl
      · rfl
      · rfl
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := orStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', orStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma orReaches_lt_len {n : ℕ} {C : Circuit} {w g : ℕ} (h : OrReaches n C w g) :
    w - n < C.gates.length := by
  by_contra hge
  unfold OrReaches at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_length]; omega)] at h
  simp at h

lemma orReaches_gate_iff {n : ℕ} {C : Circuit} {j g : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) g ↔
      g = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ OrReaches n C w g) := by
  unfold OrReaches orSets
  have h := foldl_orSets_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [Nat.add_sub_cancel_left, h, ← gateAt_eq hj]
  constructor
  · rintro ⟨_, hmem⟩
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · cases hop : (gateAt C j).op
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨w, hw, hwg⟩
        rw [List.mem_filter] at hw
        simp only [decide_eq_true_eq] at hw
        exact Or.inr ⟨rfl, w, hw.1, hw.2.1, hw.2.2, ⟨hw.2.1, hwg⟩⟩
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem; simp at hmem
  · rintro (rfl | ⟨hop, w, hw, hnw, hwnj, hwg⟩)
    · exact ⟨Nat.le_add_right n _, List.mem_cons_self⟩
    · refine ⟨Nat.le_add_right n j, List.mem_cons_of_mem j ?_⟩
      rw [hop, List.mem_flatMap]
      exact ⟨w, List.mem_filter.mpr ⟨hw, by simp [hnw, hwnj]⟩, hwg.2⟩

lemma orReaches_input_false {n : ℕ} {C : Circuit} {w g : ℕ} (hw : w < n) : ¬ OrReaches n C w g :=
  fun h => by have := h.1; omega

lemma orReaches_le {n : ℕ} {C : Circuit} {w g : ℕ} (h : OrReaches n C w g) : g ≤ w - n := by
  have hnw : n ≤ w := h.1
  have hj : w - n < C.gates.length := orReaches_lt_len h
  obtain ⟨k, hk⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  subst hk
  rw [Nat.add_sub_cancel_left] at hj ⊢
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hj] at h
    rcases h with rfl | ⟨_, u, _, hnu, hunk, hug⟩
    · exact le_refl _
    · have hlt : u - n < k := by omega
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      have := ih (u - n) hlt hug (by omega)
      omega

lemma orReaches_self {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_gate_iff hj).mpr (Or.inl rfl)

lemma orReaches_trans {n : ℕ} {C : Circuit} {w j g : ℕ}
    (h1 : OrReaches n C w j) (h2 : OrReaches n C (n + j) g) : OrReaches n C w g := by
  have hnw : n ≤ w := h1.1
  have hwn : w - n < C.gates.length := orReaches_lt_len h1
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  rw [Nat.add_sub_cancel_left] at hwn
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hwn] at h1
    rcases h1 with rfl | ⟨hop, u, hu, hnu, hunk, huj⟩
    · exact h2
    · rw [orReaches_gate_iff hwn]
      refine Or.inr ⟨hop, u, hu, hnu, hunk, ?_⟩
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at huj ⊢
      exact ih (u - n) (by omega) huj (by omega)

lemma orReaches_inCone_or_eq {n : ℕ} {C : Circuit} {j g : ℕ} (h : OrReaches n C (n + j) g) :
    g = j ∨ InCone n C g j := by
  have hj := orReaches_lt_len h
  rw [Nat.add_sub_cancel_left] at hj
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_gate_iff hj] at h
    rcases h with rfl | ⟨_, u, hu, hnu, hunj, hug⟩
    · exact Or.inl rfl
    · right
      rw [inCone_iff hj]
      refine ⟨u, hu, hnu, hunj, ?_⟩
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      exact ih (u - n) (by omega) hug (by omega)

lemma orReaches_val_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {w g : ℕ} (h : OrReaches n C w g) (hg : gateVal n C g x = true) : wval C x w = true := by
  have hnw : n ≤ w := h.1
  have hwn : w - n < C.gates.length := orReaches_lt_len h
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  rw [Nat.add_sub_cancel_left] at hwn
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hwn] at h
    rcases h with rfl | ⟨hop, u, hu, hnu, hunk, hug⟩
    · exact hg
    · rw [wval_gate_or hAO x hwn hop, Bool.or_eq_true]
      rw [gate_inputs_eq hAO hwn] at hu
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      have hvu := ih (u - n) (by omega) hug (by omega)
      rw [← hu_eq] at hvu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact Or.inl hvu
      · exact Or.inr hvu

lemma mem_orIn_input {n : ℕ} (C : Circuit) (u v : Fin n) :
    u ∈ orIn n C v.val ↔ u = v := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (heq | ⟨k, _, hreach, _, _⟩)
    · exact Fin.ext heq
    · exact absurd hreach (orReaches_input_false v.isLt)
  · rintro rfl; exact Or.inl rfl

lemma orIn_and_eq_empty {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) : orIn n C (n + j) = ∅ := by
  ext u
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_or]
  refine ⟨by have := u.isLt; omega, ?_⟩
  rintro ⟨k, hk, hreach, hor, _⟩
  rw [orReaches_gate_iff hj] at hreach
  rcases hreach with rfl | ⟨hor', _⟩
  · rw [hand] at hor; cases hor
  · rw [hand] at hor'; cases hor'

lemma orIn_or_eq_union {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext u
  simp only [Finset.mem_union, orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hreach, hork, huk⟩)
    · omega
    · rw [orReaches_gate_iff hj] at hreach
      rcases hreach with rfl | ⟨_, w, hw, hnw, hwnj, hwk⟩
      · rw [gate_inputs_eq hAO hj] at huk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
        rcases huk with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl h1)
      · rw [gate_inputs_eq hAO hj] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Or.inl (Or.inr ⟨k, hk, hwk, hork, huk⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hwk, hork, huk⟩)
  · rintro ((h0 | ⟨k, hk, hwk, hork, huk⟩) | (h1 | ⟨k, hk, hwk, hork, huk⟩))
    · right
      refine ⟨j, hj, orReaches_self hj, hor, ?_⟩
      rw [gate_inputs_eq hAO hj, h0]; simp
    · right
      refine ⟨k, hk, (orReaches_gate_iff hj).mpr (Or.inr ⟨hor, opnd C j 0, opnd_mem hAO hj 0, hwk.1,
        opnd_lt hAO hj 0, hwk⟩), hork, huk⟩
    · right
      refine ⟨j, hj, orReaches_self hj, hor, ?_⟩
      rw [gate_inputs_eq hAO hj, h1]; simp
    · right
      refine ⟨k, hk, (orReaches_gate_iff hj).mpr (Or.inr ⟨hor, opnd C j 1, opnd_mem hAO hj 1, hwk.1,
        opnd_lt hAO hj 1, hwk⟩), hork, huk⟩

lemma orIn_val_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {w : ℕ} {u : Fin n} (hu : u ∈ orIn n C w) (hx : x u = true) : wval C x w = true := by
  unfold orIn at hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with rfl | ⟨k, hk, hreach, hork, huk⟩
  · rw [wval_input C x u.val u.isLt]; exact hx
  · apply orReaches_val_mono hAO x hreach
    rw [gateVal_eq_wval, wval_gate_or hAO x hk hork, Bool.or_eq_true]
    rw [gate_inputs_eq hAO hk] at huk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
    rcases huk with h0 | h1
    · left; rw [← h0, wval_input C x u.val u.isLt]; exact hx
    · right; rw [← h1, wval_input C x u.val u.isLt]; exact hx

lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} {w k : ℕ} (h : OrReaches n C w k) :
    orIn n C (n + k) ⊆ orIn n C w := by
  intro u hu
  unfold orIn at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with hu | ⟨m, hm, hkm, horm, hum⟩
  · omega
  · exact Or.inr ⟨m, hm, orReaches_trans h hkm, horm, hum⟩

-- Section 2: Gate deletion and structure from IsLeastAO and IsLiftFixedPoint

def delWire (n j r w : ℕ) : ℕ :=
  if w = n + j then r else if n + j < w then w - 1 else w

def delCircuit (n : ℕ) (C : Circuit) (j r : ℕ) : Circuit :=
  { gates := (C.gates.eraseIdx j).map (fun g => { g with inputs := g.inputs.map (delWire n j r) })
    output := delWire n j r C.output }

lemma delCircuit_len (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) (r : ℕ) :
    (delCircuit n C j r).gates.length = C.gates.length - 1 := by
  simp [delCircuit, List.length_eraseIdx, hj]

lemma delCircuit_gateAt_lt {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C i) with inputs := (gateAt C i).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx, if_pos hj]; omega) hi]

lemma delCircuit_gateAt_ge {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C (i + 1)) with inputs := (gateAt C (i + 1)).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx, if_pos hj]; omega) hji]

lemma delCircuit_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r : ℕ}
    (hj : j < C.gates.length) (hr : r < n + j) : IsAO2 n (delCircuit n C j r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    exact hAO.1 g0 (List.mem_of_mem_eraseIdx hg0)
  · intro i hi w hw
    rw [delCircuit_len n C hj r] at hi
    by_cases hij : i < j
    · rw [delCircuit_gateAt_lt hj hij] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + i := hAO.2.1 i (by omega) u hu
      unfold delWire
      rw [if_neg (by omega), if_neg (by omega)]
      exact hult
    · rw [delCircuit_gateAt_ge hj (by omega) hi] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + (i + 1) := hAO.2.1 (i + 1) (by omega) u hu
      unfold delWire
      split_ifs <;> omega
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    simp only [List.length_map]
    exact hAO.2.2 g0 (List.mem_of_mem_eraseIdx hg0)

lemma delCircuit_opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C i b) := by
  unfold opnd
  rw [delCircuit_gateAt_lt hj hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_opnd_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C (i + 1) b) := by
  unfold opnd
  rw [delCircuit_gateAt_ge hj hji hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_wval_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j)
    (heq : wval C x r = wval C x (n + j)) :
    ∀ w < n + C.gates.length, wval (delCircuit n C j r) x (delWire n j r w) = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
      rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
    · by_cases hwj : w = n + j
      · subst hwj
        have hdw : delWire n j r (n + j) = r := by unfold delWire; simp
        have hdr : delWire n j r r = r := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
        have h1 := ih r hr (by omega)
        rw [hdr] at h1
        rw [hdw, h1, heq]
      · by_cases hlt : w < n + j
        · have hk : w - n < j := by omega
          have hdw : delWire n j r w = n + (w - n) := by
            unfold delWire; rw [if_neg hwj, if_neg (by omega)]; omega
          have hw_eq : w = n + (w - n) := by omega
          rw [hdw]
          conv_rhs => rw [hw_eq]
          have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
          have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
          rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
          have h0 := ih (opnd C (w - n) 0) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega)
          have h1 := ih (opnd C (w - n) 1) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega)
          rw [h0, h1, hg]
        · have hgt : n + j < w := by omega
          have hk : w - n - 1 < C.gates.length - 1 := by omega
          have hjk : j ≤ w - n - 1 := by omega
          have hdw : delWire n j r w = n + (w - n - 1) := by
            unfold delWire; rw [if_neg hwj, if_pos hgt]; omega
          have hw_eq : w = n + (w - n - 1 + 1) := by omega
          rw [hdw]
          conv_rhs => rw [hw_eq]
          have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
          have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
          rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
          have h0 := ih (opnd C (w - n - 1 + 1) 0) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          have h1 := ih (opnd C (w - n - 1 + 1) 1) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          rw [h0, h1, hg]

lemma delCircuit_wval_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j)
    (hle : wval C x (n + j) = true → wval C x r = true) :
    ∀ w < n + C.gates.length, wval C x w = true → wval (delCircuit n C j r) x (delWire n j r w) = true := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hval
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
      rw [hdw, wval_input _ x w hwn]; rw [wval_input _ x w hwn] at hval; exact hval
    · by_cases hwj : w = n + j
      · subst hwj
        have hdw : delWire n j r (n + j) = r := by unfold delWire; simp
        have hdr : delWire n j r r = r := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
        have h1 := ih r hr (by omega) (hle hval)
        rw [hdr] at h1
        rw [hdw]
        exact h1
      · by_cases hlt : w < n + j
        · have hk : w - n < j := by omega
          have hdw : delWire n j r w = n + (w - n) := by
            unfold delWire; rw [if_neg hwj, if_neg (by omega)]; omega
          have hw_eq : w = n + (w - n) := by omega
          rw [hdw]; rw [hw_eq] at hval
          have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
          have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega
          have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega
          rcases hAO.1 _ (gateAt_mem (by omega : w - n < C.gates.length)) with hand | hor
          · rw [wval_gate_and hAO x (by omega) hand, Bool.and_eq_true] at hval
            rw [wval_gate_and hAO' x hk' (by rw [hg]; exact hand), Bool.and_eq_true]
            rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
            exact ⟨ih _ h0lt (by omega) hval.1, ih _ h1lt (by omega) hval.2⟩
          · rw [wval_gate_or hAO x (by omega) hor, Bool.or_eq_true] at hval
            rw [wval_gate_or hAO' x hk' (by rw [hg]; exact hor), Bool.or_eq_true]
            rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
            exact hval.imp (ih _ h0lt (by omega)) (ih _ h1lt (by omega))
        · have hgt : n + j < w := by omega
          have hk : w - n - 1 < C.gates.length - 1 := by omega
          have hjk : j ≤ w - n - 1 := by omega
          have hdw : delWire n j r w = n + (w - n - 1) := by
            unfold delWire; rw [if_neg hwj, if_pos hgt]; omega
          have hw_eq : w = n + (w - n - 1 + 1) := by omega
          rw [hdw]; rw [hw_eq] at hval
          have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
          have h0lt : opnd C (w - n - 1 + 1) 0 < w := by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega
          have h1lt : opnd C (w - n - 1 + 1) 1 < w := by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega
          rcases hAO.1 _ (gateAt_mem (by omega : w - n - 1 + 1 < C.gates.length)) with hand | hor
          · rw [wval_gate_and hAO x (by omega) hand, Bool.and_eq_true] at hval
            rw [wval_gate_and hAO' x hk' (by rw [hg]; exact hand), Bool.and_eq_true]
            rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
            exact ⟨ih _ h0lt (by omega) hval.1, ih _ h1lt (by omega) hval.2⟩
          · rw [wval_gate_or hAO x (by omega) hor, Bool.or_eq_true] at hval
            rw [wval_gate_or hAO' x hk' (by rw [hg]; exact hor), Bool.or_eq_true]
            rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
            exact hval.imp (ih _ h0lt (by omega)) (ih _ h1lt (by omega))

lemma delCircuit_wval_not_inCone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j) :
    ∀ w < n + C.gates.length, w ≠ n + j → (n ≤ w → ¬ InCone n C j (w - n)) →
      wval (delCircuit n C j r) x (delWire n j r w) = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwj hnc
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
      rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
    · have hnc' : ¬ InCone n C j (w - n) := hnc (by omega)
      have hop_ok : ∀ b : Fin 2, opnd C (w - n) b ≠ n + j ∧
          (n ≤ opnd C (w - n) b → ¬ InCone n C j (opnd C (w - n) b - n)) := by
        intro b
        have hk : w - n < C.gates.length := by omega
        have hmem := opnd_mem hAO hk b
        have hlt := opnd_lt hAO hk b
        constructor
        · intro heq; apply hnc'; rw [inCone_iff hk]
          exact ⟨opnd C (w - n) b, hmem, by omega, hlt, Or.inl (by omega)⟩
        · intro hnu hin; apply hnc'; rw [inCone_iff hk]
          exact ⟨opnd C (w - n) b, hmem, hnu, hlt, Or.inr hin⟩
      by_cases hlt : w < n + j
      · have hk : w - n < j := by omega
        have hdw : delWire n j r w = n + (w - n) := by
          unfold delWire; rw [if_neg hwj, if_neg (by omega)]; omega
        have hw_eq : w = n + (w - n) := by omega
        rw [hdw]
        conv_rhs => rw [hw_eq]
        have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
        rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
        have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
        rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
        have h0 := ih (opnd C (w - n) 0) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega) (hop_ok 0).1 (hop_ok 0).2
        have h1 := ih (opnd C (w - n) 1) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega) (hop_ok 1).1 (hop_ok 1).2
        rw [h0, h1, hg]
      · have hgt : n + j < w := by omega
        have hk : w - n - 1 < C.gates.length - 1 := by omega
        have hjk : j ≤ w - n - 1 := by omega
        have hdw : delWire n j r w = n + (w - n - 1) := by
          unfold delWire; rw [if_neg hwj, if_pos hgt]; omega
        have hw_eq : w = n + (w - n - 1 + 1) := by omega
        have hidx : w - n = w - n - 1 + 1 := by omega
        rw [hdw]
        conv_rhs => rw [hw_eq]
        have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
        rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
        have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
        rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
        have h0 := ih (opnd C (w - n - 1 + 1) 0)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          (by rw [← hidx]; exact (hop_ok 0).1) (by rw [← hidx]; exact (hop_ok 0).2)
        have h1 := ih (opnd C (w - n - 1 + 1) 1)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          (by rw [← hidx]; exact (hop_ok 1).1) (by rw [← hidx]; exact (hop_ok 1).2)
        rw [h0, h1, hg]

-- GraphFun helpers

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun; simp

lemma graphFun_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (fun w => decide (w = v)) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_iff]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hab

lemma graphFun_pair_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    unfold pairInput at ha hb
    simp only [decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (G.loopless.irrefl _)
    · exact hab
    · exact hab.symm
    · exact absurd hab (G.loopless.irrefl _)
  · intro huv
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

-- Consequences of IsLeastAO + IsLiftFixedPoint

lemma output_bounds {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    n ≤ C.output ∧ C.output < n + C.gates.length := by
  obtain ⟨u, v, huv⟩ := hne
  have hfun : ∀ x, wval C x C.output = graphFun G ∅ x := fun x => congrFun hL.2.1 x
  constructor
  · by_contra hlt
    push Not at hlt
    have h1 := hfun (fun w => decide (w = ⟨C.output, hlt⟩))
    rw [wval_input C _ C.output hlt, graphFun_unit_false] at h1
    simp at h1
  · by_contra hge
    push Not at hge
    have h1 := hfun (pairInput u v)
    rw [wval_ge_len C _ hge, (graphFun_pair_iff u v).mpr huv] at h1
    cases h1

lemma least_inOutputCone {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    ∀ j < C.gates.length, InOutputCone n C j := by
  have ⟨u, _, _⟩ := hne
  have hn0 : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hout := output_bounds hL hne
  intro j hj
  refine ⟨hj, ?_⟩
  by_contra hnot
  push Not at hnot
  have hr : 0 < n + j := by omega
  let C' := delCircuit n C j 0
  have hAO' := delCircuit_isAO2 hL.1 hj hr
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval C' x C'.output = graphFun G ∅ x
    rw [← congrFun hL.2.1 x]
    exact delCircuit_wval_not_inCone hL.1 x hj hr C.output hout.2 hnot.1 (fun _ => hnot.2 hout.1)
  have hsz := hL.2.2 C' hAO' hfun'
  simp only [Circuit.size, C', delCircuit_len n C hj 0] at hsz
  omega

lemma least_no_equiv_wire {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j) :
    ¬ ∀ x : Fin n → Bool, wval C x r = wval C x (n + j) := by
  have hout := output_bounds hL hne
  intro heq
  let C' := delCircuit n C j r
  have hAO' := delCircuit_isAO2 hL.1 hj hr
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval C' x C'.output = graphFun G ∅ x
    rw [← congrFun hL.2.1 x]
    exact delCircuit_wval_eq hL.1 x hj hr (heq x) C.output hout.2
  have hsz := hL.2.2 C' hAO' hfun'
  simp only [Circuit.size, C', delCircuit_len n C hj r] at hsz
  omega

lemma least_no_belowF_and_opnd {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {a : ℕ} (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and) (b : Fin 2) :
    ¬ ∀ x : Fin n → Bool, wval C x (opnd C a b) = true → graphFun G ∅ x = true := by
  have hout := output_bounds hL hne
  intro hbelow
  set r := opnd C a b
  have hr : r < n + a := opnd_lt hL.1 ha b
  let C' := delCircuit n C a r
  have hAO' := delCircuit_isAO2 hL.1 ha hr
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval C' x C'.output = graphFun G ∅ x
    cases hFx : graphFun G ∅ x
    · have hrx : wval C x r = false := by
        cases h : wval C x r
        · rfl
        · have := hbelow x h; rw [hFx] at this; cases this
      have hax : wval C x (n + a) = false := by
        rw [wval_gate_and hL.1 x ha hand]
        fin_cases b
        · change wval C x (opnd C a 0) = false at hrx; rw [hrx]; rfl
        · change wval C x (opnd C a 1) = false at hrx; rw [hrx, Bool.and_false]
      have hcx : wval C x C.output = false := by
        change circuitFun n C x = false; rw [congrFun hL.2.1 x]; exact hFx
      change wval (delCircuit n C a r) x (delWire n a r C.output) = false
      rw [delCircuit_wval_eq hL.1 x ha hr (by rw [hrx, hax]) C.output hout.2, hcx]
    · have hcx : wval C x C.output = true := by
        change circuitFun n C x = true; rw [congrFun hL.2.1 x]; exact hFx
      change wval (delCircuit n C a r) x (delWire n a r C.output) = true
      apply delCircuit_wval_ge hL.1 x ha hr _ C.output hout.2 hcx
      intro hax
      rw [wval_gate_and hL.1 x ha hand, Bool.and_eq_true] at hax
      fin_cases b
      · exact hax.1
      · exact hax.2
  have hsz := hL.2.2 C' hAO' hfun'
  simp only [Circuit.size, C', delCircuit_len n C ha r] at hsz
  omega

lemma input_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {w : ℕ} (hw : w < n) :
    ¬ ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true := by
  intro h
  have := h (fun i => decide (i = ⟨w, hw⟩)) (by rw [wval_input C _ w hw]; simp)
  rw [graphFun_unit_false] at this
  cases this

lemma lift_no_belowF_orN_opnd {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {h : ℕ} (hh : h < C.gates.length) (hor : (gateAt C h).op = GateOp.or)
    (hnb : ¬ BelowF G C h) (b : Fin 2) :
    ¬ ∀ x : Fin n → Bool, wval C x (opnd C h b) = true → graphFun G ∅ x = true := by
  intro hbelow
  apply hLift
  refine ⟨h, hh, b, least_inOutputCone hL hne h hh, hor, hnb, hbelow, ?_⟩
  refine ⟨fun _ => true, wval_allTrue hL.1 (opnd C h b) (by have := opnd_lt hL.1 hh b; omega)⟩

lemma orT_opnds_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) {h : ℕ} (hh : h < C.gates.length)
    (hor : (gateAt C h).op = GateOp.or) (hb : BelowF G C h) (b : Fin 2) :
    n ≤ opnd C h b ∧ opnd C h b - n < C.gates.length ∧ BelowF G C (opnd C h b - n) := by
  have hwb : ∀ x, wval C x (opnd C h b) = true → graphFun G ∅ x = true := by
    intro x hwx
    apply hb x
    rw [gateVal_eq_wval, wval_gate_or hL.1 x hh hor, Bool.or_eq_true]
    fin_cases b
    · exact Or.inl hwx
    · exact Or.inr hwx
  have hge : n ≤ opnd C h b := by
    by_contra hlt; push Not at hlt; exact input_not_belowF hlt hwb
  have hlt : opnd C h b < n + h := opnd_lt hL.1 hh b
  refine ⟨hge, by omega, ?_⟩
  intro x hx
  apply hwb x
  rw [gateVal_eq_wval] at hx
  rwa [show n + (opnd C h b - n) = opnd C h b by omega] at hx

lemma mem_tops_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ tops G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ BelowF G C k := by
  letI : DecidableEq GateOp := gateOpDecEq
  unfold tops gatesWhere; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_orT_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ orT G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ BelowF G C k := by
  letI : DecidableEq GateOp := gateOpDecEq
  unfold orT gatesWhere; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_orN_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ orN G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ ¬ BelowF G C k := by
  letI : DecidableEq GateOp := gateOpDecEq
  unfold orN gatesWhere; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_junk_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ ¬ BelowF G C k := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold IsDirtyAnd IsDirty BelowF
  constructor
  · rintro ⟨hk, hand, _, x, hgx, hfx⟩
    refine ⟨hk, hand, fun hb => ?_⟩
    have := hb x hgx; rw [hfx] at this; cases this
  · rintro ⟨hk, hand, hnb⟩
    push Not at hnb
    rcases hnb with ⟨x, hgx, hfx⟩
    refine ⟨hk, hand, hk, x, hgx, ?_⟩
    cases h : graphFun G ∅ x
    · rfl
    · exact absurd h hfx

lemma belowF_reader_is_orT {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {k m : ℕ} (hk : k < C.gates.length) (hbk : BelowF G C k)
    (hm : m < C.gates.length) (hread : n + k ∈ (gateAt C m).inputs) :
    m ∈ orT G C := by
  have hwb : ∀ x, wval C x (n + k) = true → graphFun G ∅ x = true := hbk
  rw [gate_inputs_eq hL.1 hm] at hread
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
  obtain ⟨b, hb⟩ : ∃ b : Fin 2, opnd C m b = n + k := by
    rcases hread with h0 | h1
    · exact ⟨0, h0.symm⟩
    · exact ⟨1, h1.symm⟩
  rcases hL.1.1 _ (gateAt_mem hm) with hand | hor
  · exfalso
    exact least_no_belowF_and_opnd hL hne hm hand b (by rw [hb]; exact hwb)
  · rw [mem_orT_iff]
    refine ⟨hm, hor, ?_⟩
    by_contra hnb
    exact lift_no_belowF_orN_opnd hL hLift hne hm hor hnb b (by rw [hb]; exact hwb)

lemma output_gate_mem_tops_or_orT {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    C.output - n ∈ tops G C ∪ orT G C := by
  have hout := output_bounds hL hne
  have hk : C.output - n < C.gates.length := by omega
  have hb : BelowF G C (C.output - n) := by
    intro x hx
    rw [gateVal_eq_wval, show n + (C.output - n) = C.output by omega] at hx
    rw [← congrFun hL.2.1 x]; exact hx
  rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
  rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
  · exact Or.inl ⟨hk, hand, hb⟩
  · exact Or.inr ⟨hk, hor, hb⟩

lemma exists_reader_of_inCone {n : ℕ} {C : Circuit} {k j : ℕ} (h : InCone n C k j) :
    ∃ m < C.gates.length, n + k ∈ (gateAt C m).inputs := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, hw, hnw, hwnj, rfl | hsub⟩
    · exact ⟨j, hj, by rwa [show n + (w - n) = w by omega]⟩
    · exact ih (w - n) (by omega) hsub

lemma tops_le_orT_add_one {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    (tops G C).card ≤ (orT G C).card + 1 := by
  have hout := output_bounds hL hne
  have hout_mem := output_gate_mem_tops_or_orT hL hne
  have hdisj : Disjoint (tops G C) (orT G C) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [mem_tops_iff] at hk1; rw [mem_orT_iff] at hk2
    rw [hk1.2.1] at hk2; cases hk2.2.1
  let S := ((tops G C ∪ orT G C).erase (C.output - n)).image (fun k => n + k)
  let T := (orT G C ×ˢ (Finset.univ : Finset (Fin 2))).image (fun p => opnd C p.1 p.2)
  have hsub : S ⊆ T := by
    intro w hw
    simp only [S, Finset.mem_image, Finset.mem_erase, Finset.mem_union] at hw
    rcases hw with ⟨k, ⟨hne_out, hk_mem⟩, rfl⟩
    have hk_lt : k < C.gates.length := by
      rcases hk_mem with h | h
      · exact (mem_tops_iff.mp h).1
      · exact (mem_orT_iff.mp h).1
    have hk_bf : BelowF G C k := by
      rcases hk_mem with h | h
      · exact (mem_tops_iff.mp h).2.2
      · exact (mem_orT_iff.mp h).2.2
    have hcone := least_inOutputCone hL hne k hk_lt
    have hin : InCone n C k (C.output - n) := by
      rcases hcone.2 with heq | ⟨_, hin⟩
      · exfalso; apply hne_out; omega
      · exact hin
    obtain ⟨m, hm, hread⟩ := exists_reader_of_inCone hin
    have hm_orT := belowF_reader_is_orT hL hLift hne hk_lt hk_bf hm hread
    rw [gate_inputs_eq hL.1 hm] at hread
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
    simp only [T, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true]
    rcases hread with h0 | h1
    · exact ⟨(m, 0), hm_orT, h0.symm⟩
    · exact ⟨(m, 1), hm_orT, h1.symm⟩
  have hcardS : S.card = (tops G C).card + (orT G C).card - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega),
      Finset.card_erase_of_mem hout_mem, Finset.card_union_of_disjoint hdisj]
  have hcardT : T.card ≤ 2 * (orT G C).card := by
    calc T.card ≤ (orT G C ×ˢ (Finset.univ : Finset (Fin 2))).card := Finset.card_image_le
      _ = (orT G C).card * 2 := by simp
      _ = 2 * (orT G C).card := Nat.mul_comm _ _
  have hle := Finset.card_le_card hsub
  rw [hcardS] at hle
  omega

lemma circuit_size_partition {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) :
    C.size = (tops G C).card + (orT G C).card + (junk G C).card + (orN G C).card := by
  have hU : Finset.range C.gates.length = tops G C ∪ orT G C ∪ junk G C ∪ orN G C := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, mem_tops_iff, mem_orT_iff, mem_junk_iff, mem_orN_iff]
    constructor
    · intro hk
      rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
      · by_cases hb : BelowF G C k
        · exact Or.inl (Or.inl (Or.inl ⟨hk, hand, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, hand, hb⟩)
      · by_cases hb : BelowF G C k
        · exact Or.inl (Or.inl (Or.inr ⟨hk, hor, hb⟩))
        · exact Or.inr ⟨hk, hor, hb⟩
    · rintro (((⟨hk, _⟩ | ⟨hk, _⟩) | ⟨hk, _⟩) | ⟨hk, _⟩) <;> exact hk
  have hd1 : Disjoint (tops G C) (orT G C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    rw [mem_tops_iff] at h1; rw [mem_orT_iff] at h2; rw [h1.2.1] at h2; cases h2.2.1
  have hd2 : Disjoint (tops G C ∪ orT G C) (junk G C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    rw [mem_junk_iff] at h2; simp only [Finset.mem_union, mem_tops_iff, mem_orT_iff] at h1
    rcases h1 with h1 | h1 <;> exact h2.2.2 h1.2.2
  have hd3 : Disjoint (tops G C ∪ orT G C ∪ junk G C) (orN G C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    rw [mem_orN_iff] at h2; simp only [Finset.mem_union, mem_tops_iff, mem_orT_iff, mem_junk_iff] at h1
    rcases h1 with (h1 | h1) | h1
    · exact h2.2.2 h1.2.2
    · exact h2.2.2 h1.2.2
    · rw [h1.2.1] at h2; cases h2.2.1
  change C.gates.length = _
  rw [← Finset.card_range C.gates.length, hU,
    Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
    Finset.card_union_of_disjoint hd1]

lemma circuitFun_iff_exists_top {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) (x : Fin n → Bool) :
    circuitFun n C x = true ↔ ∃ a ∈ tops G C, gateVal n C a x = true := by
  have hout := output_bounds hL hne
  have hout_mem := output_gate_mem_tops_or_orT hL hne
  constructor
  · intro hcx
    have hkey : ∀ k, k ∈ tops G C ∪ orT G C → gateVal n C k x = true →
        ∃ a ∈ tops G C, gateVal n C a x = true := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk hvk
        rw [Finset.mem_union] at hk
        rcases hk with htop | horT
        · exact ⟨k, htop, hvk⟩
        · rw [mem_orT_iff] at horT
          rw [gateVal_eq_wval, wval_gate_or hL.1 x horT.1 horT.2.1, Bool.or_eq_true] at hvk
          rcases hvk with h0 | h1
          · obtain ⟨hge, hlt, hbf⟩ := orT_opnds_belowF hL horT.1 horT.2.1 horT.2.2 0
            have hlt_k : opnd C k 0 - n < k := by have := opnd_lt hL.1 horT.1 0; omega
            have hmem : opnd C k 0 - n ∈ tops G C ∪ orT G C := by
              rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
              rcases hL.1.1 _ (gateAt_mem hlt) with hand | hor
              · exact Or.inl ⟨hlt, hand, hbf⟩
              · exact Or.inr ⟨hlt, hor, hbf⟩
            exact ih _ hlt_k hmem (by rw [gateVal_eq_wval, show n + (opnd C k 0 - n) = opnd C k 0 by omega]; exact h0)
          · obtain ⟨hge, hlt, hbf⟩ := orT_opnds_belowF hL horT.1 horT.2.1 horT.2.2 1
            have hlt_k : opnd C k 1 - n < k := by have := opnd_lt hL.1 horT.1 1; omega
            have hmem : opnd C k 1 - n ∈ tops G C ∪ orT G C := by
              rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
              rcases hL.1.1 _ (gateAt_mem hlt) with hand | hor
              · exact Or.inl ⟨hlt, hand, hbf⟩
              · exact Or.inr ⟨hlt, hor, hbf⟩
            exact ih _ hlt_k hmem (by rw [gateVal_eq_wval, show n + (opnd C k 1 - n) = opnd C k 1 by omega]; exact h1)
    apply hkey (C.output - n) hout_mem
    rw [gateVal_eq_wval, show n + (C.output - n) = C.output by omega]
    exact hcx
  · rintro ⟨a, ha, hva⟩
    rw [mem_tops_iff] at ha
    rw [congrFun hL.2.1 x]
    exact ha.2.2 x hva

lemma not_belowF_wval_eq {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2) :
    ∀ w < n + C.gates.length,
      (∀ k, w = n + k → ¬ BelowF G C k) →
      ∀ x : Fin n → Bool,
        wval C x w = true ↔
          (∃ u ∈ orIn n C w, x u = true) ∨
          (OrReaches n C w g1 ∧ gateVal n C g1 x = true) ∨
          (OrReaches n C w g2 ∧ gateVal n C g2 x = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hnb x
    by_cases hwn : w < n
    · constructor
      · intro hwx
        left
        refine ⟨⟨w, hwn⟩, (mem_orIn_input C _ _).mpr rfl, ?_⟩
        rwa [wval_input C x w hwn] at hwx
      · rintro (⟨u, hu, hxu⟩ | ⟨hr, _⟩ | ⟨hr, _⟩)
        · have huw : u = ⟨w, hwn⟩ := (mem_orIn_input C u ⟨w, hwn⟩).mp hu
          subst huw; rw [wval_input C x w hwn]; exact hxu
        · exact absurd hr (orReaches_input_false hwn)
        · exact absurd hr (orReaches_input_false hwn)
    · have hk : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      have hnbk : ¬ BelowF G C (w - n) := hnb (w - n) hw_eq
      rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
      · have hmem : w - n ∈ junk G C := mem_junk_iff.mpr ⟨hk, hand, hnbk⟩
        rw [hjunk] at hmem
        constructor
        · intro hwx
          rcases hmem with h1 | h2
          · right; left
            refine ⟨?_, ?_⟩
            · rw [hw_eq, h1]; exact orReaches_self (by omega)
            · rw [gateVal_eq_wval, ← h1, ← hw_eq]; exact hwx
          · right; right
            refine ⟨?_, ?_⟩
            · rw [hw_eq, h2]; exact orReaches_self (by omega)
            · rw [gateVal_eq_wval, ← h2, ← hw_eq]; exact hwx
        · rintro (⟨u, hu, _⟩ | ⟨hr, hvg⟩ | ⟨hr, hvg⟩)
          · rw [hw_eq, orIn_and_eq_empty hk hand] at hu; simp at hu
          · exact orReaches_val_mono hL.1 x hr hvg
          · exact orReaches_val_mono hL.1 x hr hvg
      · have hop_nb : ∀ b : Fin 2, ∀ m, opnd C (w - n) b = n + m → ¬ BelowF G C m := by
          intro b m hm hbm
          exact lift_no_belowF_orN_opnd hL hLift hne hk hor hnbk b (by rw [hm]; exact hbm)
        have hlt0 : opnd C (w - n) 0 < w := by have := opnd_lt hL.1 hk 0; omega
        have hlt1 : opnd C (w - n) 1 < w := by have := opnd_lt hL.1 hk 1; omega
        have ih0 := ih (opnd C (w - n) 0) hlt0 (by omega) (hop_nb 0) x
        have ih1 := ih (opnd C (w - n) 1) hlt1 (by omega) (hop_nb 1) x
        rw [hw_eq, wval_gate_or hL.1 x hk hor, Bool.or_eq_true, ih0, ih1,
          orIn_or_eq_union hL.1 hk hor]
        have hreach_iff : ∀ g, g = g1 ∨ g = g2 →
            (OrReaches n C (n + (w - n)) g ↔
              OrReaches n C (opnd C (w - n) 0) g ∨ OrReaches n C (opnd C (w - n) 1) g) := by
          intro g hg
          have hne_g : g ≠ w - n := by
            intro heq
            have hgj : g ∈ junk G C := (hjunk g).mpr hg
            rw [heq, mem_junk_iff] at hgj
            rw [hor] at hgj; cases hgj.2.1
          rw [orReaches_gate_iff hk]
          constructor
          · rintro (heq | ⟨_, u, hu, _, _, hug⟩)
            · exact absurd heq hne_g
            · rw [gate_inputs_eq hL.1 hk] at hu
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu with rfl | rfl
              · exact Or.inl hug
              · exact Or.inr hug
          · rintro (h0 | h1)
            · exact Or.inr ⟨hor, opnd C (w - n) 0, opnd_mem hL.1 hk 0, h0.1, opnd_lt hL.1 hk 0, h0⟩
            · exact Or.inr ⟨hor, opnd C (w - n) 1, opnd_mem hL.1 hk 1, h1.1, opnd_lt hL.1 hk 1, h1⟩
        rw [hreach_iff g1 (Or.inl rfl), hreach_iff g2 (Or.inr rfl)]
        constructor
        · rintro ((⟨u, hu, hxu⟩ | ⟨h1, hg1⟩ | ⟨h2, hg2⟩) | (⟨u, hu, hxu⟩ | ⟨h1, hg1⟩ | ⟨h2, hg2⟩))
          · exact Or.inl ⟨u, Finset.mem_union_left _ hu, hxu⟩
          · exact Or.inr (Or.inl ⟨Or.inl h1, hg1⟩)
          · exact Or.inr (Or.inr ⟨Or.inl h2, hg2⟩)
          · exact Or.inl ⟨u, Finset.mem_union_right _ hu, hxu⟩
          · exact Or.inr (Or.inl ⟨Or.inr h1, hg1⟩)
          · exact Or.inr (Or.inr ⟨Or.inr h2, hg2⟩)
        · rintro (⟨u, hu, hxu⟩ | ⟨h1 | h1, hg1⟩ | ⟨h2 | h2, hg2⟩)
          · rcases Finset.mem_union.mp hu with h0 | h1
            · exact Or.inl (Or.inl ⟨u, h0, hxu⟩)
            · exact Or.inr (Or.inl ⟨u, h1, hxu⟩)
          · exact Or.inl (Or.inr (Or.inl ⟨h1, hg1⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨h1, hg1⟩))
          · exact Or.inl (Or.inr (Or.inr ⟨h2, hg2⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨h2, hg2⟩))

-- Section 3: Graph properties, clean replacement circuit C', and master size inequality

lemma noFourCycle_unique {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h4 : NoFourCycle G) {a b w1 w2 : Fin n} (hab : a ≠ b)
    (ha1 : G.Adj a w1) (hb1 : G.Adj b w1) (ha2 : G.Adj a w2) (hb2 : G.Adj b w2) : w1 = w2 := by
  by_contra hne
  have hle := h4 a b hab
  have hsub : ({w1, w2} : Finset (Fin n)) ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with rfl | rfl
    · exact ⟨ha1, hb1⟩
    · exact ⟨ha2, hb2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hcard
  omega

lemma top_sides_adj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  rw [mem_tops_iff] at ha
  have hval : gateVal n C a (pairInput u v) = true := by
    rw [gateVal_eq_wval, wval_gate_and hAO _ ha.1 ha.2.1, Bool.and_eq_true]
    exact ⟨orIn_val_mono hAO _ hu (by simp [pairInput]),
      orIn_val_mono hAO _ hv (by simp [pairInput])⟩
  exact (graphFun_pair_iff u v).mp (ha.2.2 (pairInput u v) hval)

lemma top_is_star {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 n C) (h4 : NoFourCycle G) {a : ℕ} (ha : a ∈ tops G C \ centreless G C) :
    (side (n := n) C a 0).Nonempty ∧ (side (n := n) C a 1).Nonempty ∧
      ((side (n := n) C a 0).card = 1 ∨ (side (n := n) C a 1).card = 1) := by
  rw [Finset.mem_sdiff] at ha
  have hne0 : (side (n := n) C a 0).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0; exact ha.2 (Finset.mem_filter.mpr ⟨ha.1, Or.inl h0⟩)
  have hne1 : (side (n := n) C a 1).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h1; exact ha.2 (Finset.mem_filter.mpr ⟨ha.1, Or.inr h1⟩)
  refine ⟨hne0, hne1, ?_⟩
  by_contra hboth
  push Not at hboth
  have hc0 : 1 < (side (n := n) C a 0).card := by
    have := Finset.Nonempty.card_pos hne0; omega
  have hc1 : 1 < (side (n := n) C a 1).card := by
    have := Finset.Nonempty.card_pos hne1; omega
  obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp hc0
  obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.mp hc1
  exact hv12 (noFourCycle_unique h4 hu12
    (top_sides_adj hAO ha.1 hu1 hv1) (top_sides_adj hAO ha.1 hu2 hv1)
    (top_sides_adj hAO ha.1 hu1 hv2) (top_sides_adj hAO ha.1 hu2 hv2))

-- Clean replacement circuit C' builder

lemma wval_append_lt {n : ℕ} (gs1 gs2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool)
    {w : ℕ} (hw : w < n + gs1.length) :
    wval ⟨gs1 ++ gs2, o2⟩ x w = wval ⟨gs1, o1⟩ x w := by
  unfold wval Circuit.wires
  rw [List.foldl_append]
  have hlen : w < (gs1.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x)).length := by
    rw [foldl_wires_len, List.length_ofFn]; exact hw
  exact foldl_wires_getD_lt gs2 _ w hlen

def appendOrList (n : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => (gs, 0)
  | [w] => (gs, w)
  | w :: w2 :: ws =>
    let res := appendOrList n gs (w2 :: ws)
    (res.1 ++ [⟨GateOp.or, [w, res.2]⟩], n + res.1.length)

lemma appendOrList_prefix (n : ℕ) (gs : List Gate) (ws : List ℕ) :
    ∃ extra : List Gate, (appendOrList n gs ws).1 = gs ++ extra := by
  match ws with
  | [] => exact ⟨[], by simp [appendOrList]⟩
  | [w] => exact ⟨[], by simp [appendOrList]⟩
  | w :: w2 :: ws =>
    obtain ⟨extra, heq⟩ := appendOrList_prefix n gs (w2 :: ws)
    refine ⟨extra ++ [⟨GateOp.or, [w, (appendOrList n gs (w2 :: ws)).2]⟩], ?_⟩
    simp only [appendOrList, heq, List.append_assoc]

lemma appendOrList_len (n : ℕ) (gs : List Gate) (ws : List ℕ) (hne : ws ≠ []) :
    (appendOrList n gs ws).1.length = gs.length + (ws.length - 1) := by
  match ws with
  | [] => exact absurd rfl hne
  | [w] => simp [appendOrList]
  | w :: w2 :: ws =>
    have ih := appendOrList_len n gs (w2 :: ws) (by simp)
    simp only [appendOrList, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

lemma appendOrList_isAO2 {n : ℕ} {gs : List Gate} (hAO : IsAO2 n ⟨gs, 0⟩)
    (ws : List ℕ) (hne : ws ≠ []) (hws : ∀ w ∈ ws, w < n + gs.length) :
    IsAO2 n ⟨(appendOrList n gs ws).1, 0⟩ ∧
      (appendOrList n gs ws).2 < n + (appendOrList n gs ws).1.length := by
  match ws with
  | [] => exact absurd rfl hne
  | [w] =>
    simp only [appendOrList]
    exact ⟨hAO, hws w (by simp)⟩
  | w :: w2 :: ws =>
    have ⟨hAO', hlt'⟩ := appendOrList_isAO2 hAO (w2 :: ws) (by simp) (fun u hu => hws u (by simp [hu]))
    have hglen : gs.length ≤ (appendOrList n gs (w2 :: ws)).1.length := by
      rw [appendOrList_len n gs (w2 :: ws) (by simp)]; omega
    have hwlt : w < n + (appendOrList n gs (w2 :: ws)).1.length := by have := hws w (by simp); omega
    simp only [appendOrList]
    set gs' := (appendOrList n gs (w2 :: ws)).1
    set w' := (appendOrList n gs (w2 :: ws)).2
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hAO'.1 g hg
      · exact Or.inr rfl
    · intro j hj u hu
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < gs'.length
      · have hgat : gateAt ⟨gs' ++ [⟨GateOp.or, [w, w']⟩], 0⟩ j = gateAt ⟨gs', 0⟩ j := by
          rw [gateAt_eq (by simp; omega), gateAt_eq hlt]
          simp [List.getElem_append_left hlt]
        rw [hgat] at hu
        exact hAO'.2.1 j hlt u hu
      · have hjeq : j = gs'.length := by omega
        subst hjeq
        have hgat : gateAt ⟨gs' ++ [⟨GateOp.or, [w, w']⟩], 0⟩ gs'.length = ⟨GateOp.or, [w, w']⟩ := by
          rw [gateAt_eq (by simp)]
          simp
        rw [hgat] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact hwlt
        · exact hlt'
    · intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hAO'.2.2 g hg
      · rfl
    · simp only [List.length_append, List.length_singleton]; omega

lemma appendOrList_wval {n : ℕ} {gs : List Gate} (hAO : IsAO2 n ⟨gs, 0⟩) (x : Fin n → Bool)
    (ws : List ℕ) (hne : ws ≠ []) (hws : ∀ w ∈ ws, w < n + gs.length) :
    wval ⟨(appendOrList n gs ws).1, 0⟩ x (appendOrList n gs ws).2 =
      decide (∃ w ∈ ws, wval ⟨gs, 0⟩ x w = true) := by
  match ws with
  | [] => exact absurd rfl hne
  | [w] =>
    simp only [appendOrList, List.mem_singleton, exists_eq_left]
    cases wval ⟨gs, 0⟩ x w <;> rfl
  | w :: w2 :: ws =>
    have hrest := appendOrList_isAO2 hAO (w2 :: ws) (by simp) (fun u hu => hws u (by simp [hu]))
    have ih := appendOrList_wval hAO x (w2 :: ws) (by simp) (fun u hu => hws u (by simp [hu]))
    have hfull := appendOrList_isAO2 hAO (w :: w2 :: ws) (by simp) hws
    obtain ⟨extra, hextra⟩ := appendOrList_prefix n gs (w2 :: ws)
    simp only [appendOrList] at hfull ⊢
    set gs' := (appendOrList n gs (w2 :: ws)).1
    set w' := (appendOrList n gs (w2 :: ws)).2
    have hglen : gs.length ≤ gs'.length := by rw [hextra, List.length_append]; omega
    have hwlt : w < n + gs.length := hws w (by simp)
    have hgat : gateAt ⟨gs' ++ [⟨GateOp.or, [w, w']⟩], 0⟩ gs'.length = ⟨GateOp.or, [w, w']⟩ := by
      rw [gateAt_eq (by simp)]; simp
    have hop0 : opnd ⟨gs' ++ [⟨GateOp.or, [w, w']⟩], 0⟩ gs'.length 0 = w := by
      unfold opnd; rw [hgat]; rfl
    have hop1 : opnd ⟨gs' ++ [⟨GateOp.or, [w, w']⟩], 0⟩ gs'.length 1 = w' := by
      unfold opnd; rw [hgat]; rfl
    have hlen_lt : gs'.length < (gs' ++ [({ op := GateOp.or, inputs := [w, w'] } : Gate)]).length := by simp
    rw [wval_gate_or hfull.1 x hlen_lt (by rw [hgat]), hop0, hop1]
    rw [wval_append_lt gs' [({ op := GateOp.or, inputs := [w, w'] } : Gate)] 0 0 x (by omega),
      wval_append_lt gs' [({ op := GateOp.or, inputs := [w, w'] } : Gate)] 0 0 x hrest.2]
    have hvw : wval ⟨gs', 0⟩ x w = wval ⟨gs, 0⟩ x w := by
      rw [hextra]; exact wval_append_lt gs extra 0 0 x hwlt
    rw [hvw, ih]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, exists_eq_or_imp]

lemma appendGate_isAO2 {n : ℕ} {gs : List Gate} (hAO : IsAO2 n ⟨gs, 0⟩)
    {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {w0 w1 : ℕ} (h0 : w0 < n + gs.length) (h1 : w1 < n + gs.length) :
    IsAO2 n ⟨gs ++ [⟨op, [w0, w1]⟩], 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO.1 g hg
    · exact hop
  · intro j hj u hu
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hgat : gateAt ⟨gs ++ [⟨op, [w0, w1]⟩], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        rw [gateAt_eq (by simp; omega), gateAt_eq hlt]; simp [List.getElem_append_left hlt]
      rw [hgat] at hu
      exact hAO.2.1 j hlt u hu
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have hgat : gateAt ⟨gs ++ [⟨op, [w0, w1]⟩], 0⟩ gs.length = ⟨op, [w0, w1]⟩ := by
        rw [gateAt_eq (by simp)]; simp
      rw [hgat] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> assumption
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO.2.2 g hg
    · rfl

-- Layer 1: bypass map and lamGates

def bypass (n : ℕ) (C : Circuit) (lamList : List ℕ) : ℕ → ℕ
  | w =>
    if hw : w < n then w
    else
      let k := w - n
      if hk : k < C.gates.length then
        if k ∈ lamList then n + lamList.idxOf k
        else if (orIn n C (opnd C k 0)).Nonempty then
          if hlt : opnd C k 0 < w then bypass n C lamList (opnd C k 0) else 0
        else
          if hlt : opnd C k 1 < w then bypass n C lamList (opnd C k 1) else 0
      else 0
termination_by w => w

def lamGates (n : ℕ) (C : Circuit) (lamList : List ℕ) : List Gate :=
  lamList.map fun k => ⟨GateOp.or, [bypass n C lamList (opnd C k 0), bypass n C lamList (opnd C k 1)]⟩

lemma bypass_bound {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (lamList : List ℕ)
    (hsort : lamList.Pairwise (· < ·)) :
    ∀ w < n + C.gates.length, bypass n C lamList w < n ∨
      (n ≤ w ∧ ∃ k ∈ lamList, k ≤ w - n ∧ bypass n C lamList w = n + lamList.idxOf k) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlen
    unfold bypass
    dsimp only
    split_ifs with hw hk hmem h0 hlt0 h1
    · exact Or.inl hw
    · exact Or.inr ⟨by omega, w - n, hmem, le_refl _, rfl⟩
    · rcases ih (opnd C (w - n) 0) hlt0 (by omega) with hlt | ⟨hnle, k, hkmem, hkle, heq⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, k, hkmem, by omega, heq⟩
    · exfalso; have := opnd_lt hAO hk 0; omega
    · rcases ih (opnd C (w - n) 1) h1 (by omega) with hlt | ⟨hnle, k, hkmem, hkle, heq⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, k, hkmem, by omega, heq⟩
    · exfalso; have := opnd_lt hAO hk 1; omega
    · exfalso; omega

lemma idxOf_lt_of_pairwise_lt {l : List ℕ} (hsort : l.Pairwise (· < ·))
    {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hab : a < b) : l.idxOf a < l.idxOf b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.pairwise_cons] at hsort
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · omega
    · rw [List.idxOf_cons_self]
      have hne : a ≠ b := Nat.ne_of_lt hab
      rw [List.idxOf_cons_ne _ (by simp [hne])]
      exact Nat.succ_pos _
    · have := hsort.1 a ha; omega
    · have hnea : x ≠ a := by have := hsort.1 a ha; omega
      have hneb : x ≠ b := by have := hsort.1 b hb; omega
      rw [List.idxOf_cons_ne _ (by simp [hnea]), List.idxOf_cons_ne _ (by simp [hneb])]
      exact Nat.succ_lt_succ (ih hsort.2 ha hb)

lemma idxOf_getElem_of_nodup {l : List ℕ} (hnodup : l.Nodup) (j : ℕ) (hj : j < l.length) :
    l.idxOf l[j] = j := by
  induction l generalizing j with
  | nil => cases hj
  | cons x xs ih =>
    rw [List.nodup_cons] at hnodup
    cases j with
    | zero => simp
    | succ j' =>
      simp only [List.getElem_cons_succ]
      have hj' : j' < xs.length := by simp only [List.length_cons] at hj; omega
      have hne : x ≠ xs[j'] := fun h => hnodup.1 (h ▸ List.getElem_mem hj')
      rw [List.idxOf_cons_ne _ (by simp [hne]), ih hnodup.2 j' hj']

lemma lamGates_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (lamList : List ℕ) (hsort : lamList.Pairwise (· < ·))
    (hmem_lt : ∀ k ∈ lamList, k < C.gates.length) :
    IsAO2 n ⟨lamGates n C lamList, 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [lamGates, List.mem_map] at hg
    rcases hg with ⟨k, _, rfl⟩
    exact Or.inr rfl
  · intro j hj u hu
    simp only [lamGates, List.length_map] at hj
    rw [gateAt_eq (by simp [lamGates, hj])] at hu
    simp only [lamGates, List.getElem_map, List.mem_cons, List.not_mem_nil, or_false] at hu
    set k := lamList[j]
    have hk_mem : k ∈ lamList := List.getElem_mem hj
    have hk_lt : k < C.gates.length := hmem_lt k hk_mem
    have hidx : lamList.idxOf k = j := by
      have hnodup : lamList.Nodup := hsort.imp (fun {a b} h => Nat.ne_of_lt h)
      exact idxOf_getElem_of_nodup hnodup j hj
    have check_b : ∀ b : Fin 2, bypass n C lamList (opnd C k b) < n + j := by
      intro b
      have hltb : opnd C k b < n + k := opnd_lt hAO hk_lt b
      rcases bypass_bound hAO lamList hsort (opnd C k b) (by omega) with hlt | ⟨hnle, k', hk'm, hk'le, heq⟩
      · omega
      · rw [heq]
        have hk'lt : k' < k := by omega
        have hlt_idx := idxOf_lt_of_pairwise_lt hsort hk'm hk_mem hk'lt
        rw [hidx] at hlt_idx
        omega
    rcases hu with rfl | rfl
    · exact check_b 0
    · exact check_b 1
  · intro g hg
    simp only [lamGates, List.mem_map] at hg
    rcases hg with ⟨k, _, rfl⟩
    rfl

-- Leaf-side property for wires evaluated through lamGates
def LeafWire {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  w < n + C.gates.length ∧ (orIn n C w).Nonempty ∧
    (∀ k, w = n + k → ¬ BelowF G C k) ∧
    (∀ k, OrReaches n C w k → k ∈ orN G C →
      (orIn n C (opnd C k 0)).Nonempty → (orIn n C (opnd C k 1)).Nonempty → k ∈ lam G C)

lemma leafWire_opnd {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {k : ℕ} (hk : k ∈ orN G C) (hlw : LeafWire G C (n + k))
    (b : Fin 2) (hneb : (orIn n C (opnd C k b)).Nonempty) :
    LeafWire G C (opnd C k b) := by
  have hk' := mem_orN_iff.mp hk
  have hlt : opnd C k b < n + k := opnd_lt hL.1 hk'.1 b
  refine ⟨by omega, hneb, ?_, ?_⟩
  · intro m hm hbm
    exact lift_no_belowF_orN_opnd hL hLift hne hk'.1 hk'.2.1 hk'.2.2 b (by rw [hm]; exact hbm)
  · intro m hrm hm_orN h0 h1
    apply hlw.2.2.2 m _ hm_orN h0 h1
    exact (orReaches_gate_iff hk'.1).mpr
      (Or.inr ⟨hk'.2.1, opnd C k b, opnd_mem hL.1 hk'.1 b, hrm.1, hlt, hrm⟩)

lemma leafWire_of_top_side {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hneb : (side (n := n) C a b).Nonempty) (hcard : (side (n := n) C a (1 - b)).card = 1) :
    LeafWire G C (opnd C a b) := by
  have ha' := mem_tops_iff.mp ha
  have hlt : opnd C a b < n + a := opnd_lt hL.1 ha'.1 b
  refine ⟨by omega, hneb, ?_, ?_⟩
  · intro m hm hbm
    exact least_no_belowF_and_opnd hL hne ha'.1 ha'.2.1 b (by rw [hm]; exact hbm)
  · intro m hrm hm_orN h0 h1
    unfold lam
    exact Finset.mem_filter.mpr ⟨hm_orN, h0, h1, a, ha, b, hcard, hrm⟩

lemma bypass_wval {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    (lamList : List ℕ) (hsort : lamList.Pairwise (· < ·))
    (hlam_iff : ∀ k, k ∈ lamList ↔ k ∈ lam G C)
    (x : Fin n → Bool) :
    ∀ w, LeafWire G C w →
      bypass n C lamList w < n + lamList.length ∧
      wval ⟨lamGates n C lamList, 0⟩ x (bypass n C lamList w) =
        decide (∃ u ∈ orIn n C w, x u = true) := by
  have hmem_lt : ∀ k ∈ lamList, k < C.gates.length := fun k hk => by
    have := (hlam_iff k).mp hk; exact (mem_orN_iff.mp (Finset.mem_filter.mp this).1).1
  have hAO_lam := lamGates_isAO2 hL.1 lamList hsort hmem_lt
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlw
    by_cases hwn : w < n
    · have hbp : bypass n C lamList w = w := by unfold bypass; rw [dif_pos hwn]
      rw [hbp]
      refine ⟨by omega, ?_⟩
      rw [wval_input _ x w hwn]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro h; exact ⟨⟨w, hwn⟩, (mem_orIn_input C _ _).mpr rfl, h⟩
      · rintro ⟨u, hu, hxu⟩
        have heq := (mem_orIn_input C u ⟨w, hwn⟩).mp hu
        subst heq; exact hxu
    · have hk_lt : w - n < C.gates.length := by have := hlw.1; omega
      have hw_eq : w = n + (w - n) := by omega
      set k := w - n
      have hnbk : ¬ BelowF G C k := hlw.2.2.1 k hw_eq
      have hork : (gateAt C k).op = GateOp.or := by
        rcases hL.1.1 _ (gateAt_mem hk_lt) with hand | hor
        · exfalso
          have hemp := orIn_and_eq_empty (n := n) hk_lt hand
          rw [← hw_eq] at hemp
          exact hlw.2.1.ne_empty hemp
        · exact hor
      have hk_orN : k ∈ orN G C := mem_orN_iff.mpr ⟨hk_lt, hork, hnbk⟩
      have hlw_k : LeafWire G C (n + k) := by rwa [← hw_eq]
      have horIn_eq : orIn n C w = orIn n C (opnd C k 0) ∪ orIn n C (opnd C k 1) := by
        rw [hw_eq]; exact orIn_or_eq_union hL.1 hk_lt hork
      have hlt0 : opnd C k 0 < w := by have := opnd_lt hL.1 hk_lt 0; omega
      have hlt1 : opnd C k 1 < w := by have := opnd_lt hL.1 hk_lt 1; omega
      by_cases hmem : k ∈ lamList
      · have hbp : bypass n C lamList w = n + lamList.idxOf k := by
          unfold bypass; rw [dif_neg hwn, dif_pos hk_lt, if_pos hmem]
        have hidx_lt : lamList.idxOf k < lamList.length := List.idxOf_lt_length_iff.mpr hmem
        have hkl : k ∈ lam G C := (hlam_iff k).mp hmem
        have h0ne : (orIn n C (opnd C k 0)).Nonempty := (Finset.mem_filter.mp hkl).2.1
        have h1ne : (orIn n C (opnd C k 1)).Nonempty := (Finset.mem_filter.mp hkl).2.2.1
        have ih0 := ih (opnd C k 0) hlt0 (leafWire_opnd hL hLift hne hk_orN hlw_k 0 h0ne)
        have ih1 := ih (opnd C k 1) hlt1 (leafWire_opnd hL hLift hne hk_orN hlw_k 1 h1ne)
        rw [hbp]
        refine ⟨by omega, ?_⟩
        have hj' : lamList.idxOf k < (lamGates n C lamList).length := by simp [lamGates, hidx_lt]
        have hget : lamList[lamList.idxOf k] = k := List.getElem_idxOf hidx_lt
        have hgat : gateAt ⟨lamGates n C lamList, 0⟩ (lamList.idxOf k) =
            ⟨GateOp.or, [bypass n C lamList (opnd C k 0), bypass n C lamList (opnd C k 1)]⟩ := by
          rw [gateAt_eq hj']; simp [lamGates, hget]
        rw [wval_gate_or hAO_lam x hj' (by rw [hgat])]
        have hop0 : opnd ⟨lamGates n C lamList, 0⟩ (lamList.idxOf k) 0 =
            bypass n C lamList (opnd C k 0) := by unfold opnd; rw [hgat]; rfl
        have hop1 : opnd ⟨lamGates n C lamList, 0⟩ (lamList.idxOf k) 1 =
            bypass n C lamList (opnd C k 1) := by unfold opnd; rw [hgat]; rfl
        rw [hop0, hop1, ih0.2, ih1.2, horIn_eq]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_union]
        constructor
        · rintro (⟨u, hu, hxu⟩ | ⟨u, hu, hxu⟩)
          · exact ⟨u, Or.inl hu, hxu⟩
          · exact ⟨u, Or.inr hu, hxu⟩
        · rintro ⟨u, hu | hu, hxu⟩
          · exact Or.inl ⟨u, hu, hxu⟩
          · exact Or.inr ⟨u, hu, hxu⟩
      · have hnotboth : ¬ ((orIn n C (opnd C k 0)).Nonempty ∧ (orIn n C (opnd C k 1)).Nonempty) := by
          rintro ⟨h0, h1⟩
          apply hmem
          rw [hlam_iff]
          exact hlw_k.2.2.2 k (orReaches_self hk_lt) hk_orN h0 h1
        by_cases h0ne : (orIn n C (opnd C k 0)).Nonempty
        · have h1emp : orIn n C (opnd C k 1) = ∅ := by
            by_contra hne1; exact hnotboth ⟨h0ne, Finset.nonempty_iff_ne_empty.mpr hne1⟩
          have hbp : bypass n C lamList w = bypass n C lamList (opnd C k 0) := by
            conv_lhs => unfold bypass
            dsimp only
            rw [dif_neg hwn, dif_pos hk_lt, if_neg hmem, if_pos h0ne, dif_pos hlt0]
          rw [hbp, horIn_eq, h1emp, Finset.union_empty]
          exact ih (opnd C k 0) hlt0 (leafWire_opnd hL hLift hne hk_orN hlw_k 0 h0ne)
        · have h0emp : orIn n C (opnd C k 0) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h0ne
          have h1ne : (orIn n C (opnd C k 1)).Nonempty := by
            have hne' := hlw.2.1
            rw [horIn_eq, h0emp, Finset.empty_union] at hne'
            exact hne'
          have hbp : bypass n C lamList w = bypass n C lamList (opnd C k 1) := by
            conv_lhs => unfold bypass
            dsimp only
            rw [dif_neg hwn, dif_pos hk_lt, if_neg hmem, if_neg h0ne, dif_pos hlt1]
          rw [hbp, horIn_eq, h0emp, Finset.empty_union]
          exact ih (opnd C k 1) hlt1 (leafWire_opnd hL hLift hne hk_orN hlw_k 1 h1ne)

-- Folding Layer 2 + Layer 3 cleanly:
-- Given a list of stars: each item is (v : Fin n, baseWire : Option ℕ, extraVerts : List (Fin n))
-- If baseWire = some bw and extraVerts = []: appends 1 AND gate (v, bw), cost = 1.
-- If baseWire = some bw and extraVerts ≠ []: builds OR of extraVerts (len - 1), OR with bw (1), AND with v (1), cost = extraVerts.length + 1.
-- If baseWire = none and extraVerts ≠ []: builds OR of extraVerts (len - 1), AND with v (1), cost = extraVerts.length.

def addStar (n : ℕ) (gs : List Gate) (v : Fin n) (base : Option ℕ) (extra : List (Fin n)) :
    List Gate × ℕ :=
  match base, extra with
  | some bw, [] =>
    (gs ++ [⟨GateOp.and, [v.val, bw]⟩], n + gs.length)
  | some bw, e :: es =>
    let r1 := appendOrList n gs ((e :: es).map Fin.val)
    let gs2 := r1.1 ++ [⟨GateOp.or, [bw, r1.2]⟩]
    (gs2 ++ [⟨GateOp.and, [v.val, n + r1.1.length]⟩], n + gs2.length)
  | none, e :: es =>
    let r1 := appendOrList n gs ((e :: es).map Fin.val)
    (r1.1 ++ [⟨GateOp.and, [v.val, r1.2]⟩], n + r1.1.length)
  | none, [] => (gs, 0)

def addStars (n : ℕ) (gs : List Gate) :
    List (Fin n × Option ℕ × List (Fin n)) → List Gate × List ℕ
  | [] => (gs, [])
  | (v, base, extra) :: rest =>
    let r := addStar n gs v base extra
    let r2 := addStars n r.1 rest
    (r2.1, r.2 :: r2.2)

lemma addStar_spec {n : ℕ} {gs : List Gate} (hAO : IsAO2 n ⟨gs, 0⟩)
    (v : Fin n) (base : Option ℕ) (extra : List (Fin n))
    (hbase : ∀ bw, base = some bw → bw < n + gs.length)
    (hne : base.isSome ∨ extra ≠ []) :
    (∃ ex : List Gate, (addStar n gs v base extra).1 = gs ++ ex) ∧
    (addStar n gs v base extra).1.length =
      gs.length + extra.length + (if base.isSome then 1 else 0) ∧
    IsAO2 n ⟨(addStar n gs v base extra).1, 0⟩ ∧
    (addStar n gs v base extra).2 < n + (addStar n gs v base extra).1.length ∧
    ∀ x : Fin n → Bool,
      wval ⟨(addStar n gs v base extra).1, 0⟩ x (addStar n gs v base extra).2 =
        (x v && (decide (∃ bw, base = some bw ∧ wval ⟨gs, 0⟩ x bw = true) ||
          decide (∃ u ∈ extra, x u = true))) := by
  cases base with
  | none =>
    cases extra with
    | nil => simp at hne
    | cons e es =>
      have hws : ∀ w ∈ (e :: es).map Fin.val, w < n + gs.length := by
        intro w hw; simp only [List.mem_map] at hw; rcases hw with ⟨u, _, rfl⟩; omega
      obtain ⟨ex1, hex1⟩ := appendOrList_prefix n gs ((e :: es).map Fin.val)
      have hlen1 := appendOrList_len n gs ((e :: es).map Fin.val) (by simp)
      have ⟨hAO1, hlt1⟩ := appendOrList_isAO2 hAO ((e :: es).map Fin.val) (by simp) hws
      dsimp only [addStar]
      set gs1 := (appendOrList n gs ((e :: es).map Fin.val)).1
      set w1 := (appendOrList n gs ((e :: es).map Fin.val)).2
      have hAO2 := appendGate_isAO2 hAO1 (Or.inl rfl) (by omega : v.val < n + gs1.length) hlt1
      refine ⟨⟨ex1 ++ [⟨GateOp.and, [v.val, w1]⟩], by rw [hex1, List.append_assoc]⟩,
        ?_, hAO2, by simp, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, hlen1, List.length_map,
          Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        omega
      · intro x
        have hgat : gateAt ⟨gs1 ++ [⟨GateOp.and, [v.val, w1]⟩], 0⟩ gs1.length =
            ⟨GateOp.and, [v.val, w1]⟩ := by rw [gateAt_eq (by simp)]; simp
        rw [wval_gate_and hAO2 x (by simp) (by rw [hgat])]
        have hop0 : opnd ⟨gs1 ++ [⟨GateOp.and, [v.val, w1]⟩], 0⟩ gs1.length 0 = v.val := by
          unfold opnd; rw [hgat]; rfl
        have hop1 : opnd ⟨gs1 ++ [⟨GateOp.and, [v.val, w1]⟩], 0⟩ gs1.length 1 = w1 := by
          unfold opnd; rw [hgat]; rfl
        rw [hop0, hop1, wval_input _ x v.val v.isLt,
          wval_append_lt gs1 [⟨GateOp.and, [v.val, w1]⟩] 0 0 x hlt1,
          appendOrList_wval hAO x ((e :: es).map Fin.val) (by simp) hws]
        congr 1
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_map, false_or, reduceCtorEq, false_and, exists_false]
        constructor
        · rintro ⟨_, ⟨u, hu, rfl⟩, hxu⟩
          rw [wval_input _ x u.val u.isLt] at hxu; exact ⟨u, hu, hxu⟩
        · rintro ⟨u, hu, hxu⟩
          exact ⟨u.val, ⟨u, hu, rfl⟩, by rw [wval_input _ x u.val u.isLt]; exact hxu⟩
  | some bw =>
    have hbw : bw < n + gs.length := hbase bw rfl
    cases extra with
    | nil =>
      have hAO2 := appendGate_isAO2 hAO (Or.inl rfl) (by omega : v.val < n + gs.length) hbw
      refine ⟨⟨[⟨GateOp.and, [v.val, bw]⟩], rfl⟩, ?_, hAO2, by simp [addStar], ?_⟩
      · simp [addStar]
      · intro x
        simp only [addStar]
        have hgat : gateAt ⟨gs ++ [⟨GateOp.and, [v.val, bw]⟩], 0⟩ gs.length =
            ⟨GateOp.and, [v.val, bw]⟩ := by rw [gateAt_eq (by simp)]; simp
        rw [wval_gate_and hAO2 x (by simp) (by rw [hgat])]
        have hop0 : opnd ⟨gs ++ [⟨GateOp.and, [v.val, bw]⟩], 0⟩ gs.length 0 = v.val := by
          unfold opnd; rw [hgat]; rfl
        have hop1 : opnd ⟨gs ++ [⟨GateOp.and, [v.val, bw]⟩], 0⟩ gs.length 1 = bw := by
          unfold opnd; rw [hgat]; rfl
        rw [hop0, hop1, wval_input _ x v.val v.isLt,
          wval_append_lt gs [⟨GateOp.and, [v.val, bw]⟩] 0 0 x hbw]
        congr 1
        cases h : wval ⟨gs, 0⟩ x bw <;> simp [h]
    | cons e es =>
      have hws : ∀ w ∈ (e :: es).map Fin.val, w < n + gs.length := by
        intro w hw; simp only [List.mem_map] at hw; rcases hw with ⟨u, _, rfl⟩; omega
      obtain ⟨ex1, hex1⟩ := appendOrList_prefix n gs ((e :: es).map Fin.val)
      have hlen1 := appendOrList_len n gs ((e :: es).map Fin.val) (by simp)
      have ⟨hAO1, hlt1⟩ := appendOrList_isAO2 hAO ((e :: es).map Fin.val) (by simp) hws
      dsimp only [addStar]
      set gs1 := (appendOrList n gs ((e :: es).map Fin.val)).1
      set w1 := (appendOrList n gs ((e :: es).map Fin.val)).2
      have hbw1 : bw < n + gs1.length := by rw [hex1, List.length_append]; omega
      have hAO2 := appendGate_isAO2 hAO1 (Or.inr rfl) hbw1 hlt1
      set gs2 := gs1 ++ [⟨GateOp.or, [bw, w1]⟩]
      have hAO3 := appendGate_isAO2 hAO2 (Or.inl rfl)
        (by simp [gs2]; omega : v.val < n + gs2.length) (by simp [gs2] : n + gs1.length < n + gs2.length)
      refine ⟨⟨ex1 ++ [⟨GateOp.or, [bw, w1]⟩, ⟨GateOp.and, [v.val, n + gs1.length]⟩],
          by simp only [gs2, hex1, List.append_assoc]; rfl⟩,
        ?_, hAO3, by simp [gs2], ?_⟩
      · simp only [gs2, List.length_append, List.length_cons, List.length_nil, hlen1,
          List.length_map, Option.isSome_some, ↓reduceIte]
        omega
      · intro x
        have hgat3 : gateAt ⟨gs2 ++ [⟨GateOp.and, [v.val, n + gs1.length]⟩], 0⟩ gs2.length =
            ⟨GateOp.and, [v.val, n + gs1.length]⟩ := by rw [gateAt_eq (by simp)]; simp
        rw [wval_gate_and hAO3 x (by simp) (by rw [hgat3])]
        have hop30 : opnd ⟨gs2 ++ [⟨GateOp.and, [v.val, n + gs1.length]⟩], 0⟩ gs2.length 0 = v.val := by
          unfold opnd; rw [hgat3]; rfl
        have hop31 : opnd ⟨gs2 ++ [⟨GateOp.and, [v.val, n + gs1.length]⟩], 0⟩ gs2.length 1 =
            n + gs1.length := by unfold opnd; rw [hgat3]; rfl
        rw [hop30, hop31, wval_input _ x v.val v.isLt,
          wval_append_lt gs2 [⟨GateOp.and, [v.val, n + gs1.length]⟩] 0 0 x (by simp [gs2])]
        have hgat2 : gateAt ⟨gs2, 0⟩ gs1.length = ⟨GateOp.or, [bw, w1]⟩ := by
          rw [gateAt_eq (by simp [gs2])]; simp [gs2]
        rw [wval_gate_or hAO2 x (by simp [gs2]) (by rw [hgat2])]
        have hop20 : opnd ⟨gs2, 0⟩ gs1.length 0 = bw := by unfold opnd; rw [hgat2]; rfl
        have hop21 : opnd ⟨gs2, 0⟩ gs1.length 1 = w1 := by unfold opnd; rw [hgat2]; rfl
        rw [hop20, hop21, wval_append_lt gs1 [⟨GateOp.or, [bw, w1]⟩] 0 0 x hbw1,
          wval_append_lt gs1 [⟨GateOp.or, [bw, w1]⟩] 0 0 x hlt1]
        have hvbw : wval ⟨gs1, 0⟩ x bw = wval ⟨gs, 0⟩ x bw := by
          rw [hex1]; exact wval_append_lt gs ex1 0 0 x hbw
        rw [hvbw, appendOrList_wval hAO x ((e :: es).map Fin.val) (by simp) hws]
        congr 1
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_map, Option.some.injEq, exists_eq_left']
        constructor
        · rintro (h | ⟨_, ⟨u, hu, rfl⟩, hxu⟩)
          · exact Or.inl h
          · rw [wval_input _ x u.val u.isLt] at hxu; exact Or.inr ⟨u, hu, hxu⟩
        · rintro (h | ⟨u, hu, hxu⟩)
          · exact Or.inl h
          · exact Or.inr ⟨u.val, ⟨u, hu, rfl⟩, by rw [wval_input _ x u.val u.isLt]; exact hxu⟩

lemma addStars_spec {n : ℕ} {gs : List Gate} (hAO : IsAO2 n ⟨gs, 0⟩)
    (items : List (Fin n × Option ℕ × List (Fin n)))
    (hitems : ∀ it ∈ items, (∀ bw, it.2.1 = some bw → bw < n + gs.length) ∧
      (it.2.1.isSome ∨ it.2.2 ≠ [])) :
    (∃ ex : List Gate, (addStars n gs items).1 = gs ++ ex) ∧
    (addStars n gs items).1.length =
      gs.length + (items.map fun it => it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum ∧
    (addStars n gs items).2.length = items.length ∧
    IsAO2 n ⟨(addStars n gs items).1, 0⟩ ∧
    (∀ w ∈ (addStars n gs items).2, w < n + (addStars n gs items).1.length) ∧
    ∀ x : Fin n → Bool,
      (∃ w ∈ (addStars n gs items).2, wval ⟨(addStars n gs items).1, 0⟩ x w = true) ↔
        ∃ it ∈ items, x it.1 = true ∧
          ((∃ bw, it.2.1 = some bw ∧ wval ⟨gs, 0⟩ x bw = true) ∨
            ∃ u ∈ it.2.2, x u = true) := by
  induction items generalizing gs with
  | nil =>
    refine ⟨⟨[], by simp [addStars]⟩, by simp [addStars], rfl, hAO, by simp [addStars], ?_⟩
    intro x; simp [addStars]
  | cons it rest ih =>
    rcases it with ⟨v, base, extra⟩
    have hit := hitems (v, base, extra) (by simp)
    obtain ⟨⟨ex1, hex1⟩, hlen1, hAO1, hlt1, hval1⟩ := addStar_spec hAO v base extra hit.1 hit.2
    dsimp only [addStars]
    set r := addStar n gs v base extra
    have hrest : ∀ it' ∈ rest, (∀ bw, it'.2.1 = some bw → bw < n + r.1.length) ∧
        (it'.2.1.isSome ∨ it'.2.2 ≠ []) := by
      intro it' hit'
      have h0 := hitems it' (by simp [hit'])
      exact ⟨fun bw hbw => by have := h0.1 bw hbw; rw [hex1, List.length_append]; omega, h0.2⟩
    obtain ⟨⟨ex2, hex2⟩, hlen2, hwlen2, hAO2, hlt2, hval2⟩ := ih hAO1 hrest
    refine ⟨⟨ex1 ++ ex2, by rw [hex2, hex1, List.append_assoc]⟩, ?_, ?_, hAO2, ?_, ?_⟩
    · simp only [hlen2, hlen1, List.map_cons, List.sum_cons]; omega
    · simp only [List.length_cons, hwlen2]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · rw [hex2, List.length_append]; omega
      · exact hlt2 w hw
    · intro x
      simp only [List.mem_cons, exists_eq_or_imp]
      have hvw : wval ⟨(addStars n r.1 rest).1, 0⟩ x r.2 =
          (x v && (decide (∃ bw, base = some bw ∧ wval ⟨gs, 0⟩ x bw = true) ||
            decide (∃ u ∈ extra, x u = true))) := by
        rw [hex2, wval_append_lt r.1 ex2 0 0 x hlt1, hval1 x]
      have hiff_rest : (∃ w ∈ (addStars n r.1 rest).2, wval ⟨(addStars n r.1 rest).1, 0⟩ x w = true) ↔
          ∃ it' ∈ rest, x it'.1 = true ∧
            ((∃ bw, it'.2.1 = some bw ∧ wval ⟨gs, 0⟩ x bw = true) ∨
              ∃ u ∈ it'.2.2, x u = true) := by
        rw [hval2 x]
        apply exists_congr; intro it'
        apply and_congr_right; intro hit'
        apply and_congr_right; intro _
        apply or_congr_left
        apply exists_congr; intro bw
        apply and_congr_right; intro hbw
        have hlt_bw := (hitems it' (by simp [hit'])).1 bw hbw
        rw [hex1, wval_append_lt gs ex1 0 0 x hlt_bw]
      rw [hvw, hiff_rest]
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]

-- Master size reduction lemma: if we can cover Ustar with (Zact, L, Zhas, topOf),
-- then 2 * |centreless| + |orN \ lam| + 2 <= sum_{v in Zact} |L v| + |Zact \ Zhas|.

lemma master_surgery_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    {g1 g2 : ℕ} (hg12 : g1 ≠ g2) (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
    (hne : ∃ u v : Fin n, G.Adj u v)
    (Zact Zhas : Finset (Fin n)) (L : Fin n → Finset (Fin n)) (topOf : Fin n → ℕ)
    (hZsub : Zhas ⊆ Zact)
    (hLne : ∀ v ∈ Zact, (L v).Nonempty)
    (hLadj : ∀ v ∈ Zact, ∀ u ∈ L v, G.Adj v u)
    (hUcov : ∀ e ∈ Ustar G C, ∃ v ∈ Zact, ∃ u ∈ L v, e = s(v, u))
    (htop_mem : ∀ v ∈ Zhas, topOf v ∈ tops G C \ centreless G C)
    (htop_side : ∀ v ∈ Zhas, side (n := n) C (topOf v) 0 = {v} ∨ side (n := n) C (topOf v) 1 = {v})
    (htop_inj : ∀ v1 ∈ Zhas, ∀ v2 ∈ Zhas, topOf v1 = topOf v2 → v1 = v2) :
    2 * (centreless G C).card + (orN G C \ lam G C).card + 2 ≤
      (∑ v ∈ Zact, (L v).card) + (Zact \ Zhas).card := by
  classical
  set S_tops := tops G C \ centreless G C
  set lamList := (lam G C).sort (· ≤ ·)
  have hsort : lamList.Pairwise (· < ·) :=
    ((Finset.pairwise_sort (lam G C) (· ≤ ·)).and (Finset.sort_nodup (lam G C) (· ≤ ·))).imp
      (fun ⟨h1, h2⟩ => Nat.lt_of_le_of_ne h1 h2)
  have hlam_iff : ∀ k, k ∈ lamList ↔ k ∈ lam G C := fun k => Finset.mem_sort (· ≤ ·)
  have hlam_len : lamList.length = (lam G C).card := Finset.length_sort (· ≤ ·)
  have hmem_lt : ∀ k ∈ lamList, k < C.gates.length := fun k hk =>
    (mem_orN_iff.mp (Finset.mem_filter.mp ((hlam_iff k).mp hk)).1).1
  set gs1 := lamGates n C lamList
  have hAO1 : IsAO2 n ⟨gs1, 0⟩ := lamGates_isAO2 hL.1 lamList hsort hmem_lt
  have hgs1_len : gs1.length = (lam G C).card := by simp [gs1, lamGates, hlam_len]
  -- Choose center and leaf side for every a in S_tops:
  -- if a = topOf v for some v in Zhas, choose that v and extra = (L v).toList;
  -- else choose an arbitrary center of a and extra = [].
  let mkTopItem : ℕ → Fin n × Option ℕ × List (Fin n) := fun a =>
    if h : ∃ v ∈ Zhas, topOf v = a then
      let v := Classical.choose h
      have hv := Classical.choose_spec h
      have hs : side (n := n) C a 0 = {v} ∨ side (n := n) C a 1 = {v} := by
        rw [← hv.2]; exact htop_side v hv.1
      let b : Fin 2 := if side (n := n) C a 0 = {v} then 1 else 0
      (v, some (bypass n C lamList (opnd C a b)), (L v).toList)
    else
      if ha : a ∈ S_tops then
        have hst := top_is_star hL.1 h4 ha
        if h0 : (side (n := n) C a 0).card = 1 then
          let v := Classical.choose (Finset.card_eq_one.mp h0)
          (v, some (bypass n C lamList (opnd C a 1)), [])
        else
          have h1 : (side (n := n) C a 1).card = 1 := hst.2.2.resolve_left h0
          let v := Classical.choose (Finset.card_eq_one.mp h1)
          (v, some (bypass n C lamList (opnd C a 0)), [])
      else
        (Classical.choose hne, none, [])
  let topItems := S_tops.toList.map mkTopItem
  let newItems := (Zact \ Zhas).toList.map fun v => (v, (none : Option ℕ), (L v).toList)
  let allItems := topItems ++ newItems
  -- Helper: check mkTopItem properties for a in S_tops
  have htopItem_ok : ∀ a ∈ S_tops,
      let it := mkTopItem a
      (∀ bw, it.2.1 = some bw → bw < n + gs1.length) ∧
      it.2.1.isSome ∧
      (∀ x : Fin n → Bool,
        (x it.1 = true ∧ ((∃ bw, it.2.1 = some bw ∧ wval ⟨gs1, 0⟩ x bw = true) ∨
          ∃ u ∈ it.2.2, x u = true)) ↔
        ((∃ u ∈ side (n := n) C a 0, x u = true) ∧ (∃ v ∈ side (n := n) C a 1, x v = true)) ∨
          ∃ v ∈ Zhas, topOf v = a ∧ x v = true ∧ ∃ u ∈ L v, x u = true) := by
    intro a ha
    have ha_top : a ∈ tops G C := (Finset.mem_sdiff.mp ha).1
    have hst := top_is_star hL.1 h4 ha
    by_cases h : ∃ v ∈ Zhas, topOf v = a
    · simp only [mkTopItem, dif_pos h]
      set v := Classical.choose h
      have hv := Classical.choose_spec h
      have hs : side (n := n) C a 0 = {v} ∨ side (n := n) C a 1 = {v} := by
        rw [← hv.2]; exact htop_side v hv.1
      set b : Fin 2 := if side (n := n) C a 0 = {v} then 1 else 0
      have h1mb : side (n := n) C a (1 - b) = {v} := by
        by_cases h0 : side (n := n) C a 0 = {v}
        · simp [b, h0]
        · simp [b, h0]; exact hs.resolve_left h0
      have hcard : (side (n := n) C a (1 - b)).card = 1 := by rw [h1mb]; simp
      have hneb : (side (n := n) C a b).Nonempty := by
        by_cases h0 : side (n := n) C a 0 = {v}
        · simp [b, h0]; exact hst.2.1
        · simp [b, h0]; exact hst.1
      have hlw := leafWire_of_top_side hL hne ha_top b hneb hcard
      refine ⟨?_, rfl, ?_⟩
      · intro bw hbw
        injection hbw with hbw; subst hbw
        have := (bypass_wval hL hLift hne lamList hsort hlam_iff (fun _ => false) _ hlw).1
        rw [hgs1_len, ← hlam_len]; exact this
      · intro x
        have hbp : wval ⟨gs1, 0⟩ x (bypass n C lamList (opnd C a b)) =
            decide (∃ u ∈ orIn n C (opnd C a b), x u = true) :=
          (bypass_wval hL hLift hne lamList hsort hlam_iff x _ hlw).2
        simp only [Option.some.injEq, exists_eq_left', hbp, decide_eq_true_eq, Finset.mem_toList]
        have huniq : ∀ v' ∈ Zhas, topOf v' = a → v' = v := fun v' hv' heq =>
          htop_inj v' hv' v hv.1 (heq.trans hv.2.symm)
        constructor
        · rintro ⟨hxv, hleaf | ⟨u, hu, hxu⟩⟩
          · left
            by_cases h0 : side (n := n) C a 0 = {v}
            · simp only [b, if_pos h0] at hleaf
              exact ⟨⟨v, by rw [h0]; simp, hxv⟩, hleaf⟩
            · simp only [b, if_neg h0] at hleaf
              have h1 : side (n := n) C a 1 = {v} := hs.resolve_left h0
              exact ⟨hleaf, ⟨v, by rw [h1]; simp, hxv⟩⟩
          · right; exact ⟨v, hv.1, hv.2, hxv, u, hu, hxu⟩
        · rintro (⟨h0, h1⟩ | ⟨v', hv', heq, hxv', u, hu, hxu⟩)
          · by_cases hs0 : side (n := n) C a 0 = {v}
            · simp only [b, if_pos hs0]
              rcases h0 with ⟨u0, hu0, hxu0⟩
              rw [hs0, Finset.mem_singleton] at hu0; subst hu0
              exact ⟨hxu0, Or.inl h1⟩
            · simp only [b, if_neg hs0]
              have hs1 : side (n := n) C a 1 = {v} := hs.resolve_left hs0
              rcases h1 with ⟨u1, hu1, hxu1⟩
              rw [hs1, Finset.mem_singleton] at hu1; subst hu1
              exact ⟨hxu1, Or.inl h0⟩
          · have hv'eq := huniq v' hv' heq; subst hv'eq
            exact ⟨hxv', Or.inr ⟨u, hu, hxu⟩⟩
    · simp only [mkTopItem, dif_neg h, dif_pos ha]
      by_cases h0 : (side (n := n) C a 0).card = 1
      · simp only [dif_pos h0]
        set v := Classical.choose (Finset.card_eq_one.mp h0)
        have hv : side (n := n) C a 0 = {v} := Classical.choose_spec (Finset.card_eq_one.mp h0)
        have hlw := leafWire_of_top_side hL hne ha_top 1 hst.2.1 (by simpa using h0)
        refine ⟨?_, rfl, ?_⟩
        · intro bw hbw
          injection hbw with hbw; subst hbw
          have := (bypass_wval hL hLift hne lamList hsort hlam_iff (fun _ => false) _ hlw).1
          rw [hgs1_len, ← hlam_len]; exact this
        · intro x
          have hbp : wval ⟨gs1, 0⟩ x (bypass n C lamList (opnd C a 1)) =
              decide (∃ u ∈ orIn n C (opnd C a 1), x u = true) :=
            (bypass_wval hL hLift hne lamList hsort hlam_iff x _ hlw).2
          simp only [Option.some.injEq, exists_eq_left', hbp, decide_eq_true_eq,
            List.not_mem_nil, false_and, exists_false, or_false]
          have hno : ¬ ∃ v' ∈ Zhas, topOf v' = a ∧ x v' = true ∧ ∃ u ∈ L v', x u = true := by
            rintro ⟨v', hv', heq, _⟩; exact h ⟨v', hv', heq⟩
          rw [or_iff_left hno, hv]
          simp only [Finset.mem_singleton, exists_eq_left]
          rfl
      · simp only [dif_neg h0]
        have h1 : (side (n := n) C a 1).card = 1 := hst.2.2.resolve_left h0
        set v := Classical.choose (Finset.card_eq_one.mp h1)
        have hv : side (n := n) C a 1 = {v} := Classical.choose_spec (Finset.card_eq_one.mp h1)
        have hlw := leafWire_of_top_side hL hne ha_top 0 hst.1 (by simpa using h1)
        refine ⟨?_, rfl, ?_⟩
        · intro bw hbw
          injection hbw with hbw; subst hbw
          have := (bypass_wval hL hLift hne lamList hsort hlam_iff (fun _ => false) _ hlw).1
          rw [hgs1_len, ← hlam_len]; exact this
        · intro x
          have hbp : wval ⟨gs1, 0⟩ x (bypass n C lamList (opnd C a 0)) =
              decide (∃ u ∈ orIn n C (opnd C a 0), x u = true) :=
            (bypass_wval hL hLift hne lamList hsort hlam_iff x _ hlw).2
          simp only [Option.some.injEq, exists_eq_left', hbp, decide_eq_true_eq,
            List.not_mem_nil, false_and, exists_false, or_false]
          have hno : ¬ ∃ v' ∈ Zhas, topOf v' = a ∧ x v' = true ∧ ∃ u ∈ L v', x u = true := by
            rintro ⟨v', hv', heq, _⟩; exact h ⟨v', hv', heq⟩
          rw [or_iff_left hno, hv]
          simp only [Finset.mem_singleton, exists_eq_left]
          exact and_comm
  have hall_ok : ∀ it ∈ allItems,
      (∀ bw, it.2.1 = some bw → bw < n + gs1.length) ∧ (it.2.1.isSome ∨ it.2.2 ≠ []) := by
    intro it hit
    simp only [allItems, topItems, newItems, List.mem_append, List.mem_map, Finset.mem_toList] at hit
    rcases hit with ⟨a, ha, rfl⟩ | ⟨v, hv, rfl⟩
    · have h := htopItem_ok a ha
      exact ⟨h.1, Or.inl h.2.1⟩
    · refine ⟨fun bw hbw => (by cases hbw), Or.inr ?_⟩
      intro hemp
      simp only [List.map_eq_nil_iff] at hemp
      obtain ⟨u, hu⟩ := hLne v (Finset.mem_sdiff.mp hv).1
      have : u ∈ (L v).toList := Finset.mem_toList.mpr hu
      rw [hemp] at this; cases this
  obtain ⟨⟨ex2, hex2⟩, hlen2, hwlen2, hAO2, hlt2, hval2⟩ := addStars_spec hAO1 allItems hall_ok
  set gs2 := (addStars n gs1 allItems).1
  set topWires := (addStars n gs1 allItems).2
  have hall_ne : allItems ≠ [] := by
    intro hemp
    have hSemp : S_tops = ∅ := by
      have h1 : topItems = [] := (List.append_eq_nil_iff.mp hemp).1
      simp only [topItems, List.map_eq_nil_iff] at h1
      ext a; simp only [Finset.notMem_empty, iff_false]
      intro ha; have := Finset.mem_toList.mpr ha; rw [h1] at this; cases this
    have hNemp : Zact \ Zhas = ∅ := by
      have h2 : newItems = [] := (List.append_eq_nil_iff.mp hemp).2
      simp only [newItems, List.map_eq_nil_iff] at h2
      ext v; simp only [Finset.notMem_empty, iff_false]
      intro hv; have := Finset.mem_toList.mpr hv; rw [h2] at this; cases this
    have hZhas_emp : Zhas = ∅ := by
      ext v; simp only [Finset.notMem_empty, iff_false]
      intro hv; have := htop_mem v hv; rw [hSemp] at this; exact Finset.notMem_empty _ this
    have hZact_emp : Zact = ∅ := by
      rw [hZhas_emp, Finset.sdiff_empty] at hNemp; exact hNemp
    obtain ⟨u, v, huv⟩ := hne
    have he_mem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    have hst_emp : starEdges G C = ∅ := by
      ext e; simp only [Finset.notMem_empty, iff_false, starEdges, Finset.mem_biUnion,
        Finset.mem_image, Finset.mem_product]
      rintro ⟨a, ha, ⟨p, ⟨hp0, hp1⟩, _⟩⟩
      have haS : a ∈ S_tops := by
        rw [Finset.mem_sdiff]; refine ⟨ha, fun hc => ?_⟩
        rw [centreless, Finset.mem_filter] at hc
        rcases hc.2 with h0 | h1
        · rw [h0] at hp0; exact Finset.notMem_empty _ hp0
        · rw [h1] at hp1; exact Finset.notMem_empty _ hp1
      rw [hSemp] at haS; exact Finset.notMem_empty _ haS
    have hu_mem : s(u, v) ∈ Ustar G C := by unfold Ustar; rw [hst_emp, Finset.sdiff_empty]; exact he_mem
    obtain ⟨w, hw, _⟩ := hUcov _ hu_mem
    rw [hZact_emp] at hw; exact Finset.notMem_empty _ hw
  have htw_ne : topWires ≠ [] := by
    intro h; rw [h] at hwlen2; exact hall_ne (List.eq_nil_of_length_eq_zero hwlen2.symm)
  obtain ⟨hAO3, hlt3⟩ := appendOrList_isAO2 hAO2 topWires htw_ne hlt2
  let C' : Circuit := ⟨(appendOrList n gs2 topWires).1, (appendOrList n gs2 topWires).2⟩
  have hAO' : IsAO2 n C' := hAO3
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval ⟨(appendOrList n gs2 topWires).1, 0⟩ x (appendOrList n gs2 topWires).2 = graphFun G ∅ x
    rw [appendOrList_wval hAO2 x topWires htw_ne hlt2]
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, hval2 x, graphFun_iff]
    constructor
    · rintro ⟨it, hit, hxv, hbody⟩
      simp only [allItems, topItems, newItems, List.mem_append, List.mem_map, Finset.mem_toList] at hit
      rcases hit with ⟨a, ha, rfl⟩ | ⟨v, hv, rfl⟩
      · have hiff := (htopItem_ok a ha).2.2 x
        rcases hiff.mp ⟨hxv, hbody⟩ with ⟨⟨u0, hu0, hxu0⟩, ⟨u1, hu1, hxu1⟩⟩ | ⟨v, hv, _, hxv', u, hu, hxu⟩
        · exact ⟨u0, u1, top_sides_adj hL.1 (Finset.mem_sdiff.mp ha).1 hu0 hu1, hxu0, hxu1⟩
        · exact ⟨v, u, hLadj v (hZsub hv) u hu, hxv', hxu⟩
      · rcases hbody with ⟨bw, hbw, _⟩ | ⟨u, hu, hxu⟩
        · cases hbw
        · rw [Finset.mem_toList] at hu
          exact ⟨v, u, hLadj v (Finset.mem_sdiff.mp hv).1 u hu, hxv, hxu⟩
    · rintro ⟨u, v, huv, hxu, hxv⟩
      have he : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
      by_cases hst : s(u, v) ∈ starEdges G C
      · simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at hst
        rcases hst with ⟨a, ha, ⟨p0, p1⟩, ⟨hp0, hp1⟩, hpeq⟩
        have haS : a ∈ S_tops := by
          rw [Finset.mem_sdiff]; refine ⟨ha, fun hc => ?_⟩
          rw [centreless, Finset.mem_filter] at hc
          rcases hc.2 with h0 | h1
          · rw [h0] at hp0; exact Finset.notMem_empty _ hp0
          · rw [h1] at hp1; exact Finset.notMem_empty _ hp1
        refine ⟨mkTopItem a, ?_, ?_⟩
        · simp only [allItems, topItems, List.mem_append, List.mem_map, Finset.mem_toList]
          exact Or.inl ⟨a, haS, rfl⟩
        · apply ((htopItem_ok a haS).2.2 x).mpr
          left
          rw [Sym2.eq_iff] at hpeq
          rcases hpeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨⟨p0, hp0, hxu⟩, ⟨p1, hp1, hxv⟩⟩
          · exact ⟨⟨p0, hp0, hxv⟩, ⟨p1, hp1, hxu⟩⟩
      · have hu_mem : s(u, v) ∈ Ustar G C := Finset.mem_sdiff.mpr ⟨he, hst⟩
        obtain ⟨w, hw, z, hz, heq⟩ := hUcov _ hu_mem
        rw [Sym2.eq_iff] at heq
        have hxw : x w = true := by rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        have hxz : x z = true := by rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
        by_cases hwh : w ∈ Zhas
        · refine ⟨mkTopItem (topOf w), ?_, ?_⟩
          · simp only [allItems, topItems, List.mem_append, List.mem_map, Finset.mem_toList]
            exact Or.inl ⟨topOf w, htop_mem w hwh, rfl⟩
          · apply ((htopItem_ok (topOf w) (htop_mem w hwh)).2.2 x).mpr
            right
            exact ⟨w, hwh, rfl, hxw, z, hz, hxz⟩
        · refine ⟨(w, none, (L w).toList), ?_, hxw, Or.inr ⟨z, Finset.mem_toList.mpr hz, hxz⟩⟩
          simp only [allItems, newItems, List.mem_append, List.mem_map, Finset.mem_toList]
          exact Or.inr ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwh⟩, rfl⟩
  -- Now compute C'.size and compare with C.size!
  have hsum_top : (topItems.map fun it => it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum =
      (∑ v ∈ Zhas, (L v).card) + S_tops.card := by
    have hmap : (topItems.map fun it => it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum =
        ∑ a ∈ S_tops, ((mkTopItem a).2.2.length + 1) := by
      simp only [topItems, List.map_map]
      rw [← Finset.sum_map_toList]
      congr 1
      apply List.map_congr_left
      intro a ha
      rw [Finset.mem_toList] at ha
      simp only [Function.comp_apply, (htopItem_ok a ha).2.1, ↓reduceIte]
    rw [hmap, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
    have hsum_L : ∑ a ∈ S_tops, (mkTopItem a).2.2.length =
        ∑ a ∈ S_tops, if h : ∃ v ∈ Zhas, topOf v = a then (L (Classical.choose h)).card else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : ∃ v ∈ Zhas, topOf v = a
      · simp only [mkTopItem, dif_pos h, Finset.length_toList]
      · simp only [mkTopItem, dif_neg h, dif_pos ha]
        split_ifs <;> rfl
    rw [hsum_L]
    have himg_sub : Zhas.image topOf ⊆ S_tops := by
      intro a ha; simp only [Finset.mem_image] at ha; rcases ha with ⟨v, hv, rfl⟩; exact htop_mem v hv
    rw [← Finset.sum_subset himg_sub]
    · rw [Finset.sum_image (fun v1 hv1 v2 hv2 heq => htop_inj v1 hv1 v2 hv2 heq)]
      apply Finset.sum_congr rfl
      intro v hv
      have hex : ∃ v' ∈ Zhas, topOf v' = topOf v := ⟨v, hv, rfl⟩
      rw [dif_pos hex]
      have hch := Classical.choose_spec hex
      rw [htop_inj _ hch.1 v hv hch.2]
    · intro a _ hnot
      rw [dif_neg]
      rintro ⟨v, hv, rfl⟩
      exact hnot (Finset.mem_image_of_mem topOf hv)
  have hsum_new : (newItems.map fun it => it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum =
      ∑ v ∈ Zact \ Zhas, (L v).card := by
    simp only [newItems, List.map_map]
    rw [← Finset.sum_map_toList]
    congr 1
    apply List.map_congr_left
    intro v _
    simp [Finset.length_toList]
  have hsum_all : (allItems.map fun it => it.2.2.length + (if it.2.1.isSome then 1 else 0)).sum =
      (∑ v ∈ Zact, (L v).card) + S_tops.card := by
    simp only [allItems, List.map_append, List.sum_append, hsum_top, hsum_new]
    have hsplit : ∑ v ∈ Zact, (L v).card = (∑ v ∈ Zhas, (L v).card) + (∑ v ∈ Zact \ Zhas, (L v).card) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hZsub]
    omega
  have hlen_all : allItems.length = S_tops.card + (Zact \ Zhas).card := by
    simp [allItems, topItems, newItems]
  have hC'_size : C'.size =
      (lam G C).card + (∑ v ∈ Zact, (L v).card) + 2 * S_tops.card + (Zact \ Zhas).card - 1 := by
    change (appendOrList n gs2 topWires).1.length = _
    rw [appendOrList_len n gs2 topWires htw_ne, hwlen2, hlen_all, hlen2, hgs1_len, hsum_all]
    have hpos : 0 < S_tops.card + (Zact \ Zhas).card := by
      rw [← hlen_all]; exact List.length_pos_of_ne_nil hall_ne
    omega
  have hsz_le : C.size ≤ C'.size := hL.2.2 C' hAO' hfun'
  have hpart := circuit_size_partition hL
  have horT := tops_le_orT_add_one hL hLift hne
  have hjunk_card : (junk G C).card = 2 := by
    have : junk G C = {g1, g2} := by ext k; simp [hjunk]
    rw [this, Finset.card_pair hg12]
  have hcent_sub : centreless G C ⊆ tops G C := Finset.filter_subset _ _
  have htops_split : (tops G C).card = S_tops.card + (centreless G C).card := by
    rw [card_sdiff_eq hcent_sub]; have := Finset.card_le_card hcent_sub; omega
  have hlam_sub : lam G C ⊆ orN G C := Finset.filter_subset _ _
  have horN_split : (orN G C).card = (lam G C).card + (orN G C \ lam G C).card := by
    rw [card_sdiff_eq hlam_sub]; have := Finset.card_le_card hlam_sub; omega
  omega

lemma top_opnd_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) :
    ∀ k, opnd C a b = n + k → ¬ BelowF G C k := by
  have ha' := mem_tops_iff.mp ha
  intro k hk hbk
  exact least_no_belowF_and_opnd hL hne ha'.1 ha'.2.1 b (by rw [hk]; exact hbk)

lemma mixing_of_reaches_and_nonempty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
    (hne : ∃ u v : Fin n, G.Adj u v)
    {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
    {g : ℕ} (hg : g = g1 ∨ g = g2) :
    ∀ w < n + C.gates.length, (∀ k, w = n + k → ¬ BelowF G C k) →
      (orIn n C w).Nonempty → OrReaches n C w g →
      ∃ m ∈ orN G C \ lam G C,
        OrReaches n C w m ∧ OrReaches n C (n + m) g ∧
        (orIn n C (n + m)).Nonempty ∧ orIn n C (n + m) ⊆ orIn n C w ∧
        (orIn n C (opnd C m 0) = ∅ ∨ orIn n C (opnd C m 1) = ∅) := by
  have hgj := mem_junk_iff.mp ((hjunk g).mpr hg)
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw_lt hnb hne_w hrg
    by_cases hwn : w < n
    · exact absurd hrg (orReaches_input_false hwn)
    · have hk_lt : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      set k := w - n
      have hnbk : ¬ BelowF G C k := hnb k hw_eq
      have hork : (gateAt C k).op = GateOp.or := by
        rcases hL.1.1 _ (gateAt_mem hk_lt) with hand | hor
        · exfalso; have hemp := orIn_and_eq_empty (n := n) hk_lt hand
          rw [← hw_eq] at hemp; exact hne_w.ne_empty hemp
        · exact hor
      have hk_orN : k ∈ orN G C := mem_orN_iff.mpr ⟨hk_lt, hork, hnbk⟩
      by_cases hemp : orIn n C (opnd C k 0) = ∅ ∨ orIn n C (opnd C k 1) = ∅
      · refine ⟨k, Finset.mem_sdiff.mpr ⟨hk_orN, fun hkl => ?_⟩,
          by rw [hw_eq]; exact orReaches_self hk_lt, by rwa [← hw_eq],
          by rwa [← hw_eq], by rw [← hw_eq], hemp⟩
        have hf := Finset.mem_filter.mp hkl
        rcases hemp with h0 | h1
        · exact hf.2.1.ne_empty h0
        · exact hf.2.2.1.ne_empty h1
      · push Not at hemp
        have h0ne : (orIn n C (opnd C k 0)).Nonempty := hemp.1
        have h1ne : (orIn n C (opnd C k 1)).Nonempty := hemp.2
        rw [hw_eq, orReaches_gate_iff hk_lt] at hrg
        have hkng : k ≠ g := fun h => by rw [h, hgj.2.1] at hork; cases hork
        rcases hrg with rfl | ⟨_, u, hu, hnu, hult, hrug⟩
        · exact absurd rfl hkng
        · rw [gate_inputs_eq hL.1 hk_lt] at hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          have hnbu : ∀ b : Fin 2, ∀ m, opnd C k b = n + m → ¬ BelowF G C m := fun b m hm hbm =>
            lift_no_belowF_orN_opnd hL hLift hne hk_lt hork hnbk b (by rw [hm]; exact hbm)
          have hsub_orIn : ∀ b : Fin 2, orIn n C (opnd C k b) ⊆ orIn n C w := by
            intro b; rw [hw_eq, orIn_or_eq_union hL.1 hk_lt hork]
            fin_cases b
            · exact Finset.subset_union_left
            · exact Finset.subset_union_right
          rcases hu with rfl | rfl
          · obtain ⟨m, hm, hwm, hmg, hmne, hmsub, hme⟩ :=
              ih (opnd C k 0) (by omega) (by omega) (hnbu 0) h0ne hrug
            refine ⟨m, hm, ?_, hmg, hmne, Finset.Subset.trans hmsub (hsub_orIn 0), hme⟩
            rw [hw_eq, orReaches_gate_iff hk_lt]
            exact Or.inr ⟨hork, opnd C k 0, opnd_mem hL.1 hk_lt 0, hwm.1, opnd_lt hL.1 hk_lt 0, hwm⟩
          · obtain ⟨m, hm, hwm, hmg, hmne, hmsub, hme⟩ :=
              ih (opnd C k 1) (by omega) (by omega) (hnbu 1) h1ne hrug
            refine ⟨m, hm, ?_, hmg, hmne, Finset.Subset.trans hmsub (hsub_orIn 1), hme⟩
            rw [hw_eq, orReaches_gate_iff hk_lt]
            exact Or.inr ⟨hork, opnd C k 1, opnd_mem hL.1 hk_lt 1, hwm.1, opnd_lt hL.1 hk_lt 1, hwm⟩

lemma exists_mixing_gt_g2 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {g1 g2 : ℕ} (hlt12 : g1 < g2) (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
    (hcent_emp : centreless G C = ∅) :
    ∃ m ∈ orN G C \ lam G C, g2 < m := by
  have hg2j := mem_junk_iff.mp ((hjunk g2).mpr (Or.inr rfl))
  have hout := output_bounds hL hne
  have hout_mem := output_gate_mem_tops_or_orT hL hne
  have hout_bf : BelowF G C (C.output - n) := by
    rcases Finset.mem_union.mp hout_mem with h | h
    · exact (mem_tops_iff.mp h).2.2
    · exact (mem_orT_iff.mp h).2.2
  -- First: any ¬BelowF gate k with InCone g2 k satisfies OrReaches (n + k) g2!
  have hcone_to_or : ∀ k < C.gates.length, ¬ BelowF G C k → InCone n C g2 k →
      OrReaches n C (n + k) g2 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk hnb hin
      have hgt : g2 < k := inCone_lt hin
      have hork : (gateAt C k).op = GateOp.or := by
        rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
        · exfalso
          have hkj := (hjunk k).mp (mem_junk_iff.mpr ⟨hk, hand, hnb⟩)
          rcases hkj with rfl | rfl <;> omega
        · exact hor
      rw [inCone_iff hk] at hin
      rcases hin with ⟨w, hw, hnw, hwnk, heq | hsub⟩
      · rw [orReaches_gate_iff hk]
        refine Or.inr ⟨hork, w, hw, hnw, hwnk, ?_⟩
        rw [show w = n + g2 by omega]; exact orReaches_self hg2j.1
      · have hnbw : ¬ BelowF G C (w - n) := by
          intro hbw
          rw [gate_inputs_eq hL.1 hk] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact lift_no_belowF_orN_opnd hL hLift hne hk hork hnb 0
              (by rw [show opnd C k 0 = n + (opnd C k 0 - n) by omega]; exact hbw)
          · exact lift_no_belowF_orN_opnd hL hLift hne hk hork hnb 1
              (by rw [show opnd C k 1 = n + (opnd C k 1 - n) by omega]; exact hbw)
        have hsub_or := ih (w - n) (by omega) (by omega) hnbw hsub
        rw [orReaches_gate_iff hk]
        exact Or.inr ⟨hork, w, hw, hnw, hwnk, by rwa [show n + (w - n) = w by omega] at hsub_or⟩
  -- Next: find a ∈ tops reading g2 through ORs
  have hex_top : ∀ j < C.gates.length, BelowF G C j → InCone n C g2 j →
      ∃ a ∈ tops G C, ∃ b : Fin 2, OrReaches n C (opnd C a b) g2 := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj hbf hin
      rcases hL.1.1 _ (gateAt_mem hj) with hand | hor
      · have hjtop : j ∈ tops G C := mem_tops_iff.mpr ⟨hj, hand, hbf⟩
        rw [inCone_iff hj] at hin
        rcases hin with ⟨w, hw, hnw, hwnj, heq | hsub⟩
        · rw [gate_inputs_eq hL.1 hj] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          have hrg : OrReaches n C w g2 := by rw [show w = n + g2 by omega]; exact orReaches_self hg2j.1
          rcases hw with rfl | rfl
          · exact ⟨j, hjtop, 0, hrg⟩
          · exact ⟨j, hjtop, 1, hrg⟩
        · rw [gate_inputs_eq hL.1 hj] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · have hnbw := top_opnd_not_belowF hL hne hjtop 0 (opnd C j 0 - n) (by omega)
            have hr := hcone_to_or (opnd C j 0 - n) (by omega) hnbw hsub
            exact ⟨j, hjtop, 0, by rwa [show n + (opnd C j 0 - n) = opnd C j 0 by omega] at hr⟩
          · have hnbw := top_opnd_not_belowF hL hne hjtop 1 (opnd C j 1 - n) (by omega)
            have hr := hcone_to_or (opnd C j 1 - n) (by omega) hnbw hsub
            exact ⟨j, hjtop, 1, by rwa [show n + (opnd C j 1 - n) = opnd C j 1 by omega] at hr⟩
      · rw [inCone_iff hj] at hin
        rcases hin with ⟨w, hw, hnw, hwnj, heq | hsub⟩
        · exfalso
          rw [gate_inputs_eq hL.1 hj] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          have hbfg : BelowF G C g2 := by
            rcases hw with rfl | rfl
            · have h0 := (orT_opnds_belowF hL hj hor hbf 0).2.2; rwa [← heq] at h0
            · have h1 := (orT_opnds_belowF hL hj hor hbf 1).2.2; rwa [← heq] at h1
          exact hg2j.2.2 hbfg
        · rw [gate_inputs_eq hL.1 hj] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · have h0 := orT_opnds_belowF hL hj hor hbf 0
            exact ih (opnd C j 0 - n) (by omega) h0.2.1 h0.2.2 hsub
          · have h1 := orT_opnds_belowF hL hj hor hbf 1
            exact ih (opnd C j 1 - n) (by omega) h1.2.1 h1.2.2 hsub
  have hg2_cone : InCone n C g2 (C.output - n) := by
    have hc := (least_inOutputCone hL hne g2 hg2j.1).2
    rcases hc with heq | ⟨_, hin⟩
    · exfalso; apply hg2j.2.2; rw [show g2 = C.output - n by omega]; exact hout_bf
    · exact hin
  obtain ⟨a, ha, b, hrb⟩ := hex_top (C.output - n) (by omega) hout_bf hg2_cone
  have ha' := mem_tops_iff.mp ha
  have hneb : (side (n := n) C a b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hac : a ∈ centreless G C := by
      unfold centreless; rw [Finset.mem_filter]
      refine ⟨ha, ?_⟩; fin_cases b
      · exact Or.inl hemp
      · exact Or.inr hemp
    rw [hcent_emp] at hac; exact Finset.notMem_empty _ hac
  obtain ⟨m, hm, _, hmg2, _, _, _⟩ := mixing_of_reaches_and_nonempty hL hLift hne hjunk (Or.inr rfl)
    (opnd C a b) (by have := opnd_lt hL.1 ha'.1 b; omega) (top_opnd_not_belowF hL hne ha b) hneb hrb
  have hle : g2 ≤ m := by have := orReaches_le hmg2; omega
  have hne_g2 : m ≠ g2 := by
    intro h; subst h
    have h1 := (mem_orN_iff.mp (Finset.mem_sdiff.mp hm).1).2.1
    rw [h1] at hg2j; cases hg2j.2.1
  exact ⟨m, hm, by omega⟩

lemma exists_mixing_raw {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {g1 g2 : ℕ} (hlt12 : g1 < g2) (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
    (hcent_emp : centreless G C = ∅) :
    ∃ m ∈ orN G C \ lam G C, g2 < m ∧ (orIn n C (n+m)).Nonempty ∧
      (orIn n C (opnd C m 0)=∅ ∨ orIn n C (opnd C m 1)=∅) := by
  have hg2j := mem_junk_iff.mp ((hjunk g2).mpr (Or.inr rfl))
  have hout := output_bounds hL hne
  have hout_mem := output_gate_mem_tops_or_orT hL hne
  have hout_bf : BelowF G C (C.output - n) := by
    rcases Finset.mem_union.mp hout_mem with h | h
    · exact (mem_tops_iff.mp h).2.2
    · exact (mem_orT_iff.mp h).2.2
  -- First: any ¬BelowF gate k with InCone g2 k satisfies OrReaches (n + k) g2!
  have hcone_to_or : ∀ k < C.gates.length, ¬ BelowF G C k → InCone n C g2 k →
      OrReaches n C (n + k) g2 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk hnb hin
      have hgt : g2 < k := inCone_lt hin
      have hork : (gateAt C k).op = GateOp.or := by
        rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
        · exfalso
          have hkj := (hjunk k).mp (mem_junk_iff.mpr ⟨hk, hand, hnb⟩)
          rcases hkj with rfl | rfl <;> omega
        · exact hor
      rw [inCone_iff hk] at hin
      rcases hin with ⟨w, hw, hnw, hwnk, heq | hsub⟩
      · rw [orReaches_gate_iff hk]
        refine Or.inr ⟨hork, w, hw, hnw, hwnk, ?_⟩
        rw [show w = n + g2 by omega]; exact orReaches_self hg2j.1
      · have hnbw : ¬ BelowF G C (w - n) := by
          intro hbw
          rw [gate_inputs_eq hL.1 hk] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact lift_no_belowF_orN_opnd hL hLift hne hk hork hnb 0
              (by rw [show opnd C k 0 = n + (opnd C k 0 - n) by omega]; exact hbw)
          · exact lift_no_belowF_orN_opnd hL hLift hne hk hork hnb 1
              (by rw [show opnd C k 1 = n + (opnd C k 1 - n) by omega]; exact hbw)
        have hsub_or := ih (w - n) (by omega) (by omega) hnbw hsub
        rw [orReaches_gate_iff hk]
        exact Or.inr ⟨hork, w, hw, hnw, hwnk, by rwa [show n + (w - n) = w by omega] at hsub_or⟩
  -- Next: find a ∈ tops reading g2 through ORs
  have hex_top : ∀ j < C.gates.length, BelowF G C j → InCone n C g2 j →
      ∃ a ∈ tops G C, ∃ b : Fin 2, OrReaches n C (opnd C a b) g2 := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj hbf hin
      rcases hL.1.1 _ (gateAt_mem hj) with hand | hor
      · have hjtop : j ∈ tops G C := mem_tops_iff.mpr ⟨hj, hand, hbf⟩
        rw [inCone_iff hj] at hin
        rcases hin with ⟨w, hw, hnw, hwnj, heq | hsub⟩
        · rw [gate_inputs_eq hL.1 hj] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          have hrg : OrReaches n C w g2 := by rw [show w = n + g2 by omega]; exact orReaches_self hg2j.1
          rcases hw with rfl | rfl
          · exact ⟨j, hjtop, 0, hrg⟩
          · exact ⟨j, hjtop, 1, hrg⟩
        · rw [gate_inputs_eq hL.1 hj] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · have hnbw := top_opnd_not_belowF hL hne hjtop 0 (opnd C j 0 - n) (by omega)
            have hr := hcone_to_or (opnd C j 0 - n) (by omega) hnbw hsub
            exact ⟨j, hjtop, 0, by rwa [show n + (opnd C j 0 - n) = opnd C j 0 by omega] at hr⟩
          · have hnbw := top_opnd_not_belowF hL hne hjtop 1 (opnd C j 1 - n) (by omega)
            have hr := hcone_to_or (opnd C j 1 - n) (by omega) hnbw hsub
            exact ⟨j, hjtop, 1, by rwa [show n + (opnd C j 1 - n) = opnd C j 1 by omega] at hr⟩
      · rw [inCone_iff hj] at hin
        rcases hin with ⟨w, hw, hnw, hwnj, heq | hsub⟩
        · exfalso
          rw [gate_inputs_eq hL.1 hj] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          have hbfg : BelowF G C g2 := by
            rcases hw with rfl | rfl
            · have h0 := (orT_opnds_belowF hL hj hor hbf 0).2.2; rwa [← heq] at h0
            · have h1 := (orT_opnds_belowF hL hj hor hbf 1).2.2; rwa [← heq] at h1
          exact hg2j.2.2 hbfg
        · rw [gate_inputs_eq hL.1 hj] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · have h0 := orT_opnds_belowF hL hj hor hbf 0
            exact ih (opnd C j 0 - n) (by omega) h0.2.1 h0.2.2 hsub
          · have h1 := orT_opnds_belowF hL hj hor hbf 1
            exact ih (opnd C j 1 - n) (by omega) h1.2.1 h1.2.2 hsub
  have hg2_cone : InCone n C g2 (C.output - n) := by
    have hc := (least_inOutputCone hL hne g2 hg2j.1).2
    rcases hc with heq | ⟨_, hin⟩
    · exfalso; apply hg2j.2.2; rw [show g2 = C.output - n by omega]; exact hout_bf
    · exact hin
  obtain ⟨a, ha, b, hrb⟩ := hex_top (C.output - n) (by omega) hout_bf hg2_cone
  have ha' := mem_tops_iff.mp ha
  have hneb : (side (n := n) C a b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hac : a ∈ centreless G C := by
      unfold centreless; rw [Finset.mem_filter]
      refine ⟨ha, ?_⟩; fin_cases b
      · exact Or.inl hemp
      · exact Or.inr hemp
    rw [hcent_emp] at hac; exact Finset.notMem_empty _ hac
  obtain ⟨m, hm, _, hmg2, hmne, _, hme⟩ := mixing_of_reaches_and_nonempty hL hLift hne hjunk (Or.inr rfl)
    (opnd C a b) (by have := opnd_lt hL.1 ha'.1 b; omega) (top_opnd_not_belowF hL hne ha b) hneb hrb
  have hle : g2 ≤ m := by have := orReaches_le hmg2; omega
  have hne_g2 : m ≠ g2 := by
    intro h; subst h
    have h1 := (mem_orN_iff.mp (Finset.mem_sdiff.mp hm).1).2.1
    rw [h1] at hg2j; cases hg2j.2.1
  exact ⟨m, hm, by omega, hmne, hme⟩


lemma junk_reader_extra {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    (hcent : centreless G C = ∅) {g : ℕ} (hg : g ∈ junk G C)
    (hind : ∀ k ∈ junk G C, ¬ InCone n C g k) :
    ∃ r ∈ orN G C \ lam G C, n+g ∈ (gateAt C r).inputs ∧
      (orIn n C (opnd C r 0) = ∅ ∨ orIn n C (opnd C r 1) = ∅) := by
  have hgj := mem_junk_iff.mp hg
  have hout := output_bounds hL hne
  have houtput : BelowF G C (C.output-n) := by
    intro x hx
    rw [gateVal_eq_wval,show n+(C.output-n)=C.output by omega] at hx
    rw [← congrFun hL.2.1 x]
    exact hx
  have hcone : InCone n C g (C.output-n) := by
    rcases (least_inOutputCone hL hne g hgj.1).2 with heq | ⟨_,hh⟩
    · have he : g=C.output-n := by omega
      exact (hgj.2.2 (he ▸ houtput)).elim
    · exact hh
  obtain ⟨r,hr,hread⟩ := exists_reader_of_inCone hcone
  have hread' := hread
  rw [gate_inputs_eq hL.1 hr] at hread'
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hread'
  obtain ⟨b,hb⟩ : ∃ b : Fin 2, opnd C r b = n+g := by
    rcases hread' with h0 | h1
    · exact ⟨0,h0.symm⟩
    · exact ⟨1,h1.symm⟩
  have hemp : orIn n C (opnd C r b)=∅ := by
    rw [hb]
    exact orIn_and_eq_empty hgj.1 hgj.2.1
  have hor : (gateAt C r).op = GateOp.or := by
    rcases hL.1.1 _ (gateAt_mem hr) with hand | hor
    swap
    · exact hor
    by_cases hbf : BelowF G C r
    · have htop : r ∈ tops G C := mem_tops_iff.mpr ⟨hr,hand,hbf⟩
      have hc : r ∈ centreless G C := by
        refine Finset.mem_filter.mpr ⟨htop,?_⟩
        fin_cases b
        · exact Or.inl hemp
        · exact Or.inr hemp
      rw [hcent] at hc
      exact (Finset.notMem_empty r hc).elim
    · have hjr : r ∈ junk G C := mem_junk_iff.mpr ⟨hr,hand,hbf⟩
      have hgr : InCone n C g r := by
        rw [inCone_iff hr]
        exact ⟨n+g,hread,by omega,hL.1.2.1 r hr (n+g) hread,Or.inl (by omega)⟩
      exact (hind r hjr hgr).elim
  have hnb : ¬ BelowF G C r := by
    intro hbf
    have hh := (orT_opnds_belowF hL hr hor hbf b).2.2
    rw [hb,Nat.add_sub_cancel_left] at hh
    exact hgj.2.2 hh
  have hempty : orIn n C (opnd C r 0)=∅ ∨ orIn n C (opnd C r 1)=∅ := by
    fin_cases b
    · exact Or.inl hemp
    · exact Or.inr hemp
  refine ⟨r,Finset.mem_sdiff.mpr ⟨mem_orN_iff.mpr ⟨hr,hor,hnb⟩,?_⟩,hread,hempty⟩
  intro hlam
  have hh := (Finset.mem_filter.mp hlam).2
  rcases hempty with h0 | h1
  · exact hh.1.ne_empty h0
  · exact hh.2.1.ne_empty h1

lemma two_junk_shared_reader_empty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {g h r : ℕ} (hg : g ∈ junk G C) (hh : h ∈ junk G C)
    (hgh : g ≠ h) (hr : r < C.gates.length) (hor : (gateAt C r).op = GateOp.or)
    (hreadg : n+g ∈ (gateAt C r).inputs) (hreadh : n+h ∈ (gateAt C r).inputs) :
    orIn n C (n+r)=∅ := by
  have hgj := mem_junk_iff.mp hg
  have hhj := mem_junk_iff.mp hh
  rw [gate_inputs_eq hL.1 hr] at hreadg hreadh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hreadg hreadh
  rcases hreadg with h0 | h1 <;> rcases hreadh with h0' | h1'
  · exact (hgh (by omega)).elim
  · rw [orIn_or_eq_union hL.1 hr hor,← h0,← h1',orIn_and_eq_empty hgj.1 hgj.2.1,
      orIn_and_eq_empty hhj.1 hhj.2.1,Finset.empty_union]
  · rw [orIn_or_eq_union hL.1 hr hor,← h0',← h1,orIn_and_eq_empty hhj.1 hhj.2.1,
      orIn_and_eq_empty hgj.1 hgj.2.1,Finset.empty_union]
  · exact (hgh (by omega)).elim

lemma independent_junk_two_nonsplit {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
    (hne : ∃ u v : Fin n, G.Adj u v) {g h : ℕ} (hgh : g<h)
    (hjunk : ∀ k, k ∈ junk G C ↔ k=g ∨ k=h)
    (hcent : centreless G C = ∅) (hind : ¬ InCone n C g h) :
    ∃ r ∈ orN G C \ lam G C, ∃ t ∈ orN G C \ lam G C, r ≠ t ∧
      (orIn n C (opnd C r 0)=∅ ∨ orIn n C (opnd C r 1)=∅) ∧
      (orIn n C (opnd C t 0)=∅ ∨ orIn n C (opnd C t 1)=∅) := by
  have hg : g ∈ junk G C := (hjunk g).mpr (Or.inl rfl)
  have hh : h ∈ junk G C := (hjunk h).mpr (Or.inr rfl)
  have hindg : ∀ k ∈ junk G C, ¬ InCone n C g k := by
    intro k hk hcone
    rcases (hjunk k).mp hk with rfl | rfl
    · have := inCone_lt hcone; omega
    · exact hind hcone
  have hindh : ∀ k ∈ junk G C, ¬ InCone n C h k := by
    intro k hk hcone
    have hlt := inCone_lt hcone
    rcases (hjunk k).mp hk with rfl | rfl <;> omega
  obtain ⟨r,hr,hgr,her⟩ := junk_reader_extra hL hne hcent hg hindg
  obtain ⟨t,ht,hht,het⟩ := junk_reader_extra hL hne hcent hh hindh
  by_cases hrt : r=t
  · subst t
    have hrj := mem_orN_iff.mp (Finset.mem_sdiff.mp hr).1
    have hrempty := two_junk_shared_reader_empty hL hg hh (Nat.ne_of_lt hgh) hrj.1 hrj.2.1 hgr hht
    obtain ⟨m,hm,_,hmne,hme⟩ := exists_mixing_raw hL hLift hne hgh hjunk hcent
    refine ⟨r,hr,m,hm,?_,her,hme⟩
    intro hrm
    exact hmne.ne_empty (hrm ▸ hrempty)
  · exact ⟨r,hr,t,ht,hrt,her,het⟩

lemma independent_nonsplit_count {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
    (hne : ∃ u v : Fin n, G.Adj u v) {g h : ℕ} (hgh : g<h)
    (hjunk : ∀ k, k ∈ junk G C ↔ k=g ∨ k=h)
    (hcent : centreless G C = ∅) (hind : ¬ InCone n C g h) :
    ((orN G C \ lam G C).filter (fun k => (orIn n C (opnd C k 0)).Nonempty ∧
      (orIn n C (opnd C k 1)).Nonempty)).card+2 ≤ (orN G C \ lam G C).card := by
  classical
  let S := (orN G C \ lam G C).filter (fun k => (orIn n C (opnd C k 0)).Nonempty ∧
    (orIn n C (opnd C k 1)).Nonempty)
  obtain ⟨r,hr,t,ht,hrt,her,het⟩ := independent_junk_two_nonsplit hL hLift hne hgh hjunk hcent hind
  have nr : r ∉ S := by
    intro h
    have hh := (Finset.mem_filter.mp h).2
    rcases her with he | he
    · exact hh.1.ne_empty he
    · exact hh.2.ne_empty he
  have nt : t ∉ S := by
    intro h
    have hh := (Finset.mem_filter.mp h).2
    rcases het with he | he
    · exact hh.1.ne_empty he
    · exact hh.2.ne_empty he
  have nr' : r ∉ insert t S := by simp [hrt,nr]
  have hsub : insert r (insert t S) ⊆ orN G C \ lam G C :=
    Finset.insert_subset hr (Finset.insert_subset ht (Finset.filter_subset _ _))
  have hh := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem nr',Finset.card_insert_of_notMem nt] at hh
  exact hh

lemma independent_cover_budget_exclusion {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
    (hne : ∃ u v : Fin n, G.Adj u v) {g h : ℕ} (hgh : g<h)
    (hjunk : ∀ k, k ∈ junk G C ↔ k=g ∨ k=h) (hind : ¬ InCone n C g h)
    (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (hln : ∀ v ∈ Z, (L v).Nonempty) (hla : ∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u)
    (hcov : ∀ e ∈ Ustar G C, ∃ v ∈ Z, ∃ u ∈ L v, e=s(v,u))
    (hcost : (∑ v ∈ Z, (L v).card)+Z.card ≤
      ((orN G C \ lam G C).filter (fun k => (orIn n C (opnd C k 0)).Nonempty ∧
        (orIn n C (opnd C k 1)).Nonempty)).card+3) : False := by
  classical
  have hbound : 2*(centreless G C).card+(orN G C \ lam G C).card+2 ≤
      (∑ v ∈ Z, (L v).card)+Z.card := by
    simpa only [Finset.sdiff_empty] using
      master_surgery_bound hL hLift h4 (Nat.ne_of_lt hgh) hjunk hne Z ∅ L (fun _ => 0)
        (by simp) hln hla hcov (by simp) (by simp) (by simp)
  have hfilter := Finset.card_filter_le (orN G C \ lam G C)
    (fun k => (orIn n C (opnd C k 0)).Nonempty ∧ (orIn n C (opnd C k 1)).Nonempty)
  by_cases hc : (centreless G C).card=0
  · have hcent := Finset.card_eq_zero.mp hc
    have htwo := independent_nonsplit_count hL hLift hne hgh hjunk hcent hind
    omega
  · omega

lemma orReaches_direct_reader {n : ℕ} {C : Circuit} {g : ℕ} :
    ∀ w, OrReaches n C w g → w ≠ n+g →
      ∃ r < C.gates.length, (gateAt C r).op = GateOp.or ∧
        n+g ∈ (gateAt C r).inputs ∧ OrReaches n C w r := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hne
    have hn := hw.1
    have hk := orReaches_lt_len hw
    let k := w-n
    have he : w=n+k := by dsimp [k]; omega
    rw [he] at hw
    change k < C.gates.length at hk
    rw [orReaches_gate_iff hk] at hw
    rcases hw with hkg | ⟨hor,u,hu,hnu,hult,hug⟩
    · exact (hne (by omega)).elim
    · by_cases hue : u=n+g
      · refine ⟨k,hk,hor,?_,?_⟩
        · exact hue ▸ hu
        · rw [he]; exact orReaches_self hk
      · obtain ⟨r,hr,horr,hread,hreach⟩ := ih u (by omega) hug hue
        refine ⟨r,hr,horr,hread,?_⟩
        rw [he,orReaches_gate_iff hk]
        exact Or.inr ⟨hor,u,hu,hnu,hult,hreach⟩

lemma direct_or_junk_reader_extra {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {g r : ℕ} (hg : g ∈ junk G C)
    (hr : r < C.gates.length) (hor : (gateAt C r).op = GateOp.or)
    (hread : n+g ∈ (gateAt C r).inputs) :
    r ∈ orN G C \ lam G C ∧
      (orIn n C (opnd C r 0)=∅ ∨ orIn n C (opnd C r 1)=∅) := by
  have hgj := mem_junk_iff.mp hg
  rw [gate_inputs_eq hL.1 hr] at hread
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hread
  obtain ⟨b,hb⟩ : ∃ b : Fin 2, opnd C r b=n+g := by
    rcases hread with h0 | h1
    · exact ⟨0,h0.symm⟩
    · exact ⟨1,h1.symm⟩
  have hemp : orIn n C (opnd C r b)=∅ := by
    rw [hb]
    exact orIn_and_eq_empty hgj.1 hgj.2.1
  have hnb : ¬ BelowF G C r := by
    intro hbf
    have hh := (orT_opnds_belowF hL hr hor hbf b).2.2
    rw [hb,Nat.add_sub_cancel_left] at hh
    exact hgj.2.2 hh
  have hempty : orIn n C (opnd C r 0)=∅ ∨ orIn n C (opnd C r 1)=∅ := by
    fin_cases b
    · exact Or.inl hemp
    · exact Or.inr hemp
  refine ⟨Finset.mem_sdiff.mpr ⟨mem_orN_iff.mpr ⟨hr,hor,hnb⟩,?_⟩,hempty⟩
  intro hlam
  have hh := (Finset.mem_filter.mp hlam).2
  rcases hempty with h0 | h1
  · exact hh.1.ne_empty h0
  · exact hh.2.1.ne_empty h1

lemma antichain_unused_nonsplit {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {g h : ℕ} (hgh : g<h) (hjunk : ∀ k, k ∈ junk G C ↔ k=g ∨ k=h)
    (hcent : centreless G C=∅) (A : Finset ℕ)
    (hA : ∀ r ∈ A, (orIn n C (n+r)).Nonempty ∧ OrReaches n C (n+r) g)
    (hanti : ∀ r ∈ A, ∀ q ∈ A, OrReaches n C (n+r) q → r=q) :
    ∃ r ∈ orN G C \ lam G C, r ∉ A ∧
      (orIn n C (opnd C r 0)=∅ ∨ orIn n C (opnd C r 1)=∅) := by
  have hg : g ∈ junk G C := (hjunk g).mpr (Or.inl rfl)
  have hh : h ∈ junk G C := (hjunk h).mpr (Or.inr rfl)
  have hindh : ∀ k ∈ junk G C, ¬ InCone n C h k := by
    intro k hk hcone
    have hlt := inCone_lt hcone
    rcases (hjunk k).mp hk with rfl | rfl <;> omega
  obtain ⟨r,hr,hreadh,her⟩ := junk_reader_extra hL hne hcent hh hindh
  by_cases hrA : r ∈ A
  · have hAr := hA r hrA
    have hne_rg : n+r ≠ n+g := by
      intro he
      have eq : r=g := by omega
      have hor := (mem_orN_iff.mp (Finset.mem_sdiff.mp hr).1).2.1
      rw [eq,(mem_junk_iff.mp hg).2.1] at hor
      contradiction
    obtain ⟨q,hq,hqor,hreadg,hrq⟩ := orReaches_direct_reader (n+r) hAr.2 hne_rg
    have hqextra := direct_or_junk_reader_extra hL hg hq hqor hreadg
    have hqr : q ≠ r := by
      intro eq
      subst q
      have hrempty := two_junk_shared_reader_empty hL hg hh (Nat.ne_of_lt hgh) hq hqor hreadg hreadh
      exact hAr.1.ne_empty hrempty
    refine ⟨q,hqextra.1,?_,hqextra.2⟩
    intro hqA
    exact hqr (hanti r hrA q hqA hrq).symm
  · exact ⟨r,hr,hrA,her⟩

end PEqualNP.Outside.L_meta_5012.Surgery

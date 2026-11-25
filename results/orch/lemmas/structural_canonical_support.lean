import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.StructuralSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma card_sdiff_eq {α : Type} [DecidableEq α] {A B : Finset α} (h : A ⊆ B) :
    (B \ A).card = B.card - A.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]


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

lemma pure_wire_support {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length,
      (∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
        w = n + k ∨ (n ≤ w ∧ InCone n C k (w - n)) → False) →
      ∃ S : Finset (Fin n), S.Nonempty ∧
        ∀ x : Fin n → Bool, wval C x w = decide (∃ u ∈ S, x u = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hno
    by_cases hwn : w < n
    · refine ⟨{⟨w, hwn⟩}, by simp, ?_⟩
      intro x
      rw [wval_input C x w hwn]
      simp
    · have hj : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      have hor : (gateAt C (w - n)).op = GateOp.or := by
        rcases hAO.1 _ (gateAt_mem hj) with hand | hor
        · exact False.elim (hno (w - n) hj hand (Or.inl hw_eq))
        · exact hor
      have child : ∀ b : Fin 2,
          ∃ S : Finset (Fin n), S.Nonempty ∧
            ∀ x : Fin n → Bool, wval C x (opnd C (w - n) b) =
              decide (∃ u ∈ S, x u = true) := by
        intro b
        have hlt : opnd C (w - n) b < w := by
          have := opnd_lt hAO hj b
          omega
        refine ih _ hlt (by omega) ?_
        intro k hk hand hkc
        apply hno k hk hand
        right
        refine ⟨by omega, ?_⟩
        rcases hkc with heq | ⟨hnc, hc⟩
        · apply (inCone_iff hj).mpr
          refine ⟨opnd C (w - n) b, opnd_mem hAO hj b, by omega, opnd_lt hAO hj b, ?_⟩
          left
          omega
        · apply inCone_trans hc
          apply (inCone_iff hj).mpr
          exact ⟨opnd C (w - n) b, opnd_mem hAO hj b, hnc, opnd_lt hAO hj b, Or.inl rfl⟩
      obtain ⟨S, hS, hs⟩ := child 0
      obtain ⟨T, hT, ht⟩ := child 1
      refine ⟨S ∪ T, hS.mono Finset.subset_union_left, ?_⟩
      intro x
      rw [hw_eq, wval_gate_or hAO x hj hor, hs x, ht x]
      simp only [Finset.mem_union, or_and_right, exists_or, Bool.decide_or]

lemma and_of_pure_cone_operands {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hpure : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ InCone n C k j) :
    ∃ A B : Finset (Fin n), A.Nonempty ∧ B.Nonempty ∧
      (∀ x : Fin n → Bool, wval C x (opnd C j 0) = decide (∃ a ∈ A, x a = true)) ∧
      (∀ x : Fin n → Bool, wval C x (opnd C j 1) = decide (∃ b ∈ B, x b = true)) ∧
      ∀ x : Fin n → Bool, gateVal n C j x =
        (decide (∃ a ∈ A, x a = true) && decide (∃ b ∈ B, x b = true)) := by
  have child : ∀ b : Fin 2,
      ∃ S : Finset (Fin n), S.Nonempty ∧
        ∀ x : Fin n → Bool, wval C x (opnd C j b) = decide (∃ u ∈ S, x u = true) := by
    intro b
    apply pure_wire_support hAO (opnd C j b) (by have := opnd_lt hAO hj b; omega)
    intro k hk hop hkc
    apply hpure k hk hop
    rcases hkc with heq | ⟨hnc, hc⟩
    · apply (inCone_iff hj).mpr
      refine ⟨opnd C j b, opnd_mem hAO hj b, by omega, opnd_lt hAO hj b, ?_⟩
      left
      omega
    · apply inCone_trans hc
      apply (inCone_iff hj).mpr
      exact ⟨opnd C j b, opnd_mem hAO hj b, hnc, opnd_lt hAO hj b, Or.inl rfl⟩
  obtain ⟨A, hA, ha⟩ := child 0
  obtain ⟨B, hB, hb⟩ := child 1
  refine ⟨A, B, hA, hB, ha, hb, ?_⟩
  intro x
  rw [gateVal_eq_wval, wval_gate_and hAO x hj hand, ha x, hb x]

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

lemma pure_wire_canonical {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length,
      (∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
        w = n + k ∨ (n ≤ w ∧ InCone n C k (w - n)) → False) →
      ∀ x : Fin n → Bool, wval C x w = decide (∃ u ∈ orIn n C w, x u = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hno x
    by_cases hwn : w < n
    · rw [wval_input C x w hwn]
      have hraw : orIn n C w = {⟨w, hwn⟩} := by
        ext u
        simpa only [Finset.mem_singleton] using (mem_orIn_input C u ⟨w, hwn⟩)
      simp [hraw]
    · have hj : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      have hor : (gateAt C (w - n)).op = GateOp.or := by
        rcases hAO.1 _ (gateAt_mem hj) with hand | hor
        · exact False.elim (hno (w - n) hj hand (Or.inl hw_eq))
        · exact hor
      have child : ∀ b : Fin 2, wval C x (opnd C (w - n) b) =
          decide (∃ u ∈ orIn n C (opnd C (w - n) b), x u = true) := by
        intro b
        have hlt : opnd C (w - n) b < w := by
          have := opnd_lt hAO hj b
          omega
        apply ih _ hlt (by omega) _ x
        intro k hk hop hkc
        apply hno k hk hop
        right
        refine ⟨by omega, ?_⟩
        rcases hkc with heq | ⟨hnc, hc⟩
        · apply (inCone_iff hj).mpr
          refine ⟨opnd C (w - n) b, opnd_mem hAO hj b, by omega, opnd_lt hAO hj b, ?_⟩
          left
          omega
        · apply inCone_trans hc
          apply (inCone_iff hj).mpr
          exact ⟨opnd C (w - n) b, opnd_mem hAO hj b, hnc, opnd_lt hAO hj b, Or.inl rfl⟩
      rw [hw_eq, wval_gate_or hAO x hj hor, child 0, child 1, orIn_or_eq_union hAO hj hor]
      simp only [Finset.mem_union, or_and_right, exists_or, Bool.decide_or]

lemma pure_cone_canonical_operands {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length)
    (hpure : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ InCone n C k j) :
    ∀ b : Fin 2, ∀ x : Fin n → Bool,
      wval C x (opnd C j b) = decide (∃ u ∈ side (n := n) C j b, x u = true) := by
  intro b
  apply pure_wire_canonical hAO (opnd C j b) (by have := opnd_lt hAO hj b; omega)
  intro k hk hop hkc
  apply hpure k hk hop
  rcases hkc with heq | ⟨hnc, hc⟩
  · apply (inCone_iff hj).mpr
    refine ⟨opnd C j b, opnd_mem hAO hj b, by omega, opnd_lt hAO hj b, ?_⟩
    left
    omega
  · apply inCone_trans hc
    apply (inCone_iff hj).mpr
    exact ⟨opnd C j b, opnd_mem hAO hj b, hnc, opnd_lt hAO hj b, Or.inl rfl⟩

lemma pure_cone_canonical_product {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hpure : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ InCone n C k j)
    (x : Fin n → Bool) :
    gateVal n C j x =
      (decide (∃ u ∈ side (n := n) C j 0, x u = true) &&
       decide (∃ v ∈ side (n := n) C j 1, x v = true)) := by
  rw [gateVal_eq_wval, wval_gate_and hAO x hj hand,
    pure_cone_canonical_operands hAO hj hpure 0 x,
    pure_cone_canonical_operands hAO hj hpure 1 x]

end PEqualNP.Outside.L_meta_5012.StructuralSemantics

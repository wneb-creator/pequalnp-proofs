import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_5012_apart_case.Flags
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
  ·rw [wval_input C _ w hwn]
  ·have hj : w - n < C.gates.length := by omega
   have hw_eq : w = n + (w - n) := by omega
   rw [hw_eq]
   have hop := hAO.1 _ (gateAt_mem hj)
   have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hj 0; omega
   have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hj 1; omega
   have hv0 := ih _ h0 (by omega)
   have hv1 := ih _ h1 (by omega)
   rcases hop with hand | hor
   ·rw [wval_gate_and hAO _ hj hand, hv0, hv1]; rfl
   ·rw [wval_gate_or hAO _ hj hor, hv0, hv1]; rfl
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
 ·rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
 ·rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩
lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
 induction j using Nat.strong_induction_on with
 | ind j ih =>
  intro h
  have hj := inCone_lt_len h
  rw [inCone_iff hj] at h
  rcases h with ⟨w, _, hnw, hwnj, rfl | hsub⟩
  ·omega
  ·have := ih (w - n) (by omega) hsub; omega
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
   ·rfl
   ·apply List.flatMap_congr
    intro w hw
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    have hwn : w - n < acc.length := by omega
    have hwn' : w - n < acc'.length := by omega
    rw [foldl_orSets_getD_lt n gs acc' (w - n) hwn']
    simp only [acc', orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
   ·rfl
   ·rfl
   ·rfl
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
 ·rintro ⟨_, hmem⟩
  rw [List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  ·exact Or.inl rfl
  ·cases hop : (gateAt C j).op
   ·rw [hop] at hmem; simp at hmem
   ·rw [hop] at hmem
    rw [List.mem_flatMap] at hmem
    rcases hmem with ⟨w, hw, hwg⟩
    rw [List.mem_filter] at hw
    simp only [decide_eq_true_eq] at hw
    exact Or.inr ⟨rfl, w, hw.1, hw.2.1, hw.2.2, ⟨hw.2.1, hwg⟩⟩
   ·rw [hop] at hmem; simp at hmem
   ·rw [hop] at hmem; simp at hmem
   ·rw [hop] at hmem; simp at hmem
 ·rintro (rfl | ⟨hop, w, hw, hnw, hwnj, hwg⟩)
  ·exact ⟨Nat.le_add_right n _, List.mem_cons_self⟩
  ·refine ⟨Nat.le_add_right n j, List.mem_cons_of_mem j ?_⟩
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
  ·exact le_refl _
  ·have hlt : u - n < k := by omega
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
  ·exact h2
  ·rw [orReaches_gate_iff hwn]
   refine Or.inr ⟨hop, u, hu, hnu, hunk, ?_⟩
   have hu_eq : u = n + (u - n) := by omega
   rw [hu_eq] at huj ⊢
   exact ih (u - n) (by omega) huj (by omega)
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
  ·exact hg
  ·rw [wval_gate_or hAO x hwn hop, Bool.or_eq_true]
   rw [gate_inputs_eq hAO hwn] at hu
   have hu_eq : u = n + (u - n) := by omega
   rw [hu_eq] at hug
   have hvu := ih (u - n) (by omega) hug (by omega)
   rw [← hu_eq] at hvu
   simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
   rcases hu with rfl | rfl
   ·exact Or.inl hvu
   ·exact Or.inr hvu
lemma mem_orIn_input {n : ℕ} (C : Circuit) (u v : Fin n) :
  u ∈ orIn n C v.val ↔ u = v := by
 unfold orIn
 simp only [Finset.mem_filter, Finset.mem_univ, true_and]
 constructor
 ·rintro (heq | ⟨k, _, hreach, _, _⟩)
  ·exact Fin.ext heq
  ·exact absurd hreach (orReaches_input_false v.isLt)
 ·rintro rfl; exact Or.inl rfl
lemma orIn_and_eq_empty {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
  (hand : (gateAt C j).op = GateOp.and) : orIn n C (n + j) = ∅ := by
 ext u
 simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_or]
 refine ⟨by have := u.isLt; omega, ?_⟩
 rintro ⟨k, hk, hreach, hor, _⟩
 rw [orReaches_gate_iff hj] at hreach
 rcases hreach with rfl | ⟨hor', _⟩
 ·rw [hand] at hor; cases hor
 ·rw [hand] at hor'; cases hor'
lemma orIn_or_eq_union {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
  (hor : (gateAt C j).op = GateOp.or) :
  orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
 ext u
 simp only [Finset.mem_union, orIn, Finset.mem_filter, Finset.mem_univ, true_and]
 constructor
 ·rintro (hu | ⟨k, hk, hreach, hork, huk⟩)
  ·omega
  ·rw [orReaches_gate_iff hj] at hreach
   rcases hreach with rfl | ⟨_, w, hw, hnw, hwnj, hwk⟩
   ·rw [gate_inputs_eq hAO hj] at huk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
    rcases huk with h0 | h1
    ·exact Or.inl (Or.inl h0)
    ·exact Or.inr (Or.inl h1)
   ·rw [gate_inputs_eq hAO hj] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    ·exact Or.inl (Or.inr ⟨k, hk, hwk, hork, huk⟩)
    ·exact Or.inr (Or.inr ⟨k, hk, hwk, hork, huk⟩)
 ·rintro ((h0 | ⟨k, hk, hwk, hork, huk⟩) | (h1 | ⟨k, hk, hwk, hork, huk⟩))
  ·right
   refine ⟨j, hj, orReaches_self hj, hor, ?_⟩
   rw [gate_inputs_eq hAO hj, h0]; simp
  ·right
   refine ⟨k, hk, (orReaches_gate_iff hj).mpr (Or.inr ⟨hor, opnd C j 0, opnd_mem hAO hj 0, hwk.1,
    opnd_lt hAO hj 0, hwk⟩), hork, huk⟩
  ·right
   refine ⟨j, hj, orReaches_self hj, hor, ?_⟩
   rw [gate_inputs_eq hAO hj, h1]; simp
  ·right
   refine ⟨k, hk, (orReaches_gate_iff hj).mpr (Or.inr ⟨hor, opnd C j 1, opnd_mem hAO hj 1, hwk.1,
    opnd_lt hAO hj 1, hwk⟩), hork, huk⟩
lemma orIn_val_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
  {w : ℕ} {u : Fin n} (hu : u ∈ orIn n C w) (hx : x u = true) : wval C x w = true := by
 unfold orIn at hu
 simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
 rcases hu with rfl | ⟨k, hk, hreach, hork, huk⟩
 ·rw [wval_input C x u.val u.isLt]; exact hx
 ·apply orReaches_val_mono hAO x hreach
  rw [gateVal_eq_wval, wval_gate_or hAO x hk hork, Bool.or_eq_true]
  rw [gate_inputs_eq hAO hk] at huk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
  rcases huk with h0 | h1
  ·left; rw [← h0, wval_input C x u.val u.isLt]; exact hx
  ·right; rw [← h1, wval_input C x u.val u.isLt]; exact hx
lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} {w k : ℕ} (h : OrReaches n C w k) :
  orIn n C (n + k) ⊆ orIn n C w := by
 intro u hu
 unfold orIn at hu ⊢
 simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
 rcases hu with hu | ⟨m, hm, hkm, horm, hum⟩
 ·omega
 ·exact Or.inr ⟨m, hm, orReaches_trans h hkm, horm, hum⟩
def delWire (n j r w : ℕ) : ℕ :=
 if w = n + j then r else if n + j < w then w - 1 else w
def delCircuit (n : ℕ) (C : Circuit) (j r : ℕ) : Circuit :=
 {gates := (C.gates.eraseIdx j).map (fun g => { g with inputs := g.inputs.map (delWire n j r) })
  output := delWire n j r C.output }
lemma delCircuit_len (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) (r : ℕ) :
  (delCircuit n C j r).gates.length = C.gates.length - 1 := by
 simp [delCircuit, List.length_eraseIdx, hj]
lemma delCircuit_gateAt_lt {n : ℕ} {C : Circuit} {j r i : ℕ}
  (hj : j < C.gates.length) (hi : i < j) :
  gateAt (delCircuit n C j r) i =
   {(gateAt C i) with inputs := (gateAt C i).inputs.map (delWire n j r) } := by
 have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
 rw [gateAt_eq hi', gateAt_eq (by omega)]
 simp only [delCircuit, List.getElem_map]
 rw [List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx, if_pos hj]; omega) hi]
lemma delCircuit_gateAt_ge {n : ℕ} {C : Circuit} {j r i : ℕ}
  (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) :
  gateAt (delCircuit n C j r) i =
   {(gateAt C (i + 1)) with inputs := (gateAt C (i + 1)).inputs.map (delWire n j r) } := by
 have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
 rw [gateAt_eq hi', gateAt_eq (by omega)]
 simp only [delCircuit, List.getElem_map]
 rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx, if_pos hj]; omega) hji]
lemma delCircuit_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r : ℕ}
  (hj : j < C.gates.length) (hr : r < n + j) : IsAO2 n (delCircuit n C j r) := by
 refine ⟨?_, ?_, ?_⟩
 ·intro g hg
  simp only [delCircuit, List.mem_map] at hg
  rcases hg with ⟨g0, hg0, rfl⟩
  exact hAO.1 g0 (List.mem_of_mem_eraseIdx hg0)
 ·intro i hi w hw
  rw [delCircuit_len n C hj r] at hi
  by_cases hij : i < j
  ·rw [delCircuit_gateAt_lt hj hij] at hw
   simp only [List.mem_map] at hw
   rcases hw with ⟨u, hu, rfl⟩
   have hult : u < n + i := hAO.2.1 i (by omega) u hu
   unfold delWire
   rw [if_neg (by omega), if_neg (by omega)]
   exact hult
  ·rw [delCircuit_gateAt_ge hj (by omega) hi] at hw
   simp only [List.mem_map] at hw
   rcases hw with ⟨u, hu, rfl⟩
   have hult : u < n + (i + 1) := hAO.2.1 (i + 1) (by omega) u hu
   unfold delWire
   split_ifs <;> omega
 ·intro g hg
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
  ·have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
   rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
  ·by_cases hwj : w = n + j
   ·subst hwj
    have hdw : delWire n j r (n + j) = r := by unfold delWire; simp
    have hdr : delWire n j r r = r := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
    have h1 := ih r hr (by omega)
    rw [hdr] at h1
    rw [hdw, h1, heq]
   ·by_cases hlt : w < n + j
    ·have hk : w - n < j := by omega
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
    ·have hgt : n + j < w := by omega
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
  ·have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
   rw [hdw, wval_input _ x w hwn]; rw [wval_input _ x w hwn] at hval; exact hval
  ·by_cases hwj : w = n + j
   ·subst hwj
    have hdw : delWire n j r (n + j) = r := by unfold delWire; simp
    have hdr : delWire n j r r = r := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
    have h1 := ih r hr (by omega) (hle hval)
    rw [hdr] at h1
    rw [hdw]
    exact h1
   ·by_cases hlt : w < n + j
    ·have hk : w - n < j := by omega
     have hdw : delWire n j r w = n + (w - n) := by
      unfold delWire; rw [if_neg hwj, if_neg (by omega)]; omega
     have hw_eq : w = n + (w - n) := by omega
     rw [hdw]; rw [hw_eq] at hval
     have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
     have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
     have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega
     have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega
     rcases hAO.1 _ (gateAt_mem (by omega : w - n < C.gates.length)) with hand | hor
     ·rw [wval_gate_and hAO x (by omega) hand, Bool.and_eq_true] at hval
      rw [wval_gate_and hAO' x hk' (by rw [hg]; exact hand), Bool.and_eq_true]
      rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
      exact ⟨ih _ h0lt (by omega) hval.1, ih _ h1lt (by omega) hval.2⟩
     ·rw [wval_gate_or hAO x (by omega) hor, Bool.or_eq_true] at hval
      rw [wval_gate_or hAO' x hk' (by rw [hg]; exact hor), Bool.or_eq_true]
      rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
      exact hval.imp (ih _ h0lt (by omega)) (ih _ h1lt (by omega))
    ·have hgt : n + j < w := by omega
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
     ·rw [wval_gate_and hAO x (by omega) hand, Bool.and_eq_true] at hval
      rw [wval_gate_and hAO' x hk' (by rw [hg]; exact hand), Bool.and_eq_true]
      rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
      exact ⟨ih _ h0lt (by omega) hval.1, ih _ h1lt (by omega) hval.2⟩
     ·rw [wval_gate_or hAO x (by omega) hor, Bool.or_eq_true] at hval
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
  ·have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
   rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
  ·have hnc' : ¬ InCone n C j (w - n) := hnc (by omega)
   have hop_ok : ∀ b : Fin 2, opnd C (w - n) b ≠ n + j ∧
     (n ≤ opnd C (w - n) b → ¬ InCone n C j (opnd C (w - n) b - n)) := by
    intro b
    have hk : w - n < C.gates.length := by omega
    have hmem := opnd_mem hAO hk b
    have hlt := opnd_lt hAO hk b
    constructor
    ·intro heq; apply hnc'; rw [inCone_iff hk]
     exact ⟨opnd C (w - n) b, hmem, by omega, hlt, Or.inl (by omega)⟩
    ·intro hnu hin; apply hnc'; rw [inCone_iff hk]
     exact ⟨opnd C (w - n) b, hmem, hnu, hlt, Or.inr hin⟩
   by_cases hlt : w < n + j
   ·have hk : w - n < j := by omega
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
   ·have hgt : n + j < w := by omega
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
 ·rintro ⟨a, b, hab, ha, hb⟩
  unfold pairInput at ha hb
  simp only [decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  ·exact absurd hab (G.loopless.irrefl _)
  ·exact hab
  ·exact hab.symm
  ·exact absurd hab (G.loopless.irrefl _)
 ·intro huv
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
lemma output_bounds {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
  n ≤ C.output ∧ C.output < n + C.gates.length := by
 obtain ⟨u, v, huv⟩ := hne
 have hfun : ∀ x, wval C x C.output = graphFun G ∅ x := fun x => congrFun hL.2.1 x
 constructor
 ·by_contra hlt
  push Not at hlt
  have h1 := hfun (fun w => decide (w = ⟨C.output, hlt⟩))
  rw [wval_input C _ C.output hlt, graphFun_unit_false] at h1
  simp at h1
 ·by_contra hge
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
  ·have hrx : wval C x r = false := by
    cases h : wval C x r
    ·rfl
    ·have := hbelow x h; rw [hFx] at this; cases this
   have hax : wval C x (n + a) = false := by
    rw [wval_gate_and hL.1 x ha hand]
    fin_cases b
    ·change wval C x (opnd C a 0) = false at hrx; rw [hrx]; rfl
    ·change wval C x (opnd C a 1) = false at hrx; rw [hrx, Bool.and_false]
   have hcx : wval C x C.output = false := by
    change circuitFun n C x = false; rw [congrFun hL.2.1 x]; exact hFx
   change wval (delCircuit n C a r) x (delWire n a r C.output) = false
   rw [delCircuit_wval_eq hL.1 x ha hr (by rw [hrx, hax]) C.output hout.2, hcx]
  ·have hcx : wval C x C.output = true := by
    change circuitFun n C x = true; rw [congrFun hL.2.1 x]; exact hFx
   change wval (delCircuit n C a r) x (delWire n a r C.output) = true
   apply delCircuit_wval_ge hL.1 x ha hr _ C.output hout.2 hcx
   intro hax
   rw [wval_gate_and hL.1 x ha hand, Bool.and_eq_true] at hax
   fin_cases b
   ·exact hax.1
   ·exact hax.2
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
  ·exact Or.inl hwx
  ·exact Or.inr hwx
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
 ·rintro ⟨hk, hand, _, x, hgx, hfx⟩
  refine ⟨hk, hand, fun hb => ?_⟩
  have := hb x hgx; rw [hfx] at this; cases this
 ·rintro ⟨hk, hand, hnb⟩
  push Not at hnb
  rcases hnb with ⟨x, hgx, hfx⟩
  refine ⟨hk, hand, hk, x, hgx, ?_⟩
  cases h : graphFun G ∅ x
  ·rfl
  ·exact absurd h hfx
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
  ·exact ⟨0, h0.symm⟩
  ·exact ⟨1, h1.symm⟩
 rcases hL.1.1 _ (gateAt_mem hm) with hand | hor
 ·exfalso
  exact least_no_belowF_and_opnd hL hne hm hand b (by rw [hb]; exact hwb)
 ·rw [mem_orT_iff]
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
 ·exact Or.inl ⟨hk, hand, hb⟩
 ·exact Or.inr ⟨hk, hor, hb⟩
lemma exists_reader_of_inCone {n : ℕ} {C : Circuit} {k j : ℕ} (h : InCone n C k j) :
  ∃ m < C.gates.length, n + k ∈ (gateAt C m).inputs := by
 induction j using Nat.strong_induction_on with
 | ind j ih =>
  have hj := inCone_lt_len h
  rw [inCone_iff hj] at h
  rcases h with ⟨w, hw, hnw, hwnj, rfl | hsub⟩
  ·exact ⟨j, hj, by rwa [show n + (w - n) = w by omega]⟩
  ·exact ih (w - n) (by omega) hsub
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
   ·exact (mem_tops_iff.mp h).1
   ·exact (mem_orT_iff.mp h).1
  have hk_bf : BelowF G C k := by
   rcases hk_mem with h | h
   ·exact (mem_tops_iff.mp h).2.2
   ·exact (mem_orT_iff.mp h).2.2
  have hcone := least_inOutputCone hL hne k hk_lt
  have hin : InCone n C k (C.output - n) := by
   rcases hcone.2 with heq | ⟨_, hin⟩
   ·exfalso; apply hne_out; omega
   ·exact hin
  obtain ⟨m, hm, hread⟩ := exists_reader_of_inCone hin
  have hm_orT := belowF_reader_is_orT hL hLift hne hk_lt hk_bf hm hread
  rw [gate_inputs_eq hL.1 hm] at hread
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
  simp only [T, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true]
  rcases hread with h0 | h1
  ·exact ⟨(m, 0), hm_orT, h0.symm⟩
  ·exact ⟨(m, 1), hm_orT, h1.symm⟩
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
  ·intro hk
   rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
   ·by_cases hb : BelowF G C k
    ·exact Or.inl (Or.inl (Or.inl ⟨hk, hand, hb⟩))
    ·exact Or.inl (Or.inr ⟨hk, hand, hb⟩)
   ·by_cases hb : BelowF G C k
    ·exact Or.inl (Or.inl (Or.inr ⟨hk, hor, hb⟩))
    ·exact Or.inr ⟨hk, hor, hb⟩
  ·rintro (((⟨hk, _⟩ | ⟨hk, _⟩) | ⟨hk, _⟩) | ⟨hk, _⟩) <;> exact hk
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
  ·exact h2.2.2 h1.2.2
  ·exact h2.2.2 h1.2.2
  ·rw [h1.2.1] at h2; cases h2.2.1
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
 ·intro hcx
  have hkey : ∀ k, k ∈ tops G C ∪ orT G C → gateVal n C k x = true →
    ∃ a ∈ tops G C, gateVal n C a x = true := by
   intro k
   induction k using Nat.strong_induction_on with
   | ind k ih =>
    intro hk hvk
    rw [Finset.mem_union] at hk
    rcases hk with htop | horT
    ·exact ⟨k, htop, hvk⟩
    ·rw [mem_orT_iff] at horT
     rw [gateVal_eq_wval, wval_gate_or hL.1 x horT.1 horT.2.1, Bool.or_eq_true] at hvk
     rcases hvk with h0 | h1
     ·obtain ⟨hge, hlt, hbf⟩ := orT_opnds_belowF hL horT.1 horT.2.1 horT.2.2 0
      have hlt_k : opnd C k 0 - n < k := by have := opnd_lt hL.1 horT.1 0; omega
      have hmem : opnd C k 0 - n ∈ tops G C ∪ orT G C := by
       rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
       rcases hL.1.1 _ (gateAt_mem hlt) with hand | hor
       ·exact Or.inl ⟨hlt, hand, hbf⟩
       ·exact Or.inr ⟨hlt, hor, hbf⟩
      exact ih _ hlt_k hmem (by rw [gateVal_eq_wval, show n + (opnd C k 0 - n) = opnd C k 0 by omega]; exact h0)
     ·obtain ⟨hge, hlt, hbf⟩ := orT_opnds_belowF hL horT.1 horT.2.1 horT.2.2 1
      have hlt_k : opnd C k 1 - n < k := by have := opnd_lt hL.1 horT.1 1; omega
      have hmem : opnd C k 1 - n ∈ tops G C ∪ orT G C := by
       rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
       rcases hL.1.1 _ (gateAt_mem hlt) with hand | hor
       ·exact Or.inl ⟨hlt, hand, hbf⟩
       ·exact Or.inr ⟨hlt, hor, hbf⟩
      exact ih _ hlt_k hmem (by rw [gateVal_eq_wval, show n + (opnd C k 1 - n) = opnd C k 1 by omega]; exact h1)
  apply hkey (C.output - n) hout_mem
  rw [gateVal_eq_wval, show n + (C.output - n) = C.output by omega]
  exact hcx
 ·rintro ⟨a, ha, hva⟩
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
  ·constructor
   ·intro hwx
    left
    refine ⟨⟨w, hwn⟩, (mem_orIn_input C _ _).mpr rfl, ?_⟩
    rwa [wval_input C x w hwn] at hwx
   ·rintro (⟨u, hu, hxu⟩ | ⟨hr, _⟩ | ⟨hr, _⟩)
    ·have huw : u = ⟨w, hwn⟩ := (mem_orIn_input C u ⟨w, hwn⟩).mp hu
     subst huw; rw [wval_input C x w hwn]; exact hxu
    ·exact absurd hr (orReaches_input_false hwn)
    ·exact absurd hr (orReaches_input_false hwn)
  ·have hk : w - n < C.gates.length := by omega
   have hw_eq : w = n + (w - n) := by omega
   have hnbk : ¬ BelowF G C (w - n) := hnb (w - n) hw_eq
   rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
   ·have hmem : w - n ∈ junk G C := mem_junk_iff.mpr ⟨hk, hand, hnbk⟩
    rw [hjunk] at hmem
    constructor
    ·intro hwx
     rcases hmem with h1 | h2
     ·right; left
      refine ⟨?_, ?_⟩
      ·rw [hw_eq, h1]; exact orReaches_self (by omega)
      ·rw [gateVal_eq_wval, ← h1, ← hw_eq]; exact hwx
     ·right; right
      refine ⟨?_, ?_⟩
      ·rw [hw_eq, h2]; exact orReaches_self (by omega)
      ·rw [gateVal_eq_wval, ← h2, ← hw_eq]; exact hwx
    ·rintro (⟨u, hu, _⟩ | ⟨hr, hvg⟩ | ⟨hr, hvg⟩)
     ·rw [hw_eq, orIn_and_eq_empty hk hand] at hu; simp at hu
     ·exact orReaches_val_mono hL.1 x hr hvg
     ·exact orReaches_val_mono hL.1 x hr hvg
   ·have hop_nb : ∀ b : Fin 2, ∀ m, opnd C (w - n) b = n + m → ¬ BelowF G C m := by
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
     ·rintro (heq | ⟨_, u, hu, _, _, hug⟩)
      ·exact absurd heq hne_g
      ·rw [gate_inputs_eq hL.1 hk] at hu
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
       rcases hu with rfl | rfl
       ·exact Or.inl hug
       ·exact Or.inr hug
     ·rintro (h0 | h1)
      ·exact Or.inr ⟨hor, opnd C (w - n) 0, opnd_mem hL.1 hk 0, h0.1, opnd_lt hL.1 hk 0, h0⟩
      ·exact Or.inr ⟨hor, opnd C (w - n) 1, opnd_mem hL.1 hk 1, h1.1, opnd_lt hL.1 hk 1, h1⟩
    rw [hreach_iff g1 (Or.inl rfl), hreach_iff g2 (Or.inr rfl)]
    constructor
    ·rintro ((⟨u, hu, hxu⟩ | ⟨h1, hg1⟩ | ⟨h2, hg2⟩) | (⟨u, hu, hxu⟩ | ⟨h1, hg1⟩ | ⟨h2, hg2⟩))
     ·exact Or.inl ⟨u, Finset.mem_union_left _ hu, hxu⟩
     ·exact Or.inr (Or.inl ⟨Or.inl h1, hg1⟩)
     ·exact Or.inr (Or.inr ⟨Or.inl h2, hg2⟩)
     ·exact Or.inl ⟨u, Finset.mem_union_right _ hu, hxu⟩
     ·exact Or.inr (Or.inl ⟨Or.inr h1, hg1⟩)
     ·exact Or.inr (Or.inr ⟨Or.inr h2, hg2⟩)
    ·rintro (⟨u, hu, hxu⟩ | ⟨h1 | h1, hg1⟩ | ⟨h2 | h2, hg2⟩)
     ·rcases Finset.mem_union.mp hu with h0 | h1
      ·exact Or.inl (Or.inl ⟨u, h0, hxu⟩)
      ·exact Or.inr (Or.inl ⟨u, h1, hxu⟩)
     ·exact Or.inl (Or.inr (Or.inl ⟨h1, hg1⟩))
     ·exact Or.inr (Or.inr (Or.inl ⟨h1, hg1⟩))
     ·exact Or.inl (Or.inr (Or.inr ⟨h2, hg2⟩))
     ·exact Or.inr (Or.inr (Or.inr ⟨h2, hg2⟩))
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
  ·exact ⟨ha1, hb1⟩
  ·exact ⟨ha2, hb2⟩
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
  ·intro g hg
   simp only [List.mem_append, List.mem_singleton] at hg
   rcases hg with hg | rfl
   ·exact hAO'.1 g hg
   ·exact Or.inr rfl
  ·intro j hj u hu
   simp only [List.length_append, List.length_singleton] at hj
   by_cases hlt : j < gs'.length
   ·have hgat : gateAt ⟨gs' ++ [⟨GateOp.or, [w, w']⟩], 0⟩ j = gateAt ⟨gs', 0⟩ j := by
     rw [gateAt_eq (by simp; omega), gateAt_eq hlt]
     simp [List.getElem_append_left hlt]
    rw [hgat] at hu
    exact hAO'.2.1 j hlt u hu
   ·have hjeq : j = gs'.length := by omega
    subst hjeq
    have hgat : gateAt ⟨gs' ++ [⟨GateOp.or, [w, w']⟩], 0⟩ gs'.length = ⟨GateOp.or, [w, w']⟩ := by
     rw [gateAt_eq (by simp)]
     simp
    rw [hgat] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    ·exact hwlt
    ·exact hlt'
  ·intro g hg
   simp only [List.mem_append, List.mem_singleton] at hg
   rcases hg with hg | rfl
   ·exact hAO'.2.2 g hg
   ·rfl
  ·simp only [List.length_append, List.length_singleton]; omega
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
 ·intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  ·exact hAO.1 g hg
  ·exact hop
 ·intro j hj u hu
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < gs.length
  ·have hgat : gateAt ⟨gs ++ [⟨op, [w0, w1]⟩], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
    rw [gateAt_eq (by simp; omega), gateAt_eq hlt]; simp [List.getElem_append_left hlt]
   rw [hgat] at hu
   exact hAO.2.1 j hlt u hu
  ·have hjeq : j = gs.length := by omega
   subst hjeq
   have hgat : gateAt ⟨gs ++ [⟨op, [w0, w1]⟩], 0⟩ gs.length = ⟨op, [w0, w1]⟩ := by
    rw [gateAt_eq (by simp)]; simp
   rw [hgat] at hu
   simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
   rcases hu with rfl | rfl <;> assumption
 ·intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  ·exact hAO.2.2 g hg
  ·rfl
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
  ·exact Or.inl hw
  ·exact Or.inr ⟨by omega, w - n, hmem, le_refl _, rfl⟩
  ·rcases ih (opnd C (w - n) 0) hlt0 (by omega) with hlt | ⟨hnle, k, hkmem, hkle, heq⟩
   ·exact Or.inl hlt
   ·exact Or.inr ⟨by omega, k, hkmem, by omega, heq⟩
  ·exfalso; have := opnd_lt hAO hk 0; omega
  ·rcases ih (opnd C (w - n) 1) h1 (by omega) with hlt | ⟨hnle, k, hkmem, hkle, heq⟩
   ·exact Or.inl hlt
   ·exact Or.inr ⟨by omega, k, hkmem, by omega, heq⟩
  ·exfalso; have := opnd_lt hAO hk 1; omega
  ·exfalso; omega
lemma idxOf_lt_of_pairwise_lt {l : List ℕ} (hsort : l.Pairwise (· < ·))
  {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hab : a < b) : l.idxOf a < l.idxOf b := by
 induction l with
 | nil => cases ha
 | cons x xs ih =>
  rw [List.pairwise_cons] at hsort
  simp only [List.mem_cons] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  ·omega
  ·rw [List.idxOf_cons_self]
   have hne : a ≠ b := Nat.ne_of_lt hab
   rw [List.idxOf_cons_ne _ (by simp [hne])]
   exact Nat.succ_pos _
  ·have := hsort.1 a ha; omega
  ·have hnea : x ≠ a := by have := hsort.1 a ha; omega
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
 ·intro g hg
  simp only [lamGates, List.mem_map] at hg
  rcases hg with ⟨k, _, rfl⟩
  exact Or.inr rfl
 ·intro j hj u hu
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
   ·omega
   ·rw [heq]
    have hk'lt : k' < k := by omega
    have hlt_idx := idxOf_lt_of_pairwise_lt hsort hk'm hk_mem hk'lt
    rw [hidx] at hlt_idx
    omega
  rcases hu with rfl | rfl
  ·exact check_b 0
  ·exact check_b 1
 ·intro g hg
  simp only [lamGates, List.mem_map] at hg
  rcases hg with ⟨k, _, rfl⟩
  rfl
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
 ·intro m hm hbm
  exact lift_no_belowF_orN_opnd hL hLift hne hk'.1 hk'.2.1 hk'.2.2 b (by rw [hm]; exact hbm)
 ·intro m hrm hm_orN h0 h1
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
 ·intro m hm hbm
  exact least_no_belowF_and_opnd hL hne ha'.1 ha'.2.1 b (by rw [hm]; exact hbm)
 ·intro m hrm hm_orN h0 h1
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
  ·have hbp : bypass n C lamList w = w := by unfold bypass; rw [dif_pos hwn]
   rw [hbp]
   refine ⟨by omega, ?_⟩
   rw [wval_input _ x w hwn]
   apply Bool.eq_iff_iff.mpr
   simp only [decide_eq_true_eq]
   constructor
   ·intro h; exact ⟨⟨w, hwn⟩, (mem_orIn_input C _ _).mpr rfl, h⟩
   ·rintro ⟨u, hu, hxu⟩
    have heq := (mem_orIn_input C u ⟨w, hwn⟩).mp hu
    subst heq; exact hxu
  ·have hk_lt : w - n < C.gates.length := by have := hlw.1; omega
   have hw_eq : w = n + (w - n) := by omega
   set k := w - n
   have hnbk : ¬ BelowF G C k := hlw.2.2.1 k hw_eq
   have hork : (gateAt C k).op = GateOp.or := by
    rcases hL.1.1 _ (gateAt_mem hk_lt) with hand | hor
    ·exfalso
     have hemp := orIn_and_eq_empty (n := n) hk_lt hand
     rw [← hw_eq] at hemp
     exact hlw.2.1.ne_empty hemp
    ·exact hor
   have hk_orN : k ∈ orN G C := mem_orN_iff.mpr ⟨hk_lt, hork, hnbk⟩
   have hlw_k : LeafWire G C (n + k) := by rwa [← hw_eq]
   have horIn_eq : orIn n C w = orIn n C (opnd C k 0) ∪ orIn n C (opnd C k 1) := by
    rw [hw_eq]; exact orIn_or_eq_union hL.1 hk_lt hork
   have hlt0 : opnd C k 0 < w := by have := opnd_lt hL.1 hk_lt 0; omega
   have hlt1 : opnd C k 1 < w := by have := opnd_lt hL.1 hk_lt 1; omega
   by_cases hmem : k ∈ lamList
   ·have hbp : bypass n C lamList w = n + lamList.idxOf k := by
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
    ·rintro (⟨u, hu, hxu⟩ | ⟨u, hu, hxu⟩)
     ·exact ⟨u, Or.inl hu, hxu⟩
     ·exact ⟨u, Or.inr hu, hxu⟩
    ·rintro ⟨u, hu | hu, hxu⟩
     ·exact Or.inl ⟨u, hu, hxu⟩
     ·exact Or.inr ⟨u, hu, hxu⟩
   ·have hnotboth : ¬ ((orIn n C (opnd C k 0)).Nonempty ∧ (orIn n C (opnd C k 1)).Nonempty) := by
     rintro ⟨h0, h1⟩
     apply hmem
     rw [hlam_iff]
     exact hlw_k.2.2.2 k (orReaches_self hk_lt) hk_orN h0 h1
    by_cases h0ne : (orIn n C (opnd C k 0)).Nonempty
    ·have h1emp : orIn n C (opnd C k 1) = ∅ := by
      by_contra hne1; exact hnotboth ⟨h0ne, Finset.nonempty_iff_ne_empty.mpr hne1⟩
     have hbp : bypass n C lamList w = bypass n C lamList (opnd C k 0) := by
      conv_lhs => unfold bypass
      dsimp only
      rw [dif_neg hwn, dif_pos hk_lt, if_neg hmem, if_pos h0ne, dif_pos hlt0]
     rw [hbp, horIn_eq, h1emp, Finset.union_empty]
     exact ih (opnd C k 0) hlt0 (leafWire_opnd hL hLift hne hk_orN hlw_k 0 h0ne)
    ·have h0emp : orIn n C (opnd C k 0) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h0ne
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
   ·simp only [List.length_append, List.length_cons, List.length_nil, hlen1, List.length_map,
     Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    omega
   ·intro x
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
    ·rintro ⟨_, ⟨u, hu, rfl⟩, hxu⟩
     rw [wval_input _ x u.val u.isLt] at hxu; exact ⟨u, hu, hxu⟩
    ·rintro ⟨u, hu, hxu⟩
     exact ⟨u.val, ⟨u, hu, rfl⟩, by rw [wval_input _ x u.val u.isLt]; exact hxu⟩
 | some bw =>
  have hbw : bw < n + gs.length := hbase bw rfl
  cases extra with
  | nil =>
   have hAO2 := appendGate_isAO2 hAO (Or.inl rfl) (by omega : v.val < n + gs.length) hbw
   refine ⟨⟨[⟨GateOp.and, [v.val, bw]⟩], rfl⟩, ?_, hAO2, by simp [addStar], ?_⟩
   ·simp [addStar]
   ·intro x
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
   ·simp only [gs2, List.length_append, List.length_cons, List.length_nil, hlen1,
     List.length_map, Option.isSome_some, ↓reduceIte]
    omega
   ·intro x
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
    ·rintro (h | ⟨_, ⟨u, hu, rfl⟩, hxu⟩)
     ·exact Or.inl h
     ·rw [wval_input _ x u.val u.isLt] at hxu; exact Or.inr ⟨u, hu, hxu⟩
    ·rintro (h | ⟨u, hu, hxu⟩)
     ·exact Or.inl h
     ·exact Or.inr ⟨u.val, ⟨u, hu, rfl⟩, by rw [wval_input _ x u.val u.isLt]; exact hxu⟩
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
  ·simp only [hlen2, hlen1, List.map_cons, List.sum_cons]; omega
  ·simp only [List.length_cons, hwlen2]
  ·intro w hw
   simp only [List.mem_cons] at hw
   rcases hw with rfl | hw
   ·rw [hex2, List.length_append]; omega
   ·exact hlt2 w hw
  ·intro x
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
  ·simp only [mkTopItem, dif_pos h]
   set v := Classical.choose h
   have hv := Classical.choose_spec h
   have hs : side (n := n) C a 0 = {v} ∨ side (n := n) C a 1 = {v} := by
    rw [← hv.2]; exact htop_side v hv.1
   set b : Fin 2 := if side (n := n) C a 0 = {v} then 1 else 0
   have h1mb : side (n := n) C a (1 - b) = {v} := by
    by_cases h0 : side (n := n) C a 0 = {v}
    ·simp [b, h0]
    ·simp [b, h0]; exact hs.resolve_left h0
   have hcard : (side (n := n) C a (1 - b)).card = 1 := by rw [h1mb]; simp
   have hneb : (side (n := n) C a b).Nonempty := by
    by_cases h0 : side (n := n) C a 0 = {v}
    ·simp [b, h0]; exact hst.2.1
    ·simp [b, h0]; exact hst.1
   have hlw := leafWire_of_top_side hL hne ha_top b hneb hcard
   refine ⟨?_, rfl, ?_⟩
   ·intro bw hbw
    injection hbw with hbw; subst hbw
    have := (bypass_wval hL hLift hne lamList hsort hlam_iff (fun _ => false) _ hlw).1
    rw [hgs1_len, ← hlam_len]; exact this
   ·intro x
    have hbp : wval ⟨gs1, 0⟩ x (bypass n C lamList (opnd C a b)) =
      decide (∃ u ∈ orIn n C (opnd C a b), x u = true) :=
     (bypass_wval hL hLift hne lamList hsort hlam_iff x _ hlw).2
    simp only [Option.some.injEq, exists_eq_left', hbp, decide_eq_true_eq, Finset.mem_toList]
    have huniq : ∀ v' ∈ Zhas, topOf v' = a → v' = v := fun v' hv' heq =>
     htop_inj v' hv' v hv.1 (heq.trans hv.2.symm)
    constructor
    ·rintro ⟨hxv, hleaf | ⟨u, hu, hxu⟩⟩
     ·left
      by_cases h0 : side (n := n) C a 0 = {v}
      ·simp only [b, if_pos h0] at hleaf
       exact ⟨⟨v, by rw [h0]; simp, hxv⟩, hleaf⟩
      ·simp only [b, if_neg h0] at hleaf
       have h1 : side (n := n) C a 1 = {v} := hs.resolve_left h0
       exact ⟨hleaf, ⟨v, by rw [h1]; simp, hxv⟩⟩
     ·right; exact ⟨v, hv.1, hv.2, hxv, u, hu, hxu⟩
    ·rintro (⟨h0, h1⟩ | ⟨v', hv', heq, hxv', u, hu, hxu⟩)
     ·by_cases hs0 : side (n := n) C a 0 = {v}
      ·simp only [b, if_pos hs0]
       rcases h0 with ⟨u0, hu0, hxu0⟩
       rw [hs0, Finset.mem_singleton] at hu0; subst hu0
       exact ⟨hxu0, Or.inl h1⟩
      ·simp only [b, if_neg hs0]
       have hs1 : side (n := n) C a 1 = {v} := hs.resolve_left hs0
       rcases h1 with ⟨u1, hu1, hxu1⟩
       rw [hs1, Finset.mem_singleton] at hu1; subst hu1
       exact ⟨hxu1, Or.inl h0⟩
     ·have hv'eq := huniq v' hv' heq; subst hv'eq
      exact ⟨hxv', Or.inr ⟨u, hu, hxu⟩⟩
  ·simp only [mkTopItem, dif_neg h, dif_pos ha]
   by_cases h0 : (side (n := n) C a 0).card = 1
   ·simp only [dif_pos h0]
    set v := Classical.choose (Finset.card_eq_one.mp h0)
    have hv : side (n := n) C a 0 = {v} := Classical.choose_spec (Finset.card_eq_one.mp h0)
    have hlw := leafWire_of_top_side hL hne ha_top 1 hst.2.1 (by simpa using h0)
    refine ⟨?_, rfl, ?_⟩
    ·intro bw hbw
     injection hbw with hbw; subst hbw
     have := (bypass_wval hL hLift hne lamList hsort hlam_iff (fun _ => false) _ hlw).1
     rw [hgs1_len, ← hlam_len]; exact this
    ·intro x
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
   ·simp only [dif_neg h0]
    have h1 : (side (n := n) C a 1).card = 1 := hst.2.2.resolve_left h0
    set v := Classical.choose (Finset.card_eq_one.mp h1)
    have hv : side (n := n) C a 1 = {v} := Classical.choose_spec (Finset.card_eq_one.mp h1)
    have hlw := leafWire_of_top_side hL hne ha_top 0 hst.1 (by simpa using h1)
    refine ⟨?_, rfl, ?_⟩
    ·intro bw hbw
     injection hbw with hbw; subst hbw
     have := (bypass_wval hL hLift hne lamList hsort hlam_iff (fun _ => false) _ hlw).1
     rw [hgs1_len, ← hlam_len]; exact this
    ·intro x
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
  ·have h := htopItem_ok a ha
   exact ⟨h.1, Or.inl h.2.1⟩
  ·refine ⟨fun bw hbw => (by cases hbw), Or.inr ?_⟩
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
    ·rw [h0] at hp0; exact Finset.notMem_empty _ hp0
    ·rw [h1] at hp1; exact Finset.notMem_empty _ hp1
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
  ·rintro ⟨it, hit, hxv, hbody⟩
   simp only [allItems, topItems, newItems, List.mem_append, List.mem_map, Finset.mem_toList] at hit
   rcases hit with ⟨a, ha, rfl⟩ | ⟨v, hv, rfl⟩
   ·have hiff := (htopItem_ok a ha).2.2 x
    rcases hiff.mp ⟨hxv, hbody⟩ with ⟨⟨u0, hu0, hxu0⟩, ⟨u1, hu1, hxu1⟩⟩ | ⟨v, hv, _, hxv', u, hu, hxu⟩
    ·exact ⟨u0, u1, top_sides_adj hL.1 (Finset.mem_sdiff.mp ha).1 hu0 hu1, hxu0, hxu1⟩
    ·exact ⟨v, u, hLadj v (hZsub hv) u hu, hxv', hxu⟩
   ·rcases hbody with ⟨bw, hbw, _⟩ | ⟨u, hu, hxu⟩
    ·cases hbw
    ·rw [Finset.mem_toList] at hu
     exact ⟨v, u, hLadj v (Finset.mem_sdiff.mp hv).1 u hu, hxv, hxu⟩
  ·rintro ⟨u, v, huv, hxu, hxv⟩
   have he : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
   by_cases hst : s(u, v) ∈ starEdges G C
   ·simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at hst
    rcases hst with ⟨a, ha, ⟨p0, p1⟩, ⟨hp0, hp1⟩, hpeq⟩
    have haS : a ∈ S_tops := by
     rw [Finset.mem_sdiff]; refine ⟨ha, fun hc => ?_⟩
     rw [centreless, Finset.mem_filter] at hc
     rcases hc.2 with h0 | h1
     ·rw [h0] at hp0; exact Finset.notMem_empty _ hp0
     ·rw [h1] at hp1; exact Finset.notMem_empty _ hp1
    refine ⟨mkTopItem a, ?_, ?_⟩
    ·simp only [allItems, topItems, List.mem_append, List.mem_map, Finset.mem_toList]
     exact Or.inl ⟨a, haS, rfl⟩
    ·apply ((htopItem_ok a haS).2.2 x).mpr
     left
     rw [Sym2.eq_iff] at hpeq
     rcases hpeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
     ·exact ⟨⟨p0, hp0, hxu⟩, ⟨p1, hp1, hxv⟩⟩
     ·exact ⟨⟨p0, hp0, hxv⟩, ⟨p1, hp1, hxu⟩⟩
   ·have hu_mem : s(u, v) ∈ Ustar G C := Finset.mem_sdiff.mpr ⟨he, hst⟩
    obtain ⟨w, hw, z, hz, heq⟩ := hUcov _ hu_mem
    rw [Sym2.eq_iff] at heq
    have hxw : x w = true := by rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hxz : x z = true := by rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    by_cases hwh : w ∈ Zhas
    ·refine ⟨mkTopItem (topOf w), ?_, ?_⟩
     ·simp only [allItems, topItems, List.mem_append, List.mem_map, Finset.mem_toList]
      exact Or.inl ⟨topOf w, htop_mem w hwh, rfl⟩
     ·apply ((htopItem_ok (topOf w) (htop_mem w hwh)).2.2 x).mpr
      right
      exact ⟨w, hwh, rfl, hxw, z, hz, hxz⟩
    ·refine ⟨(w, none, (L w).toList), ?_, hxw, Or.inr ⟨z, Finset.mem_toList.mpr hz, hxz⟩⟩
     simp only [allItems, newItems, List.mem_append, List.mem_map, Finset.mem_toList]
     exact Or.inr ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwh⟩, rfl⟩
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
   ·simp only [mkTopItem, dif_pos h, Finset.length_toList]
   ·simp only [mkTopItem, dif_neg h, dif_pos ha]
    split_ifs <;> rfl
  rw [hsum_L]
  have himg_sub : Zhas.image topOf ⊆ S_tops := by
   intro a ha; simp only [Finset.mem_image] at ha; rcases ha with ⟨v, hv, rfl⟩; exact htop_mem v hv
  rw [← Finset.sum_subset himg_sub]
  ·rw [Finset.sum_image (fun v1 hv1 v2 hv2 heq => htop_inj v1 hv1 v2 hv2 heq)]
   apply Finset.sum_congr rfl
   intro v hv
   have hex : ∃ v' ∈ Zhas, topOf v' = topOf v := ⟨v, hv, rfl⟩
   rw [dif_pos hex]
   have hch := Classical.choose_spec hex
   rw [htop_inj _ hch.1 v hv hch.2]
  ·intro a _ hnot
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
lemma orDag_count {α : Type} [DecidableEq α] {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
  (Items : Finset α) (H : Finset ℕ) (hH : ∀ k ∈ H, k < C.gates.length)
  (R : ℕ → Finset α)
  (hSmall : ∀ w < n + C.gates.length, (∀ k ∈ H, w ≠ n + k) → (R w).card ≤ 1)
  (hStep : ∀ k ∈ H, R (n + k) ⊆ R (opnd C k 0) ∪ R (opnd C k 1)) :
  ∃ comp : α → ℕ,
   Items.card ≤ (Items.image comp).card + H.card ∧
   ∀ w < n + C.gates.length, ∃ c : ℕ, ∀ a ∈ R w, comp a = c := by
 have haux : ∀ m ≤ C.gates.length,
   ∃ comp : α → ℕ,
    Items.card ≤ (Items.image comp).card + (H.filter (· < m)).card ∧
    ∀ w < n + m, ∃ c : ℕ, ∀ a ∈ R w, comp a = c := by
  intro m
  induction m with
  | zero =>
   intro _
   refine ⟨fun a => Items.toList.idxOf a, ?_, ?_⟩
   ·have hinj : Set.InjOn (fun a => Items.toList.idxOf a) (Items : Set α) := by
     intro a ha b hb heq
     have ha' : a ∈ Items.toList := Finset.mem_toList.mpr ha
     have hb' : b ∈ Items.toList := Finset.mem_toList.mpr hb
     have hla : Items.toList.idxOf a < Items.toList.length := List.idxOf_lt_length_iff.mpr ha'
     have hlb : Items.toList.idxOf b < Items.toList.length := List.idxOf_lt_length_iff.mpr hb'
     have h1 := List.getElem_idxOf hla
     have h2 := List.getElem_idxOf hlb
     rw [← h1, ← h2]
     simp [heq]
    rw [Finset.card_image_of_injOn hinj]
    simp
   ·intro w hw
    have hsm : (R w).card ≤ 1 := hSmall w (by omega) (fun k _ => by omega)
    by_cases hne : (R w).Nonempty
    ·obtain ⟨a, ha⟩ := hne
     refine ⟨Items.toList.idxOf a, fun b hb => ?_⟩
     have hba : b = a := by
      by_contra hne'
      have hle := Finset.card_le_card (show ({b, a} : Finset α) ⊆ R w by
       intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
       rcases hx with rfl | rfl <;> assumption)
      rw [Finset.card_pair hne'] at hle; omega
     subst hba; rfl
    ·refine ⟨0, fun b hb => absurd ⟨b, hb⟩ hne⟩
  | succ m ih =>
   intro hm
   obtain ⟨comp, hcard, hmono⟩ := ih (by omega)
   by_cases hmH : m ∈ H
   ·have hfilt : H.filter (· < m + 1) = insert m (H.filter (· < m)) := by
     ext k; simp only [Finset.mem_filter, Finset.mem_insert]
     constructor
     ·rintro ⟨hk, hlt⟩
      by_cases hkm : k = m
      ·exact Or.inl hkm
      ·exact Or.inr ⟨hk, by omega⟩
     ·rintro (rfl | ⟨hk, hlt⟩)
      ·exact ⟨hmH, by omega⟩
      ·exact ⟨hk, by omega⟩
    have hnotmem : m ∉ H.filter (· < m) := by simp
    obtain ⟨c0, hc0⟩ := hmono (opnd C m 0) (opnd_lt hAO (by omega) 0)
    obtain ⟨c1, hc1⟩ := hmono (opnd C m 1) (opnd_lt hAO (by omega) 1)
    let comp' : α → ℕ := fun a => if comp a = c1 then c0 else comp a
    refine ⟨comp', ?_, ?_⟩
    ·have himg : Items.image comp ⊆ insert c1 (Items.image comp') := by
      intro c hc
      simp only [Finset.mem_image] at hc
      rcases hc with ⟨a, ha, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_image]
      by_cases h : comp a = c1
      ·exact Or.inl h
      ·exact Or.inr ⟨a, ha, by simp [comp', h]⟩
     have hle := Finset.card_le_card himg
     have hle2 := Finset.card_insert_le c1 (Items.image comp')
     rw [hfilt, Finset.card_insert_of_notMem hnotmem]
     omega
    ·intro w hw
     by_cases hlt : w < n + m
     ·obtain ⟨c, hc⟩ := hmono w hlt
      refine ⟨if c = c1 then c0 else c, fun a ha => ?_⟩
      simp only [comp', hc a ha]
     ·have hweq : w = n + m := by omega
      subst hweq
      refine ⟨c0, fun a ha => ?_⟩
      have hmem := hStep m hmH ha
      rw [Finset.mem_union] at hmem
      rcases hmem with h0 | h1
      ·by_cases h : c0 = c1 <;> simp [comp', hc0 a h0, h]
      ·simp only [comp', hc1 a h1, ↓reduceIte]
   ·have hfilt : H.filter (· < m + 1) = H.filter (· < m) := by
     ext k; simp only [Finset.mem_filter]
     constructor
     ·rintro ⟨hk, hlt⟩; exact ⟨hk, by have : k ≠ m := fun h => hmH (h ▸ hk); omega⟩
     ·rintro ⟨hk, hlt⟩; exact ⟨hk, by omega⟩
    refine ⟨comp, by rw [hfilt]; exact hcard, ?_⟩
    intro w hw
    by_cases hlt : w < n + m
    ·exact hmono w hlt
    ·have hweq : w = n + m := by omega
     subst hweq
     have hsm : (R (n + m)).card ≤ 1 := hSmall (n + m) (by omega)
      (fun k hk heq => hmH ((show m = k by omega) ▸ hk))
     by_cases hne : (R (n + m)).Nonempty
     ·obtain ⟨a, ha⟩ := hne
      refine ⟨comp a, fun b hb => ?_⟩
      have hba : b = a := by
       by_contra hne'
       have hle := Finset.card_le_card (show ({b, a} : Finset α) ⊆ R (n + m) by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption)
       rw [Finset.card_pair hne'] at hle; omega
      subst hba; rfl
     ·refine ⟨0, fun b hb => absurd ⟨b, hb⟩ hne⟩
 obtain ⟨comp, hcard, hmono⟩ := haux C.gates.length (le_refl _)
 have hfilt : H.filter (· < C.gates.length) = H :=
  Finset.filter_true_of_mem (fun k hk => hH k hk)
 rw [hfilt] at hcard
 exact ⟨comp, hcard, hmono⟩
lemma mono_card_le {α : Type} [DecidableEq α] {Items S : Finset α} {comp : α → ℕ} {Hcard : ℕ}
  (hcard : Items.card ≤ (Items.image comp).card + Hcard)
  (hSsub : S ⊆ Items) (hSne : S.Nonempty) (hmono : ∃ c, ∀ a ∈ S, comp a = c) :
  S.card ≤ Hcard + 1 := by
 obtain ⟨c, hc⟩ := hmono
 have himg : Items.image comp ⊆ insert c ((Items \ S).image comp) := by
  intro y hy
  simp only [Finset.mem_image] at hy
  rcases hy with ⟨a, ha, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_sdiff]
  by_cases haS : a ∈ S
  ·exact Or.inl (hc a haS)
  ·exact Or.inr ⟨a, ⟨ha, haS⟩, rfl⟩
 have h1 := Finset.card_le_card himg
 have h2 := Finset.card_insert_le c ((Items \ S).image comp)
 have h3 : ((Items \ S).image comp).card ≤ (Items \ S).card := Finset.card_image_le
 have h4 := card_sdiff_eq hSsub
 have h5 := Finset.card_le_card hSsub
 omega
lemma two_mono_card_le {α : Type} [DecidableEq α] {Items S1 S2 : Finset α} {comp : α → ℕ}
  {Hcard : ℕ} (hcard : Items.card ≤ (Items.image comp).card + Hcard)
  (hSsub : S1 ∪ S2 ⊆ Items)
  (hm1 : ∃ c1, ∀ a ∈ S1, comp a = c1) (hm2 : ∃ c2, ∀ a ∈ S2, comp a = c2) :
  (S1 ∪ S2).card ≤ Hcard + 2 := by
 obtain ⟨c1, hc1⟩ := hm1
 obtain ⟨c2, hc2⟩ := hm2
 have himg : Items.image comp ⊆ insert c1 (insert c2 ((Items \ (S1 ∪ S2)).image comp)) := by
  intro y hy
  simp only [Finset.mem_image] at hy
  rcases hy with ⟨a, ha, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_sdiff, Finset.mem_union]
  by_cases ha1 : a ∈ S1
  ·exact Or.inl (hc1 a ha1)
  ·by_cases ha2 : a ∈ S2
   ·exact Or.inr (Or.inl (hc2 a ha2))
   ·exact Or.inr (Or.inr ⟨a, ⟨ha, fun h => h.elim ha1 ha2⟩, rfl⟩)
 have h1 := Finset.card_le_card himg
 have h2 := Finset.card_insert_le c1 (insert c2 ((Items \ (S1 ∪ S2)).image comp))
 have h3 := Finset.card_insert_le c2 ((Items \ (S1 ∪ S2)).image comp)
 have h4 : ((Items \ (S1 ∪ S2)).image comp).card ≤ (Items \ (S1 ∪ S2)).card := Finset.card_image_le
 have h5 := card_sdiff_eq hSsub
 have h6 := Finset.card_le_card hSsub
 omega
def IsFlag {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
  (g : ℕ) (Ci Di : Finset (Fin n)) (z zp : Fin n) : Prop :=
 G.Adj z zp ∧ z ∈ Ci ∧ zp ∈ Di ∧ (∀ c ∈ Ci, G.Adj c zp) ∧ (∀ d ∈ Di, G.Adj d z) ∧
  2 ≤ Ci.card ∧ 2 ≤ Di.card ∧
  ∀ x : Fin n → Bool, gateVal n C g x = (decide (∃ c ∈ Ci, x c = true) && decide (∃ d ∈ Di, x d = true))
def flagEdges {n : ℕ} (Ci Di : Finset (Fin n)) (z zp : Fin n) : Finset (Sym2 (Fin n)) :=
 (Di.image fun d => s(z, d)) ∪ (Ci.image fun c => s(c, zp))
lemma fin2_eq (b : Fin 2) : b = 0 ∨ b = 1 := by
 fin_cases b <;> simp
lemma fin2_sub_eq {a b : Fin 2} (h : a ≠ b) : 1 - a = b := by
 fin_cases a <;> fin_cases b <;> simp_all
lemma bool_eq_of_ne_ne {a b c : Bool} (h1 : a ≠ c) (h2 : b ≠ c) : a = b := by
 cases a <;> cases b <;> cases c <;> simp_all
lemma flag_color_C {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
  {g : ℕ} {Ci Di : Finset (Fin n)} {z zp : Fin n} (hf : IsFlag G C g Ci Di z zp)
  {c : Fin n} (hc : c ∈ Ci) : s c = s z := by
 have h1 := hbip z zp hf.1
 have h2 := hbip c zp (hf.2.2.2.1 c hc)
 cases hz : s z <;> cases hzp : s zp <;> cases hsc : s c <;> simp_all
lemma flag_color_D {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
  {g : ℕ} {Ci Di : Finset (Fin n)} {z zp : Fin n} (hf : IsFlag G C g Ci Di z zp)
  {d : Fin n} (hd : d ∈ Di) : s d = s zp := by
 have h1 := hbip z zp hf.1
 have h2 := hbip d z (hf.2.2.2.2.1 d hd)
 cases hz : s z <;> cases hzp : s zp <;> cases hsd : s d <;> simp_all
lemma flag_disjoint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
  {g : ℕ} {Ci Di : Finset (Fin n)} {z zp : Fin n} (hf : IsFlag G C g Ci Di z zp) :
  Disjoint Ci Di := by
 rw [Finset.disjoint_left]
 intro u huC huD
 have h1 := flag_color_C hbip hf huC
 have h2 := flag_color_D hbip hf huD
 exact hbip z zp hf.1 (h1.symm.trans h2)
lemma flag_nonEdge {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (h4 : NoFourCycle G)
  {g : ℕ} {Ci Di : Finset (Fin n)} {z zp : Fin n} (hf : IsFlag G C g Ci Di z zp)
  {c d : Fin n} (hc : c ∈ Ci) (hcz : c ≠ z) (hd : d ∈ Di) (hdzp : d ≠ zp) :
  ¬ G.Adj c d := by
 intro hadj
 exact hdzp (noFourCycle_unique h4 hcz hadj (hf.2.2.2.2.1 d hd).symm
  (hf.2.2.2.1 c hc) hf.1)
lemma flag_exists_other_C {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {g : ℕ} {Ci Di : Finset (Fin n)} {z zp : Fin n} (hf : IsFlag G C g Ci Di z zp) :
  ∃ c ∈ Ci, c ≠ z := by
 have hlt : 1 < Ci.card := by have := hf.2.2.2.2.2.1; omega
 obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
 by_cases haz : a = z
 ·exact ⟨b, hb, fun hbz => hab (haz.trans hbz.symm)⟩
 ·exact ⟨a, ha, haz⟩
lemma flag_exists_other_D {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {g : ℕ} {Ci Di : Finset (Fin n)} {z zp : Fin n} (hf : IsFlag G C g Ci Di z zp) :
  ∃ d ∈ Di, d ≠ zp := by
 have hlt : 1 < Di.card := by have := hf.2.2.2.2.2.2.1; omega
 obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
 by_cases haz : a = zp
 ·exact ⟨b, hb, fun hbz => hab (haz.trans hbz.symm)⟩
 ·exact ⟨a, ha, haz⟩
lemma flag_pair_edge_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
  {g : ℕ} {Ci Di : Finset (Fin n)} {z zp : Fin n} (hf : IsFlag G C g Ci Di z zp)
  {u v : Fin n} (huv : G.Adj u v) :
  gateVal n C g (pairInput u v) = true ↔ s(u, v) ∈ flagEdges Ci Di z zp := by
 have hdisj := flag_disjoint hbip hf
 rw [hf.2.2.2.2.2.2.2 (pairInput u v), Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
 simp only [pairInput, decide_eq_true_eq, flagEdges, Finset.mem_union, Finset.mem_image, Sym2.eq_iff]
 constructor
 ·rintro ⟨⟨c, hc, rfl | rfl⟩, ⟨d, hd, hdu | hdv⟩⟩
  ·subst hdu; exact absurd hc (Finset.disjoint_right.mp hdisj hd)
  ·subst hdv
   by_cases hcz : c = z
   ·subst hcz; exact Or.inl ⟨d, hd, Or.inl ⟨rfl, rfl⟩⟩
   ·by_cases hdzp : d = zp
    ·subst hdzp; exact Or.inr ⟨c, hc, Or.inl ⟨rfl, rfl⟩⟩
    ·exact absurd huv (flag_nonEdge h4 hf hc hcz hd hdzp)
  ·subst hdu
   by_cases hcz : c = z
   ·subst hcz; exact Or.inl ⟨d, hd, Or.inr ⟨rfl, rfl⟩⟩
   ·by_cases hdzp : d = zp
    ·subst hdzp; exact Or.inr ⟨c, hc, Or.inr ⟨rfl, rfl⟩⟩
    ·exact absurd huv.symm (flag_nonEdge h4 hf hc hcz hd hdzp)
  ·subst hdv; exact absurd hc (Finset.disjoint_right.mp hdisj hd)
 ·rintro (⟨d, hd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨c, hc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
  ·exact ⟨⟨z, hf.2.1, Or.inl rfl⟩, ⟨d, hd, Or.inr rfl⟩⟩
  ·exact ⟨⟨z, hf.2.1, Or.inr rfl⟩, ⟨d, hd, Or.inl rfl⟩⟩
  ·exact ⟨⟨c, hc, Or.inl rfl⟩, ⟨zp, hf.2.2.1, Or.inr rfl⟩⟩
  ·exact ⟨⟨c, hc, Or.inr rfl⟩, ⟨zp, hf.2.2.1, Or.inl rfl⟩⟩
lemma flag_wmax_not_C_other {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (h4 : NoFourCycle G)
  {g : ℕ} {Ci Di : Finset (Fin n)} {z zp : Fin n} (hf : IsFlag G C g Ci Di z zp)
  {c : Fin n} (hc : c ∈ Ci) (hcz : c ≠ z) :
  ¬ (∀ x : Fin n → Bool, gateVal n C g x = true → x c = true → graphFun G ∅ x = true) := by
 intro hw
 obtain ⟨d, hd, hdzp⟩ := flag_exists_other_D hf
 have hval : gateVal n C g (pairInput c d) = true := by
  rw [hf.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨⟨c, hc, by simp [pairInput]⟩, ⟨d, hd, by simp [pairInput]⟩⟩
 have hF := hw (pairInput c d) hval (by simp [pairInput])
 exact flag_nonEdge h4 hf hc hcz hd hdzp ((graphFun_pair_iff c d).mp hF)
lemma flag_wmax_not_D_other {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (h4 : NoFourCycle G)
  {g : ℕ} {Ci Di : Finset (Fin n)} {z zp : Fin n} (hf : IsFlag G C g Ci Di z zp)
  {d : Fin n} (hd : d ∈ Di) (hdzp : d ≠ zp) :
  ¬ (∀ x : Fin n → Bool, gateVal n C g x = true → x d = true → graphFun G ∅ x = true) := by
 intro hw
 obtain ⟨c, hc, hcz⟩ := flag_exists_other_C hf
 have hval : gateVal n C g (pairInput c d) = true := by
  rw [hf.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨⟨c, hc, by simp [pairInput]⟩, ⟨d, hd, by simp [pairInput]⟩⟩
 have hF := hw (pairInput c d) hval (by simp [pairInput])
 exact flag_nonEdge h4 hf hc hcz hd hdzp ((graphFun_pair_iff c d).mp hF)
lemma flag_wmax_adj_D {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
  {g : ℕ} {Ci Di : Finset (Fin n)} {z zp : Fin n} (hf : IsFlag G C g Ci Di z zp)
  {w : Fin n} (hw : ∀ x : Fin n → Bool, gateVal n C g x = true → x w = true → graphFun G ∅ x = true)
  (hsw : s w = s z) {d : Fin n} (hd : d ∈ Di) (hdzp : d ≠ zp) : G.Adj w d := by
 obtain ⟨c, hc, hcz⟩ := flag_exists_other_C hf
 let x : Fin n → Bool := fun v => decide (v = c ∨ v = d ∨ v = w)
 have hg : gateVal n C g x = true := by
  rw [hf.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨⟨c, hc, by simp [x]⟩, ⟨d, hd, by simp [x]⟩⟩
 have hF := (graphFun_iff x).mp (hw x hg (by simp [x]))
 rcases hF with ⟨a, b, hab, ha, hb⟩
 simp only [x, decide_eq_true_eq] at ha hb
 have hsc : s c = s z := flag_color_C hbip hf hc
 have hsd : s d = s zp := flag_color_D hbip hf hd
 have hncd : ¬ G.Adj c d := flag_nonEdge h4 hf hc hcz hd hdzp
 rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
 ·exact absurd hab (G.loopless.irrefl _)
 ·exact absurd hab hncd
 ·exact absurd (hsc.trans hsw.symm) (hbip _ _ hab)
 ·exact absurd hab.symm hncd
 ·exact absurd hab (G.loopless.irrefl _)
 ·exact hab.symm
 ·exact absurd (hsw.trans hsc.symm) (hbip _ _ hab)
 ·exact hab
 ·exact absurd hab (G.loopless.irrefl _)
lemma flag_wmax_adj_C {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
  {g : ℕ} {Ci Di : Finset (Fin n)} {z zp : Fin n} (hf : IsFlag G C g Ci Di z zp)
  {w : Fin n} (hw : ∀ x : Fin n → Bool, gateVal n C g x = true → x w = true → graphFun G ∅ x = true)
  (hsw : s w = s zp) {c : Fin n} (hc : c ∈ Ci) (hcz : c ≠ z) : G.Adj w c := by
 obtain ⟨d, hd, hdzp⟩ := flag_exists_other_D hf
 let x : Fin n → Bool := fun v => decide (v = c ∨ v = d ∨ v = w)
 have hg : gateVal n C g x = true := by
  rw [hf.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨⟨c, hc, by simp [x]⟩, ⟨d, hd, by simp [x]⟩⟩
 have hF := (graphFun_iff x).mp (hw x hg (by simp [x]))
 rcases hF with ⟨a, b, hab, ha, hb⟩
 simp only [x, decide_eq_true_eq] at ha hb
 have hsc : s c = s z := flag_color_C hbip hf hc
 have hsd : s d = s zp := flag_color_D hbip hf hd
 have hncd : ¬ G.Adj c d := flag_nonEdge h4 hf hc hcz hd hdzp
 rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
 ·exact absurd hab (G.loopless.irrefl _)
 ·exact absurd hab hncd
 ·exact hab.symm
 ·exact absurd hab.symm hncd
 ·exact absurd hab (G.loopless.irrefl _)
 ·exact absurd (hsd.trans hsw.symm) (hbip _ _ hab)
 ·exact hab
 ·exact absurd (hsw.trans hsd.symm) (hbip _ _ hab)
 ·exact absurd hab (G.loopless.irrefl _)
lemma top_opnd_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
  {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) :
  ∀ k, opnd C a b = n + k → ¬ BelowF G C k := by
 have ha' := mem_tops_iff.mp ha
 intro k hk hbk
 exact least_no_belowF_and_opnd hL hne ha'.1 ha'.2.1 b (by rw [hk]; exact hbk)
lemma ustar_sub_flagEdges {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
  {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {C1 D1 C2 D2 : Finset (Fin n)} {z1 zp1 z2 zp2 : Fin n}
  (hf1 : IsFlag G C g1 C1 D1 z1 zp1) (hf2 : IsFlag G C g2 C2 D2 z2 zp2) :
  Ustar G C ⊆ flagEdges C1 D1 z1 zp1 ∪ flagEdges C2 D2 z2 zp2 := by
 have hne : ∃ u v : Fin n, G.Adj u v := ⟨z1, zp1, hf1.1⟩
 intro e he
 rw [Ustar, Finset.mem_sdiff] at he
 rcases he with ⟨heG, heNotStar⟩
 induction e using Sym2.ind with
 | _ u v =>
  have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp heG
  have hcx : circuitFun n C (pairInput u v) = true := by
   rw [congrFun hL.2.1 (pairInput u v)]; exact (graphFun_pair_iff u v).mpr huv
  obtain ⟨a, ha, hva⟩ := (circuitFun_iff_exists_top hL hne _).mp hcx
  have ha' := mem_tops_iff.mp ha
  rw [gateVal_eq_wval, wval_gate_and hL.1 _ ha'.1 ha'.2.1, Bool.and_eq_true] at hva
  have hw0 := (not_belowF_wval_eq hL hLift hne hjunk (opnd C a 0)
   (by have := opnd_lt hL.1 ha'.1 0; omega) (top_opnd_not_belowF hL hne ha 0) (pairInput u v)).mp hva.1
  have hw1 := (not_belowF_wval_eq hL hLift hne hjunk (opnd C a 1)
   (by have := opnd_lt hL.1 ha'.1 1; omega) (top_opnd_not_belowF hL hne ha 1) (pairInput u v)).mp hva.2
  have hnotboth : ¬ ((∃ w ∈ side (n := n) C a 0, pairInput u v w = true) ∧
    (∃ w ∈ side (n := n) C a 1, pairInput u v w = true)) := by
   rintro ⟨⟨w0, hw0m, hxw0⟩, ⟨w1, hw1m, hxw1⟩⟩
   apply heNotStar
   simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
   simp only [pairInput, decide_eq_true_eq] at hxw0 hxw1
   have hne_w : w0 ≠ w1 := fun h => by subst h; exact G.loopless.irrefl w0 (top_sides_adj hL.1 ha hw0m hw1m)
   refine ⟨a, ha, (w0, w1), ⟨hw0m, hw1m⟩, ?_⟩
   rw [Sym2.eq_iff]
   rcases hxw0 with rfl | rfl <;> rcases hxw1 with rfl | rfl
   ·exact absurd rfl hne_w
   ·exact Or.inl ⟨rfl, rfl⟩
   ·exact Or.inr ⟨rfl, rfl⟩
   ·exact absurd rfl hne_w
  rw [Finset.mem_union, ← flag_pair_edge_iff hbip h4 hf1 huv, ← flag_pair_edge_iff hbip h4 hf2 huv]
  rcases hw0 with h0 | ⟨_, hg1⟩ | ⟨_, hg2⟩
  ·rcases hw1 with h1 | ⟨_, hg1⟩ | ⟨_, hg2⟩
   ·exact absurd ⟨h0, h1⟩ hnotboth
   ·exact Or.inl hg1
   ·exact Or.inr hg2
  ·exact Or.inl hg1
  ·exact Or.inr hg2
lemma pure_orN_card_ge_two {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
  {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {k : ℕ} (hk : k ∈ orN G C)
  (hn1 : ¬ OrReaches n C (n + k) g1) (hn2 : ¬ OrReaches n C (n + k) g2) :
  2 ≤ (orIn n C (n + k)).card := by
 have hk' := mem_orN_iff.mp hk
 have hval : ∀ x, wval C x (n + k) = true ↔ ∃ u ∈ orIn n C (n + k), x u = true := by
  intro x
  have h := not_belowF_wval_eq hL hLift hne hjunk (n + k) (by omega)
   (fun m hm => by have : m = k := (by omega); subst this; exact hk'.2.2) x
  simpa [hn1, hn2] using h
 have hne_orIn : (orIn n C (n + k)).Nonempty := by
  have hall := (hval (fun _ => true)).mp (wval_allTrue hL.1 (n + k) (by omega))
  rcases hall with ⟨u, hu, _⟩; exact ⟨u, hu⟩
 by_contra hlt
 push Not at hlt
 have hcard1 : (orIn n C (n + k)).card = 1 := by
  have := Finset.Nonempty.card_pos hne_orIn; omega
 obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard1
 apply least_no_equiv_wire hL hne hk'.1 (by omega : u.val < n + k)
 intro x
 apply Bool.eq_iff_iff.mpr
 rw [wval_input C x u.val u.isLt, hval x, hu]
 simp
lemma lam_below_g2_card_ge_two {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
  {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {k : ℕ} (hk : k ∈ lam G C) (hkg2 : k < g2) :
  2 ≤ (orIn n C (n + k)).card := by
 have hk_filt := Finset.mem_filter.mp hk
 have hk_orN := mem_orN_iff.mp hk_filt.1
 have h0ne : (orIn n C (opnd C k 0)).Nonempty := hk_filt.2.1
 have h1ne : (orIn n C (opnd C k 1)).Nonempty := hk_filt.2.2.1
 have horIn_eq := orIn_or_eq_union hL.1 hk_orN.1 hk_orN.2.1
 have hne_k : (orIn n C (n + k)).Nonempty := by
  rw [horIn_eq]; exact h0ne.mono Finset.subset_union_left
 by_contra hlt
 push Not at hlt
 have hcard1 : (orIn n C (n + k)).card = 1 := by
  have := Finset.Nonempty.card_pos hne_k; omega
 obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard1
 have hsub0 : orIn n C (opnd C k 0) ⊆ {u} := by rw [← hu, horIn_eq]; exact Finset.subset_union_left
 have hsub1 : orIn n C (opnd C k 1) ⊆ {u} := by rw [← hu, horIn_eq]; exact Finset.subset_union_right
 have heq0 : orIn n C (opnd C k 0) = {u} := by
  ext v; constructor
  ·exact fun h => hsub0 h
  ·intro hv; rw [Finset.mem_singleton] at hv; subst hv
   obtain ⟨w, hw⟩ := h0ne
   have := Finset.mem_singleton.mp (hsub0 hw); subst this; exact hw
 have heq1 : orIn n C (opnd C k 1) = {u} := by
  ext v; constructor
  ·exact fun h => hsub1 h
  ·intro hv; rw [Finset.mem_singleton] at hv; subst hv
   obtain ⟨w, hw⟩ := h1ne
   have := Finset.mem_singleton.mp (hsub1 hw); subst this; exact hw
 have hn2_0 : ¬ OrReaches n C (opnd C k 0) g2 := fun h => by
  have h1 := orReaches_le h; have h2 := opnd_lt hL.1 hk_orN.1 0; omega
 have hn2_1 : ¬ OrReaches n C (opnd C k 1) g2 := fun h => by
  have h1 := orReaches_le h; have h2 := opnd_lt hL.1 hk_orN.1 1; omega
 have hnb : ∀ b : Fin 2, ∀ m, opnd C k b = n + m → ¬ BelowF G C m := fun b m hm hbm =>
  lift_no_belowF_orN_opnd hL hLift hne hk_orN.1 hk_orN.2.1 hk_orN.2.2 b (by rw [hm]; exact hbm)
 have hv0 : ∀ x, wval C x (opnd C k 0) = true ↔
   x u = true ∨ (OrReaches n C (opnd C k 0) g1 ∧ gateVal n C g1 x = true) := by
  intro x
  have h := not_belowF_wval_eq hL hLift hne hjunk (opnd C k 0)
   (by have := opnd_lt hL.1 hk_orN.1 0; omega) (hnb 0) x
  simpa [heq0, hn2_0] using h
 have hv1 : ∀ x, wval C x (opnd C k 1) = true ↔
   x u = true ∨ (OrReaches n C (opnd C k 1) g1 ∧ gateVal n C g1 x = true) := by
  intro x
  have h := not_belowF_wval_eq hL hLift hne hjunk (opnd C k 1)
   (by have := opnd_lt hL.1 hk_orN.1 1; omega) (hnb 1) x
  simpa [heq1, hn2_1] using h
 by_cases hr0 : OrReaches n C (opnd C k 0) g1
 ·apply least_no_equiv_wire hL hne hk_orN.1 (opnd_lt hL.1 hk_orN.1 0)
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [wval_gate_or hL.1 x hk_orN.1 hk_orN.2.1, Bool.or_eq_true, hv0 x, hv1 x]
  simp [hr0]
  tauto
 ·apply least_no_equiv_wire hL hne hk_orN.1 (opnd_lt hL.1 hk_orN.1 1)
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [wval_gate_or hL.1 x hk_orN.1 hk_orN.2.1, Bool.or_eq_true, hv0 x, hv1 x]
  simp [hr0]
lemma lam_disjoint_ustar {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (hAO : IsAO2 n C) (h4 : NoFourCycle G)
  {v : Fin n} {k : ℕ} (hk : k ∈ lam G C)
  (hsub : ∀ u ∈ orIn n C (n + k), G.Adj v u)
  (hcard : 2 ≤ (orIn n C (n + k)).card) :
  ∀ u ∈ orIn n C (n + k), s(v, u) ∈ starEdges G C := by
 have hk_filt := Finset.mem_filter.mp hk
 rcases hk_filt.2.2.2 with ⟨a, ha, b, hcard1, hreach⟩
 obtain ⟨v', hv'⟩ := Finset.card_eq_one.mp hcard1
 have hsub_side : orIn n C (n + k) ⊆ side (n := n) C a b := orIn_subset_of_orReaches hreach
 obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp (by omega : 1 < (orIn n C (n + k)).card)
 have hadj_v' : ∀ u ∈ orIn n C (n + k), G.Adj v' u := by
  intro u hu
  have hv'm : v' ∈ side (n := n) C a (1 - b) := by rw [hv']; simp
  have hum : u ∈ side (n := n) C a b := hsub_side hu
  fin_cases b
  ·exact (top_sides_adj hAO ha hum hv'm).symm
  ·exact top_sides_adj hAO ha hv'm hum
 have hveq : v = v' := noFourCycle_unique h4 hu12
  (hsub u1 hu1).symm (hsub u2 hu2).symm (hadj_v' u1 hu1).symm (hadj_v' u2 hu2).symm
 subst hveq
 intro u hu
 simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
 have hv'm : v ∈ side (n := n) C a (1 - b) := by rw [hv']; simp
 have hum : u ∈ side (n := n) C a b := hsub_side hu
 fin_cases b
 ·exact ⟨a, ha, (u, v), ⟨hum, hv'm⟩, Sym2.eq_swap⟩
 ·exact ⟨a, ha, (v, u), ⟨hv'm, hum⟩, rfl⟩
lemma g1_operands {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
  {g1 g2 : ℕ} (hlt12 : g1 < g2) (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {C1 D1 : Finset (Fin n)} {z1 zp1 : Fin n} (hf1 : IsFlag G C g1 C1 D1 z1 zp1) :
  (¬ OrReaches n C (opnd C g1 0) g1 ∧ ¬ OrReaches n C (opnd C g1 0) g2 ∧
   ¬ OrReaches n C (opnd C g1 1) g1 ∧ ¬ OrReaches n C (opnd C g1 1) g2) ∧
  ∃ b1 : Fin 2, side (n := n) C g1 b1 = C1 ∧ side (n := n) C g1 (1 - b1) = D1 := by
 have hne : ∃ u v : Fin n, G.Adj u v := ⟨z1, zp1, hf1.1⟩
 have hg1_j := mem_junk_iff.mp ((hjunk g1).mpr (Or.inl rfl))
 have hlt0 := opnd_lt hL.1 hg1_j.1 0
 have hlt1 := opnd_lt hL.1 hg1_j.1 1
 have hn01 : ¬ OrReaches n C (opnd C g1 0) g1 := fun h => by have := h.1; have := orReaches_le h; omega
 have hn02 : ¬ OrReaches n C (opnd C g1 0) g2 := fun h => by have := h.1; have := orReaches_le h; omega
 have hn11 : ¬ OrReaches n C (opnd C g1 1) g1 := fun h => by have := h.1; have := orReaches_le h; omega
 have hn12 : ¬ OrReaches n C (opnd C g1 1) g2 := fun h => by have := h.1; have := orReaches_le h; omega
 refine ⟨⟨hn01, hn02, hn11, hn12⟩, ?_⟩
 have hnb : ∀ b : Fin 2, ∀ m, opnd C g1 b = n + m → ¬ BelowF G C m := fun b m hm hbm =>
  least_no_belowF_and_opnd hL hne hg1_j.1 hg1_j.2.1 b (by rw [hm]; exact hbm)
 have hval : ∀ x : Fin n → Bool,
   ((∃ u ∈ side (n := n) C g1 0, x u = true) ∧ (∃ v ∈ side (n := n) C g1 1, x v = true)) ↔
   ((∃ c ∈ C1, x c = true) ∧ (∃ d ∈ D1, x d = true)) := by
  intro x
  have h0 := not_belowF_wval_eq hL hLift hne hjunk (opnd C g1 0) (by omega) (hnb 0) x
  have h1 := not_belowF_wval_eq hL hLift hne hjunk (opnd C g1 1) (by omega) (hnb 1) x
  have hg := hf1.2.2.2.2.2.2.2 x
  rw [gateVal_eq_wval, wval_gate_and hL.1 x hg1_j.1 hg1_j.2.1] at hg
  have hiff := congrArg (· = true) hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hiff
  rw [← hiff, h0, h1]
  simp [hn01, hn02, hn11, hn12, side]
 have hdisjCD := flag_disjoint hbip hf1
 have hdisjS : Disjoint (side (n := n) C g1 0) (side (n := n) C g1 1) := by
  rw [Finset.disjoint_left]; intro v hv0 hv1
  have h := (hval (fun w => decide (w = v))).mp ⟨⟨v, hv0, by simp⟩, ⟨v, hv1, by simp⟩⟩
  rcases h with ⟨⟨c, hc, hvc⟩, ⟨d, hd, hvd⟩⟩
  simp only [decide_eq_true_eq] at hvc hvd
  subst hvc; subst hvd
  exact Finset.disjoint_left.mp hdisjCD hc hd
 have hpair_iff : ∀ u v : Fin n, u ≠ v →
   (((u ∈ side (n := n) C g1 0 ∧ v ∈ side (n := n) C g1 1) ∨
    (v ∈ side (n := n) C g1 0 ∧ u ∈ side (n := n) C g1 1)) ↔
   ((u ∈ C1 ∧ v ∈ D1) ∨ (v ∈ C1 ∧ u ∈ D1))) := by
  intro u v huv
  have h := hval (pairInput u v)
  simp only [pairInput, decide_eq_true_eq] at h
  constructor
  ·intro hs
   have hcd : (∃ c ∈ C1, c = u ∨ c = v) ∧ (∃ d ∈ D1, d = u ∨ d = v) := by
    apply h.mp
    rcases hs with ⟨hu, hv⟩ | ⟨hv, hu⟩
    ·exact ⟨⟨u, hu, Or.inl rfl⟩, ⟨v, hv, Or.inr rfl⟩⟩
    ·exact ⟨⟨v, hv, Or.inr rfl⟩, ⟨u, hu, Or.inl rfl⟩⟩
   rcases hcd with ⟨⟨c, hc, rfl | rfl⟩, ⟨d, hd, hdu | hdv⟩⟩
   ·subst hdu; exact absurd hc (Finset.disjoint_right.mp hdisjCD hd)
   ·subst hdv; exact Or.inl ⟨hc, hd⟩
   ·subst hdu; exact Or.inr ⟨hc, hd⟩
   ·subst hdv; exact absurd hc (Finset.disjoint_right.mp hdisjCD hd)
  ·intro hcd
   have hs : (∃ a ∈ side (n := n) C g1 0, a = u ∨ a = v) ∧
     (∃ b ∈ side (n := n) C g1 1, b = u ∨ b = v) := by
    apply h.mpr
    rcases hcd with ⟨hu, hv⟩ | ⟨hv, hu⟩
    ·exact ⟨⟨u, hu, Or.inl rfl⟩, ⟨v, hv, Or.inr rfl⟩⟩
    ·exact ⟨⟨v, hv, Or.inr rfl⟩, ⟨u, hu, Or.inl rfl⟩⟩
   rcases hs with ⟨⟨a, ha, rfl | rfl⟩, ⟨b, hb, hbu | hbv⟩⟩
   ·subst hbu; exact absurd ha (Finset.disjoint_right.mp hdisjS hb)
   ·subst hbv; exact Or.inl ⟨ha, hb⟩
   ·subst hbu; exact Or.inr ⟨ha, hb⟩
   ·subst hbv; exact absurd ha (Finset.disjoint_right.mp hdisjS hb)
 have hz_ne : z1 ≠ zp1 := G.ne_of_adj hf1.1
 have hzz := (hpair_iff z1 zp1 hz_ne).mpr (Or.inl ⟨hf1.2.1, hf1.2.2.1⟩)
 rcases hzz with ⟨hz0, hzp1⟩ | ⟨hzp0, hz1⟩
 ·refine ⟨0, ?_, ?_⟩
  ·ext u
   constructor
   ·intro hu
    have hne_u : u ≠ zp1 := fun h => by subst h; exact Finset.disjoint_left.mp hdisjS hu hzp1
    rcases (hpair_iff u zp1 hne_u).mp (Or.inl ⟨hu, hzp1⟩) with ⟨huC, _⟩ | ⟨hzpC, _⟩
    ·exact huC
    ·exact absurd hzpC (Finset.disjoint_right.mp hdisjCD hf1.2.2.1)
   ·intro hu
    have hne_u : u ≠ zp1 := fun h => by subst h; exact Finset.disjoint_left.mp hdisjCD hu hf1.2.2.1
    rcases (hpair_iff u zp1 hne_u).mpr (Or.inl ⟨hu, hf1.2.2.1⟩) with ⟨hu0, _⟩ | ⟨hzp0, _⟩
    ·exact hu0
    ·exact absurd hzp0 (Finset.disjoint_right.mp hdisjS hzp1)
  ·ext v
   simp only [sub_zero]
   constructor
   ·intro hv
    have hne_v : z1 ≠ v := fun h => by subst h; exact Finset.disjoint_left.mp hdisjS hz0 hv
    rcases (hpair_iff z1 v hne_v).mp (Or.inl ⟨hz0, hv⟩) with ⟨_, hvD⟩ | ⟨_, hzD⟩
    ·exact hvD
    ·exact absurd hzD (Finset.disjoint_left.mp hdisjCD hf1.2.1)
   ·intro hv
    have hne_v : z1 ≠ v := fun h => by subst h; exact Finset.disjoint_left.mp hdisjCD hf1.2.1 hv
    rcases (hpair_iff z1 v hne_v).mpr (Or.inl ⟨hf1.2.1, hv⟩) with ⟨_, hv1⟩ | ⟨_, hz1⟩
    ·exact hv1
    ·exact absurd hz1 (Finset.disjoint_left.mp hdisjS hz0)
 ·refine ⟨1, ?_, ?_⟩
  ·ext u
   constructor
   ·intro hu
    have hne_u : u ≠ zp1 := fun h => by subst h; exact Finset.disjoint_left.mp hdisjS hzp0 hu
    rcases (hpair_iff u zp1 hne_u).mp (Or.inr ⟨hzp0, hu⟩) with ⟨huC, _⟩ | ⟨hzpC, _⟩
    ·exact huC
    ·exact absurd hzpC (Finset.disjoint_right.mp hdisjCD hf1.2.2.1)
   ·intro hu
    have hne_u : u ≠ zp1 := fun h => by subst h; exact Finset.disjoint_left.mp hdisjCD hu hf1.2.2.1
    rcases (hpair_iff u zp1 hne_u).mpr (Or.inl ⟨hu, hf1.2.2.1⟩) with ⟨_, hzp1⟩ | ⟨_, hu1⟩
    ·exact absurd hzp1 (Finset.disjoint_left.mp hdisjS hzp0)
    ·exact hu1
  ·ext v
   have h11 : (1 : Fin 2) - 1 = 0 := rfl
   rw [h11]
   constructor
   ·intro hv
    have hne_v : z1 ≠ v := fun h => by subst h; exact Finset.disjoint_left.mp hdisjS hv hz1
    rcases (hpair_iff z1 v hne_v).mp (Or.inr ⟨hv, hz1⟩) with ⟨_, hvD⟩ | ⟨_, hzD⟩
    ·exact hvD
    ·exact absurd hzD (Finset.disjoint_left.mp hdisjCD hf1.2.1)
   ·intro hv
    have hne_v : z1 ≠ v := fun h => by subst h; exact Finset.disjoint_left.mp hdisjCD hf1.2.1 hv
    rcases (hpair_iff z1 v hne_v).mpr (Or.inl ⟨hf1.2.1, hv⟩) with ⟨hz0, _⟩ | ⟨hv0, _⟩
    ·exact absurd hz0 (Finset.disjoint_right.mp hdisjS hz1)
    ·exact hv0
lemma g2_operands {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
  {g1 g2 : ℕ} (hlt12 : g1 < g2) (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {C1 D1 C2 D2 : Finset (Fin n)} {z1 zp1 z2 zp2 : Fin n}
  (hf1 : IsFlag G C g1 C1 D1 z1 zp1) (hf2 : IsFlag G C g2 C2 D2 z2 zp2)
  (hsz : s z1 = s z2) (hszp : s zp1 = s zp2) :
  ¬ OrReaches n C (opnd C g2 0) g2 ∧ ¬ OrReaches n C (opnd C g2 1) g2 ∧
  ∃ b2 : Fin 2,
   side (n := n) C g2 b2 ⊆ C2 ∧ side (n := n) C g2 (1 - b2) ⊆ D2 ∧
   (OrReaches n C (opnd C g2 b2) g1 → C1 ⊆ C2 ∧ zp1 = zp2 ∧ C2 = C1 ∪ side (n := n) C g2 b2) ∧
   (¬ OrReaches n C (opnd C g2 b2) g1 → side (n := n) C g2 b2 = C2) ∧
   (OrReaches n C (opnd C g2 (1 - b2)) g1 → D1 ⊆ D2 ∧ z1 = z2 ∧ D2 = D1 ∪ side (n := n) C g2 (1 - b2)) ∧
   (¬ OrReaches n C (opnd C g2 (1 - b2)) g1 → side (n := n) C g2 (1 - b2) = D2) := by
 have hne : ∃ u v : Fin n, G.Adj u v := ⟨z1, zp1, hf1.1⟩
 have hg2_j := mem_junk_iff.mp ((hjunk g2).mpr (Or.inr rfl))
 have hlt0 := opnd_lt hL.1 hg2_j.1 0
 have hlt1 := opnd_lt hL.1 hg2_j.1 1
 have hn02 : ¬ OrReaches n C (opnd C g2 0) g2 := fun h => by have := orReaches_le h; omega
 have hn12 : ¬ OrReaches n C (opnd C g2 1) g2 := fun h => by have := orReaches_le h; omega
 refine ⟨hn02, hn12, ?_⟩
 have hnb : ∀ b : Fin 2, ∀ m, opnd C g2 b = n + m → ¬ BelowF G C m := fun b m hm hbm =>
  least_no_belowF_and_opnd hL hne hg2_j.1 hg2_j.2.1 b (by rw [hm]; exact hbm)
 have hval : ∀ x,
   (((∃ u ∈ side (n := n) C g2 0, x u = true) ∨ (OrReaches n C (opnd C g2 0) g1 ∧ gateVal n C g1 x = true)) ∧
    ((∃ v ∈ side (n := n) C g2 1, x v = true) ∨ (OrReaches n C (opnd C g2 1) g1 ∧ gateVal n C g1 x = true))) ↔
   ((∃ c ∈ C2, x c = true) ∧ (∃ d ∈ D2, x d = true)) := by
  intro x
  have h0 := not_belowF_wval_eq hL hLift hne hjunk (opnd C g2 0) (by omega) (hnb 0) x
  have h1 := not_belowF_wval_eq hL hLift hne hjunk (opnd C g2 1) (by omega) (hnb 1) x
  have hg := hf2.2.2.2.2.2.2.2 x
  rw [gateVal_eq_wval, wval_gate_and hL.1 x hg2_j.1 hg2_j.2.1] at hg
  have hiff := congrArg (· = true) hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hiff
  rw [← hiff, h0, h1]
  simp [hn02, hn12, side]
 have hdisj2 := flag_disjoint hbip hf2
 have hdisj1 := flag_disjoint hbip hf1
 have hcol_ne : s z2 ≠ s zp2 := hbip z2 zp2 hf2.1
 have hsep_C : ∀ b : Fin 2, OrReaches n C (opnd C g2 b) g1 →
   (∃ d ∈ D2, d ∈ side (n := n) C g2 (1 - b)) → C1 ⊆ C2 := by
  intro b hrb ⟨d2, hd2, hd2s⟩ c1 hc1
  let x : Fin n → Bool := fun v => decide (v = c1 ∨ v = zp1 ∨ v = d2)
  have hg1x : gateVal n C g1 x = true := by
   rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
   exact ⟨⟨c1, hc1, by simp [x]⟩, ⟨zp1, hf1.2.2.1, by simp [x]⟩⟩
  have hside_other : ∃ v ∈ side (n := n) C g2 (1 - b), x v = true := ⟨d2, hd2s, by simp [x]⟩
  have h2 : (∃ c ∈ C2, x c = true) ∧ (∃ d ∈ D2, x d = true) := by
   apply (hval x).mp
   fin_cases b
   ·exact ⟨Or.inr ⟨hrb, hg1x⟩, Or.inl hside_other⟩
   ·exact ⟨Or.inl hside_other, Or.inr ⟨hrb, hg1x⟩⟩
  rcases h2.1 with ⟨c, hcC2, hxc⟩
  simp only [x, decide_eq_true_eq] at hxc
  have hsc : s c = s z2 := flag_color_C hbip hf2 hcC2
  rcases hxc with rfl | rfl | rfl
  ·exact hcC2
  ·exact absurd (hsc.symm.trans hszp) hcol_ne
  ·exact absurd (hsc.symm.trans (flag_color_D hbip hf2 hd2)) hcol_ne
 have hsep_D : ∀ b : Fin 2, OrReaches n C (opnd C g2 b) g1 →
   (∃ c ∈ C2, c ∈ side (n := n) C g2 (1 - b)) → D1 ⊆ D2 := by
  intro b hrb ⟨c2, hc2, hc2s⟩ d1 hd1
  let x : Fin n → Bool := fun v => decide (v = z1 ∨ v = d1 ∨ v = c2)
  have hg1x : gateVal n C g1 x = true := by
   rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
   exact ⟨⟨z1, hf1.2.1, by simp [x]⟩, ⟨d1, hd1, by simp [x]⟩⟩
  have hside_other : ∃ v ∈ side (n := n) C g2 (1 - b), x v = true := ⟨c2, hc2s, by simp [x]⟩
  have h2 : (∃ c ∈ C2, x c = true) ∧ (∃ d ∈ D2, x d = true) := by
   apply (hval x).mp
   fin_cases b
   ·exact ⟨Or.inr ⟨hrb, hg1x⟩, Or.inl hside_other⟩
   ·exact ⟨Or.inl hside_other, Or.inr ⟨hrb, hg1x⟩⟩
  rcases h2.2 with ⟨d, hdD2, hxd⟩
  simp only [x, decide_eq_true_eq] at hxd
  have hsd : s d = s zp2 := flag_color_D hbip hf2 hdD2
  rcases hxd with rfl | rfl | rfl
  ·exact absurd (hsz.symm.trans hsd) hcol_ne
  ·exact hdD2
  ·exact absurd ((flag_color_C hbip hf2 hc2).symm.trans hsd) hcol_ne
 have hC_eq_zp : C1 ⊆ C2 → zp1 = zp2 := by
  intro hsub
  obtain ⟨c, hc, hcz⟩ := flag_exists_other_C hf1
  exact noFourCycle_unique h4 hcz (hf1.2.2.2.1 c hc) hf1.1
   (hf2.2.2.2.1 c (hsub hc)) (hf2.2.2.2.1 z1 (hsub hf1.2.1))
 have hD_eq_z : D1 ⊆ D2 → z1 = z2 := by
  intro hsub
  obtain ⟨d, hd, hdzp⟩ := flag_exists_other_D hf1
  exact noFourCycle_unique h4 hdzp (hf1.2.2.2.2.1 d hd) hf1.1.symm
   (hf2.2.2.2.2.1 d (hsub hd)) (hf2.2.2.2.2.1 zp1 (hsub hf1.2.2.1))
 have hnot_emp : ∀ b : Fin 2, side (n := n) C g2 b = ∅ → OrReaches n C (opnd C g2 b) g1 := by
  intro b hemp
  by_contra hnr
  have h := (hval (fun _ => true)).mpr ⟨⟨z2, hf2.2.1, rfl⟩, ⟨zp2, hf2.2.2.1, rfl⟩⟩
  fin_cases b
  ·dsimp at hemp hnr
   rcases h.1 with ⟨u, hu, _⟩ | ⟨hr, _⟩
   ·rw [hemp] at hu; exact Finset.notMem_empty _ hu
   ·exact hnr hr
  ·dsimp at hemp hnr
   rcases h.2 with ⟨u, hu, _⟩ | ⟨hr, _⟩
   ·rw [hemp] at hu; exact Finset.notMem_empty _ hu
   ·exact hnr hr
 have hdisjS : Disjoint (side (n := n) C g2 0) (side (n := n) C g2 1) := by
  rw [Finset.disjoint_left]; intro v hv0 hv1
  have h := (hval (fun w => decide (w = v))).mp ⟨Or.inl ⟨v, hv0, by simp⟩, Or.inl ⟨v, hv1, by simp⟩⟩
  rcases h with ⟨⟨c, hc, hvc⟩, ⟨d, hd, hvd⟩⟩
  simp only [decide_eq_true_eq] at hvc hvd; subst hvc; subst hvd
  exact Finset.disjoint_left.mp hdisj2 hc hd
 have hcross : ∀ u ∈ side (n := n) C g2 0, ∀ v ∈ side (n := n) C g2 1,
   (u ∈ C2 ∧ v ∈ D2) ∨ (u ∈ D2 ∧ v ∈ C2) := by
  intro u hu v hv
  have h := (hval (pairInput u v)).mp
   ⟨Or.inl ⟨u, hu, by simp [pairInput]⟩, Or.inl ⟨v, hv, by simp [pairInput]⟩⟩
  simp only [pairInput, decide_eq_true_eq] at h
  rcases h with ⟨⟨c, hc, rfl | rfl⟩, ⟨d, hd, hdu | hdv⟩⟩
  ·subst hdu; exact absurd hc (Finset.disjoint_right.mp hdisj2 hd)
  ·subst hdv; exact Or.inl ⟨hc, hd⟩
  ·subst hdu; exact Or.inr ⟨hd, hc⟩
  ·subst hdv; exact absurd hc (Finset.disjoint_right.mp hdisj2 hd)
 have hg12_ne_fun : ∃ x, gateVal n C g1 x ≠ gateVal n C g2 x := by
  by_contra hall; push Not at hall
  exact least_no_equiv_wire hL hne hg2_j.1 (by omega : n + g1 < n + g2) hall
 have hex_orient : ∃ b2 : Fin 2, side (n := n) C g2 b2 ⊆ C2 ∧ side (n := n) C g2 (1 - b2) ⊆ D2 := by
  by_cases h0ne : (side (n := n) C g2 0).Nonempty
  ·by_cases h1ne : (side (n := n) C g2 1).Nonempty
   ·obtain ⟨u0, hu0⟩ := h0ne
    obtain ⟨v0, hv0⟩ := h1ne
    rcases hcross u0 hu0 v0 hv0 with ⟨hu0C, hv0D⟩ | ⟨hu0D, hv0C⟩
    ·refine ⟨0, ?_, ?_⟩
     ·intro u hu
      rcases hcross u hu v0 hv0 with ⟨huC, _⟩ | ⟨_, hv0C⟩
      ·exact huC
      ·exact absurd hv0C (Finset.disjoint_right.mp hdisj2 hv0D)
     ·intro v hv
      simp only [sub_zero] at hv
      rcases hcross u0 hu0 v hv with ⟨_, hvD⟩ | ⟨hu0D, _⟩
      ·exact hvD
      ·exact absurd hu0D (Finset.disjoint_left.mp hdisj2 hu0C)
    ·refine ⟨1, ?_, ?_⟩
     ·intro v hv
      rcases hcross u0 hu0 v hv with ⟨hu0C, _⟩ | ⟨_, hvC⟩
      ·exact absurd hu0C (Finset.disjoint_right.mp hdisj2 hu0D)
      ·exact hvC
     ·intro u hu
      have h11 : (1 : Fin 2) - 1 = 0 := rfl; rw [h11] at hu
      rcases hcross u hu v0 hv0 with ⟨_, hv0D⟩ | ⟨huD, _⟩
      ·exact absurd hv0D (Finset.disjoint_left.mp hdisj2 hv0C)
      ·exact huD
   ·have h1emp : side (n := n) C g2 1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h1ne
    have hr1 : OrReaches n C (opnd C g2 1) g1 := hnot_emp 1 h1emp
    have hle1 : ∀ x, gateVal n C g2 x = true → gateVal n C g1 x = true := by
     intro x hx
     have h := (hval x).mpr (by
      rw [hf2.2.2.2.2.2.2.2] at hx; simpa [Bool.and_eq_true, decide_eq_true_eq] using hx)
     rcases h.2 with ⟨v, hv, _⟩ | ⟨_, hg1⟩
     ·rw [h1emp] at hv; exact absurd hv (Finset.notMem_empty _)
     ·exact hg1
    have hC2sub1 : C2 ⊆ C1 := by
     intro c hc
     have h1 := hle1 (pairInput c zp2) (by
      rw [hf2.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨⟨c, hc, by simp [pairInput]⟩, ⟨zp2, hf2.2.2.1, by simp [pairInput]⟩⟩)
     rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h1
     rcases h1.1 with ⟨c', hc', hcc'⟩
     simp only [pairInput, decide_eq_true_eq] at hcc'
     rcases hcc' with rfl | rfl
     ·exact hc'
     ·exact absurd ((flag_color_C hbip hf1 hc').trans hsz).symm hcol_ne
    have hD2sub1 : D2 ⊆ D1 := by
     intro d hd
     have h1 := hle1 (pairInput z2 d) (by
      rw [hf2.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨⟨z2, hf2.2.1, by simp [pairInput]⟩, ⟨d, hd, by simp [pairInput]⟩⟩)
     rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h1
     rcases h1.2 with ⟨d', hd', hdd'⟩
     simp only [pairInput, decide_eq_true_eq] at hdd'
     rcases hdd' with rfl | rfl
     ·exact absurd ((flag_color_D hbip hf1 hd').trans hszp) (hsz.symm ▸ hcol_ne)
     ·exact hd'
    have hu_mem : ∀ u ∈ side (n := n) C g2 0, (u ∈ C2 ∧ D1 ⊆ D2) ∨ (u ∈ D2 ∧ C1 ⊆ C2) := by
     intro u hu
     by_cases hsu : s u = s z2
     ·left
      have hD : D1 ⊆ D2 := by
       intro d1 hd1
       let x : Fin n → Bool := fun w => decide (w = u ∨ w = z1 ∨ w = d1)
       have hg1x : gateVal n C g1 x = true := by
        rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨⟨z1, hf1.2.1, by simp [x]⟩, ⟨d1, hd1, by simp [x]⟩⟩
       have h2 := (hval x).mp ⟨Or.inl ⟨u, hu, by simp [x]⟩, Or.inr ⟨hr1, hg1x⟩⟩
       rcases h2.2 with ⟨d, hdD2, hxd⟩
       simp only [x, decide_eq_true_eq] at hxd
       have hsd := flag_color_D hbip hf2 hdD2
       rcases hxd with rfl | rfl | rfl
       ·exact absurd (hsu.symm.trans hsd) hcol_ne
       ·exact absurd (hsz.symm.trans hsd) hcol_ne
       ·exact hdD2
      have huC2 : u ∈ C2 := by
       have hD_eq : D1 = D2 := Finset.Subset.antisymm hD hD2sub1
       have hC_ne : C1 ≠ C2 := by
        intro heq
        rcases hg12_ne_fun with ⟨x, hx⟩
        apply hx
        rw [hf1.2.2.2.2.2.2.2, hf2.2.2.2.2.2.2.2, heq, hD_eq]
       have hex_c : ∃ c1 ∈ C1, c1 ∉ C2 := by
        by_contra hno; push Not at hno
        exact hC_ne (Finset.Subset.antisymm hno hC2sub1)
       obtain ⟨c1, hc1, hc1n⟩ := hex_c
       let x : Fin n → Bool := fun w => decide (w = u ∨ w = c1 ∨ w = zp1)
       have hg1x : gateVal n C g1 x = true := by
        rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨⟨c1, hc1, by simp [x]⟩, ⟨zp1, hf1.2.2.1, by simp [x]⟩⟩
       have h2 := (hval x).mp ⟨Or.inl ⟨u, hu, by simp [x]⟩, Or.inr ⟨hr1, hg1x⟩⟩
       rcases h2.1 with ⟨c, hcC2, hxc⟩
       simp only [x, decide_eq_true_eq] at hxc
       rcases hxc with rfl | rfl | rfl
       ·exact hcC2
       ·exact absurd hcC2 hc1n
       ·exact absurd ((flag_color_C hbip hf2 hcC2).symm.trans hszp) hcol_ne
      exact ⟨huC2, hD⟩
     ·right
      have hsu' : s u = s zp2 := by cases hu' : s u <;> cases hz' : s z2 <;> cases hzp' : s zp2 <;> simp_all
      have hC : C1 ⊆ C2 := by
       intro c1 hc1
       let x : Fin n → Bool := fun w => decide (w = u ∨ w = c1 ∨ w = zp1)
       have hg1x : gateVal n C g1 x = true := by
        rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨⟨c1, hc1, by simp [x]⟩, ⟨zp1, hf1.2.2.1, by simp [x]⟩⟩
       have h2 := (hval x).mp ⟨Or.inl ⟨u, hu, by simp [x]⟩, Or.inr ⟨hr1, hg1x⟩⟩
       rcases h2.1 with ⟨c, hcC2, hxc⟩
       simp only [x, decide_eq_true_eq] at hxc
       have hsc := flag_color_C hbip hf2 hcC2
       rcases hxc with rfl | rfl | rfl
       ·exact absurd (hsu'.symm.trans hsc).symm hcol_ne
       ·exact hcC2
       ·exact absurd (hszp.symm.trans hsc).symm hcol_ne
      have huD2 : u ∈ D2 := by
       have hC_eq : C1 = C2 := Finset.Subset.antisymm hC hC2sub1
       have hD_ne : D1 ≠ D2 := by
        intro heq
        rcases hg12_ne_fun with ⟨x, hx⟩
        apply hx
        rw [hf1.2.2.2.2.2.2.2, hf2.2.2.2.2.2.2.2, hC_eq, heq]
       have hex_d : ∃ d1 ∈ D1, d1 ∉ D2 := by
        by_contra hno; push Not at hno
        exact hD_ne (Finset.Subset.antisymm hno hD2sub1)
       obtain ⟨d1, hd1, hd1n⟩ := hex_d
       let x : Fin n → Bool := fun w => decide (w = u ∨ w = z1 ∨ w = d1)
       have hg1x : gateVal n C g1 x = true := by
        rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨⟨z1, hf1.2.1, by simp [x]⟩, ⟨d1, hd1, by simp [x]⟩⟩
       have h2 := (hval x).mp ⟨Or.inl ⟨u, hu, by simp [x]⟩, Or.inr ⟨hr1, hg1x⟩⟩
       rcases h2.2 with ⟨d, hdD2, hxd⟩
       simp only [x, decide_eq_true_eq] at hxd
       rcases hxd with rfl | rfl | rfl
       ·exact hdD2
       ·exact absurd (hsz.symm.trans (flag_color_D hbip hf2 hdD2)) hcol_ne
       ·exact absurd hdD2 hd1n
      exact ⟨huD2, hC⟩
    obtain ⟨u0, hu0⟩ := h0ne
    rcases hu_mem u0 hu0 with ⟨hu0C, hDsub⟩ | ⟨hu0D, hCsub⟩
    ·refine ⟨0, ?_, by simp [h1emp]⟩
     intro u hu
     rcases hu_mem u hu with ⟨huC, _⟩ | ⟨_, hCsub⟩
     ·exact huC
     ·exfalso
      have hCeq : C1 = C2 := Finset.Subset.antisymm hCsub hC2sub1
      have hDeq : D1 = D2 := Finset.Subset.antisymm hDsub hD2sub1
      rcases hg12_ne_fun with ⟨x, hx⟩
      exact hx (by rw [hf1.2.2.2.2.2.2.2, hf2.2.2.2.2.2.2.2, hCeq, hDeq])
    ·refine ⟨1, by simp [h1emp], ?_⟩
     have h11 : (1 : Fin 2) - 1 = 0 := rfl; rw [h11]
     intro u hu
     rcases hu_mem u hu with ⟨_, hDsub⟩ | ⟨huD, _⟩
     ·exfalso
      have hCeq : C1 = C2 := Finset.Subset.antisymm hCsub hC2sub1
      have hDeq : D1 = D2 := Finset.Subset.antisymm hDsub hD2sub1
      rcases hg12_ne_fun with ⟨x, hx⟩
      exact hx (by rw [hf1.2.2.2.2.2.2.2, hf2.2.2.2.2.2.2.2, hCeq, hDeq])
     ·exact huD
  ·have h0emp : side (n := n) C g2 0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h0ne
   have hr0 : OrReaches n C (opnd C g2 0) g1 := hnot_emp 0 h0emp
   by_cases h1ne : (side (n := n) C g2 1).Nonempty
   ·
    have hle1 : ∀ x, gateVal n C g2 x = true → gateVal n C g1 x = true := by
     intro x hx
     have h := (hval x).mpr (by
      rw [hf2.2.2.2.2.2.2.2] at hx; simpa [Bool.and_eq_true, decide_eq_true_eq] using hx)
     rcases h.1 with ⟨v, hv, _⟩ | ⟨_, hg1⟩
     ·rw [h0emp] at hv; exact absurd hv (Finset.notMem_empty _)
     ·exact hg1
    have hC2sub1 : C2 ⊆ C1 := by
     intro c hc
     have h1 := hle1 (pairInput c zp2) (by
      rw [hf2.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨⟨c, hc, by simp [pairInput]⟩, ⟨zp2, hf2.2.2.1, by simp [pairInput]⟩⟩)
     rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h1
     rcases h1.1 with ⟨c', hc', hcc'⟩
     simp only [pairInput, decide_eq_true_eq] at hcc'
     rcases hcc' with rfl | rfl
     ·exact hc'
     ·exact absurd ((flag_color_C hbip hf1 hc').trans hsz).symm hcol_ne
    have hD2sub1 : D2 ⊆ D1 := by
     intro d hd
     have h1 := hle1 (pairInput z2 d) (by
      rw [hf2.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨⟨z2, hf2.2.1, by simp [pairInput]⟩, ⟨d, hd, by simp [pairInput]⟩⟩)
     rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h1
     rcases h1.2 with ⟨d', hd', hdd'⟩
     simp only [pairInput, decide_eq_true_eq] at hdd'
     rcases hdd' with rfl | rfl
     ·exact absurd ((flag_color_D hbip hf1 hd').trans hszp) (hsz.symm ▸ hcol_ne)
     ·exact hd'
    have hu_mem : ∀ u ∈ side (n := n) C g2 1, (u ∈ C2 ∧ D1 ⊆ D2) ∨ (u ∈ D2 ∧ C1 ⊆ C2) := by
     intro u hu
     by_cases hsu : s u = s z2
     ·left
      have hD : D1 ⊆ D2 := by
       intro d1 hd1
       let x : Fin n → Bool := fun w => decide (w = u ∨ w = z1 ∨ w = d1)
       have hg1x : gateVal n C g1 x = true := by
        rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨⟨z1, hf1.2.1, by simp [x]⟩, ⟨d1, hd1, by simp [x]⟩⟩
       have h2 := (hval x).mp ⟨Or.inr ⟨hr0, hg1x⟩, Or.inl ⟨u, hu, by simp [x]⟩⟩
       rcases h2.2 with ⟨d, hdD2, hxd⟩
       simp only [x, decide_eq_true_eq] at hxd
       have hsd := flag_color_D hbip hf2 hdD2
       rcases hxd with rfl | rfl | rfl
       ·exact absurd (hsu.symm.trans hsd) hcol_ne
       ·exact absurd (hsz.symm.trans hsd) hcol_ne
       ·exact hdD2
      have huC2 : u ∈ C2 := by
       have hD_eq : D1 = D2 := Finset.Subset.antisymm hD hD2sub1
       have hC_ne : C1 ≠ C2 := by
        intro heq; rcases hg12_ne_fun with ⟨x, hx⟩
        exact hx (by rw [hf1.2.2.2.2.2.2.2, hf2.2.2.2.2.2.2.2, heq, hD_eq])
       have hex_c : ∃ c1 ∈ C1, c1 ∉ C2 := by
        by_contra hno; push Not at hno; exact hC_ne (Finset.Subset.antisymm hno hC2sub1)
       obtain ⟨c1, hc1, hc1n⟩ := hex_c
       let x : Fin n → Bool := fun w => decide (w = u ∨ w = c1 ∨ w = zp1)
       have hg1x : gateVal n C g1 x = true := by
        rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨⟨c1, hc1, by simp [x]⟩, ⟨zp1, hf1.2.2.1, by simp [x]⟩⟩
       have h2 := (hval x).mp ⟨Or.inr ⟨hr0, hg1x⟩, Or.inl ⟨u, hu, by simp [x]⟩⟩
       rcases h2.1 with ⟨c, hcC2, hxc⟩
       simp only [x, decide_eq_true_eq] at hxc
       rcases hxc with rfl | rfl | rfl
       ·exact hcC2
       ·exact absurd hcC2 hc1n
       ·exact absurd ((flag_color_C hbip hf2 hcC2).symm.trans hszp) hcol_ne
      exact ⟨huC2, hD⟩
     ·right
      have hsu' : s u = s zp2 := by cases hu' : s u <;> cases hz' : s z2 <;> cases hzp' : s zp2 <;> simp_all
      have hC : C1 ⊆ C2 := by
       intro c1 hc1
       let x : Fin n → Bool := fun w => decide (w = u ∨ w = c1 ∨ w = zp1)
       have hg1x : gateVal n C g1 x = true := by
        rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨⟨c1, hc1, by simp [x]⟩, ⟨zp1, hf1.2.2.1, by simp [x]⟩⟩
       have h2 := (hval x).mp ⟨Or.inr ⟨hr0, hg1x⟩, Or.inl ⟨u, hu, by simp [x]⟩⟩
       rcases h2.1 with ⟨c, hcC2, hxc⟩
       simp only [x, decide_eq_true_eq] at hxc
       have hsc := flag_color_C hbip hf2 hcC2
       rcases hxc with rfl | rfl | rfl
       ·exact absurd (hsu'.symm.trans hsc).symm hcol_ne
       ·exact hcC2
       ·exact absurd (hszp.symm.trans hsc).symm hcol_ne
      have huD2 : u ∈ D2 := by
       have hC_eq : C1 = C2 := Finset.Subset.antisymm hC hC2sub1
       have hD_ne : D1 ≠ D2 := by
        intro heq; rcases hg12_ne_fun with ⟨x, hx⟩
        exact hx (by rw [hf1.2.2.2.2.2.2.2, hf2.2.2.2.2.2.2.2, hC_eq, heq])
       have hex_d : ∃ d1 ∈ D1, d1 ∉ D2 := by
        by_contra hno; push Not at hno; exact hD_ne (Finset.Subset.antisymm hno hD2sub1)
       obtain ⟨d1, hd1, hd1n⟩ := hex_d
       let x : Fin n → Bool := fun w => decide (w = u ∨ w = z1 ∨ w = d1)
       have hg1x : gateVal n C g1 x = true := by
        rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨⟨z1, hf1.2.1, by simp [x]⟩, ⟨d1, hd1, by simp [x]⟩⟩
       have h2 := (hval x).mp ⟨Or.inr ⟨hr0, hg1x⟩, Or.inl ⟨u, hu, by simp [x]⟩⟩
       rcases h2.2 with ⟨d, hdD2, hxd⟩
       simp only [x, decide_eq_true_eq] at hxd
       rcases hxd with rfl | rfl | rfl
       ·exact hdD2
       ·exact absurd (hsz.symm.trans (flag_color_D hbip hf2 hdD2)) hcol_ne
       ·exact absurd hdD2 hd1n
      exact ⟨huD2, hC⟩
    obtain ⟨u0, hu0⟩ := h1ne
    rcases hu_mem u0 hu0 with ⟨hu0C, hDsub⟩ | ⟨hu0D, hCsub⟩
    ·refine ⟨1, ?_, by simp [h0emp]⟩
     intro u hu
     rcases hu_mem u hu with ⟨huC, _⟩ | ⟨_, hCsub⟩
     ·exact huC
     ·exfalso
      have hCeq : C1 = C2 := Finset.Subset.antisymm hCsub hC2sub1
      have hDeq : D1 = D2 := Finset.Subset.antisymm hDsub hD2sub1
      rcases hg12_ne_fun with ⟨x, hx⟩
      exact hx (by rw [hf1.2.2.2.2.2.2.2, hf2.2.2.2.2.2.2.2, hCeq, hDeq])
    ·refine ⟨0, by simp [h0emp], ?_⟩
     simp only [sub_zero]
     intro u hu
     rcases hu_mem u hu with ⟨_, hDsub⟩ | ⟨huD, _⟩
     ·exfalso
      have hCeq : C1 = C2 := Finset.Subset.antisymm hCsub hC2sub1
      have hDeq : D1 = D2 := Finset.Subset.antisymm hDsub hD2sub1
      rcases hg12_ne_fun with ⟨x, hx⟩
      exact hx (by rw [hf1.2.2.2.2.2.2.2, hf2.2.2.2.2.2.2.2, hCeq, hDeq])
     ·exact huD
   ·
    exfalso
    have h1emp : side (n := n) C g2 1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h1ne
    have hr1 : OrReaches n C (opnd C g2 1) g1 := hnot_emp 1 h1emp
    rcases hg12_ne_fun with ⟨x, hx⟩
    apply hx
    apply Bool.eq_iff_iff.mpr
    rw [hf2.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, ← hval x]
    simp [h0emp, h1emp, hr0, hr1]
 obtain ⟨b2, hsubC, hsubD⟩ := hex_orient
 refine ⟨b2, hsubC, hsubD, ?_, ?_, ?_, ?_⟩
 ·intro hrb
  have hC12 : C1 ⊆ C2 := by
   by_cases hneD : (side (n := n) C g2 (1 - b2)).Nonempty
   ·obtain ⟨d, hd⟩ := hneD
    exact hsep_C b2 hrb ⟨d, hsubD hd, hd⟩
   ·have hempD : side (n := n) C g2 (1 - b2) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hneD
    have hrb' := hnot_emp (1 - b2) hempD
    intro c1 hc1
    have h2 := (hval (pairInput c1 zp1)).mp (by
     have hg1x : gateVal n C g1 (pairInput c1 zp1) = true := by
      rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨⟨c1, hc1, by simp [pairInput]⟩, ⟨zp1, hf1.2.2.1, by simp [pairInput]⟩⟩
     fin_cases b2
     ·exact ⟨Or.inr ⟨hrb, hg1x⟩, Or.inr ⟨hrb', hg1x⟩⟩
     ·exact ⟨Or.inr ⟨hrb', hg1x⟩, Or.inr ⟨hrb, hg1x⟩⟩)
    rcases h2.1 with ⟨c, hcC2, hxc⟩
    simp only [pairInput, decide_eq_true_eq] at hxc
    rcases hxc with rfl | rfl
    ·exact hcC2
    ·exact absurd ((flag_color_C hbip hf2 hcC2).symm.trans hszp) hcol_ne
  refine ⟨hC12, hC_eq_zp hC12, ?_⟩
  apply Finset.Subset.antisymm
  ·intro c hc
   rw [Finset.mem_union]
   by_cases hcS : c ∈ side (n := n) C g2 b2
   ·exact Or.inr hcS
   ·left
    have h := (hval (pairInput c zp2)).mpr
     ⟨⟨c, hc, by simp [pairInput]⟩, ⟨zp2, hf2.2.2.1, by simp [pairInput]⟩⟩
    have hside : (∃ u ∈ side (n := n) C g2 b2, pairInput c zp2 u = true) ∨
      (OrReaches n C (opnd C g2 b2) g1 ∧ gateVal n C g1 (pairInput c zp2) = true) := by
     fin_cases b2
     ·exact h.1
     ·exact h.2
    rcases hside with ⟨u, hu, hxu⟩ | ⟨_, hg1x⟩
    ·simp only [pairInput, decide_eq_true_eq] at hxu
     rcases hxu with rfl | rfl
     ·exact absurd hu hcS
     ·exact absurd (hsubC hu) (Finset.disjoint_right.mp hdisj2 hf2.2.2.1)
    ·rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hg1x
     rcases hg1x.1 with ⟨c', hc', hcc'⟩
     simp only [pairInput, decide_eq_true_eq] at hcc'
     rcases hcc' with rfl | rfl
     ·exact hc'
     ·exact absurd ((flag_color_C hbip hf1 hc').trans hsz).symm hcol_ne
  ·exact Finset.union_subset hC12 hsubC
 ·intro hnrb
  apply Finset.Subset.antisymm hsubC
  intro c hc
  have h := (hval (pairInput c zp2)).mpr
   ⟨⟨c, hc, by simp [pairInput]⟩, ⟨zp2, hf2.2.2.1, by simp [pairInput]⟩⟩
  have hside : (∃ u ∈ side (n := n) C g2 b2, pairInput c zp2 u = true) ∨
    (OrReaches n C (opnd C g2 b2) g1 ∧ gateVal n C g1 (pairInput c zp2) = true) := by
   fin_cases b2
   ·exact h.1
   ·exact h.2
  rcases hside with ⟨u, hu, hxu⟩ | ⟨hr, _⟩
  ·simp only [pairInput, decide_eq_true_eq] at hxu
   rcases hxu with rfl | rfl
   ·exact hu
   ·exact absurd (hsubC hu) (Finset.disjoint_right.mp hdisj2 hf2.2.2.1)
  ·exact absurd hr hnrb
 ·intro hrb'
  have hD12 : D1 ⊆ D2 := by
   by_cases hneC : (side (n := n) C g2 b2).Nonempty
   ·obtain ⟨c, hc⟩ := hneC
    have h1mb : 1 - (1 - b2) = b2 := by fin_cases b2 <;> rfl
    exact hsep_D (1 - b2) hrb' ⟨c, hsubC hc, by rw [h1mb]; exact hc⟩
   ·have hempC : side (n := n) C g2 b2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hneC
    have hrb := hnot_emp b2 hempC
    intro d1 hd1
    have h2 := (hval (pairInput z1 d1)).mp (by
     have hg1x : gateVal n C g1 (pairInput z1 d1) = true := by
      rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨⟨z1, hf1.2.1, by simp [pairInput]⟩, ⟨d1, hd1, by simp [pairInput]⟩⟩
     fin_cases b2
     ·exact ⟨Or.inr ⟨hrb, hg1x⟩, Or.inr ⟨hrb', hg1x⟩⟩
     ·exact ⟨Or.inr ⟨hrb', hg1x⟩, Or.inr ⟨hrb, hg1x⟩⟩)
    rcases h2.2 with ⟨d, hdD2, hxd⟩
    simp only [pairInput, decide_eq_true_eq] at hxd
    rcases hxd with rfl | rfl
    ·exact absurd (hsz.symm.trans (flag_color_D hbip hf2 hdD2)) hcol_ne
    ·exact hdD2
  refine ⟨hD12, hD_eq_z hD12, ?_⟩
  apply Finset.Subset.antisymm
  ·intro d hd
   rw [Finset.mem_union]
   by_cases hdS : d ∈ side (n := n) C g2 (1 - b2)
   ·exact Or.inr hdS
   ·left
    have h := (hval (pairInput z2 d)).mpr
     ⟨⟨z2, hf2.2.1, by simp [pairInput]⟩, ⟨d, hd, by simp [pairInput]⟩⟩
    have hside : (∃ u ∈ side (n := n) C g2 (1 - b2), pairInput z2 d u = true) ∨
      (OrReaches n C (opnd C g2 (1 - b2)) g1 ∧ gateVal n C g1 (pairInput z2 d) = true) := by
     fin_cases b2
     ·exact h.2
     ·exact h.1
    rcases hside with ⟨u, hu, hxu⟩ | ⟨_, hg1x⟩
    ·simp only [pairInput, decide_eq_true_eq] at hxu
     rcases hxu with rfl | rfl
     ·exact absurd (hsubD hu) (Finset.disjoint_left.mp hdisj2 hf2.2.1)
     ·exact absurd hu hdS
    ·rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hg1x
     rcases hg1x.2 with ⟨d', hd', hdd'⟩
     simp only [pairInput, decide_eq_true_eq] at hdd'
     rcases hdd' with rfl | rfl
     ·exact absurd ((flag_color_D hbip hf1 hd').trans hszp) (hsz.symm ▸ hcol_ne)
     ·exact hd'
  ·exact Finset.union_subset hD12 hsubD
 ·intro hnrb'
  apply Finset.Subset.antisymm hsubD
  intro d hd
  have h := (hval (pairInput z2 d)).mpr
   ⟨⟨z2, hf2.2.1, by simp [pairInput]⟩, ⟨d, hd, by simp [pairInput]⟩⟩
  have hside : (∃ u ∈ side (n := n) C g2 (1 - b2), pairInput z2 d u = true) ∨
    (OrReaches n C (opnd C g2 (1 - b2)) g1 ∧ gateVal n C g1 (pairInput z2 d) = true) := by
   fin_cases b2
   ·exact h.2
   ·exact h.1
  rcases hside with ⟨u, hu, hxu⟩ | ⟨hr, _⟩
  ·simp only [pairInput, decide_eq_true_eq] at hxu
   rcases hxu with rfl | rfl
   ·exact absurd (hsubD hu) (Finset.disjoint_left.mp hdisj2 hf2.2.1)
   ·exact hu
  ·exact absurd hr hnrb'
def facR {n : ℕ} (C : Circuit) (H lamSet : Finset ℕ) (g1 : ℕ)
  (zItem : Option (Fin n)) (M S : Finset (Fin n)) : ℕ → Finset (Option (Fin n))
 | w =>
  if hw : w < n then
   let u : Fin n := ⟨w, hw⟩
   if u ∈ M then {some u} else if u ∈ S then {none} else ∅
  else
   let k := w - n
   if hk : k < C.gates.length then
    if k = g1 then {zItem}
    else if k ∈ lamSet then {none}
    else if k ∈ H then
     if h0 : opnd C k 0 < w then
      if h1 : opnd C k 1 < w then
       facR C H lamSet g1 zItem M S (opnd C k 0) ∪ facR C H lamSet g1 zItem M S (opnd C k 1)
      else ∅
     else ∅
    else ∅
   else ∅
termination_by w => w
lemma facR_small {n : ℕ} {C : Circuit} (H lamSet : Finset ℕ) (g1 : ℕ)
  (zItem : Option (Fin n)) (M S : Finset (Fin n))
  {w : ℕ} (hnot : ∀ k ∈ H, w ≠ n + k) :
  (facR C H lamSet g1 zItem M S w).card ≤ 1 := by
 by_cases hw : w < n
 ·unfold facR; simp only [dif_pos hw]; split_ifs <;> simp
 ·by_cases hkH : w - n ∈ H
  ·exact absurd (by omega : w = n + (w - n)) (hnot (w - n) hkH)
  ·unfold facR; simp only [dif_neg hw, hkH, ↓reduceIte]; split_ifs <;> simp
lemma facR_step {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (H lamSet : Finset ℕ) (g1 : ℕ)
  (zItem : Option (Fin n)) (M S : Finset (Fin n))
  (hH_lt : ∀ k ∈ H, k < C.gates.length)
  (hH_ng1 : g1 ∉ H) (hH_nlam : Disjoint H lamSet)
  {k : ℕ} (hk : k ∈ H) :
  facR C H lamSet g1 zItem M S (n + k) ⊆
   facR C H lamSet g1 zItem M S (opnd C k 0) ∪ facR C H lamSet g1 zItem M S (opnd C k 1) := by
 have hk_lt := hH_lt k hk
 have hlt0 := opnd_lt hAO hk_lt 0
 have hlt1 := opnd_lt hAO hk_lt 1
 have hng1 : k ≠ g1 := fun h => hH_ng1 (h ▸ hk)
 have hnlam : k ∉ lamSet := Finset.disjoint_left.mp hH_nlam hk
 conv_lhs => unfold facR
 rw [dif_neg (by omega), Nat.add_sub_cancel_left, dif_pos hk_lt, if_neg hng1, if_neg hnlam,
  if_pos hk, dif_pos hlt0, dif_pos hlt1]
lemma facR_reaches_props {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
  (hne : ∃ u v : Fin n, G.Adj u v)
  {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  (H : Finset ℕ) (v : Fin n) (zItem : Option (Fin n)) (M S : Finset (Fin n))
  (hSadj : ∀ u ∈ S, G.Adj v u)
  (hM_U : ∀ u ∈ M, s(v, u) ∈ Ustar G C)
  (hH_lt : ∀ k ∈ H, k < C.gates.length)
  (hH_ng1 : g1 ∉ H) (hH_nlam : Disjoint H (lam G C)) :
  ∀ w < n + g2,
   (∀ k, OrReaches n C w k → k < C.gates.length ∧ k ∈ orN G C ∪ {g1}) →
   (∀ k, OrReaches n C w k → k ∈ orN G C \ lam G C → k ∈ H) →
   orIn n C w ⊆ S →
   (∀ u ∈ orIn n C w, u ∈ M → some u ∈ facR C H (lam G C) g1 zItem M S w) ∧
   (∀ u ∈ orIn n C w, u ∉ M → none ∈ facR C H (lam G C) g1 zItem M S w) ∧
   (OrReaches n C w g1 → zItem ∈ facR C H (lam G C) g1 zItem M S w ∨
    none ∈ facR C H (lam G C) g1 zItem M S w) := by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hw_lt hreach_ok hreach_H horIn_sub
  by_cases hwn : w < n
  ·refine ⟨?_, ?_, fun hr => absurd hr (orReaches_input_false hwn)⟩
   ·intro u hu huM
    have heq := (mem_orIn_input C u ⟨w, hwn⟩).mp hu
    subst heq; unfold facR; rw [dif_pos hwn, if_pos huM]; simp
   ·intro u hu huM
    have heq := (mem_orIn_input C u ⟨w, hwn⟩).mp hu
    have huS := horIn_sub hu
    subst heq; unfold facR; rw [dif_pos hwn, if_neg huM, if_pos huS]; simp
  ·have hk_lt : w - n < C.gates.length := by
    have hg2j := mem_junk_iff.mp ((hjunk g2).mpr (Or.inr rfl)); omega
   have hw_eq : w = n + (w - n) := by omega
   set k := w - n
   have hself : OrReaches n C w k := by rw [hw_eq]; exact orReaches_self hk_lt
   have hk_mem := (hreach_ok k hself).2
   rw [Finset.mem_union, Finset.mem_singleton] at hk_mem
   rcases hk_mem with hk_orN | rfl
   ·have hkg1 : k ≠ g1 := by
     intro h; subst h
     have h1 := (mem_orN_iff.mp hk_orN).2.1
     have h2 := (mem_junk_iff.mp ((hjunk k).mpr (Or.inl rfl))).2.1
     rw [h1] at h2; cases h2
    by_cases hk_lam : k ∈ lam G C
    ·have hcard2 : 2 ≤ (orIn n C (n + k)).card :=
      lam_below_g2_card_ge_two hL hLift hne hjunk hk_lam (by omega)
     have hstar := lam_disjoint_ustar hL.1 h4 hk_lam
      (fun u hu => hSadj u (horIn_sub (by rwa [hw_eq]))) hcard2
     have hfac_eq : facR C H (lam G C) g1 zItem M S w = {none} := by
      unfold facR; rw [dif_neg hwn, dif_pos hk_lt, if_neg hkg1, if_pos hk_lam]
     rw [hfac_eq]
     refine ⟨?_, fun _ _ _ => Finset.mem_singleton_self none, fun _ => Or.inr (Finset.mem_singleton_self none)⟩
     intro u hu huM
     exfalso
     have h1 := hstar u (by rwa [← hw_eq])
     have h2 := (Finset.mem_sdiff.mp (hM_U u huM)).2
     exact h2 h1
    ·have hk_H : k ∈ H := hreach_H k hself (Finset.mem_sdiff.mpr ⟨hk_orN, hk_lam⟩)
     have hk' := mem_orN_iff.mp hk_orN
     have hlt0 : opnd C k 0 < w := by have := opnd_lt hL.1 hk'.1 0; omega
     have hlt1 : opnd C k 1 < w := by have := opnd_lt hL.1 hk'.1 1; omega
     have hfac_eq : facR C H (lam G C) g1 zItem M S w =
       facR C H (lam G C) g1 zItem M S (opnd C k 0) ∪
       facR C H (lam G C) g1 zItem M S (opnd C k 1) := by
      conv_lhs => unfold facR
      rw [dif_neg hwn, dif_pos hk_lt, if_neg hkg1, if_neg hk_lam, if_pos hk_H,
       dif_pos hlt0, dif_pos hlt1]
     have hsub_reach : ∀ b : Fin 2, ∀ m, OrReaches n C (opnd C k b) m → OrReaches n C w m := by
      intro b m hrm
      rw [hw_eq, orReaches_gate_iff hk'.1]
      exact Or.inr ⟨hk'.2.1, opnd C k b, opnd_mem hL.1 hk'.1 b, hrm.1, opnd_lt hL.1 hk'.1 b, hrm⟩
     have horIn_eq : orIn n C w = orIn n C (opnd C k 0) ∪ orIn n C (opnd C k 1) := by
      rw [hw_eq]; exact orIn_or_eq_union hL.1 hk'.1 hk'.2.1
     have ih0 := ih (opnd C k 0) hlt0 (by omega)
      (fun m hm => hreach_ok m (hsub_reach 0 m hm))
      (fun m hm => hreach_H m (hsub_reach 0 m hm))
      (fun u hu => horIn_sub (by rw [horIn_eq]; exact Finset.mem_union_left _ hu))
     have ih1 := ih (opnd C k 1) hlt1 (by omega)
      (fun m hm => hreach_ok m (hsub_reach 1 m hm))
      (fun m hm => hreach_H m (hsub_reach 1 m hm))
      (fun u hu => horIn_sub (by rw [horIn_eq]; exact Finset.mem_union_right _ hu))
     rw [hfac_eq]
     refine ⟨?_, ?_, ?_⟩
     ·intro u hu huM
      rw [horIn_eq, Finset.mem_union] at hu
      rcases hu with h0 | h1
      ·exact Finset.mem_union_left _ (ih0.1 u h0 huM)
      ·exact Finset.mem_union_right _ (ih1.1 u h1 huM)
     ·intro u hu huM
      rw [horIn_eq, Finset.mem_union] at hu
      rcases hu with h0 | h1
      ·exact Finset.mem_union_left _ (ih0.2.1 u h0 huM)
      ·exact Finset.mem_union_right _ (ih1.2.1 u h1 huM)
     ·intro hr
      rw [hw_eq, orReaches_gate_iff hk'.1] at hr
      rcases hr with heq | ⟨_, u, hu, _, _, hug1⟩
      ·exact absurd heq.symm hkg1
      ·rw [gate_inputs_eq hL.1 hk'.1] at hu
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
       rcases hu with rfl | rfl
       ·exact (ih0.2.2 hug1).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
       ·exact (ih1.2.2 hug1).imp (Finset.mem_union_right _) (Finset.mem_union_right _)
   ·have hfac_eq : facR C H (lam G C) k zItem M S w = {zItem} := by
     unfold facR; rw [dif_neg hwn, dif_pos hk_lt, if_pos rfl]
    have hg1j := mem_junk_iff.mp ((hjunk k).mpr (Or.inl rfl))
    have hemp : orIn n C w = ∅ := by rw [hw_eq]; exact orIn_and_eq_empty (n := n) hk_lt hg1j.2.1
    rw [hfac_eq, hemp]
    exact ⟨by simp, by simp, fun _ => Or.inl (Finset.mem_singleton_self zItem)⟩
lemma single_opnd_fac_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
  (hne : ∃ u v : Fin n, G.Adj u v)
  {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {w : ℕ} (hw_lt : w < n + g2)
  (hw_nb : ∀ k, w = n + k → ¬ BelowF G C k)
  (hn1 : ¬ OrReaches n C w g1)
  {v : Fin n} {S : Finset (Fin n)} (hS : orIn n C w = S) (hSadj : ∀ u ∈ S, G.Adj v u) :
  let M := S.filter (fun u => s(v, u) ∈ Ustar G C)
  let H := (orN G C \ lam G C).filter (fun k => OrReaches n C w k)
  (M.Nonempty → M.card ≤ H.card + 1) ∧
  ((∃ r ∈ S, r ∉ M) → M.card ≤ H.card) := by
 intro M H
 have hH_lt : ∀ k ∈ H, k < C.gates.length := fun k hk =>
  (mem_orN_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).1).1
 have hH_ng1 : g1 ∉ H := fun hg => by
  have h1 := (mem_orN_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hg).1).1).2.1
  have h2 := (mem_junk_iff.mp ((hjunk g1).mpr (Or.inl rfl))).2.1
  rw [h1] at h2; cases h2
 have hH_nlam : Disjoint H (lam G C) := by
  rw [Finset.disjoint_left]; intro k hk hkl
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).2 hkl
 have hreach_ok : ∀ k, OrReaches n C w k → k < C.gates.length ∧ k ∈ orN G C ∪ {g1} := by
  intro k hk
  have hk_le : k ≤ w - n := orReaches_le hk
  have hk_lt : k < C.gates.length := by
   have hg2j := mem_junk_iff.mp ((hjunk g2).mpr (Or.inr rfl)); omega
  refine ⟨hk_lt, ?_⟩
  have hnbk : ¬ BelowF G C k := by
   intro hbk
   by_cases hwn : w < n
   ·exact orReaches_input_false hwn hk
   ·have hw_eq : w = n + (w - n) := by omega
    have hval := orReaches_val_mono hL.1
    have hstep : ∀ u < n + C.gates.length, (∀ m, u = n + m → ¬ BelowF G C m) →
      OrReaches n C u k → False := by
     intro u
     induction u using Nat.strong_induction_on with
     | ind u ihu =>
      intro hu_lt hu_nb hruk
      by_cases hun : u < n
      ·exact orReaches_input_false hun hruk
      ·have hm_lt : u - n < C.gates.length := by omega
       have hu_eq : u = n + (u - n) := by omega
       rw [hu_eq, orReaches_gate_iff hm_lt] at hruk
       rcases hruk with rfl | ⟨horm, x, hx, hnx, hxlt, hxrk⟩
       ·exact hu_nb (u - n) hu_eq hbk
       ·rw [gate_inputs_eq hL.1 hm_lt] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        have hnbx : ∀ m, x = n + m → ¬ BelowF G C m := by
         intro m hm hbm
         rcases hx with rfl | rfl
         ·exact lift_no_belowF_orN_opnd hL hLift hne hm_lt horm (hu_nb _ hu_eq) 0 (by rw [hm]; exact hbm)
         ·exact lift_no_belowF_orN_opnd hL hLift hne hm_lt horm (hu_nb _ hu_eq) 1 (by rw [hm]; exact hbm)
        exact ihu x (by omega) (by omega) hnbx hxrk
    have hg2j := mem_junk_iff.mp ((hjunk g2).mpr (Or.inr rfl))
    exact hstep w (by omega) hw_nb hk
  rcases hL.1.1 _ (gateAt_mem hk_lt) with hand | hor
  ·have hkj : k ∈ junk G C := mem_junk_iff.mpr ⟨hk_lt, hand, hnbk⟩
   rw [hjunk] at hkj
   rcases hkj with rfl | rfl
   ·exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
   ·have := hk.1; omega
  ·exact Finset.mem_union_left _ (mem_orN_iff.mpr ⟨hk_lt, hor, hnbk⟩)
 have hM_U : ∀ u ∈ M, s(v, u) ∈ Ustar G C := fun u hu => (Finset.mem_filter.mp hu).2
 have hprops := facR_reaches_props hL hLift h4 hne hjunk H v none M S hSadj hM_U hH_lt hH_ng1 hH_nlam
  w hw_lt hreach_ok (fun k hk hkd => Finset.mem_filter.mpr ⟨hkd, hk⟩) (by rw [hS])
 let Items : Finset (Option (Fin n)) := insert none (M.image some)
 obtain ⟨comp, hcard, hmono⟩ := orDag_count hL.1 Items H hH_lt
  (facR C H (lam G C) g1 none M S)
  (fun u _ hnot => facR_small H (lam G C) g1 none M S hnot)
  (fun k hk => facR_step hL.1 H (lam G C) g1 none M S hH_lt hH_ng1 hH_nlam hk)
 have hg2j := mem_junk_iff.mp ((hjunk g2).mpr (Or.inr rfl))
 obtain ⟨c, hc⟩ := hmono w (by omega)
 have hM_sub_R : M.image some ⊆ facR C H (lam G C) g1 none M S w := by
  intro y hy; simp only [Finset.mem_image] at hy; rcases hy with ⟨u, hu, rfl⟩
  exact hprops.1 u (by rw [hS]; exact (Finset.mem_filter.mp hu).1) hu
 have hM_card : (M.image some).card = M.card := Finset.card_image_of_injective M (Option.some_injective (Fin n))
 constructor
 ·intro hMne
  have hle := mono_card_le hcard (Finset.subset_insert none (M.image some))
   (hMne.image some) ⟨c, fun a ha => hc a (hM_sub_R ha)⟩
  omega
 ·rintro ⟨r, hrS, hrnM⟩
  have hnone_R : none ∈ facR C H (lam G C) g1 none M S w := hprops.2.1 r (by rw [hS]; exact hrS) hrnM
  have hItems_sub : Items ⊆ facR C H (lam G C) g1 none M S w := by
   intro a ha; simp only [Items, Finset.mem_insert] at ha
   rcases ha with rfl | ha
   ·exact hnone_R
   ·exact hM_sub_R ha
  have hle := mono_card_le hcard (Finset.Subset.refl Items) ⟨none, Finset.mem_insert_self _ _⟩
   ⟨c, fun a ha => hc a (hItems_sub ha)⟩
  have hnone_nmem : none ∉ M.image some := by simp
  have hItems_card : Items.card = M.card + 1 := by
   simp only [Items, Finset.card_insert_of_notMem hnone_nmem, hM_card]
  omega
lemma merged_opnds_fac_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (h4 : NoFourCycle G)
  (hne : ∃ u v : Fin n, G.Adj u v)
  {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {w1 w2 : ℕ} (hw1_lt : w1 < n + g2) (hw2_lt : w2 < n + g2)
  (hw1_nb : ∀ k, w1 = n + k → ¬ BelowF G C k) (hw2_nb : ∀ k, w2 = n + k → ¬ BelowF G C k)
  {v : Fin n} {S1 S2 : Finset (Fin n)}
  (hS1 : orIn n C w1 = S1) (hS2_sub : orIn n C w2 ⊆ S2)
  (hUnion : S1 ∪ S2 = S1 ∪ orIn n C w2)
  (hSadj : ∀ u ∈ S1 ∪ S2, G.Adj v u)
  {z0 : Fin n} (hz0_1 : z0 ∈ S1)
  (hz0_2 : z0 ∈ orIn n C w2 ∨ OrReaches n C w2 g1) :
  let S := S1 ∪ S2
  let M := S.filter (fun u => s(v, u) ∈ Ustar G C)
  let H := (orN G C \ lam G C).filter (fun k => OrReaches n C w1 k ∨ OrReaches n C w2 k)
  (M.Nonempty → M.card ≤ H.card + 1) ∧
  (z0 ∉ M → M.card ≤ H.card) ∧
  (¬ OrReaches n C w2 g1 → (∃ r ∈ S, r ∉ M) → M.card ≤ H.card) := by
 intro S M H
 have hH_lt : ∀ k ∈ H, k < C.gates.length := fun k hk =>
  (mem_orN_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).1).1
 have hH_ng1 : g1 ∉ H := fun hg => by
  have h1 := (mem_orN_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hg).1).1).2.1
  have h2 := (mem_junk_iff.mp ((hjunk g1).mpr (Or.inl rfl))).2.1
  rw [h1] at h2; cases h2
 have hH_nlam : Disjoint H (lam G C) := by
  rw [Finset.disjoint_left]; intro k hk hkl
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).2 hkl
 have hreach_ok_gen : ∀ w < n + g2, (∀ k, w = n + k → ¬ BelowF G C k) →
   ∀ k, OrReaches n C w k → k < C.gates.length ∧ k ∈ orN G C ∪ {g1} := by
  intro w hw_lt hw_nb k hk
  have hk_le : k ≤ w - n := orReaches_le hk
  have hg2j := mem_junk_iff.mp ((hjunk g2).mpr (Or.inr rfl))
  have hk_lt : k < C.gates.length := by omega
  refine ⟨hk_lt, ?_⟩
  have hnbk : ¬ BelowF G C k := by
   intro hbk
   have hstep : ∀ u < n + C.gates.length, (∀ m, u = n + m → ¬ BelowF G C m) →
     OrReaches n C u k → False := by
    intro u
    induction u using Nat.strong_induction_on with
    | ind u ihu =>
     intro hu_lt hu_nb hruk
     by_cases hun : u < n
     ·exact orReaches_input_false hun hruk
     ·have hm_lt : u - n < C.gates.length := by omega
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq, orReaches_gate_iff hm_lt] at hruk
      rcases hruk with rfl | ⟨horm, x, hx, hnx, hxlt, hxrk⟩
      ·exact hu_nb (u - n) hu_eq hbk
      ·rw [gate_inputs_eq hL.1 hm_lt] at hx
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
       have hnbx : ∀ m, x = n + m → ¬ BelowF G C m := by
        intro m hm hbm
        rcases hx with rfl | rfl
        ·exact lift_no_belowF_orN_opnd hL hLift hne hm_lt horm (hu_nb _ hu_eq) 0 (by rw [hm]; exact hbm)
        ·exact lift_no_belowF_orN_opnd hL hLift hne hm_lt horm (hu_nb _ hu_eq) 1 (by rw [hm]; exact hbm)
       exact ihu x (by omega) (by omega) hnbx hxrk
   exact hstep w (by omega) hw_nb hk
  rcases hL.1.1 _ (gateAt_mem hk_lt) with hand | hor
  ·have hkj : k ∈ junk G C := mem_junk_iff.mpr ⟨hk_lt, hand, hnbk⟩
   rw [hjunk] at hkj
   rcases hkj with rfl | rfl
   ·exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
   ·have := hk.1; omega
  ·exact Finset.mem_union_left _ (mem_orN_iff.mpr ⟨hk_lt, hor, hnbk⟩)
 let zItem : Option (Fin n) := if z0 ∈ M then some z0 else none
 have hM_U : ∀ u ∈ M, s(v, u) ∈ Ustar G C := fun u hu => (Finset.mem_filter.mp hu).2
 have hp1 := facR_reaches_props hL hLift h4 hne hjunk H v zItem M S hSadj hM_U hH_lt hH_ng1 hH_nlam
  w1 hw1_lt (hreach_ok_gen w1 hw1_lt hw1_nb) (fun k hk hkd => Finset.mem_filter.mpr ⟨hkd, Or.inl hk⟩)
  (by rw [hS1]; exact Finset.subset_union_left)
 have hp2 := facR_reaches_props hL hLift h4 hne hjunk H v zItem M S hSadj hM_U hH_lt hH_ng1 hH_nlam
  w2 hw2_lt (hreach_ok_gen w2 hw2_lt hw2_nb) (fun k hk hkd => Finset.mem_filter.mpr ⟨hkd, Or.inr hk⟩)
  (Finset.Subset.trans hS2_sub Finset.subset_union_right)
 let Items : Finset (Option (Fin n)) := insert none (M.image some)
 obtain ⟨comp, hcard, hmono⟩ := orDag_count hL.1 Items H hH_lt
  (facR C H (lam G C) g1 zItem M S)
  (fun u _ hnot => facR_small H (lam G C) g1 zItem M S hnot)
  (fun k hk => facR_step hL.1 H (lam G C) g1 zItem M S hH_lt hH_ng1 hH_nlam hk)
 have hg2j := mem_junk_iff.mp ((hjunk g2).mpr (Or.inr rfl))
 obtain ⟨c1, hc1⟩ := hmono w1 (by omega)
 obtain ⟨c2, hc2⟩ := hmono w2 (by omega)
 set R1 := facR C H (lam G C) g1 zItem M S w1
 set R2 := facR C H (lam G C) g1 zItem M S w2
 have hM_sub : M.image some ⊆ R1 ∪ R2 := by
  intro y hy; simp only [Finset.mem_image] at hy; rcases hy with ⟨u, hu, rfl⟩
  have huS : u ∈ S1 ∪ orIn n C w2 := by rw [← hUnion]; exact (Finset.mem_filter.mp hu).1
  rw [Finset.mem_union] at huS
  rcases huS with h1 | h2
  ·exact Finset.mem_union_left _ (hp1.1 u (by rw [hS1]; exact h1) hu)
  ·exact Finset.mem_union_right _ (hp2.1 u h2 hu)
 have hzItem_R1 : zItem ∈ R1 := by
  by_cases hzM : z0 ∈ M
  ·simp only [zItem, if_pos hzM]; exact hp1.1 z0 (by rw [hS1]; exact hz0_1) hzM
  ·simp only [zItem, if_neg hzM]; exact hp1.2.1 z0 (by rw [hS1]; exact hz0_1) hzM
 have hzItem_or_none_R2 : zItem ∈ R2 ∨ none ∈ R2 := by
  rcases hz0_2 with hz2 | hr2
  ·left
   by_cases hzM : z0 ∈ M
   ·simp only [zItem, if_pos hzM]; exact hp2.1 z0 hz2 hzM
   ·simp only [zItem, if_neg hzM]; exact hp2.2.1 z0 hz2 hzM
  ·exact hp2.2.2 hr2
 have hM_card : (M.image some).card = M.card := Finset.card_image_of_injective M (Option.some_injective (Fin n))
 have hnone_nmem : none ∉ M.image some := by simp
 have hItems_card : Items.card = M.card + 1 := by
  simp only [Items, Finset.card_insert_of_notMem hnone_nmem, hM_card]
 refine ⟨?_, ?_, ?_⟩
 ·intro hMne
  rcases hzItem_or_none_R2 with hzR2 | hnoneR2
  ·have hc12 : c1 = c2 := (hc1 zItem hzItem_R1).symm.trans (hc2 zItem hzR2)
   have hle := mono_card_le hcard (Finset.subset_insert none (M.image some))
    (hMne.image some) ⟨c1, fun a ha => by
     rcases Finset.mem_union.mp (hM_sub ha) with h1 | h2
     ·exact hc1 a h1
     ·rw [hc12]; exact hc2 a h2⟩
   omega
  ·have hcov : Items ⊆ (R1 ∩ Items) ∪ (R2 ∩ Items) := by
    intro a ha
    simp only [Finset.mem_union, Finset.mem_inter]
    by_cases ha_none : a = none
    ·subst ha_none; exact Or.inr ⟨hnoneR2, ha⟩
    ·have haM : a ∈ M.image some := by
      simp only [Items, Finset.mem_insert] at ha; exact ha.resolve_left ha_none
     rcases Finset.mem_union.mp (hM_sub haM) with h1 | h2
     ·exact Or.inl ⟨h1, ha⟩
     ·exact Or.inr ⟨h2, ha⟩
   have hle := two_mono_card_le hcard
    (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
    ⟨c1, fun a ha => hc1 a (Finset.mem_inter.mp ha).1⟩
    ⟨c2, fun a ha => hc2 a (Finset.mem_inter.mp ha).1⟩
   have hI_le := Finset.card_le_card hcov
   omega
 ·intro hz0_nM
  have hzItem_eq : zItem = none := by simp [zItem, hz0_nM]
  have hnone_R1 : none ∈ R1 := by rwa [← hzItem_eq]
  have hnone_R2 : none ∈ R2 := by
   rcases hzItem_or_none_R2 with h | h
   ·rwa [hzItem_eq] at h
   ·exact h
  have hc12 : c1 = c2 := (hc1 none hnone_R1).symm.trans (hc2 none hnone_R2)
  have hItems_sub : Items ⊆ R1 ∪ R2 := by
   intro a ha; simp only [Items, Finset.mem_insert] at ha
   rcases ha with rfl | ha
   ·exact Finset.mem_union_left _ hnone_R1
   ·exact hM_sub ha
  have hle := mono_card_le hcard (Finset.Subset.refl Items) ⟨none, Finset.mem_insert_self _ _⟩
   ⟨c1, fun a ha => by
    rcases Finset.mem_union.mp (hItems_sub ha) with h1 | h2
    ·exact hc1 a h1
    ·rw [hc12]; exact hc2 a h2⟩
  omega
 ·intro hnr2 ⟨r, hrS, hrnM⟩
  have hz2 : z0 ∈ orIn n C w2 := hz0_2.resolve_right hnr2
  have hzR2 : zItem ∈ R2 := by
   by_cases hzM : z0 ∈ M
   ·simp only [zItem, if_pos hzM]; exact hp2.1 z0 hz2 hzM
   ·simp only [zItem, if_neg hzM]; exact hp2.2.1 z0 hz2 hzM
  have hc12 : c1 = c2 := (hc1 zItem hzItem_R1).symm.trans (hc2 zItem hzR2)
  have hnone_U : none ∈ R1 ∪ R2 := by
   have hr' : r ∈ S1 ∪ orIn n C w2 := by rwa [← hUnion]
   rcases Finset.mem_union.mp hr' with h1 | h2
   ·exact Finset.mem_union_left _ (hp1.2.1 r (by rw [hS1]; exact h1) hrnM)
   ·exact Finset.mem_union_right _ (hp2.2.1 r h2 hrnM)
  have hItems_sub : Items ⊆ R1 ∪ R2 := by
   intro a ha; simp only [Items, Finset.mem_insert] at ha
   rcases ha with rfl | ha
   ·exact hnone_U
   ·exact hM_sub ha
  have hle := mono_card_le hcard (Finset.Subset.refl Items) ⟨none, Finset.mem_insert_self _ _⟩
   ⟨c1, fun a ha => by
    rcases Finset.mem_union.mp (hItems_sub ha) with h1 | h2
    ·exact hc1 a h1
    ·rw [hc12]; exact hc2 a h2⟩
  omega
def reachesFlag (n : ℕ) (C : Circuit) (g1 g2 w : ℕ) : Prop :=
 OrReaches n C w g1 ∨ OrReaches n C w g2
noncomputable def topOwner {n : ℕ} (C : Circuit) (s : Fin n → Bool) (z1 : Fin n) (g1 g2 a : ℕ) : Fin n :=
 letI := Classical.dec
 if h0 : (side (n := n) C a 0).card = 1 then
  let u := Classical.choose (Finset.card_eq_one.mp h0)
  if h1 : (side (n := n) C a 1).card = 1 then
   let v := Classical.choose (Finset.card_eq_one.mp h1)
   if reachesFlag n C g1 g2 (opnd C a 0) ∧ ¬ reachesFlag n C g1 g2 (opnd C a 1) then v
   else if reachesFlag n C g1 g2 (opnd C a 1) ∧ ¬ reachesFlag n C g1 g2 (opnd C a 0) then u
   else if s u = s z1 then u else v
  else u
 else if h1 : (side (n := n) C a 1).card = 1 then
  Classical.choose (Finset.card_eq_one.mp h1)
 else z1
lemma topOwner_side {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (hAO : IsAO2 n C) (h4 : NoFourCycle G) (s : Fin n → Bool) (z1 : Fin n) (g1 g2 : ℕ)
  {a : ℕ} (ha : a ∈ tops G C \ centreless G C) :
  side (n := n) C a 0 = {topOwner C s z1 g1 g2 a} ∨
   side (n := n) C a 1 = {topOwner C s z1 g1 g2 a} := by
 have hst := top_is_star hAO h4 ha
 unfold topOwner
 by_cases h0 : (side (n := n) C a 0).card = 1
 ·simp only [dif_pos h0]
  have hu := Classical.choose_spec (Finset.card_eq_one.mp h0)
  by_cases h1 : (side (n := n) C a 1).card = 1
  ·simp only [dif_pos h1]
   have hv := Classical.choose_spec (Finset.card_eq_one.mp h1)
   split_ifs
   ·exact Or.inr hv
   ·exact Or.inl hu
   ·exact Or.inl hu
   ·exact Or.inr hv
  ·simp only [dif_neg h1]; exact Or.inl hu
 ·have h1 : (side (n := n) C a 1).card = 1 := hst.2.2.resolve_left h0
  simp only [dif_neg h0, dif_pos h1]
  exact Or.inr (Classical.choose_spec (Finset.card_eq_one.mp h1))
lemma topOwner_of_starEdge {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (hAO : IsAO2 n C) (h4 : NoFourCycle G) (s : Fin n → Bool) (z1 : Fin n) (g1 g2 : ℕ)
  {u v : Fin n} (he : s(u, v) ∈ starEdges G C) :
  ∃ a ∈ tops G C \ centreless G C, topOwner C s z1 g1 g2 a = u ∨ topOwner C s z1 g1 g2 a = v := by
 simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at he
 rcases he with ⟨a, ha, ⟨p0, p1⟩, ⟨hp0, hp1⟩, hpeq⟩
 have haS : a ∈ tops G C \ centreless G C := by
  rw [Finset.mem_sdiff]; refine ⟨ha, fun hc => ?_⟩
  rw [centreless, Finset.mem_filter] at hc
  rcases hc.2 with h0 | h1
  ·rw [h0] at hp0; exact Finset.notMem_empty _ hp0
  ·rw [h1] at hp1; exact Finset.notMem_empty _ hp1
 refine ⟨a, haS, ?_⟩
 rw [Sym2.eq_iff] at hpeq
 rcases topOwner_side hAO h4 s z1 g1 g2 haS with h0 | h1
 ·rw [h0, Finset.mem_singleton] at hp0
  rcases hpeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·exact Or.inl hp0.symm
  ·exact Or.inr hp0.symm
 ·rw [h1, Finset.mem_singleton] at hp1
  rcases hpeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·exact Or.inr hp1.symm
  ·exact Or.inl hp1.symm
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
  ·exact absurd hrg (orReaches_input_false hwn)
  ·have hk_lt : w - n < C.gates.length := by omega
   have hw_eq : w = n + (w - n) := by omega
   set k := w - n
   have hnbk : ¬ BelowF G C k := hnb k hw_eq
   have hork : (gateAt C k).op = GateOp.or := by
    rcases hL.1.1 _ (gateAt_mem hk_lt) with hand | hor
    ·exfalso; have hemp := orIn_and_eq_empty (n := n) hk_lt hand
     rw [← hw_eq] at hemp; exact hne_w.ne_empty hemp
    ·exact hor
   have hk_orN : k ∈ orN G C := mem_orN_iff.mpr ⟨hk_lt, hork, hnbk⟩
   by_cases hemp : orIn n C (opnd C k 0) = ∅ ∨ orIn n C (opnd C k 1) = ∅
   ·refine ⟨k, Finset.mem_sdiff.mpr ⟨hk_orN, fun hkl => ?_⟩,
     by rw [hw_eq]; exact orReaches_self hk_lt, by rwa [← hw_eq],
     by rwa [← hw_eq], by rw [← hw_eq], hemp⟩
    have hf := Finset.mem_filter.mp hkl
    rcases hemp with h0 | h1
    ·exact hf.2.1.ne_empty h0
    ·exact hf.2.2.1.ne_empty h1
   ·push Not at hemp
    have h0ne : (orIn n C (opnd C k 0)).Nonempty := hemp.1
    have h1ne : (orIn n C (opnd C k 1)).Nonempty := hemp.2
    rw [hw_eq, orReaches_gate_iff hk_lt] at hrg
    have hkng : k ≠ g := fun h => by rw [h, hgj.2.1] at hork; cases hork
    rcases hrg with rfl | ⟨_, u, hu, hnu, hult, hrug⟩
    ·exact absurd rfl hkng
    ·rw [gate_inputs_eq hL.1 hk_lt] at hu
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
     have hnbu : ∀ b : Fin 2, ∀ m, opnd C k b = n + m → ¬ BelowF G C m := fun b m hm hbm =>
      lift_no_belowF_orN_opnd hL hLift hne hk_lt hork hnbk b (by rw [hm]; exact hbm)
     have hsub_orIn : ∀ b : Fin 2, orIn n C (opnd C k b) ⊆ orIn n C w := by
      intro b; rw [hw_eq, orIn_or_eq_union hL.1 hk_lt hork]
      fin_cases b
      ·exact Finset.subset_union_left
      ·exact Finset.subset_union_right
     rcases hu with rfl | rfl
     ·obtain ⟨m, hm, hwm, hmg, hmne, hmsub, hme⟩ :=
       ih (opnd C k 0) (by omega) (by omega) (hnbu 0) h0ne hrug
      refine ⟨m, hm, ?_, hmg, hmne, Finset.Subset.trans hmsub (hsub_orIn 0), hme⟩
      rw [hw_eq, orReaches_gate_iff hk_lt]
      exact Or.inr ⟨hork, opnd C k 0, opnd_mem hL.1 hk_lt 0, hwm.1, opnd_lt hL.1 hk_lt 0, hwm⟩
     ·obtain ⟨m, hm, hwm, hmg, hmne, hmsub, hme⟩ :=
       ih (opnd C k 1) (by omega) (by omega) (hnbu 1) h1ne hrug
      refine ⟨m, hm, ?_, hmg, hmne, Finset.Subset.trans hmsub (hsub_orIn 1), hme⟩
      rw [hw_eq, orReaches_gate_iff hk_lt]
      exact Or.inr ⟨hork, opnd C k 1, opnd_mem hL.1 hk_lt 1, hwm.1, opnd_lt hL.1 hk_lt 1, hwm⟩
lemma pureFlagOr_of_reaches_both {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {C : Circuit} (hL : IsLeastAO G C)
  {g1 g2 : ℕ} (hlt12 : g1 < g2) (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {w : ℕ} (hw_lt : w < n + C.gates.length) (hnb : ∀ k, w = n + k → ¬ BelowF G C k)
  (hemp : orIn n C w = ∅) (hr1 : OrReaches n C w g1) (hr2 : OrReaches n C w g2) :
  ∃ m ∈ orN G C \ lam G C, g2 < m ∧ orIn n C (n + m) = ∅ := by
 have hnw : n ≤ w := hr1.1
 have hk_lt : w - n < C.gates.length := by omega
 have hw_eq : w = n + (w - n) := by omega
 set k := w - n
 have hnbk : ¬ BelowF G C k := hnb k hw_eq
 have hle2 : g2 ≤ k := by have := orReaches_le hr2; omega
 have hng2 : k ≠ g2 := by
  intro h; subst h
  have hg2j := mem_junk_iff.mp ((hjunk k).mpr (Or.inr rfl))
  rw [hw_eq, orReaches_gate_iff hk_lt] at hr1
  rcases hr1 with h1 | ⟨hor, _⟩
  ·omega
  ·rw [hg2j.2.1] at hor; cases hor
 have hork : (gateAt C k).op = GateOp.or := by
  rcases hL.1.1 _ (gateAt_mem hk_lt) with hand | hor
  ·exfalso
   have hkj := (hjunk k).mp (mem_junk_iff.mpr ⟨hk_lt, hand, hnbk⟩)
   rcases hkj with rfl | rfl <;> omega
  ·exact hor
 have hk_orN : k ∈ orN G C := mem_orN_iff.mpr ⟨hk_lt, hork, hnbk⟩
 have h0emp : orIn n C (opnd C k 0) = ∅ := by
  have hu := orIn_or_eq_union hL.1 hk_lt hork
  rw [← hw_eq, hemp] at hu
  exact (Finset.union_eq_empty.mp hu.symm).1
 refine ⟨k, Finset.mem_sdiff.mpr ⟨hk_orN, fun hkl => (Finset.mem_filter.mp hkl).2.1.ne_empty h0emp⟩,
  by omega, by rwa [← hw_eq]⟩
lemma top_reaches_flag_wmax {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
  {g : ℕ} (hr : OrReaches n C (opnd C a b) g)
  {w : Fin n} (hw : w ∈ side (n := n) C a (1 - b)) :
  ∀ x : Fin n → Bool, gateVal n C g x = true → x w = true → graphFun G ∅ x = true := by
 have ha' := mem_tops_iff.mp ha
 intro x hgx hxw
 apply ha'.2.2 x
 rw [gateVal_eq_wval, wval_gate_and hAO x ha'.1 ha'.2.1, Bool.and_eq_true]
 have hv1 := orReaches_val_mono hAO x hr hgx
 have hv2 := orIn_val_mono hAO x hw hxw
 fin_cases b
 ·exact ⟨hv1, hv2⟩
 ·exact ⟨hv2, hv1⟩
lemma golden_edge_cover {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
  {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {C1 D1 C2 D2 : Finset (Fin n)} {z1 zp1 z2 zp2 : Fin n}
  (hf1 : IsFlag G C g1 C1 D1 z1 zp1) (hf2 : IsFlag G C g2 C2 D2 z2 zp2)
  (hsz : s z1 = s z2) (hszp : s zp1 = s zp2)
  {v u : Fin n} (hvu_U : s(v, u) ∈ Ustar G C)
  (hvu_not_wmax :
   (gateVal n C g1 (pairInput v u) = true →
    (¬ ∀ x, gateVal n C g1 x = true → x u = true → graphFun G ∅ x = true) ∧
    (∀ w : Fin n, s w = s v → (∀ x, gateVal n C g1 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w u)) ∧
   (gateVal n C g2 (pairInput v u) = true →
    (¬ ∀ x, gateVal n C g2 x = true → x u = true → graphFun G ∅ x = true) ∧
    (∀ w : Fin n, s w = s v → (∀ x, gateVal n C g2 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w u)))
  (hnot_both_flags : ¬ (gateVal n C g1 (pairInput v u) = true ∧ gateVal n C g2 (pairInput v u) = true ∧
   ∀ x, gateVal n C g1 x = true → gateVal n C g2 x = true → graphFun G ∅ x = true)) :
  (∃ a ∈ tops G C \ centreless G C, topOwner C s z1 g1 g2 a = v) ∨
  (∃ a ∈ centreless G C, ∃ b : Fin 2, ∃ g : ℕ, (g = g1 ∨ g = g2) ∧
   gateVal n C g (pairInput v u) = true ∧
   side (n := n) C a b = ∅ ∧ OrReaches n C (opnd C a b) g ∧ v ∈ side (n := n) C a (1 - b)) ∨
  (s v = s zp1 ∧ ∃ a ∈ tops G C \ centreless G C, ∃ b : Fin 2, ∃ g : ℕ, (g = g1 ∨ g = g2) ∧
   gateVal n C g (pairInput v u) = true ∧
   side (n := n) C a (1 - b) = {v} ∧ OrReaches n C (opnd C a b) g ∧
   ∃ g' : ℕ, (g' = g1 ∨ g' = g2) ∧ g' ≠ g ∧ OrReaches n C (opnd C a (1 - b)) g' ∧
   ∃ mv ∈ orN G C \ lam G C, OrReaches n C (n + mv) g' ∧ orIn n C (n + mv) = {v} ∧
   ∃ u' : Fin n, side (n := n) C a b = {u'} ∧ s u' = s z1 ∧
   ∃ mu ∈ orN G C \ lam G C, OrReaches n C (n + mu) g ∧ orIn n C (n + mu) = {u'}) := by
 have hne : ∃ a b : Fin n, G.Adj a b := ⟨z1, zp1, hf1.1⟩
 have hvu_G : G.Adj v u := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hvu_U).1
 have hvu_nstar : s(v, u) ∉ starEdges G C := (Finset.mem_sdiff.mp hvu_U).2
 have hcx : circuitFun n C (pairInput v u) = true := by
  rw [congrFun hL.2.1 (pairInput v u)]; exact (graphFun_pair_iff v u).mpr hvu_G
 obtain ⟨a, ha, hva⟩ := (circuitFun_iff_exists_top hL hne _).mp hcx
 have ha' := mem_tops_iff.mp ha
 rw [gateVal_eq_wval, wval_gate_and hL.1 _ ha'.1 ha'.2.1, Bool.and_eq_true] at hva
 have hw0 := (not_belowF_wval_eq hL hLift hne hjunk (opnd C a 0)
  (by have := opnd_lt hL.1 ha'.1 0; omega) (top_opnd_not_belowF hL hne ha 0) (pairInput v u)).mp hva.1
 have hw1 := (not_belowF_wval_eq hL hLift hne hjunk (opnd C a 1)
  (by have := opnd_lt hL.1 ha'.1 1; omega) (top_opnd_not_belowF hL hne ha 1) (pairInput v u)).mp hva.2
 have hnot_both_side : ¬ ((∃ w ∈ side (n := n) C a 0, pairInput v u w = true) ∧
   (∃ w ∈ side (n := n) C a 1, pairInput v u w = true)) := by
  rintro ⟨⟨w0, hw0m, hxw0⟩, ⟨w1, hw1m, hxw1⟩⟩
  apply hvu_nstar
  simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
  simp only [pairInput, decide_eq_true_eq] at hxw0 hxw1
  have hne_w : w0 ≠ w1 := fun h => by subst h; exact G.loopless.irrefl w0 (top_sides_adj hL.1 ha hw0m hw1m)
  refine ⟨a, ha, (w0, w1), ⟨hw0m, hw1m⟩, ?_⟩
  rw [Sym2.eq_iff]
  rcases hxw0 with rfl | rfl <;> rcases hxw1 with rfl | rfl
  ·exact absurd rfl hne_w
  ·exact Or.inl ⟨rfl, rfl⟩
  ·exact Or.inr ⟨rfl, rfl⟩
  ·exact absurd rfl hne_w
 have hnot_same_flag : ∀ g, (g = g1 ∨ g = g2) →
   ¬ (OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) g) := by
  rintro g hg ⟨h0, h1⟩
  have hgj := mem_junk_iff.mp ((hjunk g).mpr hg)
  apply hgj.2.2
  intro x hgx
  apply ha'.2.2 x
  rw [gateVal_eq_wval, wval_gate_and hL.1 x ha'.1 ha'.2.1, Bool.and_eq_true]
  exact ⟨orReaches_val_mono hL.1 x h0 hgx, orReaches_val_mono hL.1 x h1 hgx⟩
 have hnot_opp_flags : ∀ g g', (g = g1 ∧ g' = g2 ∨ g = g2 ∧ g' = g1) →
   gateVal n C g (pairInput v u) = true → gateVal n C g' (pairInput v u) = true →
   ¬ (OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) g') := by
  rintro g g' hgg' hgv hg'v ⟨h0, h1⟩
  apply hnot_both_flags
  rcases hgg' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·refine ⟨hgv, hg'v, fun x hx1 hx2 => ha'.2.2 x ?_⟩
   rw [gateVal_eq_wval, wval_gate_and hL.1 x ha'.1 ha'.2.1, Bool.and_eq_true]
   exact ⟨orReaches_val_mono hL.1 x h0 hx1, orReaches_val_mono hL.1 x h1 hx2⟩
  ·refine ⟨hg'v, hgv, fun x hx1 hx2 => ha'.2.2 x ?_⟩
   rw [gateVal_eq_wval, wval_gate_and hL.1 x ha'.1 ha'.2.1, Bool.and_eq_true]
   exact ⟨orReaches_val_mono hL.1 x h0 hx2, orReaches_val_mono hL.1 x h1 hx1⟩
 have hside_must_be_v : ∀ b : Fin 2, ∀ g, (g = g1 ∨ g = g2) →
   OrReaches n C (opnd C a b) g → gateVal n C g (pairInput v u) = true →
   (∃ w ∈ side (n := n) C a (1 - b), pairInput v u w = true) →
   v ∈ side (n := n) C a (1 - b) := by
  intro b g hg hrb hgv ⟨w, hwm, hxw⟩
  simp only [pairInput, decide_eq_true_eq] at hxw
  rcases hxw with rfl | rfl
  ·exact hwm
  ·exfalso
   have hwmax := top_reaches_flag_wmax hL.1 ha b hrb hwm
   rcases hg with rfl | rfl
   ·exact (hvu_not_wmax.1 hgv).1 hwmax
   ·exact (hvu_not_wmax.2 hgv).1 hwmax
 have hex_bg : ∃ b : Fin 2, ∃ g : ℕ, (g = g1 ∨ g = g2) ∧
   OrReaches n C (opnd C a b) g ∧ gateVal n C g (pairInput v u) = true ∧
   v ∈ side (n := n) C a (1 - b) := by
  rcases hw0 with h0 | ⟨hr0, hg1⟩ | ⟨hr0, hg2⟩
  ·rcases hw1 with h1 | ⟨hr1, hg1⟩ | ⟨hr1, hg2⟩
   ·exact absurd ⟨h0, h1⟩ hnot_both_side
   ·exact ⟨1, g1, Or.inl rfl, hr1, hg1, hside_must_be_v 1 g1 (Or.inl rfl) hr1 hg1 (by simpa [side] using h0)⟩
   ·exact ⟨1, g2, Or.inr rfl, hr1, hg2, hside_must_be_v 1 g2 (Or.inr rfl) hr1 hg2 (by simpa [side] using h0)⟩
  ·rcases hw1 with h1 | ⟨hr1, _⟩ | ⟨hr1, hg2⟩
   ·exact ⟨0, g1, Or.inl rfl, hr0, hg1, hside_must_be_v 0 g1 (Or.inl rfl) hr0 hg1 (by simpa [side] using h1)⟩
   ·exact absurd ⟨hr0, hr1⟩ (hnot_same_flag g1 (Or.inl rfl))
   ·exact absurd ⟨hr0, hr1⟩ (hnot_opp_flags g1 g2 (Or.inl ⟨rfl, rfl⟩) hg1 hg2)
  ·rcases hw1 with h1 | ⟨hr1, hg1⟩ | ⟨hr1, _⟩
   ·exact ⟨0, g2, Or.inr rfl, hr0, hg2, hside_must_be_v 0 g2 (Or.inr rfl) hr0 hg2 (by simpa [side] using h1)⟩
   ·exact absurd ⟨hr0, hr1⟩ (hnot_opp_flags g2 g1 (Or.inr ⟨rfl, rfl⟩) hg2 hg1)
   ·exact absurd ⟨hr0, hr1⟩ (hnot_same_flag g2 (Or.inr rfl))
 obtain ⟨b, g, hg, hrb, hgv, hv_side⟩ := hex_bg
 by_cases hemp : side (n := n) C a b = ∅
 ·right; left
  have haC : a ∈ centreless G C := by
   unfold centreless; rw [Finset.mem_filter]
   refine ⟨ha, ?_⟩
   fin_cases b
   ·exact Or.inl hemp
   ·exact Or.inr hemp
  exact ⟨a, haC, b, g, hg, hgv, hemp, hrb, hv_side⟩
 ·have hneb : (side (n := n) C a b).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
  have haS : a ∈ tops G C \ centreless G C := by
   rw [Finset.mem_sdiff]; refine ⟨ha, fun hc => ?_⟩
   unfold centreless at hc; rw [Finset.mem_filter] at hc
   rcases fin2_eq b with rfl | rfl
   ·rcases hc.2 with h0 | h1
    ·exact hemp h0
    ·simp only [sub_zero] at hv_side; rw [h1] at hv_side; exact Finset.notMem_empty _ hv_side
   ·rcases hc.2 with h0 | h1
    ·have h11 : (1 : Fin 2) - 1 = 0 := rfl; rw [h11, h0] at hv_side; exact Finset.notMem_empty _ hv_side
    ·exact hemp h1
  have hside_eq_v : side (n := n) C a (1 - b) = {v} := by
   ext w
   simp only [Finset.mem_singleton]
   constructor
   ·intro hw
    by_contra hne_w
    have hcard_other : 1 < (side (n := n) C a (1 - b)).card :=
     Finset.one_lt_card.mpr ⟨w, hw, v, hv_side, hne_w⟩
    have hst := top_is_star hL.1 h4 haS
    have hcard_b : (side (n := n) C a b).card = 1 := by
     rcases fin2_eq b with rfl | rfl
     ·simp only [sub_zero] at hcard_other; exact hst.2.2.resolve_right (by omega)
     ·have h11 : (1 : Fin 2) - 1 = 0 := rfl; rw [h11] at hcard_other
      exact hst.2.2.resolve_left (by omega)
    obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hcard_b
    have hw0m : w0 ∈ side (n := n) C a b := by rw [hw0]; simp
    have hadj_v_w0 : G.Adj v w0 := by
     rcases fin2_eq b with rfl | rfl
     ·exact (top_sides_adj hL.1 ha hw0m hv_side).symm
     ·exact top_sides_adj hL.1 ha hv_side hw0m
    have hadj_w_w0 : G.Adj w w0 := by
     rcases fin2_eq b with rfl | rfl
     ·exact (top_sides_adj hL.1 ha hw0m hw).symm
     ·exact top_sides_adj hL.1 ha hw hw0m
    have hswv : s w = s v := bool_eq_of_ne_ne (hbip w w0 hadj_w_w0) (hbip v w0 hadj_v_w0)
    have hwmax := top_reaches_flag_wmax hL.1 ha b hrb hw
    have hadj_wu : G.Adj w u := by
     rcases hg with rfl | rfl
     ·exact (hvu_not_wmax.1 hgv).2 w hswv hwmax
     ·exact (hvu_not_wmax.2 hgv).2 w hswv hwmax
    have hw0_eq_u : w0 = u := noFourCycle_unique h4 hne_w hadj_w_w0 hadj_v_w0 hadj_wu hvu_G
    subst hw0_eq_u
    apply hvu_nstar
    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
    rcases fin2_eq b with rfl | rfl
    ·exact ⟨a, ha, (w0, v), ⟨hw0m, hv_side⟩, Sym2.eq_swap⟩
    ·exact ⟨a, ha, (v, w0), ⟨hv_side, hw0m⟩, rfl⟩
   ·rintro rfl; exact hv_side
  by_cases hown : topOwner C s z1 g1 g2 a = v
  ·exact Or.inl ⟨a, haS, hown⟩
  ·right; right
   have hcard_1mb : (side (n := n) C a (1 - b)).card = 1 := by rw [hside_eq_v]; simp
   have hcard_b : (side (n := n) C a b).card = 1 := by
    by_contra hnb1
    apply hown
    unfold topOwner
    rcases fin2_eq b with rfl | rfl
    ·simp only [sub_zero] at hcard_1mb hside_eq_v
     rw [dif_neg hnb1, dif_pos hcard_1mb]
     have hch := Classical.choose_spec (Finset.card_eq_one.mp hcard_1mb)
     exact Finset.singleton_injective (hch.symm.trans hside_eq_v)
    ·have h11 : (1 : Fin 2) - 1 = 0 := rfl
     rw [h11] at hcard_1mb hside_eq_v
     rw [dif_pos hcard_1mb, dif_neg hnb1]
     have hch := Classical.choose_spec (Finset.card_eq_one.mp hcard_1mb)
     exact Finset.singleton_injective (hch.symm.trans hside_eq_v)
   obtain ⟨u', hu'⟩ := Finset.card_eq_one.mp hcard_b
   have hrf_b : reachesFlag n C g1 g2 (opnd C a b) := by
    rcases hg with rfl | rfl
    ·exact Or.inl hrb
    ·exact Or.inr hrb
   have hrf_1mb : reachesFlag n C g1 g2 (opnd C a (1 - b)) := by
    by_contra hnrf
    apply hown
    unfold topOwner
    rcases fin2_eq b with rfl | rfl
    ·simp only [sub_zero] at hcard_1mb hside_eq_v hnrf
     rw [dif_pos hcard_b, dif_pos hcard_1mb, if_pos ⟨hrf_b, hnrf⟩]
     have hch := Classical.choose_spec (Finset.card_eq_one.mp hcard_1mb)
     exact Finset.singleton_injective (hch.symm.trans hside_eq_v)
    ·have h11 : (1 : Fin 2) - 1 = 0 := rfl
     rw [h11] at hcard_1mb hside_eq_v hnrf
     rw [dif_pos hcard_1mb, dif_pos hcard_b, if_neg (fun h => hnrf h.1), if_pos ⟨hrf_b, hnrf⟩]
     have hch := Classical.choose_spec (Finset.card_eq_one.mp hcard_1mb)
     exact Finset.singleton_injective (hch.symm.trans hside_eq_v)
   have hsu'_z1 : s u' = s z1 := by
    have hadj_u'v : G.Adj u' v := by
     have hu'm : u' ∈ side (n := n) C a b := by rw [hu']; simp
     rcases fin2_eq b with rfl | rfl
     ·exact top_sides_adj hL.1 ha hu'm hv_side
     ·exact (top_sides_adj hL.1 ha hv_side hu'm).symm
    have hcol_u'v : s u' ≠ s v := hbip u' v hadj_u'v
    by_contra hne_s
    have hsv_z1 : s v = s z1 := bool_eq_of_ne_ne hcol_u'v.symm (Ne.symm hne_s)
    apply hown
    unfold topOwner
    rcases fin2_eq b with rfl | rfl
    ·simp only [sub_zero] at hcard_1mb hside_eq_v hrf_1mb
     have hch0 := Classical.choose_spec (Finset.card_eq_one.mp hcard_b)
     have hch1 := Classical.choose_spec (Finset.card_eq_one.mp hcard_1mb)
     have h0eq : Classical.choose (Finset.card_eq_one.mp hcard_b) = u' :=
      Finset.singleton_injective (hch0.symm.trans hu')
     have h1eq : Classical.choose (Finset.card_eq_one.mp hcard_1mb) = v :=
      Finset.singleton_injective (hch1.symm.trans hside_eq_v)
     rw [dif_pos hcard_b, dif_pos hcard_1mb, if_neg (fun h => h.2 hrf_1mb),
      if_neg (fun h => h.2 hrf_b), h0eq, if_neg hne_s, h1eq]
    ·have h11 : (1 : Fin 2) - 1 = 0 := rfl
     rw [h11] at hcard_1mb hside_eq_v hrf_1mb
     have hch0 := Classical.choose_spec (Finset.card_eq_one.mp hcard_1mb)
     have hch1 := Classical.choose_spec (Finset.card_eq_one.mp hcard_b)
     have h0eq : Classical.choose (Finset.card_eq_one.mp hcard_1mb) = v :=
      Finset.singleton_injective (hch0.symm.trans hside_eq_v)
     have h1eq : Classical.choose (Finset.card_eq_one.mp hcard_b) = u' :=
      Finset.singleton_injective (hch1.symm.trans hu')
     rw [dif_pos hcard_1mb, dif_pos hcard_b, if_neg (fun h => h.2 hrf_b),
      if_neg (fun h => h.2 hrf_1mb), h0eq, if_pos hsv_z1]
   have hsv_zp1 : s v = s zp1 := by
    have hadj_u'v : G.Adj u' v := by
     have hu'm : u' ∈ side (n := n) C a b := by rw [hu']; simp
     rcases fin2_eq b with rfl | rfl
     ·exact top_sides_adj hL.1 ha hu'm hv_side
     ·exact (top_sides_adj hL.1 ha hv_side hu'm).symm
    exact bool_eq_of_ne_ne (hbip u' v hadj_u'v).symm (by rw [hsu'_z1]; exact (hbip z1 zp1 hf1.1).symm)
   obtain ⟨g', hg', hrg'⟩ : ∃ g', (g' = g1 ∨ g' = g2) ∧ OrReaches n C (opnd C a (1 - b)) g' := by
    rcases hrf_1mb with h1 | h2
    ·exact ⟨g1, Or.inl rfl, h1⟩
    ·exact ⟨g2, Or.inr rfl, h2⟩
   have hg'ne : g' ≠ g := by
    intro heq; subst heq
    apply hnot_same_flag g' hg'
    fin_cases b
    ·exact ⟨hrb, by simpa using hrg'⟩
    ·exact ⟨by simpa using hrg', hrb⟩
   obtain ⟨mv, hmv_mem, _, hmv_g', hmv_ne, hmv_sub, _⟩ :=
    mixing_of_reaches_and_nonempty hL hLift hne hjunk hg'
     (opnd C a (1 - b)) (by have := opnd_lt hL.1 ha'.1 (1 - b); omega)
     (top_opnd_not_belowF hL hne ha (1 - b)) (by rw [side] at hside_eq_v; rw [hside_eq_v]; simp) hrg'
   have hmv_orIn : orIn n C (n + mv) = {v} := by
    rw [side] at hside_eq_v; rw [hside_eq_v] at hmv_sub
    ext w; constructor
    ·exact fun hw => hmv_sub hw
    ·intro hw; rw [Finset.mem_singleton] at hw; subst hw
     obtain ⟨y, hy⟩ := hmv_ne
     have := Finset.mem_singleton.mp (hmv_sub hy); subst this; exact hy
   obtain ⟨mu, hmu_mem, _, hmu_g, hmu_ne, hmu_sub, _⟩ :=
    mixing_of_reaches_and_nonempty hL hLift hne hjunk hg
     (opnd C a b) (by have := opnd_lt hL.1 ha'.1 b; omega)
     (top_opnd_not_belowF hL hne ha b) (by rw [side] at hu'; rw [hu']; simp) hrb
   have hmu_orIn : orIn n C (n + mu) = {u'} := by
    rw [side] at hu'; rw [hu'] at hmu_sub
    ext w; constructor
    ·exact fun hw => hmu_sub hw
    ·intro hw; rw [Finset.mem_singleton] at hw; subst hw
     obtain ⟨y, hy⟩ := hmu_ne
     have := Finset.mem_singleton.mp (hmu_sub hy); subst this; exact hy
   exact ⟨hsv_zp1, a, haS, b, g, hg, hgv, hside_eq_v, hrb, g', hg', hg'ne, hrg',
    mv, hmv_mem, hmv_g', hmv_orIn, u', hu', hsu'_z1, mu, hmu_mem, hmu_g, hmu_orIn⟩
lemma w_merge_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
  {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {w : ℕ} (hw_lt : w < n + C.gates.length) (hw_nb : ∀ k, w = n + k → ¬ BelowF G C k)
  (A : Finset (Fin n)) (hAne : A.Nonempty) (hAsub : A ⊆ orIn n C w)
  (FacAll : Finset ℕ)
  (hno_pair : ∀ k, OrReaches n C w k → k ∈ lam G C ∪ FacAll → (orIn n C (n + k) ∩ A).card ≤ 1) :
  let H := (orN G C \ lam G C).filter (fun k =>
   OrReaches n C w k ∧ k ∉ FacAll ∧ 2 ≤ (orIn n C (n + k) ∩ A).card)
  A.card ≤ H.card + 1 := by
 intro H
 let R : ℕ → Finset (Fin n) := fun u =>
  if hu : u < n then
   if ⟨u, hu⟩ ∈ A then {⟨u, hu⟩} else ∅
  else if OrReaches n C w (u - n) then orIn n C u ∩ A else ∅
 have hH_lt : ∀ k ∈ H, k < C.gates.length := fun k hk =>
  (mem_orN_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).1).1
 have hSmall : ∀ u < n + C.gates.length, (∀ k ∈ H, u ≠ n + k) → (R u).card ≤ 1 := by
  intro u hu hnot
  dsimp only [R]
  split_ifs with hun hmem hreach
  ·simp
  ·simp
  ·have hk_lt : u - n < C.gates.length := by omega
   have hu_eq : u = n + (u - n) := by omega
   set k := u - n
   have hnbk : ¬ BelowF G C k := by
    intro hbk
    have hstep : ∀ x < n + C.gates.length, (∀ m, x = n + m → ¬ BelowF G C m) →
      OrReaches n C x k → False := by
     intro x
     induction x using Nat.strong_induction_on with
     | ind x ihx =>
      intro hx_lt hx_nb hrxk
      by_cases hxn : x < n
      ·exact orReaches_input_false hxn hrxk
      ·have hm_lt : x - n < C.gates.length := by omega
       have hx_eq : x = n + (x - n) := by omega
       rw [hx_eq, orReaches_gate_iff hm_lt] at hrxk
       rcases hrxk with heq | ⟨horm, y, hy, hny, hylt, hyrk⟩
       ·exact hx_nb (x - n) hx_eq (heq ▸ hbk)
       ·rw [gate_inputs_eq hL.1 hm_lt] at hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        have hnby : ∀ m, y = n + m → ¬ BelowF G C m := by
         intro m hm hbm
         rcases hy with rfl | rfl
         ·exact lift_no_belowF_orN_opnd hL hLift hne hm_lt horm (hx_nb _ hx_eq) 0 (by rw [hm]; exact hbm)
         ·exact lift_no_belowF_orN_opnd hL hLift hne hm_lt horm (hx_nb _ hx_eq) 1 (by rw [hm]; exact hbm)
        exact ihx y (by omega) (by omega) hnby hyrk
    exact hstep w hw_lt hw_nb hreach
   rcases hL.1.1 _ (gateAt_mem hk_lt) with hand | hor
   ·rw [hu_eq, orIn_and_eq_empty (n := n) hk_lt hand]; simp
   ·have hk_orN : k ∈ orN G C := mem_orN_iff.mpr ⟨hk_lt, hor, hnbk⟩
    by_cases hkl : k ∈ lam G C
    ·rw [hu_eq]; exact hno_pair k hreach (Finset.mem_union_left _ hkl)
    ·by_cases hkf : k ∈ FacAll
     ·rw [hu_eq]; exact hno_pair k hreach (Finset.mem_union_right _ hkf)
     ·by_contra hgt
      push Not at hgt
      have hkH : k ∈ H := Finset.mem_filter.mpr
       ⟨Finset.mem_sdiff.mpr ⟨hk_orN, hkl⟩, hreach, hkf, by rw [← hu_eq]; omega⟩
      exact hnot k hkH hu_eq
  ·simp
 have hStep : ∀ k ∈ H, R (n + k) ⊆ R (opnd C k 0) ∪ R (opnd C k 1) := by
  intro k hk
  have hkf := Finset.mem_filter.mp hk
  have hk_orN := mem_orN_iff.mp (Finset.mem_sdiff.mp hkf.1).1
  have hreach : OrReaches n C w k := hkf.2.1
  intro a ha
  dsimp only [R] at ha
  rw [dif_neg (by omega), Nat.add_sub_cancel_left, if_pos hreach, Finset.mem_inter,
   orIn_or_eq_union hL.1 hk_orN.1 hk_orN.2.1, Finset.mem_union] at ha
  rw [Finset.mem_union]
  rcases ha.1 with h0 | h1
  ·left
   dsimp only [R]
   by_cases h0n : opnd C k 0 < n
   ·rw [dif_pos h0n]
    have haeq : a = ⟨opnd C k 0, h0n⟩ := (mem_orIn_input C a ⟨opnd C k 0, h0n⟩).mp h0
    subst haeq; rw [if_pos ha.2]; exact Finset.mem_singleton_self _
   ·rw [dif_neg h0n]
    have hr0 : OrReaches n C w (opnd C k 0 - n) := by
     apply orReaches_trans hreach
     rw [orReaches_gate_iff hk_orN.1]
     refine Or.inr ⟨hk_orN.2.1, opnd C k 0, opnd_mem hL.1 hk_orN.1 0, by omega,
      opnd_lt hL.1 hk_orN.1 0, ?_⟩
     have h0eq : opnd C k 0 = n + (opnd C k 0 - n) := by omega
     have hrs : OrReaches n C (n + (opnd C k 0 - n)) (opnd C k 0 - n) :=
      orReaches_self (by have := opnd_lt hL.1 hk_orN.1 0; have := hk_orN.1; omega)
     rwa [← h0eq] at hrs
    rw [if_pos hr0, Finset.mem_inter]; exact ⟨h0, ha.2⟩
  ·right
   dsimp only [R]
   by_cases h1n : opnd C k 1 < n
   ·rw [dif_pos h1n]
    have haeq : a = ⟨opnd C k 1, h1n⟩ := (mem_orIn_input C a ⟨opnd C k 1, h1n⟩).mp h1
    subst haeq; rw [if_pos ha.2]; exact Finset.mem_singleton_self _
   ·rw [dif_neg h1n]
    have hr1 : OrReaches n C w (opnd C k 1 - n) := by
     apply orReaches_trans hreach
     rw [orReaches_gate_iff hk_orN.1]
     refine Or.inr ⟨hk_orN.2.1, opnd C k 1, opnd_mem hL.1 hk_orN.1 1, by omega,
      opnd_lt hL.1 hk_orN.1 1, ?_⟩
     have h1eq : opnd C k 1 = n + (opnd C k 1 - n) := by omega
     have hrs : OrReaches n C (n + (opnd C k 1 - n)) (opnd C k 1 - n) :=
      orReaches_self (by have := opnd_lt hL.1 hk_orN.1 1; have := hk_orN.1; omega)
     rwa [← h1eq] at hrs
    rw [if_pos hr1, Finset.mem_inter]; exact ⟨h1, ha.2⟩
 obtain ⟨comp, hcard, hmono⟩ := orDag_count hL.1 A H hH_lt R hSmall hStep
 obtain ⟨c, hc⟩ := hmono w hw_lt
 have hA_sub_Rw : A ⊆ R w := by
  intro a ha
  dsimp only [R]
  by_cases hwn : w < n
  ·rw [dif_pos hwn]
   have haeq : a = ⟨w, hwn⟩ := (mem_orIn_input C a ⟨w, hwn⟩).mp (hAsub ha)
   subst haeq; rw [if_pos ha]; exact Finset.mem_singleton_self _
  ·rw [dif_neg hwn]
   have hrw : OrReaches n C w (w - n) := by
    have hweq : w = n + (w - n) := by omega
    have hrs : OrReaches n C (n + (w - n)) (w - n) := orReaches_self (by omega)
    rwa [← hweq] at hrs
   rw [if_pos hrw, Finset.mem_inter]; exact ⟨hAsub ha, ha⟩
 exact mono_card_le hcard (Finset.Subset.refl A) hAne ⟨c, fun a ha => hc a (hA_sub_Rw ha)⟩
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
  ·exact (mem_tops_iff.mp h).2.2
  ·exact (mem_orT_iff.mp h).2.2
 have hcone_to_or : ∀ k < C.gates.length, ¬ BelowF G C k → InCone n C g2 k →
   OrReaches n C (n + k) g2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
   intro hk hnb hin
   have hgt : g2 < k := inCone_lt hin
   have hork : (gateAt C k).op = GateOp.or := by
    rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
    ·exfalso
     have hkj := (hjunk k).mp (mem_junk_iff.mpr ⟨hk, hand, hnb⟩)
     rcases hkj with rfl | rfl <;> omega
    ·exact hor
   rw [inCone_iff hk] at hin
   rcases hin with ⟨w, hw, hnw, hwnk, heq | hsub⟩
   ·rw [orReaches_gate_iff hk]
    refine Or.inr ⟨hork, w, hw, hnw, hwnk, ?_⟩
    rw [show w = n + g2 by omega]; exact orReaches_self hg2j.1
   ·have hnbw : ¬ BelowF G C (w - n) := by
     intro hbw
     rw [gate_inputs_eq hL.1 hk] at hw
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
     rcases hw with rfl | rfl
     ·exact lift_no_belowF_orN_opnd hL hLift hne hk hork hnb 0
       (by rw [show opnd C k 0 = n + (opnd C k 0 - n) by omega]; exact hbw)
     ·exact lift_no_belowF_orN_opnd hL hLift hne hk hork hnb 1
       (by rw [show opnd C k 1 = n + (opnd C k 1 - n) by omega]; exact hbw)
    have hsub_or := ih (w - n) (by omega) (by omega) hnbw hsub
    rw [orReaches_gate_iff hk]
    exact Or.inr ⟨hork, w, hw, hnw, hwnk, by rwa [show n + (w - n) = w by omega] at hsub_or⟩
 have hex_top : ∀ j < C.gates.length, BelowF G C j → InCone n C g2 j →
   ∃ a ∈ tops G C, ∃ b : Fin 2, OrReaches n C (opnd C a b) g2 := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
   intro hj hbf hin
   rcases hL.1.1 _ (gateAt_mem hj) with hand | hor
   ·have hjtop : j ∈ tops G C := mem_tops_iff.mpr ⟨hj, hand, hbf⟩
    rw [inCone_iff hj] at hin
    rcases hin with ⟨w, hw, hnw, hwnj, heq | hsub⟩
    ·rw [gate_inputs_eq hL.1 hj] at hw
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
     have hrg : OrReaches n C w g2 := by rw [show w = n + g2 by omega]; exact orReaches_self hg2j.1
     rcases hw with rfl | rfl
     ·exact ⟨j, hjtop, 0, hrg⟩
     ·exact ⟨j, hjtop, 1, hrg⟩
    ·rw [gate_inputs_eq hL.1 hj] at hw
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
     rcases hw with rfl | rfl
     ·have hnbw := top_opnd_not_belowF hL hne hjtop 0 (opnd C j 0 - n) (by omega)
      have hr := hcone_to_or (opnd C j 0 - n) (by omega) hnbw hsub
      exact ⟨j, hjtop, 0, by rwa [show n + (opnd C j 0 - n) = opnd C j 0 by omega] at hr⟩
     ·have hnbw := top_opnd_not_belowF hL hne hjtop 1 (opnd C j 1 - n) (by omega)
      have hr := hcone_to_or (opnd C j 1 - n) (by omega) hnbw hsub
      exact ⟨j, hjtop, 1, by rwa [show n + (opnd C j 1 - n) = opnd C j 1 by omega] at hr⟩
   ·rw [inCone_iff hj] at hin
    rcases hin with ⟨w, hw, hnw, hwnj, heq | hsub⟩
    ·exfalso
     rw [gate_inputs_eq hL.1 hj] at hw
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
     have hbfg : BelowF G C g2 := by
      rcases hw with rfl | rfl
      ·have h0 := (orT_opnds_belowF hL hj hor hbf 0).2.2; rwa [← heq] at h0
      ·have h1 := (orT_opnds_belowF hL hj hor hbf 1).2.2; rwa [← heq] at h1
     exact hg2j.2.2 hbfg
    ·rw [gate_inputs_eq hL.1 hj] at hw
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
     rcases hw with rfl | rfl
     ·have h0 := orT_opnds_belowF hL hj hor hbf 0
      exact ih (opnd C j 0 - n) (by omega) h0.2.1 h0.2.2 hsub
     ·have h1 := orT_opnds_belowF hL hj hor hbf 1
      exact ih (opnd C j 1 - n) (by omega) h1.2.1 h1.2.2 hsub
 have hg2_cone : InCone n C g2 (C.output - n) := by
  have hc := (least_inOutputCone hL hne g2 hg2j.1).2
  rcases hc with heq | ⟨_, hin⟩
  ·exfalso; apply hg2j.2.2; rw [show g2 = C.output - n by omega]; exact hout_bf
  ·exact hin
 obtain ⟨a, ha, b, hrb⟩ := hex_top (C.output - n) (by omega) hout_bf hg2_cone
 have ha' := mem_tops_iff.mp ha
 have hneb : (side (n := n) C a b).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hemp
  have hac : a ∈ centreless G C := by
   unfold centreless; rw [Finset.mem_filter]
   refine ⟨ha, ?_⟩; fin_cases b
   ·exact Or.inl hemp
   ·exact Or.inr hemp
  rw [hcent_emp] at hac; exact Finset.notMem_empty _ hac
 obtain ⟨m, hm, _, hmg2, _, _, _⟩ := mixing_of_reaches_and_nonempty hL hLift hne hjunk (Or.inr rfl)
  (opnd C a b) (by have := opnd_lt hL.1 ha'.1 b; omega) (top_opnd_not_belowF hL hne ha b) hneb hrb
 have hle : g2 ≤ m := by have := orReaches_le hmg2; omega
 have hne_g2 : m ≠ g2 := by
  intro h; subst h
  have h1 := (mem_orN_iff.mp (Finset.mem_sdiff.mp hm).1).2.1
  rw [h1] at hg2j; cases hg2j.2.1
 exact ⟨m, hm, by omega⟩
lemma case_two_centers {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
  {g1 g2 : ℕ} (hlt12 : g1 < g2) (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {C1 D1 C2 D2 : Finset (Fin n)} {z zp : Fin n}
  (hf1 : IsFlag G C g1 C1 D1 z zp) (hf2 : IsFlag G C g2 C2 D2 z zp) : False := by
 classical
 have hne : ∃ u v : Fin n, G.Adj u v := ⟨z, zp, hf1.1⟩
 have hg12 : g1 ≠ g2 := Nat.ne_of_lt hlt12
 have hg1j := mem_junk_iff.mp ((hjunk g1).mpr (Or.inl rfl))
 have hg2j := mem_junk_iff.mp ((hjunk g2).mpr (Or.inr rfl))
 have hz_ne_zp : z ≠ zp := G.ne_of_adj hf1.1
 obtain ⟨⟨hn10_1, hn10_2, hn11_1, hn11_2⟩, b1, hb1C, hb1D⟩ :=
  g1_operands hbip hL hLift hlt12 hjunk hf1
 obtain ⟨hn20_2, hn21_2, b2, hb2C_sub, hb2D_sub, hb2C_r, hb2C_nr, hb2D_r, hb2D_nr⟩ :=
  g2_operands hbip h4 hL hLift hlt12 hjunk hf1 hf2 rfl rfl
 set w1C := opnd C g1 b1
 set w1D := opnd C g1 (1 - b1)
 set w2C := opnd C g2 b2
 set w2D := opnd C g2 (1 - b2)
 set Cs := C1 ∪ C2
 set Ds := D1 ∪ D2
 set MC := Cs.filter (fun c => s(c, zp) ∈ Ustar G C)
 set MD := Ds.filter (fun d => s(z, d) ∈ Ustar G C)
 set FacC := (orN G C \ lam G C).filter (fun k => OrReaches n C w1C k ∨ OrReaches n C w2C k)
 set FacD := (orN G C \ lam G C).filter (fun k => OrReaches n C w1D k ∨ OrReaches n C w2D k)
 have hFacC_lt : ∀ k ∈ FacC, k < g2 := by
  intro k hk
  have hr := (Finset.mem_filter.mp hk).2
  rcases hr with h1 | h2
  ·have := orReaches_le h1; have := opnd_lt hL.1 hg1j.1 b1; omega
  ·have := orReaches_le h2; have := opnd_lt hL.1 hg2j.1 b2; omega
 have hFacD_lt : ∀ k ∈ FacD, k < g2 := by
  intro k hk
  have hr := (Finset.mem_filter.mp hk).2
  rcases hr with h1 | h2
  ·have := orReaches_le h1; have := opnd_lt hL.1 hg1j.1 (1 - b1); omega
  ·have := orReaches_le h2; have := opnd_lt hL.1 hg2j.1 (1 - b2); omega
 have hDisjCD_all : Disjoint Cs Ds := by
  rw [Finset.disjoint_left]; intro u huC huD
  have hsc : s u = s z := by
   rcases Finset.mem_union.mp huC with h | h
   ·exact flag_color_C hbip hf1 h
   ·exact flag_color_C hbip hf2 h
  have hsd : s u = s zp := by
   rcases Finset.mem_union.mp huD with h | h
   ·exact flag_color_D hbip hf1 h
   ·exact flag_color_D hbip hf2 h
  exact hbip z zp hf1.1 (hsc.symm.trans hsd)
 have hDisjFac : Disjoint FacC FacD := by
  rw [Finset.disjoint_left]; intro k hkC hkD
  have hk_orN := mem_orN_iff.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hkC).1).1
  have hsubC : orIn n C (n + k) ⊆ Cs := by
   rcases (Finset.mem_filter.mp hkC).2 with h1 | h2
   ·exact Finset.Subset.trans (orIn_subset_of_orReaches h1) (by rw [show orIn n C w1C = C1 from hb1C]; exact Finset.subset_union_left)
   ·exact Finset.Subset.trans (orIn_subset_of_orReaches h2) (Finset.Subset.trans hb2C_sub Finset.subset_union_right)
  have hsubD : orIn n C (n + k) ⊆ Ds := by
   rcases (Finset.mem_filter.mp hkD).2 with h1 | h2
   ·exact Finset.Subset.trans (orIn_subset_of_orReaches h1) (by rw [show orIn n C w1D = D1 from hb1D]; exact Finset.subset_union_left)
   ·exact Finset.Subset.trans (orIn_subset_of_orReaches h2) (Finset.Subset.trans hb2D_sub Finset.subset_union_right)
  have hemp : orIn n C (n + k) = ∅ := by
   ext u; simp only [Finset.notMem_empty, iff_false]
   intro hu; exact Finset.disjoint_left.mp hDisjCD_all (hsubC hu) (hsubD hu)
  have hkg2 : k < g2 := hFacC_lt k hkC
  have hn2 : ¬ OrReaches n C (n + k) g2 := fun h => by have := orReaches_le h; omega
  have hval : ∀ x, wval C x (n + k) = true ↔ OrReaches n C (n + k) g1 ∧ gateVal n C g1 x = true := by
   intro x
   have h := not_belowF_wval_eq hL hLift hne hjunk (n + k) (by omega)
    (fun m hm => by have : m = k := (by omega); subst this; exact hk_orN.2.2) x
   simpa [hemp, hn2] using h
  have hr1 : OrReaches n C (n + k) g1 := ((hval (fun _ => true)).mp (wval_allTrue hL.1 (n + k) (by omega))).1
  have hle1 : g1 ≤ k := by have := orReaches_le hr1; omega
  have hne1 : k ≠ g1 := fun h => by rw [h, hg1j.2.1] at hk_orN; cases hk_orN.2.1
  apply least_no_equiv_wire hL hne hk_orN.1 (by omega : n + g1 < n + k)
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [hval x]; simp [hr1, gateVal_eq_wval]
 have hnb_w : ∀ a, a ∈ junk G C → ∀ b : Fin 2, ∀ m, opnd C a b = n + m → ¬ BelowF G C m := by
  intro a ha b m hm hbm
  have ha' := mem_junk_iff.mp ha
  exact least_no_belowF_and_opnd hL hne ha'.1 ha'.2.1 b (by rw [hm]; exact hbm)
 have hC_union : C1 ∪ C2 = C1 ∪ orIn n C w2C := by
  by_cases hr : OrReaches n C w2C g1
  ·have h := hb2C_r hr
   rw [Finset.union_eq_right.mpr h.1, h.2.2]; rfl
  ·rw [show orIn n C w2C = C2 from hb2C_nr hr]
 have hD_union : D1 ∪ D2 = D1 ∪ orIn n C w2D := by
  by_cases hr : OrReaches n C w2D g1
  ·have h := hb2D_r hr
   rw [Finset.union_eq_right.mpr h.1, h.2.2]; rfl
  ·rw [show orIn n C w2D = D2 from hb2D_nr hr]
 have hz_w2C : z ∈ orIn n C w2C ∨ OrReaches n C w2C g1 := by
  by_cases hr : OrReaches n C w2C g1
  ·exact Or.inr hr
  ·left; rw [show orIn n C w2C = C2 from hb2C_nr hr]; exact hf2.2.1
 have hzp_w2D : zp ∈ orIn n C w2D ∨ OrReaches n C w2D g1 := by
  by_cases hr : OrReaches n C w2D g1
  ·exact Or.inr hr
  ·left; rw [show orIn n C w2D = D2 from hb2D_nr hr]; exact hf2.2.2.1
 have hFacC_b := merged_opnds_fac_bound hL hLift h4 hne hjunk
  (by have := opnd_lt hL.1 hg1j.1 b1; omega : w1C < n + g2)
  (opnd_lt hL.1 hg2j.1 b2)
  (hnb_w g1 ((hjunk g1).mpr (Or.inl rfl)) b1)
  (hnb_w g2 ((hjunk g2).mpr (Or.inr rfl)) b2)
  (show orIn n C w1C = C1 from hb1C) hb2C_sub hC_union
  (fun u hu => by rcases Finset.mem_union.mp hu with h | h; exact (hf1.2.2.2.1 u h).symm; exact (hf2.2.2.2.1 u h).symm)
  hf1.2.1 hz_w2C
 have hFacD_b := merged_opnds_fac_bound hL hLift h4 hne hjunk
  (by have := opnd_lt hL.1 hg1j.1 (1 - b1); omega : w1D < n + g2)
  (opnd_lt hL.1 hg2j.1 (1 - b2))
  (hnb_w g1 ((hjunk g1).mpr (Or.inl rfl)) (1 - b1))
  (hnb_w g2 ((hjunk g2).mpr (Or.inr rfl)) (1 - b2))
  (show orIn n C w1D = D1 from hb1D) hb2D_sub hD_union
  (fun u hu => by rcases Finset.mem_union.mp hu with h | h; exact (hf1.2.2.2.2.1 u h).symm; exact (hf2.2.2.2.2.1 u h).symm)
  hf1.2.2.1 hzp_w2D
 have hMC_eq : Cs.filter (fun u => s(zp, u) ∈ Ustar G C) = MC := by
  ext u; simp [MC, Sym2.eq_swap]
 dsimp only at hFacC_b hFacD_b
 rw [hMC_eq] at hFacC_b
 have hFac_sub : FacC ∪ FacD ⊆ orN G C \ lam G C :=
  Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
 have hUsub := ustar_sub_flagEdges hbip hL hLift h4 hjunk hf1 hf2
 have run_surgery : ∀ L : Fin n → Finset (Fin n),
   (∀ u ∈ L z, G.Adj z u) → (∀ u ∈ L zp, G.Adj zp u) →
   (∀ e ∈ Ustar G C, (∃ u ∈ L z, e = s(z, u)) ∨ (∃ u ∈ L zp, e = s(zp, u))) →
   let Zact := ({z, zp} : Finset (Fin n)).filter (fun v => (L v).Nonempty)
   let Zhas := Zact.filter (fun v => ∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = v)
   2 * (centreless G C).card + (orN G C \ lam G C).card + 2 ≤
    (L z).card + (L zp).card + (Zact \ Zhas).card := by
  intro L hLz hLzp hcov Zact Zhas
  let topOf : Fin n → ℕ := fun v =>
   if h : ∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = v then Classical.choose h else 0
  have hbound := master_surgery_bound hL hLift h4 hg12 hjunk hne Zact Zhas L topOf
   (Finset.filter_subset _ _)
   (fun v hv => (Finset.mem_filter.mp hv).2)
   (fun v hv u hu => by
    have hv' := (Finset.mem_filter.mp hv).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
    rcases hv' with rfl | rfl
    ·exact hLz u hu
    ·exact hLzp u hu)
   (fun e he => by
    rcases hcov e he with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    ·exact ⟨z, Finset.mem_filter.mpr ⟨by simp, ⟨u, hu⟩⟩, u, hu, rfl⟩
    ·exact ⟨zp, Finset.mem_filter.mpr ⟨by simp, ⟨u, hu⟩⟩, u, hu, rfl⟩)
   (fun v hv => by
    have h := (Finset.mem_filter.mp hv).2
    simp only [topOf, dif_pos h]; exact (Classical.choose_spec h).1)
   (fun v hv => by
    have h := (Finset.mem_filter.mp hv).2
    simp only [topOf, dif_pos h]
    have hsp := Classical.choose_spec h
    have hside := topOwner_side hL.1 h4 s z g1 g2 hsp.1
    rwa [hsp.2] at hside)
   (fun v1 hv1 v2 hv2 heq => by
    have h1 := (Finset.mem_filter.mp hv1).2
    have h2 := (Finset.mem_filter.mp hv2).2
    simp only [topOf, dif_pos h1, dif_pos h2] at heq
    have hsp1 := Classical.choose_spec h1
    have hsp2 := Classical.choose_spec h2
    rw [← hsp1.2, heq, hsp2.2])
  have hsum_le : ∑ v ∈ Zact, (L v).card ≤ (L z).card + (L zp).card := by
   calc ∑ v ∈ Zact, (L v).card ≤ ∑ v ∈ ({z, zp} : Finset (Fin n)), (L v).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = (L z).card + (L zp).card := Finset.sum_pair hz_ne_zp
  omega
 by_cases he0 : s(z, zp) ∈ Ustar G C
 ·
  have hzMC : z ∈ MC := Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hf1.2.1, he0⟩
  have hzpMD : zp ∈ MD := Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hf1.2.2.1, he0⟩
  have hMC_le : MC.card ≤ FacC.card + 1 := hFacC_b.1 ⟨z, hzMC⟩
  have hMD_le : MD.card ≤ FacD.card + 1 := hFacD_b.1 ⟨zp, hzpMD⟩
  have hFac_le : FacC.card + FacD.card ≤ (orN G C \ lam G C).card := by
   rw [← Finset.card_union_of_disjoint hDisjFac]; exact Finset.card_le_card hFac_sub
  by_cases hMD1 : (MD.erase zp).Nonempty
  ·
   let L : Fin n → Finset (Fin n) := fun v => if v = z then MD else if v = zp then MC.erase z else ∅
   have hLz : L z = MD := by simp [L]
   have hLzp : L zp = MC.erase z := by simp [L, hz_ne_zp.symm]
   have hcov : ∀ e ∈ Ustar G C, (∃ u ∈ L z, e = s(z, u)) ∨ (∃ u ∈ L zp, e = s(zp, u)) := by
    intro e he
    have heF := hUsub he
    simp only [Finset.mem_union, flagEdges, Finset.mem_image] at heF
    rcases heF with (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩) | (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩)
    ·left; exact ⟨d, by rw [hLz]; exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hd, he⟩, rfl⟩
    ·by_cases hcz : c = z
     ·subst hcz; left; exact ⟨zp, by rw [hLz]; exact hzpMD, rfl⟩
     ·right; exact ⟨c, by rw [hLzp]; exact Finset.mem_erase.mpr ⟨hcz, Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hc, he⟩⟩, Sym2.eq_swap⟩
    ·left; exact ⟨d, by rw [hLz]; exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hd, he⟩, rfl⟩
    ·by_cases hcz : c = z
     ·subst hcz; left; exact ⟨zp, by rw [hLz]; exact hzpMD, rfl⟩
     ·right; exact ⟨c, by rw [hLzp]; exact Finset.mem_erase.mpr ⟨hcz, Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hc, he⟩⟩, Sym2.eq_swap⟩
   have hsurg := run_surgery L
    (fun u hu => by rw [hLz] at hu; rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with h | h; exact (hf1.2.2.2.2.1 u h).symm; exact (hf2.2.2.2.2.1 u h).symm)
    (fun u hu => by rw [hLzp] at hu; rcases Finset.mem_union.mp (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1 with h | h; exact (hf1.2.2.2.1 u h).symm; exact (hf2.2.2.2.1 u h).symm)
    hcov
   dsimp only at hsurg
   set Zact := ({z, zp} : Finset (Fin n)).filter (fun v => (L v).Nonempty)
   set Zhas := Zact.filter (fun v => ∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = v)
   have hZnew_le2 : (Zact \ Zhas).card ≤ 2 := by
    calc (Zact \ Zhas).card ≤ Zact.card := Finset.card_le_card Finset.sdiff_subset
     _ ≤ ({z, zp} : Finset (Fin n)).card := Finset.card_le_card (Finset.filter_subset _ _)
     _ = 2 := Finset.card_pair hz_ne_zp
   have hcard_er : (MC.erase z).card = MC.card - 1 := Finset.card_erase_of_mem hzMC
   rw [hLz, hLzp, hcard_er] at hsurg
   by_cases hcent0 : centreless G C = ∅
   ·obtain ⟨m, hm_mem, hmg2⟩ := exists_mixing_gt_g2 hL hLift hne hlt12 hjunk hcent0
    have hm_nFac : m ∉ FacC ∪ FacD := by
     intro hmF; rcases Finset.mem_union.mp hmF with h | h
     ·have := hFacC_lt m h; omega
     ·have := hFacD_lt m h; omega
    have hFac_strict : FacC.card + FacD.card + 1 ≤ (orN G C \ lam G C).card := by
     have hsub' : insert m (FacC ∪ FacD) ⊆ orN G C \ lam G C := Finset.insert_subset hm_mem hFac_sub
     have hle' := Finset.card_le_card hsub'
     rw [Finset.card_insert_of_notMem hm_nFac, Finset.card_union_of_disjoint hDisjFac] at hle'
     exact hle'
    have hz_has : z ∈ Zhas := by
     have hz_act : z ∈ Zact := Finset.mem_filter.mpr ⟨by simp, by rw [hLz]; exact ⟨zp, hzpMD⟩⟩
     rw [Finset.mem_filter]; refine ⟨hz_act, ?_⟩
     obtain ⟨d, hd⟩ := hMD1
     have hdzp : d ≠ zp := (Finset.mem_erase.mp hd).1
     have hd_filt := Finset.mem_filter.mp (Finset.mem_of_mem_erase hd)
     have hzd_U : s(z, d) ∈ Ustar G C := hd_filt.2
     have hzd_G : G.Adj z d := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hzd_U).1
     have hnot_both : ¬ (gateVal n C g1 (pairInput z d) = true ∧ gateVal n C g2 (pairInput z d) = true ∧
       ∀ x, gateVal n C g1 x = true → gateVal n C g2 x = true → graphFun G ∅ x = true) := by
      rintro ⟨_, _, hall⟩
      obtain ⟨c1, hc1, hc1z⟩ := flag_exists_other_C hf1
      obtain ⟨d1, hd1, hd1zp⟩ := flag_exists_other_D hf1
      obtain ⟨c2, hc2, hc2z⟩ := flag_exists_other_C hf2
      obtain ⟨d2, hd2, hd2zp⟩ := flag_exists_other_D hf2
      let x : Fin n → Bool := fun w => decide (w = c1 ∨ w = d1 ∨ w = c2 ∨ w = d2)
      have hg1x : gateVal n C g1 x = true := by
       rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
       exact ⟨⟨c1, hc1, by simp [x]⟩, ⟨d1, hd1, by simp [x]⟩⟩
      have hg2x : gateVal n C g2 x = true := by
       rw [hf2.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
       exact ⟨⟨c2, hc2, by simp [x]⟩, ⟨d2, hd2, by simp [x]⟩⟩
      have hFx := (graphFun_iff x).mp (hall x hg1x hg2x)
      rcases hFx with ⟨a, b, hab, ha, hb⟩
      simp only [x, decide_eq_true_eq] at ha hb
      have hcol_c1 : s c1 = s z := flag_color_C hbip hf1 hc1
      have hcol_c2 : s c2 = s z := flag_color_C hbip hf2 hc2
      have hcol_d1 : s d1 = s zp := flag_color_D hbip hf1 hd1
      have hcol_d2 : s d2 = s zp := flag_color_D hbip hf2 hd2
      have hno_cd : ∀ c d', (c = c1 ∨ c = c2) → (d' = d1 ∨ d' = d2) → ¬ G.Adj c d' := by
       intro c d' hc hd' hadj
       have hcz' : c ≠ z := hc.elim (fun h => h ▸ hc1z) (fun h => h ▸ hc2z)
       have hdzp' : d' ≠ zp := hd'.elim (fun h => h ▸ hd1zp) (fun h => h ▸ hd2zp)
       have hczp : G.Adj c zp := hc.elim (fun h => h ▸ hf1.2.2.2.1 c1 hc1) (fun h => h ▸ hf2.2.2.2.1 c2 hc2)
       have hdz : G.Adj d' z := hd'.elim (fun h => h ▸ hf1.2.2.2.2.1 d1 hd1) (fun h => h ▸ hf2.2.2.2.2.1 d2 hd2)
       exact hdzp' (noFourCycle_unique h4 hcz' hadj hdz.symm hczp hf1.1)
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
      ·exact G.loopless.irrefl _ hab
      ·exact hno_cd _ _ (Or.inl rfl) (Or.inl rfl) hab
      ·exact hbip _ _ hab (hcol_c1.trans hcol_c2.symm)
      ·exact hno_cd _ _ (Or.inl rfl) (Or.inr rfl) hab
      ·exact hno_cd _ _ (Or.inl rfl) (Or.inl rfl) hab.symm
      ·exact G.loopless.irrefl _ hab
      ·exact hno_cd _ _ (Or.inr rfl) (Or.inl rfl) hab.symm
      ·exact hbip _ _ hab (hcol_d1.trans hcol_d2.symm)
      ·exact hbip _ _ hab (hcol_c2.trans hcol_c1.symm)
      ·exact hno_cd _ _ (Or.inr rfl) (Or.inl rfl) hab
      ·exact G.loopless.irrefl _ hab
      ·exact hno_cd _ _ (Or.inr rfl) (Or.inr rfl) hab
      ·exact hno_cd _ _ (Or.inl rfl) (Or.inr rfl) hab.symm
      ·exact hbip _ _ hab (hcol_d2.trans hcol_d1.symm)
      ·exact hno_cd _ _ (Or.inr rfl) (Or.inr rfl) hab.symm
      ·exact G.loopless.irrefl _ hab
     have hnw :
       (gateVal n C g1 (pairInput z d) = true →
        (¬ ∀ x, gateVal n C g1 x = true → x d = true → graphFun G ∅ x = true) ∧
        (∀ w : Fin n, s w = s z → (∀ x, gateVal n C g1 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w d)) ∧
       (gateVal n C g2 (pairInput z d) = true →
        (¬ ∀ x, gateVal n C g2 x = true → x d = true → graphFun G ∅ x = true) ∧
        (∀ w : Fin n, s w = s z → (∀ x, gateVal n C g2 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w d)) := by
      constructor
      ·intro h1
       have hd1 : d ∈ D1 := by
        rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h1
        rcases h1.2 with ⟨d', hd', hdd'⟩
        simp only [pairInput, decide_eq_true_eq] at hdd'
        rcases hdd' with rfl | rfl
        ·exact absurd (flag_color_D hbip hf1 hd') (hbip _ zp hf1.1)
        ·exact hd'
       exact ⟨flag_wmax_not_D_other h4 hf1 hd1 hdzp,
        fun w hsw hw => flag_wmax_adj_D hbip h4 hf1 hw hsw hd1 hdzp⟩
      ·intro h2
       have hd2 : d ∈ D2 := by
        rw [hf2.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h2
        rcases h2.2 with ⟨d', hd', hdd'⟩
        simp only [pairInput, decide_eq_true_eq] at hdd'
        rcases hdd' with rfl | rfl
        ·exact absurd (flag_color_D hbip hf2 hd') (hbip _ zp hf2.1)
        ·exact hd'
       exact ⟨flag_wmax_not_D_other h4 hf2 hd2 hdzp,
        fun w hsw hw => flag_wmax_adj_D hbip h4 hf2 hw hsw hd2 hdzp⟩
     rcases golden_edge_cover hbip h4 hL hLift hjunk hf1 hf2 rfl rfl hzd_U hnw hnot_both with
      hA | ⟨a, haC, _⟩ | ⟨hcol, _⟩
     ·exact hA
     ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
     ·exact absurd hcol (hbip z zp hf1.1)
    have hZnew_le1 : (Zact \ Zhas).card ≤ 1 := by
     have hsub1 : Zact \ Zhas ⊆ {zp} := by
      intro v hv
      have hv1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
      have hv2 := (Finset.mem_sdiff.mp hv).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv1 ⊢
      exact hv1.resolve_left (fun h => hv2 (h ▸ hz_has))
     exact (Finset.card_le_card hsub1).trans (by simp)
    omega
   ·have hcent_pos : 1 ≤ (centreless G C).card :=
     Finset.Nonempty.card_pos (Finset.nonempty_iff_ne_empty.mpr hcent0)
    omega
  ·
   have hMD_eq : MD = {zp} := by
    ext d; simp only [Finset.mem_singleton]
    constructor
    ·intro hd; by_contra hne'
     exact hMD1 ⟨d, Finset.mem_erase.mpr ⟨hne', hd⟩⟩
    ·rintro rfl; exact hzpMD
   let L : Fin n → Finset (Fin n) := fun v => if v = zp then MC else ∅
   have hLz : L z = ∅ := by simp [L, hz_ne_zp]
   have hLzp : L zp = MC := by simp [L]
   have hcov : ∀ e ∈ Ustar G C, (∃ u ∈ L z, e = s(z, u)) ∨ (∃ u ∈ L zp, e = s(zp, u)) := by
    intro e he
    have heF := hUsub he
    simp only [Finset.mem_union, flagEdges, Finset.mem_image] at heF
    rcases heF with (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩) | (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩)
    ·have hdMD : d ∈ MD := Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hd, he⟩
     rw [hMD_eq, Finset.mem_singleton] at hdMD; subst hdMD
     right; exact ⟨z, by rw [hLzp]; exact hzMC, Sym2.eq_swap⟩
    ·right; exact ⟨c, by rw [hLzp]; exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hc, he⟩, Sym2.eq_swap⟩
    ·have hdMD : d ∈ MD := Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hd, he⟩
     rw [hMD_eq, Finset.mem_singleton] at hdMD; subst hdMD
     right; exact ⟨z, by rw [hLzp]; exact hzMC, Sym2.eq_swap⟩
    ·right; exact ⟨c, by rw [hLzp]; exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hc, he⟩, Sym2.eq_swap⟩
   have hsurg := run_surgery L
    (fun u hu => by rw [hLz] at hu; exact absurd hu (Finset.notMem_empty _))
    (fun u hu => by rw [hLzp] at hu; rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with h | h; exact (hf1.2.2.2.1 u h).symm; exact (hf2.2.2.2.1 u h).symm)
    hcov
   dsimp only at hsurg
   set Zact := ({z, zp} : Finset (Fin n)).filter (fun v => (L v).Nonempty)
   set Zhas := Zact.filter (fun v => ∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = v)
   have hZnew_le1 : (Zact \ Zhas).card ≤ 1 := by
    have hsub1 : Zact \ Zhas ⊆ {zp} := by
     intro v hv
     have hv1 := Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1
     simp only [Finset.mem_insert, Finset.mem_singleton] at hv1 ⊢
     rcases hv1.1 with rfl | rfl
     ·rw [hLz] at hv1; exact absurd hv1.2 (by simp)
     ·rfl
    exact (Finset.card_le_card hsub1).trans (by simp)
   rw [hLz, hLzp, Finset.card_empty, zero_add] at hsurg
   have hFacC_le : FacC.card ≤ (orN G C \ lam G C).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
   by_cases hcent0 : centreless G C = ∅
   ·obtain ⟨m, hm_mem, hmg2⟩ := exists_mixing_gt_g2 hL hLift hne hlt12 hjunk hcent0
    have hm_nFac : m ∉ FacC := fun h => by have := hFacC_lt m h; omega
    have hFac_strict : FacC.card + 1 ≤ (orN G C \ lam G C).card := by
     have hsub' := Finset.insert_subset hm_mem (Finset.filter_subset _ _ : FacC ⊆ orN G C \ lam G C)
     have hle' := Finset.card_le_card hsub'
     rw [Finset.card_insert_of_notMem hm_nFac] at hle'; exact hle'
    omega
   ·have hcent_pos : 1 ≤ (centreless G C).card :=
     Finset.Nonempty.card_pos (Finset.nonempty_iff_ne_empty.mpr hcent0)
    omega
 ·
  have hz_nMC : z ∉ MC := fun h => he0 (Finset.mem_filter.mp h).2
  have hzp_nMD : zp ∉ MD := fun h => he0 (Finset.mem_filter.mp h).2
  have hMC_le : MC.card ≤ FacC.card := hFacC_b.2.1 hz_nMC
  have hMD_le : MD.card ≤ FacD.card := hFacD_b.2.1 hzp_nMD
  have hFac_le : FacC.card + FacD.card ≤ (orN G C \ lam G C).card := by
   rw [← Finset.card_union_of_disjoint hDisjFac]; exact Finset.card_le_card hFac_sub
  have he0_star : s(z, zp) ∈ starEdges G C := by
   by_contra hns
   exact he0 (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hf1.1, hns⟩)
  obtain ⟨a0, ha0S, ha0own⟩ := topOwner_of_starEdge hL.1 h4 s z g1 g2 he0_star
  let L : Fin n → Finset (Fin n) := fun v => if v = z then MD else if v = zp then MC else ∅
  have hLz : L z = MD := by simp [L]
  have hLzp : L zp = MC := by simp [L, hz_ne_zp.symm]
  have hcov : ∀ e ∈ Ustar G C, (∃ u ∈ L z, e = s(z, u)) ∨ (∃ u ∈ L zp, e = s(zp, u)) := by
   intro e he
   have heF := hUsub he
   simp only [Finset.mem_union, flagEdges, Finset.mem_image] at heF
   rcases heF with (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩) | (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩)
   ·left; exact ⟨d, by rw [hLz]; exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hd, he⟩, rfl⟩
   ·right; exact ⟨c, by rw [hLzp]; exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hc, he⟩, Sym2.eq_swap⟩
   ·left; exact ⟨d, by rw [hLz]; exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hd, he⟩, rfl⟩
   ·right; exact ⟨c, by rw [hLzp]; exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hc, he⟩, Sym2.eq_swap⟩
  have hsurg := run_surgery L
   (fun u hu => by rw [hLz] at hu; rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with h | h; exact (hf1.2.2.2.2.1 u h).symm; exact (hf2.2.2.2.2.1 u h).symm)
   (fun u hu => by rw [hLzp] at hu; rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with h | h; exact (hf1.2.2.2.1 u h).symm; exact (hf2.2.2.2.1 u h).symm)
   hcov
  dsimp only at hsurg
  set Zact := ({z, zp} : Finset (Fin n)).filter (fun v => (L v).Nonempty)
  set Zhas := Zact.filter (fun v => ∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = v)
  have hZnew_le1 : (Zact \ Zhas).card ≤ 1 := by
   rcases ha0own with hown_z | hown_zp
   ·have hsub1 : Zact \ Zhas ⊆ {zp} := by
     intro v hv
     have hv1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
     have hv2 := (Finset.mem_sdiff.mp hv).2
     simp only [Finset.mem_insert, Finset.mem_singleton] at hv1 ⊢
     rcases hv1 with rfl | rfl
     ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1, a0, ha0S, hown_z⟩) hv2
     ·rfl
    exact (Finset.card_le_card hsub1).trans (by simp)
   ·have hsub1 : Zact \ Zhas ⊆ {z} := by
     intro v hv
     have hv1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
     have hv2 := (Finset.mem_sdiff.mp hv).2
     simp only [Finset.mem_insert, Finset.mem_singleton] at hv1 ⊢
     rcases hv1 with rfl | rfl
     ·rfl
     ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1, a0, ha0S, hown_zp⟩) hv2
    exact (Finset.card_le_card hsub1).trans (by simp)
  rw [hLz, hLzp] at hsurg
  omega
lemma bichrom_w_extra {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
  {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {w : ℕ} (hw_lt : w < n + C.gates.length) (hw_nb : ∀ k, w = n + k → ¬ BelowF G C k)
  {u v : Fin n} (hu : u ∈ orIn n C w) (hv : v ∈ orIn n C w) (hcol : s u ≠ s v)
  (FacAll : Finset ℕ) (hFac_mono : ∀ k ∈ FacAll, ∀ x y, x ∈ orIn n C (n + k) → y ∈ orIn n C (n + k) → s x = s y) :
  ∃ m ∈ orN G C \ lam G C, m ∉ FacAll ∧ 2 ≤ (orIn n C (n + m)).card := by
 have huv : u ≠ v := fun h => hcol (h ▸ rfl)
 let A : Finset (Fin n) := {u, v}
 have hno_pair : ∀ k, OrReaches n C w k → k ∈ lam G C ∪ FacAll → (orIn n C (n + k) ∩ A).card ≤ 1 := by
  intro k _ hk
  by_contra hgt; push Not at hgt
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hgt
  have hx' := Finset.mem_inter.mp hx
  have hy' := Finset.mem_inter.mp hy
  have hsxy : s x ≠ s y := by
   simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx' hy'
   rcases hx'.2 with rfl | rfl <;> rcases hy'.2 with rfl | rfl
   ·exact absurd rfl hxy
   ·exact hcol
   ·exact hcol.symm
   ·exact absurd rfl hxy
  rcases Finset.mem_union.mp hk with hlam | hfac
  ·rcases (Finset.mem_filter.mp hlam).2.2.2 with ⟨a, ha, b, hcard1, hr⟩
   obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
   have hsub := orIn_subset_of_orReaches hr
   have hcm : c ∈ side (n := n) C a (1 - b) := by rw [hc]; simp
   have hax : G.Adj c x := by
    fin_cases b
    ·exact (top_sides_adj hL.1 ha (hsub hx'.1) hcm).symm
    ·exact top_sides_adj hL.1 ha hcm (hsub hx'.1)
   have hay : G.Adj c y := by
    fin_cases b
    ·exact (top_sides_adj hL.1 ha (hsub hy'.1) hcm).symm
    ·exact top_sides_adj hL.1 ha hcm (hsub hy'.1)
   have h1 := hbip c x hax
   have h2 := hbip c y hay
   cases sc : s c <;> cases sx : s x <;> cases sy : s y <;> simp_all
  ·exact hsxy (hFac_mono k hfac x y hx'.1 hy'.1)
 have hwb := w_merge_bound hL hLift hne hjunk hw_lt hw_nb A ⟨u, by simp [A]⟩
  (fun x hx => by simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption)
  FacAll hno_pair
 rw [Finset.card_pair huv] at hwb
 have hHne : ((orN G C \ lam G C).filter (fun k =>
   OrReaches n C w k ∧ k ∉ FacAll ∧ 2 ≤ (orIn n C (n + k) ∩ A).card)).Nonempty :=
  Finset.card_pos.mp (by omega)
 obtain ⟨m, hm⟩ := hHne
 have hmf := Finset.mem_filter.mp hm
 exact ⟨m, hmf.1, hmf.2.2.1, le_trans hmf.2.2.2 (Finset.card_le_card Finset.inter_subset_left)⟩
lemma case_three_centers {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
  {g1 g2 : ℕ} (hlt12 : g1 < g2) (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {C1 D1 C2 D2 : Finset (Fin n)} {z zp1 zp2 : Fin n} (hzp12 : zp1 ≠ zp2)
  (hf1 : IsFlag G C g1 C1 D1 z zp1) (hf2 : IsFlag G C g2 C2 D2 z zp2) : False := by
 classical
 have hne : ∃ u v : Fin n, G.Adj u v := ⟨z, zp1, hf1.1⟩
 have hg12 : g1 ≠ g2 := Nat.ne_of_lt hlt12
 have hg1j := mem_junk_iff.mp ((hjunk g1).mpr (Or.inl rfl))
 have hg2j := mem_junk_iff.mp ((hjunk g2).mpr (Or.inr rfl))
 have hszp : s zp1 = s zp2 := by
  have h1 := hbip z zp1 hf1.1
  have h2 := hbip z zp2 hf2.1
  cases sz : s z <;> cases s1 : s zp1 <;> cases s2 : s zp2 <;> simp_all
 have hz_ne1 : z ≠ zp1 := G.ne_of_adj hf1.1
 have hz_ne2 : z ≠ zp2 := G.ne_of_adj hf2.1
 obtain ⟨⟨hn10_1, hn10_2, hn11_1, hn11_2⟩, b1, hb1C, hb1D⟩ :=
  g1_operands hbip hL hLift hlt12 hjunk hf1
 obtain ⟨hn20_2, hn21_2, b2, hb2C_sub, hb2D_sub, hb2C_r, hb2C_nr, hb2D_r, hb2D_nr⟩ :=
  g2_operands hbip h4 hL hLift hlt12 hjunk hf1 hf2 rfl hszp
 set w1C := opnd C g1 b1
 set w1D := opnd C g1 (1 - b1)
 set w2C := opnd C g2 b2
 set w2D := opnd C g2 (1 - b2)
 have hnw1C_1 : ¬ OrReaches n C w1C g1 := by fin_cases b1 <;> assumption
 have hnw1C_2 : ¬ OrReaches n C w1C g2 := by fin_cases b1 <;> assumption
 have hnw1D_1 : ¬ OrReaches n C w1D g1 := by fin_cases b1 <;> assumption
 have hnw1D_2 : ¬ OrReaches n C w1D g2 := by fin_cases b1 <;> assumption
 have hnw2C_1 : ¬ OrReaches n C w2C g1 := fun h => hzp12 (hb2C_r h).2.1
 have hnw2C_2 : ¬ OrReaches n C w2C g2 := by fin_cases b2 <;> assumption
 have hnw2D_2 : ¬ OrReaches n C w2D g2 := by fin_cases b2 <;> assumption
 have hw2C_eq : orIn n C w2C = C2 := hb2C_nr hnw2C_1
 set MC1 := C1.filter (fun c => s(c, zp1) ∈ Ustar G C)
 set MC2 := C2.filter (fun c => s(c, zp2) ∈ Ustar G C)
 set MD1 := D1.filter (fun d => s(z, d) ∈ Ustar G C)
 set MD2 := D2.filter (fun d => s(z, d) ∈ Ustar G C)
 set MD := MD1 ∪ MD2
 set FacC1 := (orN G C \ lam G C).filter (fun k => OrReaches n C w1C k)
 set FacC2 := (orN G C \ lam G C).filter (fun k => OrReaches n C w2C k)
 set FacD := (orN G C \ lam G C).filter (fun k => OrReaches n C w1D k ∨ OrReaches n C w2D k)
 have hnb_w : ∀ a, a ∈ junk G C → ∀ b : Fin 2, ∀ m, opnd C a b = n + m → ¬ BelowF G C m := by
  intro a ha b m hm hbm
  have ha' := mem_junk_iff.mp ha
  exact least_no_belowF_and_opnd hL hne ha'.1 ha'.2.1 b (by rw [hm]; exact hbm)
 have hFC1_raw := single_opnd_fac_bound hL hLift h4 hne hjunk
  (by have := opnd_lt hL.1 hg1j.1 b1; omega : w1C < n + g2)
  (hnb_w g1 ((hjunk g1).mpr (Or.inl rfl)) b1) hnw1C_1
  (show orIn n C w1C = C1 from hb1C) (fun u hu => (hf1.2.2.2.1 u hu).symm)
 have hFC2_raw := single_opnd_fac_bound hL hLift h4 hne hjunk
  (opnd_lt hL.1 hg2j.1 b2)
  (hnb_w g2 ((hjunk g2).mpr (Or.inr rfl)) b2) hnw2C_1
  hw2C_eq (fun u hu => (hf2.2.2.2.1 u hu).symm)
 have hMC1_swap : C1.filter (fun u => s(zp1, u) ∈ Ustar G C) = MC1 := by ext u; simp [MC1, Sym2.eq_swap]
 have hMC2_swap : C2.filter (fun u => s(zp2, u) ∈ Ustar G C) = MC2 := by ext u; simp [MC2, Sym2.eq_swap]
 dsimp only at hFC1_raw hFC2_raw
 rw [hMC1_swap] at hFC1_raw
 rw [hMC2_swap] at hFC2_raw
 have hFC1_er : (MC1.erase z).card ≤ FacC1.card := by
  by_cases hzM : z ∈ MC1
  ·rw [Finset.card_erase_of_mem hzM]; have h1 : MC1.card ≤ FacC1.card + 1 := hFC1_raw.1 ⟨z, hzM⟩; omega
  ·rw [Finset.erase_eq_of_notMem hzM]; exact hFC1_raw.2 ⟨z, hf1.2.1, hzM⟩
 have hFC2_er : (MC2.erase z).card ≤ FacC2.card := by
  by_cases hzM : z ∈ MC2
  ·rw [Finset.card_erase_of_mem hzM]; have h2 : MC2.card ≤ FacC2.card + 1 := hFC2_raw.1 ⟨z, hzM⟩; omega
  ·rw [Finset.erase_eq_of_notMem hzM]; exact hFC2_raw.2 ⟨z, hf2.2.1, hzM⟩
 have hFacC1_pure : ∀ k ∈ FacC1, k < g2 ∧ ¬ OrReaches n C (n + k) g1 ∧ ¬ OrReaches n C (n + k) g2 ∧
   orIn n C (n + k) ⊆ C1 ∧ 2 ≤ (orIn n C (n + k)).card := by
  intro k hk
  have hkf := Finset.mem_filter.mp hk
  have hle := orReaches_le hkf.2
  have hlt := opnd_lt hL.1 hg1j.1 b1
  have hn1 : ¬ OrReaches n C (n + k) g1 := fun h => hnw1C_1 (orReaches_trans hkf.2 h)
  have hn2 : ¬ OrReaches n C (n + k) g2 := fun h => hnw1C_2 (orReaches_trans hkf.2 h)
  have hsub : orIn n C (n + k) ⊆ C1 := by
   have := orIn_subset_of_orReaches hkf.2; rwa [show orIn n C w1C = C1 from hb1C] at this
  exact ⟨by omega, hn1, hn2, hsub,
   pure_orN_card_ge_two hL hLift hne hjunk (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
 have hFacC2_pure : ∀ k ∈ FacC2, k < g2 ∧ ¬ OrReaches n C (n + k) g1 ∧ ¬ OrReaches n C (n + k) g2 ∧
   orIn n C (n + k) ⊆ C2 ∧ 2 ≤ (orIn n C (n + k)).card := by
  intro k hk
  have hkf := Finset.mem_filter.mp hk
  have hle := orReaches_le hkf.2
  have hlt := opnd_lt hL.1 hg2j.1 b2
  have hn1 : ¬ OrReaches n C (n + k) g1 := fun h => hnw2C_1 (orReaches_trans hkf.2 h)
  have hn2 : ¬ OrReaches n C (n + k) g2 := fun h => hnw2C_2 (orReaches_trans hkf.2 h)
  have hsub : orIn n C (n + k) ⊆ C2 := by
   have := orIn_subset_of_orReaches hkf.2; rwa [hw2C_eq] at this
  exact ⟨by omega, hn1, hn2, hsub,
   pure_orN_card_ge_two hL hLift hne hjunk (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
 have hFacD_lt : ∀ k ∈ FacD, k < g2 ∧ orIn n C (n + k) ⊆ D1 ∪ D2 := by
  intro k hk
  rcases (Finset.mem_filter.mp hk).2 with h1 | h2
  ·have := orReaches_le h1; have := opnd_lt hL.1 hg1j.1 (1 - b1)
   have hsub := orIn_subset_of_orReaches h1
   rw [show orIn n C w1D = D1 from hb1D] at hsub
   exact ⟨by omega, Finset.Subset.trans hsub Finset.subset_union_left⟩
  ·have := orReaches_le h2; have := opnd_lt hL.1 hg2j.1 (1 - b2)
   exact ⟨by omega, Finset.Subset.trans (orIn_subset_of_orReaches h2) (Finset.Subset.trans hb2D_sub Finset.subset_union_right)⟩
 have hDisjC1C2 : Disjoint FacC1 FacC2 := by
  rw [Finset.disjoint_left]; intro k hk1 hk2
  have h1 := hFacC1_pure k hk1
  have h2 := hFacC2_pure k hk2
  obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp (by omega : 1 < (orIn n C (n + k)).card)
  exact hzp12 (noFourCycle_unique h4 hu12
   (hf1.2.2.2.1 u1 (h1.2.2.2.1 hu1)) (hf1.2.2.2.1 u2 (h1.2.2.2.1 hu2))
   (hf2.2.2.2.1 u1 (h2.2.2.2.1 hu1)) (hf2.2.2.2.1 u2 (h2.2.2.2.1 hu2)))
 have hDisjC1D : Disjoint FacC1 FacD := by
  rw [Finset.disjoint_left]; intro k hk1 hkD
  have h1 := hFacC1_pure k hk1
  have hD := hFacD_lt k hkD
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (orIn n C (n + k)).card)
  have hsc := flag_color_C hbip hf1 (h1.2.2.2.1 hu)
  have hsd : s u = s zp1 := by
   rcases Finset.mem_union.mp (hD.2 hu) with h | h
   ·exact flag_color_D hbip hf1 h
   ·exact (flag_color_D hbip hf2 h).trans hszp.symm
  exact hbip z zp1 hf1.1 (hsc.symm.trans hsd)
 have hDisjC2D : Disjoint FacC2 FacD := by
  rw [Finset.disjoint_left]; intro k hk2 hkD
  have h2 := hFacC2_pure k hk2
  have hD := hFacD_lt k hkD
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (orIn n C (n + k)).card)
  have hsc := flag_color_C hbip hf2 (h2.2.2.2.1 hu)
  have hsd : s u = s zp1 := by
   rcases Finset.mem_union.mp (hD.2 hu) with h | h
   ·exact flag_color_D hbip hf1 h
   ·exact (flag_color_D hbip hf2 h).trans hszp.symm
  exact hbip z zp1 hf1.1 (hsc.symm.trans hsd)
 set FacAll := FacC1 ∪ FacC2 ∪ FacD
 have hFacAll_sub : FacAll ⊆ orN G C \ lam G C :=
  Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
   (Finset.filter_subset _ _)
 have hFacAll_card : FacAll.card = FacC1.card + FacC2.card + FacD.card := by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hDisjC1D, hDisjC2D⟩),
   Finset.card_union_of_disjoint hDisjC1C2]
 have hFacAll_lt : ∀ k ∈ FacAll, k < g2 := by
  intro k hk; simp only [FacAll, Finset.mem_union] at hk
  rcases hk with (h | h) | h
  ·exact (hFacC1_pure k h).1
  ·exact (hFacC2_pure k h).1
  ·exact (hFacD_lt k h).1
 have hFacAll_mono : ∀ k ∈ FacAll, ∀ x y, x ∈ orIn n C (n + k) → y ∈ orIn n C (n + k) → s x = s y := by
  intro k hk x y hx hy; simp only [FacAll, Finset.mem_union] at hk
  rcases hk with (h | h) | h
  ·exact (flag_color_C hbip hf1 ((hFacC1_pure k h).2.2.2.1 hx)).trans
    (flag_color_C hbip hf1 ((hFacC1_pure k h).2.2.2.1 hy)).symm
  ·exact (flag_color_C hbip hf2 ((hFacC2_pure k h).2.2.2.1 hx)).trans
    (flag_color_C hbip hf2 ((hFacC2_pure k h).2.2.2.1 hy)).symm
  ·have hsD : ∀ u ∈ D1 ∪ D2, s u = s zp1 := fun u hu => by
    rcases Finset.mem_union.mp hu with h1 | h2
    ·exact flag_color_D hbip hf1 h1
    ·exact (flag_color_D hbip hf2 h2).trans hszp.symm
   exact (hsD x ((hFacD_lt k h).2 hx)).trans (hsD y ((hFacD_lt k h).2 hy)).symm
 have hUsub := ustar_sub_flagEdges hbip hL hLift h4 hjunk hf1 hf2
 have run_surgery3 : ∀ L : Fin n → Finset (Fin n),
   (∀ u ∈ L z, G.Adj z u) → (∀ u ∈ L zp1, G.Adj zp1 u) → (∀ u ∈ L zp2, G.Adj zp2 u) →
   (∀ e ∈ Ustar G C, (∃ u ∈ L z, e = s(z, u)) ∨ (∃ u ∈ L zp1, e = s(zp1, u)) ∨ (∃ u ∈ L zp2, e = s(zp2, u))) →
   let Zact := ({z, zp1, zp2} : Finset (Fin n)).filter (fun v => (L v).Nonempty)
   let Zhas := Zact.filter (fun v => ∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = v)
   2 * (centreless G C).card + (orN G C \ lam G C).card + 2 ≤
    (L z).card + (L zp1).card + (L zp2).card + (Zact \ Zhas).card := by
  intro L hLz hL1 hL2 hcov Zact Zhas
  let topOf : Fin n → ℕ := fun v =>
   if h : ∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = v then Classical.choose h else 0
  have hbound := master_surgery_bound hL hLift h4 hg12 hjunk hne Zact Zhas L topOf
   (Finset.filter_subset _ _)
   (fun v hv => (Finset.mem_filter.mp hv).2)
   (fun v hv u hu => by
    have hv' := (Finset.mem_filter.mp hv).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
    rcases hv' with rfl | rfl | rfl
    ·exact hLz u hu
    ·exact hL1 u hu
    ·exact hL2 u hu)
   (fun e he => by
    rcases hcov e he with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    ·exact ⟨z, Finset.mem_filter.mpr ⟨by simp, ⟨u, hu⟩⟩, u, hu, rfl⟩
    ·exact ⟨zp1, Finset.mem_filter.mpr ⟨by simp, ⟨u, hu⟩⟩, u, hu, rfl⟩
    ·exact ⟨zp2, Finset.mem_filter.mpr ⟨by simp, ⟨u, hu⟩⟩, u, hu, rfl⟩)
   (fun v hv => by
    have h := (Finset.mem_filter.mp hv).2
    simp only [topOf, dif_pos h]; exact (Classical.choose_spec h).1)
   (fun v hv => by
    have h := (Finset.mem_filter.mp hv).2
    simp only [topOf, dif_pos h]
    have hsp := Classical.choose_spec h
    have hside := topOwner_side hL.1 h4 s z g1 g2 hsp.1
    rwa [hsp.2] at hside)
   (fun v1 hv1 v2 hv2 heq => by
    have h1 := (Finset.mem_filter.mp hv1).2
    have h2 := (Finset.mem_filter.mp hv2).2
    simp only [topOf, dif_pos h1, dif_pos h2] at heq
    have hsp1 := Classical.choose_spec h1
    have hsp2 := Classical.choose_spec h2
    rw [← hsp1.2, heq, hsp2.2])
  have hsum_le : ∑ v ∈ Zact, (L v).card ≤ (L z).card + (L zp1).card + (L zp2).card := by
   calc ∑ v ∈ Zact, (L v).card ≤ ∑ v ∈ ({z, zp1, zp2} : Finset (Fin n)), (L v).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = (L z).card + (L zp1).card + (L zp2).card := by
      rw [Finset.sum_insert (by simp [hz_ne1, hz_ne2]), Finset.sum_pair hzp12]; omega
  omega
 have hgolden_zp1 : ∀ c1 ∈ MC1.erase z,
   (∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = zp1) ∨
   (∃ a ∈ centreless G C, ∃ b : Fin 2, side (n := n) C a b = ∅ ∧ OrReaches n C (opnd C a b) g1 ∧ zp1 ∈ side (n := n) C a (1 - b)) ∨
   (∃ mv ∈ orN G C \ lam G C, g2 < mv ∧ orIn n C (n + mv) = {zp1} ∧
    ∃ u' : Fin n, s u' = s z ∧ ∃ mu ∈ orN G C \ lam G C, OrReaches n C (n + mu) g1 ∧ orIn n C (n + mu) = {u'}) := by
  intro c1 hc1
  have hc1z : c1 ≠ z := (Finset.mem_erase.mp hc1).1
  have hc1_filt := Finset.mem_filter.mp (Finset.mem_of_mem_erase hc1)
  have hU : s(zp1, c1) ∈ Ustar G C := by rw [Sym2.eq_swap]; exact hc1_filt.2
  have hG : G.Adj zp1 c1 := (hf1.2.2.2.1 c1 hc1_filt.1).symm
  have hg2_false : gateVal n C g2 (pairInput zp1 c1) = false := by
   rw [Bool.eq_false_iff, ne_eq, flag_pair_edge_iff hbip h4 hf2 hG]
   simp only [flagEdges, Finset.mem_union, Finset.mem_image, Sym2.eq_iff]
   rintro (⟨d, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨c, hc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
   ·exact hz_ne1 rfl
   ·exact hc1z rfl
   ·exact absurd (flag_color_C hbip hf2 hc).symm (hbip z _ hf1.1)
   ·exact hzp12 rfl
  have hnw :
    (gateVal n C g1 (pairInput zp1 c1) = true →
     (¬ ∀ x, gateVal n C g1 x = true → x c1 = true → graphFun G ∅ x = true) ∧
     (∀ w : Fin n, s w = s zp1 → (∀ x, gateVal n C g1 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w c1)) ∧
    (gateVal n C g2 (pairInput zp1 c1) = true →
     (¬ ∀ x, gateVal n C g2 x = true → x c1 = true → graphFun G ∅ x = true) ∧
     (∀ w : Fin n, s w = s zp1 → (∀ x, gateVal n C g2 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w c1)) :=
   ⟨fun _ => ⟨flag_wmax_not_C_other h4 hf1 hc1_filt.1 hc1z,
    fun w hsw hw => flag_wmax_adj_C hbip h4 hf1 hw hsw hc1_filt.1 hc1z⟩,
    fun h2 => by rw [hg2_false] at h2; cases h2⟩
  rcases golden_edge_cover hbip h4 hL hLift hjunk hf1 hf2 rfl hszp hU hnw
    (fun h => by rw [hg2_false] at h; cases h.2.1) with
   hA | ⟨a, haC, b, g, hg, hgv, hemp, hrb, hv_s⟩ | ⟨_, a, haS, b, g, hg, hgv, _, _, g', hg', hg'ne, _, mv, hmv, hmv_g', hmv_orIn, u', _, hsu', mu, hmu, hmu_g, hmu_orIn⟩
  ·exact Or.inl hA
  ·have hgeq : g = g1 := hg.resolve_right (fun h => by rw [h, hg2_false] at hgv; cases hgv)
   subst hgeq
   exact Or.inr (Or.inl ⟨a, haC, b, hemp, hrb, hv_s⟩)
  ·have hgeq : g = g1 := hg.resolve_right (fun h => by rw [h, hg2_false] at hgv; cases hgv)
   rw [hgeq] at hmu_g
   have hg'eq : g' = g2 := hg'.resolve_left (by rw [hgeq] at hg'ne; exact hg'ne)
   rw [hg'eq] at hmv_g'
   have hmv_gt : g2 < mv := by
    have hle := orReaches_le hmv_g'
    have hne' : mv ≠ g2 := fun h => by
     have h1 := (mem_orN_iff.mp (Finset.mem_sdiff.mp hmv).1).2.1
     rw [h, hg2j.2.1] at h1; cases h1
    omega
   exact Or.inr (Or.inr ⟨mv, hmv, hmv_gt, hmv_orIn, u', hsu', mu, hmu, hmu_g, hmu_orIn⟩)
 have hgolden_zp2 : ∀ c2 ∈ MC2.erase z,
   (∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = zp2) ∨
   (∃ a ∈ centreless G C, ∃ b : Fin 2, side (n := n) C a b = ∅ ∧ OrReaches n C (opnd C a b) g2 ∧ zp2 ∈ side (n := n) C a (1 - b)) ∨
   (∃ mv ∈ orN G C \ lam G C, OrReaches n C (n + mv) g1 ∧ orIn n C (n + mv) = {zp2} ∧
    ∃ u' : Fin n, s u' = s z ∧ ∃ mu ∈ orN G C \ lam G C, g2 < mu ∧ orIn n C (n + mu) = {u'}) := by
  intro c2 hc2
  have hc2z : c2 ≠ z := (Finset.mem_erase.mp hc2).1
  have hc2_filt := Finset.mem_filter.mp (Finset.mem_of_mem_erase hc2)
  have hU : s(zp2, c2) ∈ Ustar G C := by rw [Sym2.eq_swap]; exact hc2_filt.2
  have hG : G.Adj zp2 c2 := (hf2.2.2.2.1 c2 hc2_filt.1).symm
  have hg1_false : gateVal n C g1 (pairInput zp2 c2) = false := by
   rw [Bool.eq_false_iff, ne_eq, flag_pair_edge_iff hbip h4 hf1 hG]
   simp only [flagEdges, Finset.mem_union, Finset.mem_image, Sym2.eq_iff]
   rintro (⟨d, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨c, hc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
   ·exact hz_ne2 rfl
   ·exact hc2z rfl
   ·exact absurd ((flag_color_C hbip hf1 hc).symm.trans hszp.symm) (hbip z zp1 hf1.1)
   ·exact hzp12.symm rfl
  have hnw :
    (gateVal n C g1 (pairInput zp2 c2) = true →
     (¬ ∀ x, gateVal n C g1 x = true → x c2 = true → graphFun G ∅ x = true) ∧
     (∀ w : Fin n, s w = s zp2 → (∀ x, gateVal n C g1 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w c2)) ∧
    (gateVal n C g2 (pairInput zp2 c2) = true →
     (¬ ∀ x, gateVal n C g2 x = true → x c2 = true → graphFun G ∅ x = true) ∧
     (∀ w : Fin n, s w = s zp2 → (∀ x, gateVal n C g2 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w c2)) :=
   ⟨fun h1 => (by rw [hg1_false] at h1; cases h1),
    fun _ => ⟨flag_wmax_not_C_other h4 hf2 hc2_filt.1 hc2z,
    fun w hsw hw => flag_wmax_adj_C hbip h4 hf2 hw hsw hc2_filt.1 hc2z⟩⟩
  rcases golden_edge_cover hbip h4 hL hLift hjunk hf1 hf2 rfl hszp hU hnw
    (fun h => by rw [hg1_false] at h; cases h.1) with
   hA | ⟨a, haC, b, g, hg, hgv, hemp, hrb, hv_s⟩ | ⟨_, a, haS, b, g, hg, hgv, _, _, g', hg', hg'ne, _, mv, hmv, hmv_g', hmv_orIn, u', _, hsu', mu, hmu, hmu_g, hmu_orIn⟩
  ·exact Or.inl hA
  ·have hgeq : g = g2 := hg.resolve_left (fun h => by rw [h, hg1_false] at hgv; cases hgv)
   subst hgeq
   exact Or.inr (Or.inl ⟨a, haC, b, hemp, hrb, hv_s⟩)
  ·have hgeq : g = g2 := hg.resolve_left (fun h => by rw [h, hg1_false] at hgv; cases hgv)
   rw [hgeq] at hmu_g
   have hg'eq : g' = g1 := hg'.resolve_right (by rw [hgeq] at hg'ne; exact hg'ne)
   rw [hg'eq] at hmv_g'
   have hmu_gt : g2 < mu := by
    have hle := orReaches_le hmu_g
    have hne' : mu ≠ g2 := fun h => by
     have h1 := (mem_orN_iff.mp (Finset.mem_sdiff.mp hmu).1).2.1
     rw [h, hg2j.2.1] at h1; cases h1
    omega
   exact Or.inr (Or.inr ⟨mv, hmv, hmv_g', hmv_orIn, u', hsu', mu, hmu, hmu_gt, hmu_orIn⟩)
 have hgolden_z : ∀ d ∈ MD, d ≠ zp1 → d ≠ zp2 →
   (∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = z) ∨
   (∃ a ∈ centreless G C, ∃ b : Fin 2, ∃ g : ℕ, (g = g1 ∨ g = g2) ∧
    gateVal n C g (pairInput z d) = true ∧
    side (n := n) C a b = ∅ ∧ OrReaches n C (opnd C a b) g ∧ z ∈ side (n := n) C a (1 - b)) := by
  intro d hd hdzp1 hdzp2
  have hzd_U : s(z, d) ∈ Ustar G C := by
   rcases Finset.mem_union.mp hd with h1 | h2
   ·exact (Finset.mem_filter.mp h1).2
   ·exact (Finset.mem_filter.mp h2).2
  have hnot_both : ¬ (gateVal n C g1 (pairInput z d) = true ∧ gateVal n C g2 (pairInput z d) = true ∧
    ∀ x, gateVal n C g1 x = true → gateVal n C g2 x = true → graphFun G ∅ x = true) := by
   rintro ⟨hg1d, hg2d, hall⟩
   have hd1 : d ∈ D1 := by
    rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hg1d
    rcases hg1d.2 with ⟨d', hd', hdd'⟩
    simp only [pairInput, decide_eq_true_eq] at hdd'
    rcases hdd' with rfl | rfl
    ·exact absurd (flag_color_D hbip hf1 hd') (hbip _ zp1 hf1.1)
    ·exact hd'
   have hd2 : d ∈ D2 := by
    rw [hf2.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hg2d
    rcases hg2d.2 with ⟨d', hd', hdd'⟩
    simp only [pairInput, decide_eq_true_eq] at hdd'
    rcases hdd' with rfl | rfl
    ·exact absurd (flag_color_D hbip hf2 hd') (hbip _ zp2 hf2.1)
    ·exact hd'
   obtain ⟨c1, hc1, hc1z⟩ := flag_exists_other_C hf1
   obtain ⟨c2, hc2, hc2z⟩ := flag_exists_other_C hf2
   let x : Fin n → Bool := fun w => decide (w = c1 ∨ w = c2 ∨ w = d)
   have hg1x : gateVal n C g1 x = true := by
    rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨⟨c1, hc1, by simp [x]⟩, ⟨d, hd1, by simp [x]⟩⟩
   have hg2x : gateVal n C g2 x = true := by
    rw [hf2.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨⟨c2, hc2, by simp [x]⟩, ⟨d, hd2, by simp [x]⟩⟩
   have hFx := (graphFun_iff x).mp (hall x hg1x hg2x)
   rcases hFx with ⟨a, b, hab, ha, hb⟩
   simp only [x, decide_eq_true_eq] at ha hb
   have hsc1 := flag_color_C hbip hf1 hc1
   have hsc2 := flag_color_C hbip hf2 hc2
   have hnc1d := flag_nonEdge h4 hf1 hc1 hc1z hd1 hdzp1
   have hnc2d := flag_nonEdge h4 hf2 hc2 hc2z hd2 hdzp2
   rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
   ·exact G.loopless.irrefl _ hab
   ·exact hbip _ _ hab (hsc1.trans hsc2.symm)
   ·exact hnc1d hab
   ·exact hbip _ _ hab (hsc2.trans hsc1.symm)
   ·exact G.loopless.irrefl _ hab
   ·exact hnc2d hab
   ·exact hnc1d hab.symm
   ·exact hnc2d hab.symm
   ·exact G.loopless.irrefl _ hab
  have hnw :
    (gateVal n C g1 (pairInput z d) = true →
     (¬ ∀ x, gateVal n C g1 x = true → x d = true → graphFun G ∅ x = true) ∧
     (∀ w : Fin n, s w = s z → (∀ x, gateVal n C g1 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w d)) ∧
    (gateVal n C g2 (pairInput z d) = true →
     (¬ ∀ x, gateVal n C g2 x = true → x d = true → graphFun G ∅ x = true) ∧
     (∀ w : Fin n, s w = s z → (∀ x, gateVal n C g2 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w d)) := by
   constructor
   ·intro h1
    have hd1 : d ∈ D1 := by
     rw [hf1.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h1
     rcases h1.2 with ⟨d', hd', hdd'⟩
     simp only [pairInput, decide_eq_true_eq] at hdd'
     rcases hdd' with rfl | rfl
     ·exact absurd (flag_color_D hbip hf1 hd') (hbip _ zp1 hf1.1)
     ·exact hd'
    exact ⟨flag_wmax_not_D_other h4 hf1 hd1 hdzp1,
     fun w hsw hw => flag_wmax_adj_D hbip h4 hf1 hw hsw hd1 hdzp1⟩
   ·intro h2
    have hd2 : d ∈ D2 := by
     rw [hf2.2.2.2.2.2.2.2, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h2
     rcases h2.2 with ⟨d', hd', hdd'⟩
     simp only [pairInput, decide_eq_true_eq] at hdd'
     rcases hdd' with rfl | rfl
     ·exact absurd (flag_color_D hbip hf2 hd') (hbip _ zp2 hf2.1)
     ·exact hd'
    exact ⟨flag_wmax_not_D_other h4 hf2 hd2 hdzp2,
     fun w hsw hw => flag_wmax_adj_D hbip h4 hf2 hw hsw hd2 hdzp2⟩
  rcases golden_edge_cover hbip h4 hL hLift hjunk hf1 hf2 rfl hszp hzd_U hnw hnot_both with
   hA | hB | ⟨hcol, _⟩
  ·exact Or.inl hA
  ·exact Or.inr hB
  ·exact absurd hcol (hbip z zp1 hf1.1)
 have close_slack1 : MD.card + (MC1.erase z).card + (MC2.erase z).card ≤ FacAll.card + 1 → False := by
  intro hsum_fac
  let L1 : Fin n → Finset (Fin n) := fun v =>
   if v = z then MD else if v = zp1 then MC1.erase z else if v = zp2 then MC2.erase z else ∅
  have hL1z : L1 z = MD := by simp [L1]
  have hL1_1 : L1 zp1 = MC1.erase z := by simp [L1, hz_ne1.symm]
  have hL1_2 : L1 zp2 = MC2.erase z := by simp [L1, hz_ne2.symm, hzp12.symm]
  have hcov1 : ∀ e ∈ Ustar G C, (∃ u ∈ L1 z, e = s(z, u)) ∨ (∃ u ∈ L1 zp1, e = s(zp1, u)) ∨ (∃ u ∈ L1 zp2, e = s(zp2, u)) := by
   intro e he
   have heF := hUsub he
   simp only [Finset.mem_union, flagEdges, Finset.mem_image] at heF
   rcases heF with (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩) | (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩)
   ·left; exact ⟨d, by rw [hL1z]; exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd, he⟩), rfl⟩
   ·by_cases hcz : c = z
    ·subst hcz; left; exact ⟨zp1, by rw [hL1z]; exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hf1.2.2.1, he⟩), rfl⟩
    ·right; left; exact ⟨c, by rw [hL1_1]; exact Finset.mem_erase.mpr ⟨hcz, Finset.mem_filter.mpr ⟨hc, he⟩⟩, Sym2.eq_swap⟩
   ·left; exact ⟨d, by rw [hL1z]; exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd, he⟩), rfl⟩
   ·by_cases hcz : c = z
    ·subst hcz; left; exact ⟨zp2, by rw [hL1z]; exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf2.2.2.1, he⟩), rfl⟩
    ·right; right; exact ⟨c, by rw [hL1_2]; exact Finset.mem_erase.mpr ⟨hcz, Finset.mem_filter.mpr ⟨hc, he⟩⟩, Sym2.eq_swap⟩
  have hsurg1 := run_surgery3 L1
   (fun u hu => by rw [hL1z] at hu; rcases Finset.mem_union.mp hu with h | h; exact (hf1.2.2.2.2.1 u (Finset.mem_filter.mp h).1).symm; exact (hf2.2.2.2.2.1 u (Finset.mem_filter.mp h).1).symm)
   (fun u hu => by rw [hL1_1] at hu; exact (hf1.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm)
   (fun u hu => by rw [hL1_2] at hu; exact (hf2.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm)
   hcov1
  dsimp only at hsurg1
  set Zact := ({z, zp1, zp2} : Finset (Fin n)).filter (fun v => (L1 v).Nonempty)
  set Zhas := Zact.filter (fun v => ∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = v)
  rw [hL1z, hL1_1, hL1_2] at hsurg1
  have hFac_le : FacAll.card ≤ (orN G C \ lam G C).card := Finset.card_le_card hFacAll_sub
  have hZnew_le3 : (Zact \ Zhas).card ≤ 3 := by
   calc (Zact \ Zhas).card ≤ ({z, zp1, zp2} : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))
    _ = 3 := by rw [Finset.card_insert_of_notMem (by simp [hz_ne1, hz_ne2]), Finset.card_pair hzp12]
  by_cases hcent2 : 2 ≤ (centreless G C).card
  ·omega
  ·by_cases hcent1 : (centreless G C).card = 1
   ·
    by_cases hZ3 : (Zact \ Zhas).card ≤ 2
    ·omega
    ·have hZ_eq3 : Zact \ Zhas = {z, zp1, zp2} := by
      apply Finset.eq_of_subset_of_card_le
      ·exact Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _)
      ·rw [Finset.card_insert_of_notMem (by simp [hz_ne1, hz_ne2]), Finset.card_pair hzp12]; omega
     have hzp1_new : zp1 ∈ Zact \ Zhas := by rw [hZ_eq3]; simp
     have hzp2_new : zp2 ∈ Zact \ Zhas := by rw [hZ_eq3]; simp
     obtain ⟨c1, hc1⟩ : (MC1.erase z).Nonempty := by
      have := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzp1_new).1).2; rwa [hL1_1] at this
     obtain ⟨c2, hc2⟩ : (MC2.erase z).Nonempty := by
      have := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzp2_new).1).2; rwa [hL1_2] at this
     have hex_gt : ∃ m ∈ orN G C \ lam G C, g2 < m := by
      rcases hgolden_zp1 c1 hc1 with hA1 | ⟨a1, ha1C, b1', hemp1, hrb1, hzp1s⟩ | ⟨mv, hmv, hmv_gt, _⟩
      ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp1_new).1, hA1⟩) (Finset.mem_sdiff.mp hzp1_new).2
      ·rcases hgolden_zp2 c2 hc2 with hA2 | ⟨a2, ha2C, b2', hemp2, hrb2, hzp2s⟩ | ⟨_, _, _, _, _, _, mu, hmu, hmu_gt, _⟩
       ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp2_new).1, hA2⟩) (Finset.mem_sdiff.mp hzp2_new).2
       ·obtain ⟨a0, ha0⟩ := Finset.card_eq_one.mp hcent1
        have ha1eq : a1 = a0 := Finset.mem_singleton.mp (ha0 ▸ ha1C)
        have ha2eq : a2 = a0 := Finset.mem_singleton.mp (ha0 ▸ ha2C)
        rw [ha1eq] at ha1C hemp1 hrb1 hzp1s
        rw [ha2eq] at hemp2 hrb2
        have hb12 : b1' = b2' := by
         by_contra hne_b
         have h1mb : 1 - b1' = b2' := fin2_sub_eq hne_b
         rw [h1mb, hemp2] at hzp1s; exact Finset.notMem_empty _ hzp1s
        subst hb12
        have ha0_top : a0 ∈ tops G C := (Finset.mem_filter.mp ha1C).1
        have ha0' := mem_tops_iff.mp ha0_top
        obtain ⟨m, hm, hmg2, _⟩ := pureFlagOr_of_reaches_both hL hlt12 hjunk
         (by have := opnd_lt hL.1 ha0'.1 b1'; omega) (top_opnd_not_belowF hL hne ha0_top b1')
         hemp1 hrb1 hrb2
        exact ⟨m, hm, hmg2⟩
       ·exact ⟨mu, hmu, hmu_gt⟩
      ·exact ⟨mv, hmv, hmv_gt⟩
     obtain ⟨m, hm, hmg2⟩ := hex_gt
     have hm_nF : m ∉ FacAll := fun h => by have := hFacAll_lt m h; omega
     have hFac_s : FacAll.card + 1 ≤ (orN G C \ lam G C).card := by
      have := Finset.card_le_card (Finset.insert_subset hm hFacAll_sub)
      rwa [Finset.card_insert_of_notMem hm_nF] at this
     omega
   ·
    have hcent0 : centreless G C = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨m0, hm0, hm0_gt⟩ := exists_mixing_gt_g2 hL hLift hne hlt12 hjunk hcent0
    have hm0_nF : m0 ∉ FacAll := fun h => by have := hFacAll_lt m0 h; omega
    have hFac_s1 : FacAll.card + 1 ≤ (orN G C \ lam G C).card := by
     have := Finset.card_le_card (Finset.insert_subset hm0 hFacAll_sub)
     rwa [Finset.card_insert_of_notMem hm0_nF] at this
    by_cases hMD_nonsp : ∃ d ∈ MD, d ≠ zp1 ∧ d ≠ zp2
    ·obtain ⟨d, hd, hd1, hd2⟩ := hMD_nonsp
     have hz_own : ∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = z := by
      rcases hgolden_z d hd hd1 hd2 with hA | ⟨a, haC, _⟩
      ·exact hA
      ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
     have hz_nnew : z ∉ Zact \ Zhas := fun h =>
      (Finset.mem_sdiff.mp h).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp h).1, hz_own⟩)
     have hZsub : Zact \ Zhas ⊆ {zp1, zp2} := by
      intro v hv
      have hv1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv1 ⊢
      exact hv1.resolve_left (fun h => hz_nnew (h ▸ hv))
     have hZle2 : (Zact \ Zhas).card ≤ 2 := (Finset.card_le_card hZsub).trans (by rw [Finset.card_pair hzp12])
     by_cases hZle1 : (Zact \ Zhas).card ≤ 1
     ·omega
     ·have hZeq2 : Zact \ Zhas = {zp1, zp2} :=
       Finset.eq_of_subset_of_card_le hZsub (by rw [Finset.card_pair hzp12]; omega)
      have hzp1_new : zp1 ∈ Zact \ Zhas := by rw [hZeq2]; simp
      have hzp2_new : zp2 ∈ Zact \ Zhas := by rw [hZeq2]; simp
      obtain ⟨c1, hc1⟩ : (MC1.erase z).Nonempty := by
       have := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzp1_new).1).2; rwa [hL1_1] at this
      obtain ⟨c2, hc2⟩ : (MC2.erase z).Nonempty := by
       have := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzp2_new).1).2; rwa [hL1_2] at this
      obtain ⟨m1, hm1, hm1_gt, hm1_orIn⟩ : ∃ m1 ∈ orN G C \ lam G C, g2 < m1 ∧ orIn n C (n + m1) = {zp1} := by
       rcases hgolden_zp1 c1 hc1 with hA | ⟨a, haC, _⟩ | ⟨mv, hmv, hmv_gt, hmv_orIn, _⟩
       ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp1_new).1, hA⟩) (Finset.mem_sdiff.mp hzp1_new).2
       ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
       ·exact ⟨mv, hmv, hmv_gt, hmv_orIn⟩
      obtain ⟨m2, hm2, hm2_gt, u', hsu', hm2_orIn⟩ :
        ∃ m2 ∈ orN G C \ lam G C, g2 < m2 ∧ ∃ u' : Fin n, s u' = s z ∧ orIn n C (n + m2) = {u'} := by
       rcases hgolden_zp2 c2 hc2 with hA | ⟨a, haC, _⟩ | ⟨_, _, _, _, u', hsu', mu, hmu, hmu_gt, hmu_orIn⟩
       ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp2_new).1, hA⟩) (Finset.mem_sdiff.mp hzp2_new).2
       ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
       ·exact ⟨mu, hmu, hmu_gt, u', hsu', hmu_orIn⟩
      have hm12 : m1 ≠ m2 := by
       intro heq; subst heq
       rw [hm1_orIn] at hm2_orIn
       have hzp1_eq : zp1 = u' := Finset.singleton_injective hm2_orIn
       exact hbip z zp1 hf1.1 (hsu'.symm.trans (congrArg s hzp1_eq.symm))
      have hdisj_m : Disjoint ({m1, m2} : Finset ℕ) FacAll := by
       rw [Finset.disjoint_left]; intro k hk hkf
       simp only [Finset.mem_insert, Finset.mem_singleton] at hk
       have := hFacAll_lt k hkf
       rcases hk with rfl | rfl <;> omega
      have hsub2 : {m1, m2} ∪ FacAll ⊆ orN G C \ lam G C :=
       Finset.union_subset (Finset.insert_subset hm1 (Finset.singleton_subset_iff.mpr hm2)) hFacAll_sub
      have hFac_s2 := Finset.card_le_card hsub2
      rw [Finset.card_union_of_disjoint hdisj_m, Finset.card_pair hm12] at hFac_s2
      omega
    ·
     push Not at hMD_nonsp
     let L2 : Fin n → Finset (Fin n) := fun v =>
      if v = zp1 then MC1 else if v = zp2 then MC2 else ∅
     have hL2z : L2 z = ∅ := by simp [L2, hz_ne1, hz_ne2]
     have hL2_1 : L2 zp1 = MC1 := by simp [L2]
     have hL2_2 : L2 zp2 = MC2 := by simp [L2, hzp12.symm]
     have hcov2 : ∀ e ∈ Ustar G C, (∃ u ∈ L2 z, e = s(z, u)) ∨ (∃ u ∈ L2 zp1, e = s(zp1, u)) ∨ (∃ u ∈ L2 zp2, e = s(zp2, u)) := by
      intro e he
      have heF := hUsub he
      simp only [Finset.mem_union, flagEdges, Finset.mem_image] at heF
      rcases heF with (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩) | (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩)
      ·have hdMD : d ∈ MD := Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd, he⟩)
       by_cases hd1 : d = zp1
       ·subst hd1; right; left; exact ⟨z, by rw [hL2_1]; exact Finset.mem_filter.mpr ⟨hf1.2.1, he⟩, Sym2.eq_swap⟩
       ·have hd2 : d = zp2 := hMD_nonsp d hdMD hd1
        subst hd2; right; right; exact ⟨z, by rw [hL2_2]; exact Finset.mem_filter.mpr ⟨hf2.2.1, he⟩, Sym2.eq_swap⟩
      ·right; left; exact ⟨c, by rw [hL2_1]; exact Finset.mem_filter.mpr ⟨hc, he⟩, Sym2.eq_swap⟩
      ·have hdMD : d ∈ MD := Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd, he⟩)
       by_cases hd1 : d = zp1
       ·subst hd1; right; left; exact ⟨z, by rw [hL2_1]; exact Finset.mem_filter.mpr ⟨hf1.2.1, he⟩, Sym2.eq_swap⟩
       ·have hd2 : d = zp2 := hMD_nonsp d hdMD hd1
        subst hd2; right; right; exact ⟨z, by rw [hL2_2]; exact Finset.mem_filter.mpr ⟨hf2.2.1, he⟩, Sym2.eq_swap⟩
      ·right; right; exact ⟨c, by rw [hL2_2]; exact Finset.mem_filter.mpr ⟨hc, he⟩, Sym2.eq_swap⟩
     have hsurg2 := run_surgery3 L2
      (fun u hu => by rw [hL2z] at hu; exact absurd hu (Finset.notMem_empty _))
      (fun u hu => by rw [hL2_1] at hu; exact (hf1.2.2.2.1 u (Finset.mem_filter.mp hu).1).symm)
      (fun u hu => by rw [hL2_2] at hu; exact (hf2.2.2.2.1 u (Finset.mem_filter.mp hu).1).symm)
      hcov2
     dsimp only at hsurg2
     set Zact2 := ({z, zp1, zp2} : Finset (Fin n)).filter (fun v => (L2 v).Nonempty)
     set Zhas2 := Zact2.filter (fun v => ∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = v)
     rw [hL2z, hL2_1, hL2_2, Finset.card_empty, zero_add] at hsurg2
     have hZ2sub : Zact2 \ Zhas2 ⊆ {zp1, zp2} := by
      intro v hv
      have hv1 := Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv1 ⊢
      rcases hv1.1 with rfl | rfl | rfl
      ·rw [hL2z] at hv1; exact absurd hv1.2 (by simp)
      ·exact Or.inl rfl
      ·exact Or.inr rfl
     have hZ2le2 : (Zact2 \ Zhas2).card ≤ 2 := (Finset.card_le_card hZ2sub).trans (by rw [Finset.card_pair hzp12])
     have hMD_card_eq : MD.card = (if z ∈ MC1 then 1 else 0) + (if z ∈ MC2 then 1 else 0) := by
      have hMD_eq : MD = ({zp1, zp2} : Finset (Fin n)).filter (fun d => s(z, d) ∈ Ustar G C) := by
       ext d; constructor
       ·intro hd
        have hU_d : s(z, d) ∈ Ustar G C := by
         rcases Finset.mem_union.mp hd with h | h <;> exact (Finset.mem_filter.mp h).2
        by_cases h1 : d = zp1
        ·subst h1; exact Finset.mem_filter.mpr ⟨by simp, hU_d⟩
        ·have h2 := hMD_nonsp d hd h1; subst h2; exact Finset.mem_filter.mpr ⟨by simp, hU_d⟩
       ·intro hd; have hdf := Finset.mem_filter.mp hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hdf
        rcases hdf.1 with rfl | rfl
        ·exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hf1.2.2.1, hdf.2⟩)
        ·exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf2.2.2.1, hdf.2⟩)
      rw [hMD_eq]
      have h1_iff : z ∈ MC1 ↔ s(z, zp1) ∈ Ustar G C := by
       simp [MC1, hf1.2.1]
      have h2_iff : z ∈ MC2 ↔ s(z, zp2) ∈ Ustar G C := by
       simp [MC2, hf2.2.1]
      rw [Finset.filter_insert, Finset.filter_singleton]
      by_cases h1 : s(z, zp1) ∈ Ustar G C <;> by_cases h2 : s(z, zp2) ∈ Ustar G C <;>
       simp [h1, h2, h1_iff, h2_iff, hzp12]
     have hMC_sum : MC1.card + MC2.card = MD.card + (MC1.erase z).card + (MC2.erase z).card := by
      rw [hMD_card_eq]
      by_cases h1 : z ∈ MC1 <;> by_cases h2 : z ∈ MC2
      ·rw [Finset.card_erase_of_mem h1, Finset.card_erase_of_mem h2]; simp [h1, h2]
       have := Finset.card_pos.mpr ⟨z, h1⟩; have := Finset.card_pos.mpr ⟨z, h2⟩; omega
      ·rw [Finset.card_erase_of_mem h1, Finset.erase_eq_of_notMem h2]; simp [h1, h2]
       have := Finset.card_pos.mpr ⟨z, h1⟩; omega
      ·rw [Finset.erase_eq_of_notMem h1, Finset.card_erase_of_mem h2]; simp [h1, h2]
       have := Finset.card_pos.mpr ⟨z, h2⟩; omega
      ·rw [Finset.erase_eq_of_notMem h1, Finset.erase_eq_of_notMem h2]; simp [h1, h2]
     by_cases hZ2le1 : (Zact2 \ Zhas2).card ≤ 1
     ·omega
     ·have hZ2eq2 : Zact2 \ Zhas2 = {zp1, zp2} :=
       Finset.eq_of_subset_of_card_le hZ2sub (by rw [Finset.card_pair hzp12]; omega)
      have hzp1_new : zp1 ∈ Zact2 \ Zhas2 := by rw [hZ2eq2]; simp
      have hzp2_new : zp2 ∈ Zact2 \ Zhas2 := by rw [hZ2eq2]; simp
      by_cases h1ne : (MC1.erase z).Nonempty
      ·by_cases h2ne : (MC2.erase z).Nonempty
       ·obtain ⟨c1, hc1⟩ := h1ne
        obtain ⟨c2, hc2⟩ := h2ne
        obtain ⟨m1, hm1, hm1_gt, hm1_orIn⟩ : ∃ m1 ∈ orN G C \ lam G C, g2 < m1 ∧ orIn n C (n + m1) = {zp1} := by
         rcases hgolden_zp1 c1 hc1 with hA | ⟨a, haC, _⟩ | ⟨mv, hmv, hmv_gt, hmv_orIn, _⟩
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp1_new).1, hA⟩) (Finset.mem_sdiff.mp hzp1_new).2
         ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
         ·exact ⟨mv, hmv, hmv_gt, hmv_orIn⟩
        obtain ⟨m2, hm2, hm2_gt, u', hsu', hm2_orIn⟩ :
          ∃ m2 ∈ orN G C \ lam G C, g2 < m2 ∧ ∃ u' : Fin n, s u' = s z ∧ orIn n C (n + m2) = {u'} := by
         rcases hgolden_zp2 c2 hc2 with hA | ⟨a, haC, _⟩ | ⟨_, _, _, _, u', hsu', mu, hmu, hmu_gt, hmu_orIn⟩
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp2_new).1, hA⟩) (Finset.mem_sdiff.mp hzp2_new).2
         ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
         ·exact ⟨mu, hmu, hmu_gt, u', hsu', hmu_orIn⟩
        have hm12 : m1 ≠ m2 := by
         intro heq; subst heq
         rw [hm1_orIn] at hm2_orIn
         have hzp1_eq : zp1 = u' := Finset.singleton_injective hm2_orIn
         exact hbip z zp1 hf1.1 (hsu'.symm.trans (congrArg s hzp1_eq.symm))
        have hdisj_m : Disjoint ({m1, m2} : Finset ℕ) FacAll := by
         rw [Finset.disjoint_left]; intro k hk hkf
         simp only [Finset.mem_insert, Finset.mem_singleton] at hk
         have := hFacAll_lt k hkf
         rcases hk with rfl | rfl <;> omega
        have hsub2 : {m1, m2} ∪ FacAll ⊆ orN G C \ lam G C :=
         Finset.union_subset (Finset.insert_subset hm1 (Finset.singleton_subset_iff.mpr hm2)) hFacAll_sub
        have hFac_s2 := Finset.card_le_card hsub2
        rw [Finset.card_union_of_disjoint hdisj_m, Finset.card_pair hm12] at hFac_s2
        omega
       ·
        have hMC2_ne : MC2.Nonempty := by
         have := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzp2_new).1).2; rwa [hL2_2] at this
        obtain ⟨c2, hc2, hc2z⟩ := flag_exists_other_C hf2
        have hc2_nM : c2 ∉ MC2 := fun h => h2ne ⟨c2, Finset.mem_erase.mpr ⟨hc2z, h⟩⟩
        have hMC2_le : MC2.card ≤ FacC2.card := hFC2_raw.2 ⟨c2, hc2, hc2_nM⟩
        have hMC1_le : MC1.card ≤ FacC1.card + 1 := hFC1_raw.1 (by
         have := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzp1_new).1).2; rwa [hL2_1] at this)
        obtain ⟨c1, hc1⟩ := h1ne
        obtain ⟨mv, hmv, hmv_gt, hmv_orIn, u', hsu', mu, hmu, hmu_g1, hmu_orIn⟩ :
          ∃ mv ∈ orN G C \ lam G C, g2 < mv ∧ orIn n C (n + mv) = {zp1} ∧
           ∃ u' : Fin n, s u' = s z ∧ ∃ mu ∈ orN G C \ lam G C, OrReaches n C (n + mu) g1 ∧ orIn n C (n + mu) = {u'} := by
         rcases hgolden_zp1 c1 hc1 with hA | ⟨a, haC, _⟩ | hC
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp1_new).1, hA⟩) (Finset.mem_sdiff.mp hzp1_new).2
         ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
         ·exact hC
        have hmv_mu : mv ≠ mu := by
         intro heq; subst heq; rw [hmv_orIn] at hmu_orIn
         exact hbip z zp1 hf1.1 (hsu'.symm.trans (congrArg s (Finset.singleton_injective hmu_orIn).symm))
        have hmv_nF : mv ∉ FacAll := fun h => by have := hFacAll_lt mv h; omega
        have hmu_nF : mu ∉ FacAll := by
         intro h; simp only [FacAll, Finset.mem_union] at h
         rcases h with (h1 | h2) | hD
         ·exact (hFacC1_pure mu h1).2.1 hmu_g1
         ·exact (hFacC2_pure mu h2).2.1 hmu_g1
         ·have hu'_D : u' ∈ D1 ∪ D2 := (hFacD_lt mu hD).2 (by rw [hmu_orIn]; simp)
          rcases Finset.mem_union.mp hu'_D with h1 | h2
          ·exact hbip z zp1 hf1.1 (hsu'.symm.trans (flag_color_D hbip hf1 h1))
          ·exact hbip z zp2 hf2.1 (hsu'.symm.trans (flag_color_D hbip hf2 h2))
        have hdisj_m : Disjoint ({mv, mu} : Finset ℕ) FacAll := by
         rw [Finset.disjoint_left]; intro k hk hkf
         simp only [Finset.mem_insert, Finset.mem_singleton] at hk
         rcases hk with rfl | rfl
         ·exact hmv_nF hkf
         ·exact hmu_nF hkf
        have hFac_s2 : FacAll.card + 2 ≤ (orN G C \ lam G C).card := by
         have hsub2 : {mv, mu} ∪ FacAll ⊆ orN G C \ lam G C :=
          Finset.union_subset (Finset.insert_subset hmv (Finset.singleton_subset_iff.mpr hmu)) hFacAll_sub
         have := Finset.card_le_card hsub2
         rw [Finset.card_union_of_disjoint hdisj_m, Finset.card_pair hmv_mu] at this
         omega
        omega
      ·
       have hMC1_ne : MC1.Nonempty := by
        have := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzp1_new).1).2; rwa [hL2_1] at this
       obtain ⟨c1, hc1, hc1z⟩ := flag_exists_other_C hf1
       have hc1_nM : c1 ∉ MC1 := fun h => h1ne ⟨c1, Finset.mem_erase.mpr ⟨hc1z, h⟩⟩
       have hMC1_le : MC1.card ≤ FacC1.card := hFC1_raw.2 ⟨c1, hc1, hc1_nM⟩
       by_cases h2ne : (MC2.erase z).Nonempty
       ·have hMC2_le : MC2.card ≤ FacC2.card + 1 := hFC2_raw.1 (by
         have := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzp2_new).1).2; rwa [hL2_2] at this)
        obtain ⟨c2, hc2⟩ := h2ne
        obtain ⟨mv, hmv, hmv_g1, hmv_orIn, u', hsu', mu, hmu, hmu_gt, hmu_orIn⟩ :
          ∃ mv ∈ orN G C \ lam G C, OrReaches n C (n + mv) g1 ∧ orIn n C (n + mv) = {zp2} ∧
           ∃ u' : Fin n, s u' = s z ∧ ∃ mu ∈ orN G C \ lam G C, g2 < mu ∧ orIn n C (n + mu) = {u'} := by
         rcases hgolden_zp2 c2 hc2 with hA | ⟨a, haC, _⟩ | hC
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp2_new).1, hA⟩) (Finset.mem_sdiff.mp hzp2_new).2
         ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
         ·exact hC
        have hmu_nF : mu ∉ FacAll := fun h => by have := hFacAll_lt mu h; omega
        have hmv_mu : mv ≠ mu := by
         intro heq; subst heq; rw [hmv_orIn] at hmu_orIn
         exact hbip z zp2 hf2.1 (hsu'.symm.trans (congrArg s (Finset.singleton_injective hmu_orIn).symm))
        have hFac12_2 : FacC1.card + FacC2.card + 2 ≤ (orN G C \ lam G C).card := by
         by_cases hmv_F : mv ∈ FacAll
         ·have hmv_D : mv ∈ FacD := by
           simp only [FacAll, Finset.mem_union] at hmv_F
           rcases hmv_F with (h1 | h2) | hD
           ·exact absurd hmv_g1 (hFacC1_pure mv h1).2.1
           ·exact absurd hmv_g1 (hFacC2_pure mv h2).2.1
           ·exact hD
          have hDpos : 1 ≤ FacD.card := Finset.card_pos.mpr ⟨mv, hmv_D⟩
          have hFac_s : FacAll.card + 1 ≤ (orN G C \ lam G C).card := by
           have := Finset.card_le_card (Finset.insert_subset hmu hFacAll_sub)
           rwa [Finset.card_insert_of_notMem hmu_nF] at this
          rw [hFacAll_card] at hFac_s; omega
         ·have hdisj_m : Disjoint ({mv, mu} : Finset ℕ) FacAll := by
           rw [Finset.disjoint_left]; intro k hk hkf
           simp only [Finset.mem_insert, Finset.mem_singleton] at hk
           rcases hk with rfl | rfl
           ·exact hmv_F hkf
           ·exact hmu_nF hkf
          have hsub2 : {mv, mu} ∪ FacAll ⊆ orN G C \ lam G C :=
           Finset.union_subset (Finset.insert_subset hmv (Finset.singleton_subset_iff.mpr hmu)) hFacAll_sub
          have := Finset.card_le_card hsub2
          rw [Finset.card_union_of_disjoint hdisj_m, Finset.card_pair hmv_mu, hFacAll_card] at this
          omega
        omega
       ·obtain ⟨c2, hc2, hc2z⟩ := flag_exists_other_C hf2
        have hc2_nM : c2 ∉ MC2 := fun h => h2ne ⟨c2, Finset.mem_erase.mpr ⟨hc2z, h⟩⟩
        have hMC2_le : MC2.card ≤ FacC2.card := hFC2_raw.2 ⟨c2, hc2, hc2_nM⟩
        omega
 by_cases hDinter : (D1 ∩ D2).Nonempty
 ·obtain ⟨d0, hd0⟩ := hDinter
  have hd0_1 := (Finset.mem_inter.mp hd0).1
  have hd0_2 := (Finset.mem_inter.mp hd0).2
  have hD_union : D1 ∪ D2 = D1 ∪ orIn n C w2D := by
   by_cases hr : OrReaches n C w2D g1
   ·have h := hb2D_r hr; rw [Finset.union_eq_right.mpr h.1, h.2.2]; rfl
   ·rw [show orIn n C w2D = D2 from hb2D_nr hr]
  have hd0_w2D : d0 ∈ orIn n C w2D ∨ OrReaches n C w2D g1 := by
   by_cases hr : OrReaches n C w2D g1
   ·exact Or.inr hr
   ·left; rw [show orIn n C w2D = D2 from hb2D_nr hr]; exact hd0_2
  have hFD_b := merged_opnds_fac_bound hL hLift h4 hne hjunk
   (by have := opnd_lt hL.1 hg1j.1 (1 - b1); omega : w1D < n + g2)
   (opnd_lt hL.1 hg2j.1 (1 - b2))
   (hnb_w g1 ((hjunk g1).mpr (Or.inl rfl)) (1 - b1))
   (hnb_w g2 ((hjunk g2).mpr (Or.inr rfl)) (1 - b2))
   (show orIn n C w1D = D1 from hb1D) hb2D_sub hD_union
   (fun u hu => by rcases Finset.mem_union.mp hu with h | h; exact (hf1.2.2.2.2.1 u h).symm; exact (hf2.2.2.2.2.1 u h).symm)
   hd0_1 hd0_w2D
  have hMD_eq_filt : (D1 ∪ D2).filter (fun u => s(z, u) ∈ Ustar G C) = MD := by
   ext u; simp [MD, MD1, MD2, Finset.filter_union]
  dsimp only at hFD_b
  rw [hMD_eq_filt] at hFD_b
  have hMD_le : MD.card ≤ FacD.card + 1 := by
   by_cases hne_MD : MD.Nonempty
   ·exact hFD_b.1 hne_MD
   ·rw [Finset.not_nonempty_iff_eq_empty.mp hne_MD]; simp
  exact close_slack1 (by rw [hFacAll_card]; omega)
 ·
  have hDisjD : Disjoint D1 D2 := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hDinter)
  have hnw2D_1 : ¬ OrReaches n C w2D g1 := fun hr =>
   Finset.disjoint_left.mp hDisjD hf1.2.2.1 ((hb2D_r hr).1 hf1.2.2.1)
  have hw2D_eq : orIn n C w2D = D2 := hb2D_nr hnw2D_1
  set FacD1 := (orN G C \ lam G C).filter (fun k => OrReaches n C w1D k)
  set FacD2 := (orN G C \ lam G C).filter (fun k => OrReaches n C w2D k)
  have hFacD_eq : FacD = FacD1 ∪ FacD2 := by ext k; simp [FacD, FacD1, FacD2, and_or_left]
  have hFacD1_pure : ∀ k ∈ FacD1, ¬ OrReaches n C (n + k) g1 ∧ ¬ OrReaches n C (n + k) g2 ∧
    orIn n C (n + k) ⊆ D1 ∧ 2 ≤ (orIn n C (n + k)).card := by
   intro k hk
   have hkf := Finset.mem_filter.mp hk
   have hn1 : ¬ OrReaches n C (n + k) g1 := fun h => hnw1D_1 (orReaches_trans hkf.2 h)
   have hn2 : ¬ OrReaches n C (n + k) g2 := fun h => hnw1D_2 (orReaches_trans hkf.2 h)
   have hsub : orIn n C (n + k) ⊆ D1 := by
    have := orIn_subset_of_orReaches hkf.2; rwa [show orIn n C w1D = D1 from hb1D] at this
   exact ⟨hn1, hn2, hsub, pure_orN_card_ge_two hL hLift hne hjunk (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
  have hFacD2_pure : ∀ k ∈ FacD2, ¬ OrReaches n C (n + k) g1 ∧ ¬ OrReaches n C (n + k) g2 ∧
    orIn n C (n + k) ⊆ D2 ∧ 2 ≤ (orIn n C (n + k)).card := by
   intro k hk
   have hkf := Finset.mem_filter.mp hk
   have hn1 : ¬ OrReaches n C (n + k) g1 := fun h => hnw2D_1 (orReaches_trans hkf.2 h)
   have hn2 : ¬ OrReaches n C (n + k) g2 := fun h => hnw2D_2 (orReaches_trans hkf.2 h)
   have hsub : orIn n C (n + k) ⊆ D2 := by
    have := orIn_subset_of_orReaches hkf.2; rwa [hw2D_eq] at this
   exact ⟨hn1, hn2, hsub, pure_orN_card_ge_two hL hLift hne hjunk (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
  have hDisjD1D2 : Disjoint FacD1 FacD2 := by
   rw [Finset.disjoint_left]; intro k hk1 hk2
   obtain ⟨u, hu⟩ := Finset.card_pos.mp (by have := (hFacD1_pure k hk1).2.2.2; omega : 0 < (orIn n C (n + k)).card)
   exact Finset.disjoint_left.mp hDisjD ((hFacD1_pure k hk1).2.2.1 hu) ((hFacD2_pure k hk2).2.2.1 hu)
  have hFacD_card : FacD.card = FacD1.card + FacD2.card := by
   rw [hFacD_eq, Finset.card_union_of_disjoint hDisjD1D2]
  have hFacAll_pure : ∀ k ∈ FacAll, ¬ OrReaches n C (n + k) g1 ∧ ¬ OrReaches n C (n + k) g2 := by
   intro k hk; simp only [FacAll, hFacD_eq, Finset.mem_union] at hk
   rcases hk with (h | h) | (h | h)
   ·exact ⟨(hFacC1_pure k h).2.1, (hFacC1_pure k h).2.2.1⟩
   ·exact ⟨(hFacC2_pure k h).2.1, (hFacC2_pure k h).2.2.1⟩
   ·exact ⟨(hFacD1_pure k h).1, (hFacD1_pure k h).2.1⟩
   ·exact ⟨(hFacD2_pure k h).1, (hFacD2_pure k h).2.1⟩
  have hFD1_raw := single_opnd_fac_bound hL hLift h4 hne hjunk
   (by have := opnd_lt hL.1 hg1j.1 (1 - b1); omega : w1D < n + g2)
   (hnb_w g1 ((hjunk g1).mpr (Or.inl rfl)) (1 - b1)) hnw1D_1
   (show orIn n C w1D = D1 from hb1D) (fun u hu => (hf1.2.2.2.2.1 u hu).symm)
  have hFD2_raw := single_opnd_fac_bound hL hLift h4 hne hjunk
   (opnd_lt hL.1 hg2j.1 (1 - b2))
   (hnb_w g2 ((hjunk g2).mpr (Or.inr rfl)) (1 - b2)) hnw2D_1
   hw2D_eq (fun u hu => (hf2.2.2.2.2.1 u hu).symm)
  have hMD_card : MD.card = MD1.card + MD2.card :=
   Finset.card_union_of_disjoint (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hDisjD)
  dsimp only at hFD1_raw hFD2_raw
  by_cases hall_U : MC1 = C1 ∧ MC2 = C2 ∧ MD1 = D1 ∧ MD2 = D2
  ·
   obtain ⟨hMC1_eq, hMC2_eq, hMD1_eq, hMD2_eq⟩ := hall_U
   have hMD1_le : MD1.card ≤ FacD1.card + 1 := hFD1_raw.1 ⟨zp1, by change zp1 ∈ MD1; rw [hMD1_eq]; exact hf1.2.2.1⟩
   have hMD2_le : MD2.card ≤ FacD2.card + 1 := hFD2_raw.1 ⟨zp2, by change zp2 ∈ MD2; rw [hMD2_eq]; exact hf2.2.2.1⟩
   let L1 : Fin n → Finset (Fin n) := fun v =>
    if v = z then MD else if v = zp1 then MC1.erase z else if v = zp2 then MC2.erase z else ∅
   have hL1z : L1 z = MD := by simp [L1]
   have hL1_1 : L1 zp1 = MC1.erase z := by simp [L1, hz_ne1.symm]
   have hL1_2 : L1 zp2 = MC2.erase z := by simp [L1, hz_ne2.symm, hzp12.symm]
   have hcov1 : ∀ e ∈ Ustar G C, (∃ u ∈ L1 z, e = s(z, u)) ∨ (∃ u ∈ L1 zp1, e = s(zp1, u)) ∨ (∃ u ∈ L1 zp2, e = s(zp2, u)) := by
    intro e he
    have heF := hUsub he
    simp only [Finset.mem_union, flagEdges, Finset.mem_image] at heF
    rcases heF with (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩) | (⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩)
    ·left; exact ⟨d, by rw [hL1z]; exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd, he⟩), rfl⟩
    ·by_cases hcz : c = z
     ·subst hcz; left; exact ⟨zp1, by rw [hL1z]; exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hf1.2.2.1, he⟩), rfl⟩
     ·right; left; exact ⟨c, by rw [hL1_1]; exact Finset.mem_erase.mpr ⟨hcz, Finset.mem_filter.mpr ⟨hc, he⟩⟩, Sym2.eq_swap⟩
    ·left; exact ⟨d, by rw [hL1z]; exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd, he⟩), rfl⟩
    ·by_cases hcz : c = z
     ·subst hcz; left; exact ⟨zp2, by rw [hL1z]; exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf2.2.2.1, he⟩), rfl⟩
     ·right; right; exact ⟨c, by rw [hL1_2]; exact Finset.mem_erase.mpr ⟨hcz, Finset.mem_filter.mpr ⟨hc, he⟩⟩, Sym2.eq_swap⟩
   have hsurg1 := run_surgery3 L1
    (fun u hu => by rw [hL1z] at hu; rcases Finset.mem_union.mp hu with h | h; exact (hf1.2.2.2.2.1 u (Finset.mem_filter.mp h).1).symm; exact (hf2.2.2.2.2.1 u (Finset.mem_filter.mp h).1).symm)
    (fun u hu => by rw [hL1_1] at hu; exact (hf1.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm)
    (fun u hu => by rw [hL1_2] at hu; exact (hf2.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm)
    hcov1
   dsimp only at hsurg1
   set Zact := ({z, zp1, zp2} : Finset (Fin n)).filter (fun v => (L1 v).Nonempty)
   set Zhas := Zact.filter (fun v => ∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = v)
   rw [hL1z, hL1_1, hL1_2] at hsurg1
   have hZnew_le3 : (Zact \ Zhas).card ≤ 3 := by
    calc (Zact \ Zhas).card ≤ ({z, zp1, zp2} : Finset (Fin n)).card :=
       Finset.card_le_card (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))
     _ = 3 := by rw [Finset.card_insert_of_notMem (by simp [hz_ne1, hz_ne2]), Finset.card_pair hzp12]
   obtain ⟨c1, hc1, hc1z⟩ := flag_exists_other_C hf1
   obtain ⟨c2, hc2, hc2z⟩ := flag_exists_other_C hf2
   obtain ⟨d1, hd1, hd1zp⟩ := flag_exists_other_D hf1
   obtain ⟨d2, hd2, hd2zp⟩ := flag_exists_other_D hf2
   have hc1_er : c1 ∈ MC1.erase z := Finset.mem_erase.mpr ⟨hc1z, by rw [hMC1_eq]; exact hc1⟩
   have hc2_er : c2 ∈ MC2.erase z := Finset.mem_erase.mpr ⟨hc2z, by rw [hMC2_eq]; exact hc2⟩
   have hd1_MD : d1 ∈ MD := Finset.mem_union_left _ (by rw [hMD1_eq]; exact hd1)
   have hd2_MD : d2 ∈ MD := Finset.mem_union_right _ (by rw [hMD2_eq]; exact hd2)
   have hd1_nzp2 : d1 ≠ zp2 := fun h => Finset.disjoint_left.mp hDisjD hd1 (h ▸ hf2.2.2.1)
   have hd2_nzp1 : d2 ≠ zp1 := fun h => Finset.disjoint_right.mp hDisjD hd2 (h ▸ hf1.2.2.1)
   have hnFac_of_reach : ∀ k, (OrReaches n C (n + k) g1 ∨ OrReaches n C (n + k) g2) → k ∉ FacAll := by
    intro k hr hkf
    rcases hr with h1 | h2
    ·exact (hFacAll_pure k hkf).1 h1
    ·exact (hFacAll_pure k hkf).2 h2
   have hFac_le : FacAll.card ≤ (orN G C \ lam G C).card := Finset.card_le_card hFacAll_sub
   by_cases hcent2 : 2 ≤ (centreless G C).card
   ·omega
   ·by_cases hcent1 : (centreless G C).card = 1
    ·
     by_cases hZle1 : (Zact \ Zhas).card ≤ 1
     ·omega
     ·obtain ⟨a0, ha0⟩ := Finset.card_eq_one.mp hcent1
      have ha0_cent : a0 ∈ centreless G C := by rw [ha0]; simp
      have ha0_top : a0 ∈ tops G C := (Finset.mem_filter.mp ha0_cent).1
      have ha0' := mem_tops_iff.mp ha0_top
      by_cases hZ3 : (Zact \ Zhas).card = 3
      ·
       have hZ_eq3 : Zact \ Zhas = {z, zp1, zp2} :=
        Finset.eq_of_subset_of_card_le
         (Finset.Subset.trans Finset.sdiff_subset (Finset.filter_subset _ _))
         (by rw [Finset.card_insert_of_notMem (by simp [hz_ne1, hz_ne2]), Finset.card_pair hzp12]; omega)
       have hz_new : z ∈ Zact \ Zhas := by rw [hZ_eq3]; simp
       have hzp1_new : zp1 ∈ Zact \ Zhas := by rw [hZ_eq3]; simp
       obtain ⟨b0, hemp0, hrb0_1, hzs0⟩ : ∃ b0 : Fin 2, side (n := n) C a0 b0 = ∅ ∧
         OrReaches n C (opnd C a0 b0) g1 ∧ z ∈ side (n := n) C a0 (1 - b0) := by
        rcases hgolden_z d1 hd1_MD hd1zp hd1_nzp2 with hA | ⟨a, haC, b, g, hg, hgv, hemp, hrb, hzs⟩
        ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz_new).1, hA⟩) (Finset.mem_sdiff.mp hz_new).2
        ·have haeq : a = a0 := Finset.mem_singleton.mp (ha0 ▸ haC); subst haeq
         have hg2f : gateVal n C g2 (pairInput z d1) = false := by
          rw [Bool.eq_false_iff, ne_eq, flag_pair_edge_iff hbip h4 hf2 (hf1.2.2.2.2.1 d1 hd1).symm]
          simp only [flagEdges, Finset.mem_union, Finset.mem_image, Sym2.eq_iff]
          rintro (⟨d, hd, ⟨_, rfl⟩ | ⟨h1, _⟩⟩ | ⟨c, _, ⟨_, rfl⟩ | ⟨_, h2⟩⟩)
          ·exact Finset.disjoint_left.mp hDisjD hd1 hd
          ·exact absurd (h1 ▸ flag_color_D hbip hf1 hd1) (hbip z zp1 hf1.1)
          ·exact hd1_nzp2 rfl
          ·exact hz_ne2.symm h2
         have hgeq : g = g1 := hg.resolve_right (fun h => by rw [h, hg2f] at hgv; cases hgv)
         subst hgeq; exact ⟨b, hemp, hrb, hzs⟩
       have hrb0_2 : OrReaches n C (opnd C a0 b0) g2 := by
        rcases hgolden_z d2 hd2_MD hd2_nzp1 hd2zp with hA | ⟨a, haC, b, g, hg, hgv, hemp, hrb, hzs⟩
        ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz_new).1, hA⟩) (Finset.mem_sdiff.mp hz_new).2
        ·have haeq : a = a0 := Finset.mem_singleton.mp (ha0 ▸ haC); subst haeq
         have hg1f : gateVal n C g1 (pairInput z d2) = false := by
          rw [Bool.eq_false_iff, ne_eq, flag_pair_edge_iff hbip h4 hf1 (hf2.2.2.2.2.1 d2 hd2).symm]
          simp only [flagEdges, Finset.mem_union, Finset.mem_image, Sym2.eq_iff]
          rintro (⟨d, hd, ⟨_, rfl⟩ | ⟨h1, _⟩⟩ | ⟨c, _, ⟨_, rfl⟩ | ⟨_, h2⟩⟩)
          ·exact Finset.disjoint_left.mp hDisjD hd hd2
          ·exact absurd (h1 ▸ flag_color_D hbip hf2 hd2) (hbip z zp2 hf2.1)
          ·exact hd2_nzp1 rfl
          ·exact hz_ne1.symm h2
         have hgeq : g = g2 := hg.resolve_left (fun h => by rw [h, hg1f] at hgv; cases hgv)
         subst hgeq
         have hbe : b = b0 := by
          by_contra hne_b
          have h1mb : 1 - b0 = b := fin2_sub_eq (Ne.symm hne_b)
          rw [h1mb, hemp] at hzs0; exact Finset.notMem_empty _ hzs0
         rwa [← hbe]
       obtain ⟨mp, hmp, hmp_gt, hmp_emp⟩ := pureFlagOr_of_reaches_both hL hlt12 hjunk
        (by have := opnd_lt hL.1 ha0'.1 b0; omega) (top_opnd_not_belowF hL hne ha0_top b0)
        hemp0 hrb0_1 hrb0_2
       obtain ⟨m2, hm2, hm2_nF, hm2_ne⟩ : ∃ m2 ∈ orN G C \ lam G C, m2 ∉ FacAll ∧ (orIn n C (n + m2)).Nonempty := by
        rcases hgolden_zp1 c1 hc1_er with hA | ⟨a, haC, b, hemp, _, hzp1s⟩ | ⟨mv, hmv, hmv_gt, hmv_orIn, _⟩
        ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp1_new).1, hA⟩) (Finset.mem_sdiff.mp hzp1_new).2
        ·have haeq : a = a0 := Finset.mem_singleton.mp (ha0 ▸ haC); subst haeq
         have hbe : b = b0 := by
          by_contra hne_b
          have h1mb : 1 - b0 = b := fin2_sub_eq (Ne.symm hne_b)
          rw [h1mb, hemp] at hzs0; exact Finset.notMem_empty _ hzs0
         rw [hbe] at hzp1s
         obtain ⟨mw, hmw, hmw_nF, hmw_c⟩ := bichrom_w_extra hbip hL hLift hne hjunk
          (by have := opnd_lt hL.1 ha0'.1 (1 - b0); omega)
          (top_opnd_not_belowF hL hne ha0_top (1 - b0)) hzs0 hzp1s (hbip z zp1 hf1.1)
          FacAll hFacAll_mono
         exact ⟨mw, hmw, hmw_nF, Finset.card_pos.mp (by omega)⟩
        ·exact ⟨mv, hmv, fun h => by have := hFacAll_lt mv h; omega, by rw [hmv_orIn]; simp⟩
       have hmp_nF : mp ∉ FacAll := fun h => by have := hFacAll_lt mp h; omega
       have hmp_ne2 : mp ≠ m2 := fun h => by rw [← h, hmp_emp] at hm2_ne; exact hm2_ne.ne_empty rfl
       have hdisj_m : Disjoint ({mp, m2} : Finset ℕ) FacAll := by
        rw [Finset.disjoint_left]; intro k hk hkf
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        ·exact hmp_nF hkf
        ·exact hm2_nF hkf
       have hFac_s2 := Finset.card_le_card (Finset.union_subset
        (Finset.insert_subset hmp (Finset.singleton_subset_iff.mpr hm2)) hFacAll_sub)
       rw [Finset.card_union_of_disjoint hdisj_m, Finset.card_pair hmp_ne2] at hFac_s2
       omega
      ·
       have hZ_eq2 : (Zact \ Zhas).card = 2 := by omega
       have hex_extra : ∃ m ∈ orN G C \ lam G C, m ∉ FacAll := by
        by_cases hz_in : z ∈ Zact \ Zhas
        ·
         obtain ⟨b0, hemp0, hzs0⟩ : ∃ b0 : Fin 2, side (n := n) C a0 b0 = ∅ ∧ z ∈ side (n := n) C a0 (1 - b0) := by
          rcases hgolden_z d1 hd1_MD hd1zp hd1_nzp2 with hA | ⟨a, haC, b, _, _, _, hemp, _, hzs⟩
          ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz_in).1, hA⟩) (Finset.mem_sdiff.mp hz_in).2
          ·have haeq : a = a0 := Finset.mem_singleton.mp (ha0 ▸ haC); subst haeq
           exact ⟨b, hemp, hzs⟩
         have hex_zp : zp1 ∈ Zact \ Zhas ∨ zp2 ∈ Zact \ Zhas := by
          by_contra hno; push Not at hno
          have hsub : Zact \ Zhas ⊆ {z} := by
           intro v hv
           have hv1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
           simp only [Finset.mem_insert, Finset.mem_singleton] at hv1 ⊢
           rcases hv1 with rfl | rfl | rfl
           ·rfl
           ·exact absurd hv hno.1
           ·exact absurd hv hno.2
          have := (Finset.card_le_card hsub).trans (by simp : ({z} : Finset (Fin n)).card ≤ 1)
          omega
         rcases hex_zp with hzp1_new | hzp2_new
         ·rcases hgolden_zp1 c1 hc1_er with hA | ⟨a, haC, b, hemp, _, hzp1s⟩ | ⟨mv, hmv, hmv_gt, _⟩
          ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp1_new).1, hA⟩) (Finset.mem_sdiff.mp hzp1_new).2
          ·have haeq : a = a0 := Finset.mem_singleton.mp (ha0 ▸ haC); subst haeq
           have hbe : b = b0 := by
            by_contra hne_b
            have h1mb : 1 - b0 = b := fin2_sub_eq (Ne.symm hne_b)
            rw [h1mb, hemp] at hzs0; exact Finset.notMem_empty _ hzs0
           rw [hbe] at hzp1s
           obtain ⟨mw, hmw, hmw_nF, _⟩ := bichrom_w_extra hbip hL hLift hne hjunk
            (by have := opnd_lt hL.1 ha0'.1 (1 - b0); omega)
            (top_opnd_not_belowF hL hne ha0_top (1 - b0)) hzs0 hzp1s (hbip z zp1 hf1.1)
            FacAll hFacAll_mono
           exact ⟨mw, hmw, hmw_nF⟩
          ·exact ⟨mv, hmv, fun h => by have := hFacAll_lt mv h; omega⟩
         ·rcases hgolden_zp2 c2 hc2_er with hA | ⟨a, haC, b, hemp, _, hzp2s⟩ | ⟨_, _, _, _, _, _, mu, hmu, hmu_gt, _⟩
          ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp2_new).1, hA⟩) (Finset.mem_sdiff.mp hzp2_new).2
          ·have haeq : a = a0 := Finset.mem_singleton.mp (ha0 ▸ haC); subst haeq
           have hbe : b = b0 := by
            by_contra hne_b
            have h1mb : 1 - b0 = b := fin2_sub_eq (Ne.symm hne_b)
            rw [h1mb, hemp] at hzs0; exact Finset.notMem_empty _ hzs0
           rw [hbe] at hzp2s
           obtain ⟨mw, hmw, hmw_nF, _⟩ := bichrom_w_extra hbip hL hLift hne hjunk
            (by have := opnd_lt hL.1 ha0'.1 (1 - b0); omega)
            (top_opnd_not_belowF hL hne ha0_top (1 - b0)) hzs0 hzp2s (hbip z zp2 hf2.1)
            FacAll hFacAll_mono
           exact ⟨mw, hmw, hmw_nF⟩
          ·exact ⟨mu, hmu, fun h => by have := hFacAll_lt mu h; omega⟩
        ·
         have hsub : Zact \ Zhas ⊆ {zp1, zp2} := by
          intro v hv
          have hv1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv1 ⊢
          exact hv1.resolve_left (fun h => hz_in (h ▸ hv))
         have hZ_eq : Zact \ Zhas = {zp1, zp2} :=
          Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hzp12]; omega)
         have hzp1_new : zp1 ∈ Zact \ Zhas := by rw [hZ_eq]; simp
         have hzp2_new : zp2 ∈ Zact \ Zhas := by rw [hZ_eq]; simp
         rcases hgolden_zp1 c1 hc1_er with hA1 | ⟨a1, ha1C, b1', hemp1, hrb1, hzp1s⟩ | ⟨mv, hmv, hmv_gt, _⟩
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp1_new).1, hA1⟩) (Finset.mem_sdiff.mp hzp1_new).2
         ·rcases hgolden_zp2 c2 hc2_er with hA2 | ⟨a2, ha2C, b2', hemp2, hrb2, hzp2s⟩ | ⟨_, _, _, _, _, _, mu, hmu, hmu_gt, _⟩
          ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp2_new).1, hA2⟩) (Finset.mem_sdiff.mp hzp2_new).2
          ·have ha1eq : a1 = a0 := Finset.mem_singleton.mp (ha0 ▸ ha1C)
           have ha2eq : a2 = a0 := Finset.mem_singleton.mp (ha0 ▸ ha2C)
           subst ha1eq; subst ha2eq
           have hb12 : b1' = b2' := by
            by_contra hne_b
            have h1mb : 1 - b1' = b2' := fin2_sub_eq hne_b
            rw [h1mb, hemp2] at hzp1s; exact Finset.notMem_empty _ hzp1s
           subst hb12
           obtain ⟨mp, hmp, hmp_gt, _⟩ := pureFlagOr_of_reaches_both hL hlt12 hjunk
            (by have := opnd_lt hL.1 ha0'.1 b1'; omega) (top_opnd_not_belowF hL hne ha0_top b1')
            hemp1 hrb1 hrb2
           exact ⟨mp, hmp, fun h => by have := hFacAll_lt mp h; omega⟩
          ·exact ⟨mu, hmu, fun h => by have := hFacAll_lt mu h; omega⟩
         ·exact ⟨mv, hmv, fun h => by have := hFacAll_lt mv h; omega⟩
       obtain ⟨m, hm, hm_nF⟩ := hex_extra
       have hFac_s1 := Finset.card_le_card (Finset.insert_subset hm hFacAll_sub)
       rw [Finset.card_insert_of_notMem hm_nF] at hFac_s1
       omega
    ·
     have hcent0 : centreless G C = ∅ := Finset.card_eq_zero.mp (by omega)
     have hz_own : ∃ a ∈ tops G C \ centreless G C, topOwner C s z g1 g2 a = z := by
      rcases hgolden_z d1 hd1_MD hd1zp hd1_nzp2 with hA | ⟨a, haC, _⟩
      ·exact hA
      ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
     have hz_nnew : z ∉ Zact \ Zhas := fun h =>
      (Finset.mem_sdiff.mp h).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp h).1, hz_own⟩)
     have hZsub : Zact \ Zhas ⊆ {zp1, zp2} := by
      intro v hv
      have hv1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv1 ⊢
      exact hv1.resolve_left (fun h => hz_nnew (h ▸ hv))
     have hZle2 : (Zact \ Zhas).card ≤ 2 := (Finset.card_le_card hZsub).trans (by rw [Finset.card_pair hzp12])
     by_cases hZ0 : (Zact \ Zhas).card = 0
     ·obtain ⟨m0, hm0, hm0_gt⟩ := exists_mixing_gt_g2 hL hLift hne hlt12 hjunk hcent0
      have hm0_nF : m0 ∉ FacAll := fun h => by have := hFacAll_lt m0 h; omega
      have hFac_s1 := Finset.card_le_card (Finset.insert_subset hm0 hFacAll_sub)
      rw [Finset.card_insert_of_notMem hm0_nF] at hFac_s1
      omega
     ·by_cases hZ1 : (Zact \ Zhas).card = 1
      ·
       have hex2 : ∃ m1 m2, m1 ≠ m2 ∧ m1 ∈ orN G C \ lam G C ∧ m2 ∈ orN G C \ lam G C ∧
         m1 ∉ FacAll ∧ m2 ∉ FacAll := by
        have hne_Z : (Zact \ Zhas).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨v, hv⟩ := hne_Z
        have hv' := hZsub hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
        rcases hv' with hv_eq | hv_eq
        ·rw [hv_eq] at hv
         rcases hgolden_zp1 c1 hc1_er with hA | ⟨a, haC, _⟩ | ⟨mv, hmv, hmv_gt, hmv_orIn, u', hsu', mu, hmu, hmu_g, hmu_orIn⟩
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1, hA⟩) (Finset.mem_sdiff.mp hv).2
         ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
         ·have hne_m : mv ≠ mu := fun h => by
           rw [h, hmu_orIn] at hmv_orIn
           have := Finset.singleton_injective hmv_orIn
           exact hbip z zp1 hf1.1 (hsu'.symm.trans (congrArg s this))
          exact ⟨mv, mu, hne_m, hmv, hmu, fun h => by have := hFacAll_lt mv h; omega,
           hnFac_of_reach mu (Or.inl hmu_g)⟩
        ·rw [hv_eq] at hv
         rcases hgolden_zp2 c2 hc2_er with hA | ⟨a, haC, _⟩ | ⟨mv, hmv, hmv_g, hmv_orIn, u', hsu', mu, hmu, hmu_gt, hmu_orIn⟩
         ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1, hA⟩) (Finset.mem_sdiff.mp hv).2
         ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
         ·have hne_m : mv ≠ mu := fun h => by
           rw [h, hmu_orIn] at hmv_orIn
           have := Finset.singleton_injective hmv_orIn
           exact hbip z zp2 hf2.1 (hsu'.symm.trans (congrArg s this))
          exact ⟨mv, mu, hne_m, hmv, hmu, hnFac_of_reach mv (Or.inl hmv_g),
           fun h => by have := hFacAll_lt mu h; omega⟩
       obtain ⟨m1, m2, hm12, hm1, hm2, hm1_nF, hm2_nF⟩ := hex2
       have hdisj_m : Disjoint ({m1, m2} : Finset ℕ) FacAll := by
        rw [Finset.disjoint_left]; intro k hk hkf
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        ·exact hm1_nF hkf
        ·exact hm2_nF hkf
       have hFac_s2 := Finset.card_le_card (Finset.union_subset
        (Finset.insert_subset hm1 (Finset.singleton_subset_iff.mpr hm2)) hFacAll_sub)
       rw [Finset.card_union_of_disjoint hdisj_m, Finset.card_pair hm12] at hFac_s2
       omega
      ·
       have hZ_eq : Zact \ Zhas = {zp1, zp2} :=
        Finset.eq_of_subset_of_card_le hZsub (by rw [Finset.card_pair hzp12]; omega)
       have hzp1_new : zp1 ∈ Zact \ Zhas := by rw [hZ_eq]; simp
       have hzp2_new : zp2 ∈ Zact \ Zhas := by rw [hZ_eq]; simp
       obtain ⟨m1, hm1, hm1_nF, hm1_orIn, u', hsu', m3, hm3, hm3_nF, hm3_orIn⟩ :
         ∃ m1 ∈ orN G C \ lam G C, m1 ∉ FacAll ∧ orIn n C (n + m1) = {zp1} ∧
         ∃ u' : Fin n, s u' = s z ∧ ∃ m3 ∈ orN G C \ lam G C, m3 ∉ FacAll ∧ orIn n C (n + m3) = {u'} := by
        rcases hgolden_zp1 c1 hc1_er with hA | ⟨a, haC, _⟩ | ⟨mv, hmv, hmv_gt, hmv_orIn, u', hsu', mu, hmu, hmu_g, hmu_orIn⟩
        ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp1_new).1, hA⟩) (Finset.mem_sdiff.mp hzp1_new).2
        ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
        ·exact ⟨mv, hmv, fun h => by have := hFacAll_lt mv h; omega, hmv_orIn,
          u', hsu', mu, hmu, hnFac_of_reach mu (Or.inl hmu_g), hmu_orIn⟩
       obtain ⟨m2, hm2, hm2_nF, hm2_orIn⟩ :
         ∃ m2 ∈ orN G C \ lam G C, m2 ∉ FacAll ∧ orIn n C (n + m2) = {zp2} := by
        rcases hgolden_zp2 c2 hc2_er with hA | ⟨a, haC, _⟩ | ⟨mv, hmv, hmv_g, hmv_orIn, _⟩
        ·exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hzp2_new).1, hA⟩) (Finset.mem_sdiff.mp hzp2_new).2
        ·rw [hcent0] at haC; exact absurd haC (Finset.notMem_empty _)
        ·exact ⟨mv, hmv, hnFac_of_reach mv (Or.inl hmv_g), hmv_orIn⟩
       have hm12 : m1 ≠ m2 := fun h => by
        rw [h, hm2_orIn] at hm1_orIn; exact hzp12.symm (Finset.singleton_injective hm1_orIn)
       have hm13 : m1 ≠ m3 := fun h => by
        rw [h, hm3_orIn] at hm1_orIn
        have := Finset.singleton_injective hm1_orIn
        exact hbip z zp1 hf1.1 (hsu'.symm.trans (congrArg s this))
       have hm23 : m2 ≠ m3 := fun h => by
        rw [h, hm3_orIn] at hm2_orIn
        have := Finset.singleton_injective hm2_orIn
        exact hbip z zp2 hf2.1 (hsu'.symm.trans (congrArg s this))
       have hdisj_m : Disjoint ({m1, m2, m3} : Finset ℕ) FacAll := by
        rw [Finset.disjoint_left]; intro k hk hkf
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl
        ·exact hm1_nF hkf
        ·exact hm2_nF hkf
        ·exact hm3_nF hkf
       have hFac_s3 := Finset.card_le_card (Finset.union_subset
        (Finset.insert_subset hm1 (Finset.insert_subset hm2 (Finset.singleton_subset_iff.mpr hm3))) hFacAll_sub)
       rw [Finset.card_union_of_disjoint hdisj_m,
        Finset.card_insert_of_notMem (by simp [hm12, hm13]), Finset.card_pair hm23] at hFac_s3
       omega
  ·
   have hMD1_le : MD1.card ≤ FacD1.card + 1 := by
    by_cases h : MD1.Nonempty
    ·exact hFD1_raw.1 h
    ·rw [Finset.not_nonempty_iff_eq_empty.mp h]; simp
   have hMD2_le : MD2.card ≤ FacD2.card + 1 := by
    by_cases h : MD2.Nonempty
    ·exact hFD2_raw.1 h
    ·rw [Finset.not_nonempty_iff_eq_empty.mp h]; simp
   apply close_slack1
   rw [hFacAll_card, hFacD_card, hMD_card]
   by_cases hMD1_eq : MD1 = D1
   ·by_cases hMD2_eq : MD2 = D2
    ·
     have hzMC1 : z ∈ MC1 := Finset.mem_filter.mpr ⟨hf1.2.1, (Finset.mem_filter.mp (by rw [hMD1_eq]; exact hf1.2.2.1 : zp1 ∈ MD1)).2⟩
     have hzMC2 : z ∈ MC2 := Finset.mem_filter.mpr ⟨hf2.2.1, (Finset.mem_filter.mp (by rw [hMD2_eq]; exact hf2.2.2.1 : zp2 ∈ MD2)).2⟩
     by_cases hMC1_eq : MC1 = C1
     ·have hMC2_ne : MC2 ≠ C2 := fun h => hall_U ⟨hMC1_eq, h, hMD1_eq, hMD2_eq⟩
      have hex : ∃ r ∈ C2, r ∉ MC2 := by
       by_contra hno; push Not at hno
       exact hMC2_ne (Finset.Subset.antisymm (Finset.filter_subset _ _) hno)
      have hle : MC2.card ≤ FacC2.card := hFC2_raw.2 hex
      rw [Finset.card_erase_of_mem hzMC2]
      have hpos := Finset.card_pos.mpr ⟨z, hzMC2⟩
      omega
     ·have hex : ∃ r ∈ C1, r ∉ MC1 := by
       by_contra hno; push Not at hno
       exact hMC1_eq (Finset.Subset.antisymm (Finset.filter_subset _ _) hno)
      have hle : MC1.card ≤ FacC1.card := hFC1_raw.2 hex
      rw [Finset.card_erase_of_mem hzMC1]
      have hpos := Finset.card_pos.mpr ⟨z, hzMC1⟩
      omega
    ·have hex : ∃ r ∈ D2, r ∉ MD2 := by
      by_contra hno; push Not at hno
      exact hMD2_eq (Finset.Subset.antisymm (Finset.filter_subset _ _) hno)
     have hle : MD2.card ≤ FacD2.card := hFD2_raw.2 hex
     omega
   ·have hex : ∃ r ∈ D1, r ∉ MD1 := by
     by_contra hno; push Not at hno
     exact hMD1_eq (Finset.Subset.antisymm (Finset.filter_subset _ _) hno)
    have hle : MD1.card ≤ FacD1.card := hFD1_raw.2 hex
    omega
lemma case_four_centers {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {s : Fin n → Bool} (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
  {g1 g2 : ℕ} (hlt12 : g1 < g2) (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
  {C1 D1 C2 D2 : Finset (Fin n)} {z1 zp1 z2 zp2 : Fin n}
  (hz12 : z1 ≠ z2) (hzp12 : zp1 ≠ zp2) (hsz : s z1 = s z2) (hszp : s zp1 = s zp2)
  (hf1 : IsFlag G C g1 C1 D1 z1 zp1) (hf2 : IsFlag G C g2 C2 D2 z2 zp2) : False := by
 classical
 have hne : ∃ u v : Fin n, G.Adj u v := ⟨z1, zp1, hf1.1⟩
 have hg12 : g1 ≠ g2 := Nat.ne_of_lt hlt12
 have hg1j := mem_junk_iff.mp ((hjunk g1).mpr (Or.inl rfl))
 have hg2j := mem_junk_iff.mp ((hjunk g2).mpr (Or.inr rfl))
 have hcol_ne : s z1 ≠ s zp1 := hbip z1 zp1 hf1.1
 have hz1_zp1 : z1 ≠ zp1 := fun h => hcol_ne (congrArg s h)
 have hz1_zp2 : z1 ≠ zp2 := fun h => hcol_ne ((congrArg s h).trans hszp.symm)
 have hz2_zp1 : z2 ≠ zp1 := fun h => hcol_ne (hsz.trans (congrArg s h))
 have hz2_zp2 : z2 ≠ zp2 := fun h => hcol_ne (hsz.trans ((congrArg s h).trans hszp.symm))
 obtain ⟨⟨hn10_1, hn10_2, hn11_1, hn11_2⟩, b1, hb1C, hb1D⟩ :=
  g1_operands hbip hL hLift hlt12 hjunk hf1
 obtain ⟨hn20_2, hn21_2, b2, hb2C_sub, hb2D_sub, hb2C_r, hb2C_nr, hb2D_r, hb2D_nr⟩ :=
  g2_operands hbip h4 hL hLift hlt12 hjunk hf1 hf2 hsz hszp
 set w1C := opnd C g1 b1
 set w1D := opnd C g1 (1 - b1)
 set w2C := opnd C g2 b2
 set w2D := opnd C g2 (1 - b2)
 have hnw1C_1 : ¬ OrReaches n C w1C g1 := by fin_cases b1 <;> assumption
 have hnw1C_2 : ¬ OrReaches n C w1C g2 := by fin_cases b1 <;> assumption
 have hnw1D_1 : ¬ OrReaches n C w1D g1 := by fin_cases b1 <;> assumption
 have hnw1D_2 : ¬ OrReaches n C w1D g2 := by fin_cases b1 <;> assumption
 have hnw2C_1 : ¬ OrReaches n C w2C g1 := fun h => hzp12 (hb2C_r h).2.1
 have hnw2C_2 : ¬ OrReaches n C w2C g2 := by fin_cases b2 <;> assumption
 have hnw2D_1 : ¬ OrReaches n C w2D g1 := fun h => hz12 (hb2D_r h).2.1
 have hnw2D_2 : ¬ OrReaches n C w2D g2 := by fin_cases b2 <;> assumption
 have hw2C_eq : orIn n C w2C = C2 := hb2C_nr hnw2C_1
 have hw2D_eq : orIn n C w2D = D2 := hb2D_nr hnw2D_1
 set FacC1 := (orN G C \ lam G C).filter (fun k => OrReaches n C w1C k)
 set FacD1 := (orN G C \ lam G C).filter (fun k => OrReaches n C w1D k)
 set FacC2 := (orN G C \ lam G C).filter (fun k => OrReaches n C w2C k)
 set FacD2 := (orN G C \ lam G C).filter (fun k => OrReaches n C w2D k)
 have hnb_w : ∀ a, a ∈ junk G C → ∀ b : Fin 2, ∀ m, opnd C a b = n + m → ¬ BelowF G C m := by
  intro a ha b m hm hbm
  have ha' := mem_junk_iff.mp ha
  exact least_no_belowF_and_opnd hL hne ha'.1 ha'.2.1 b (by rw [hm]; exact hbm)
 have hFC1_p : ∀ k ∈ FacC1, ¬ OrReaches n C (n + k) g1 ∧ ¬ OrReaches n C (n + k) g2 ∧
   orIn n C (n + k) ⊆ C1 ∧ 2 ≤ (orIn n C (n + k)).card := by
  intro k hk; have hkf := Finset.mem_filter.mp hk
  have hn1 : ¬ OrReaches n C (n + k) g1 := fun h => hnw1C_1 (orReaches_trans hkf.2 h)
  have hn2 : ¬ OrReaches n C (n + k) g2 := fun h => hnw1C_2 (orReaches_trans hkf.2 h)
  have hsub := orIn_subset_of_orReaches hkf.2; rw [show orIn n C w1C = C1 from hb1C] at hsub
  exact ⟨hn1, hn2, hsub, pure_orN_card_ge_two hL hLift hne hjunk (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
 have hFD1_p : ∀ k ∈ FacD1, ¬ OrReaches n C (n + k) g1 ∧ ¬ OrReaches n C (n + k) g2 ∧
   orIn n C (n + k) ⊆ D1 ∧ 2 ≤ (orIn n C (n + k)).card := by
  intro k hk; have hkf := Finset.mem_filter.mp hk
  have hn1 : ¬ OrReaches n C (n + k) g1 := fun h => hnw1D_1 (orReaches_trans hkf.2 h)
  have hn2 : ¬ OrReaches n C (n + k) g2 := fun h => hnw1D_2 (orReaches_trans hkf.2 h)
  have hsub := orIn_subset_of_orReaches hkf.2; rw [show orIn n C w1D = D1 from hb1D] at hsub
  exact ⟨hn1, hn2, hsub, pure_orN_card_ge_two hL hLift hne hjunk (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
 have hFC2_p : ∀ k ∈ FacC2, ¬ OrReaches n C (n + k) g1 ∧ ¬ OrReaches n C (n + k) g2 ∧
   orIn n C (n + k) ⊆ C2 ∧ 2 ≤ (orIn n C (n + k)).card := by
  intro k hk; have hkf := Finset.mem_filter.mp hk
  have hn1 : ¬ OrReaches n C (n + k) g1 := fun h => hnw2C_1 (orReaches_trans hkf.2 h)
  have hn2 : ¬ OrReaches n C (n + k) g2 := fun h => hnw2C_2 (orReaches_trans hkf.2 h)
  have hsub := orIn_subset_of_orReaches hkf.2; rw [hw2C_eq] at hsub
  exact ⟨hn1, hn2, hsub, pure_orN_card_ge_two hL hLift hne hjunk (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
 have hFD2_p : ∀ k ∈ FacD2, ¬ OrReaches n C (n + k) g1 ∧ ¬ OrReaches n C (n + k) g2 ∧
   orIn n C (n + k) ⊆ D2 ∧ 2 ≤ (orIn n C (n + k)).card := by
  intro k hk; have hkf := Finset.mem_filter.mp hk
  have hn1 : ¬ OrReaches n C (n + k) g1 := fun h => hnw2D_1 (orReaches_trans hkf.2 h)
  have hn2 : ¬ OrReaches n C (n + k) g2 := fun h => hnw2D_2 (orReaches_trans hkf.2 h)
  have hsub := orIn_subset_of_orReaches hkf.2; rw [hw2D_eq] at hsub
  exact ⟨hn1, hn2, hsub, pure_orN_card_ge_two hL hLift hne hjunk (Finset.mem_sdiff.mp hkf.1).1 hn1 hn2⟩
 have hdisj_center : ∀ {v1 v2 : Fin n} {F1 F2 : Finset ℕ}, v1 ≠ v2 →
   (∀ k ∈ F1, (∀ u ∈ orIn n C (n + k), G.Adj v1 u) ∧ 2 ≤ (orIn n C (n + k)).card) →
   (∀ k ∈ F2, ∀ u ∈ orIn n C (n + k), G.Adj v2 u) → Disjoint F1 F2 := by
  intro v1 v2 F1 F2 hvne h1 h2
  rw [Finset.disjoint_left]; intro k hk1 hk2
  obtain ⟨u1, hu1, u2, hu2, hu12⟩ := Finset.one_lt_card.mp (by have := (h1 k hk1).2; omega : 1 < (orIn n C (n + k)).card)
  exact hvne (noFourCycle_unique h4 hu12
   ((h1 k hk1).1 u1 hu1).symm ((h1 k hk1).1 u2 hu2).symm
   (h2 k hk2 u1 hu1).symm (h2 k hk2 u2 hu2).symm)
 have hd_C1D1 : Disjoint FacC1 FacD1 := hdisj_center hz1_zp1.symm
  (fun k hk => ⟨fun u hu => (hf1.2.2.2.1 u ((hFC1_p k hk).2.2.1 hu)).symm, (hFC1_p k hk).2.2.2⟩)
  (fun k hk u hu => (hf1.2.2.2.2.1 u ((hFD1_p k hk).2.2.1 hu)).symm)
 have hd_C1C2 : Disjoint FacC1 FacC2 := hdisj_center hzp12
  (fun k hk => ⟨fun u hu => (hf1.2.2.2.1 u ((hFC1_p k hk).2.2.1 hu)).symm, (hFC1_p k hk).2.2.2⟩)
  (fun k hk u hu => (hf2.2.2.2.1 u ((hFC2_p k hk).2.2.1 hu)).symm)
 have hd_C1D2 : Disjoint FacC1 FacD2 := hdisj_center hz2_zp1.symm
  (fun k hk => ⟨fun u hu => (hf1.2.2.2.1 u ((hFC1_p k hk).2.2.1 hu)).symm, (hFC1_p k hk).2.2.2⟩)
  (fun k hk u hu => (hf2.2.2.2.2.1 u ((hFD2_p k hk).2.2.1 hu)).symm)
 have hd_D1C2 : Disjoint FacD1 FacC2 := hdisj_center hz1_zp2
  (fun k hk => ⟨fun u hu => (hf1.2.2.2.2.1 u ((hFD1_p k hk).2.2.1 hu)).symm, (hFD1_p k hk).2.2.2⟩)
  (fun k hk u hu => (hf2.2.2.2.1 u ((hFC2_p k hk).2.2.1 hu)).symm)
 have hd_D1D2 : Disjoint FacD1 FacD2 := hdisj_center hz12
  (fun k hk => ⟨fun u hu => (hf1.2.2.2.2.1 u ((hFD1_p k hk).2.2.1 hu)).symm, (hFD1_p k hk).2.2.2⟩)
  (fun k hk u hu => (hf2.2.2.2.2.1 u ((hFD2_p k hk).2.2.1 hu)).symm)
 have hd_C2D2 : Disjoint FacC2 FacD2 := hdisj_center hz2_zp2.symm
  (fun k hk => ⟨fun u hu => (hf2.2.2.2.1 u ((hFC2_p k hk).2.2.1 hu)).symm, (hFC2_p k hk).2.2.2⟩)
  (fun k hk u hu => (hf2.2.2.2.2.1 u ((hFD2_p k hk).2.2.1 hu)).symm)
 set FacAll := (FacC1 ∪ FacD1) ∪ (FacC2 ∪ FacD2)
 set Extra := (orN G C \ lam G C) \ FacAll
 have hFacAll_sub : FacAll ⊆ orN G C \ lam G C :=
  Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
   (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
 have hFacAll_card : FacAll.card = FacC1.card + FacD1.card + FacC2.card + FacD2.card := by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
   ⟨Finset.disjoint_union_right.mpr ⟨hd_C1C2, hd_C1D2⟩, Finset.disjoint_union_right.mpr ⟨hd_D1C2, hd_D1D2⟩⟩),
   Finset.card_union_of_disjoint hd_C1D1, Finset.card_union_of_disjoint hd_C2D2]
  omega
 have horN_split : (orN G C \ lam G C).card = FacAll.card + Extra.card := by
  rw [card_sdiff_eq hFacAll_sub]; have := Finset.card_le_card hFacAll_sub; omega
 have hFacAll_pure : ∀ k ∈ FacAll, ¬ OrReaches n C (n + k) g1 ∧ ¬ OrReaches n C (n + k) g2 := by
  intro k hk; simp only [FacAll, Finset.mem_union] at hk
  rcases hk with (h | h) | (h | h)
  ·exact ⟨(hFC1_p k h).1, (hFC1_p k h).2.1⟩
  ·exact ⟨(hFD1_p k h).1, (hFD1_p k h).2.1⟩
  ·exact ⟨(hFC2_p k h).1, (hFC2_p k h).2.1⟩
  ·exact ⟨(hFD2_p k h).1, (hFD2_p k h).2.1⟩
 have hExtra_of_reach : ∀ k ∈ orN G C \ lam G C, (OrReaches n C (n + k) g1 ∨ OrReaches n C (n + k) g2) → k ∈ Extra := by
  intro k hk hr
  exact Finset.mem_sdiff.mpr ⟨hk, fun hkf => hr.elim (hFacAll_pure k hkf).1 (hFacAll_pure k hkf).2⟩
 set E1 := flagEdges C1 D1 z1 zp1
 set E2 := flagEdges C2 D2 z2 zp2
 set U1 := Ustar G C ∩ E1
 set U2 := Ustar G C ∩ E2
 set U12 := U1 ∩ U2
 have hUsub := ustar_sub_flagEdges hbip hL hLift h4 hjunk hf1 hf2
 have hUstar_eq : Ustar G C = U1 ∪ U2 := by
  ext e; simp only [U1, U2, Finset.mem_union, Finset.mem_inter]
  constructor
  ·intro he; rcases Finset.mem_union.mp (hUsub he) with h1 | h2
   ·exact Or.inl ⟨he, h1⟩
   ·exact Or.inr ⟨he, h2⟩
  ·rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
 have hU12_mem : ∀ e ∈ U12, e = s(z1, zp2) ∨ e = s(z2, zp1) := by
  intro e he
  have he1 : e ∈ E1 := (Finset.mem_inter.mp (Finset.mem_inter.mp he).1).2
  have he2 : e ∈ E2 := (Finset.mem_inter.mp (Finset.mem_inter.mp he).2).2
  simp only [E1, E2, flagEdges, Finset.mem_union, Finset.mem_image] at he1 he2
  rcases he1 with ⟨d1, hd1, rfl⟩ | ⟨c1, hc1, rfl⟩ <;>
  rcases he2 with ⟨d2, hd2, h2⟩ | ⟨c2, hc2, h2⟩ <;>
  rw [Sym2.eq_iff] at h2
  ·rcases h2 with ⟨h, _⟩ | ⟨h, _⟩
   ·exact absurd h.symm hz12
   ·exact absurd (hsz.trans (by rw [h]; exact flag_color_D hbip hf1 hd1)) hcol_ne
  ·rcases h2 with ⟨h, h'⟩ | ⟨_, h'⟩
   ·exact Or.inl (by rw [← h, ← h'])
   ·exact absurd (hszp.trans (congrArg s h')).symm hcol_ne
  ·rcases h2 with ⟨h, h'⟩ | ⟨h, _⟩
   ·exact Or.inr (by rw [← h, ← h'])
   ·exact absurd (hsz.trans (congrArg s h)) hcol_ne
  ·rcases h2 with ⟨_, h⟩ | ⟨h, _⟩
   ·exact absurd h.symm hzp12
   ·exact absurd ((hsz.trans (flag_color_C hbip hf2 hc2).symm).trans (congrArg s h)) hcol_ne
 have hU12_le1 : U12.card ≤ 1 := by
  by_contra hgt; push Not at hgt
  obtain ⟨e1, he1, e2, he2, he12⟩ := Finset.one_lt_card.mp hgt
  have hm1 := hU12_mem e1 he1
  have hm2 := hU12_mem e2 he2
  have hboth : s(z1, zp2) ∈ U12 ∧ s(z2, zp1) ∈ U12 := by
   rcases hm1 with rfl | rfl <;> rcases hm2 with rfl | rfl
   ·exact absurd rfl he12
   ·exact ⟨he1, he2⟩
   ·exact ⟨he2, he1⟩
   ·exact absurd rfl he12
  have hadj1 : G.Adj z1 zp2 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_inter.mp hboth.1).1).1).1
  have hadj2 : G.Adj z2 zp1 := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_inter.mp hboth.2).1).1).1
  exact hzp12 (noFourCycle_unique h4 hz12 hf1.1 hadj2 hadj1 hf2.1)
 have hU12_side : (∀ e ∈ U12, e = s(z1, zp2)) ∨ (∀ e ∈ U12, e = s(z2, zp1)) := by
  by_cases hemp : U12 = ∅
  ·left; intro e he; rw [hemp] at he; exact absurd he (Finset.notMem_empty _)
  ·obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
   have hcard1 : U12.card = 1 := by have := Finset.Nonempty.card_pos ⟨e0, he0⟩; omega
   obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard1
   have hx0 : e0 = x := Finset.mem_singleton.mp (hx ▸ he0)
   subst hx0
   rcases hU12_mem e0 he0 with rfl | rfl
   ·left; intro e he; rw [hx, Finset.mem_singleton] at he; exact he
   ·right; intro e he; rw [hx, Finset.mem_singleton] at he; exact he
 set MC1 := C1.filter (fun c => s(c, zp1) ∈ Ustar G C)
 set MD1 := D1.filter (fun d => s(z1, d) ∈ Ustar G C)
 set MC2 := C2.filter (fun c => s(c, zp2) ∈ Ustar G C)
 set MD2 := D2.filter (fun d => s(z2, d) ∈ Ustar G C)
 have hFC1_b := single_opnd_fac_bound hL hLift h4 hne hjunk
  (by have := opnd_lt hL.1 hg1j.1 b1; omega : w1C < n + g2)
  (hnb_w g1 ((hjunk g1).mpr (Or.inl rfl)) b1) hnw1C_1
  (show orIn n C w1C = C1 from hb1C) (fun u hu => (hf1.2.2.2.1 u hu).symm)
 have hFD1_b := single_opnd_fac_bound hL hLift h4 hne hjunk
  (by have := opnd_lt hL.1 hg1j.1 (1 - b1); omega : w1D < n + g2)
  (hnb_w g1 ((hjunk g1).mpr (Or.inl rfl)) (1 - b1)) hnw1D_1
  (show orIn n C w1D = D1 from hb1D) (fun u hu => (hf1.2.2.2.2.1 u hu).symm)
 have hFC2_b := single_opnd_fac_bound hL hLift h4 hne hjunk
  (opnd_lt hL.1 hg2j.1 b2)
  (hnb_w g2 ((hjunk g2).mpr (Or.inr rfl)) b2) hnw2C_1
  hw2C_eq (fun u hu => (hf2.2.2.2.1 u hu).symm)
 have hFD2_b := single_opnd_fac_bound hL hLift h4 hne hjunk
  (opnd_lt hL.1 hg2j.1 (1 - b2))
  (hnb_w g2 ((hjunk g2).mpr (Or.inr rfl)) (1 - b2)) hnw2D_1
  hw2D_eq (fun u hu => (hf2.2.2.2.2.1 u hu).symm)
 have hMC1_sw : C1.filter (fun u => s(zp1, u) ∈ Ustar G C) = MC1 := by ext u; simp [MC1, Sym2.eq_swap]
 have hMC2_sw : C2.filter (fun u => s(zp2, u) ∈ Ustar G C) = MC2 := by ext u; simp [MC2, Sym2.eq_swap]
 dsimp only at hFC1_b hFD1_b hFC2_b hFD2_b
 rw [hMC1_sw] at hFC1_b; rw [hMC2_sw] at hFC2_b
 have hU1_card : U1.card = MD1.card + (MC1.erase z1).card := by
  have hdisj : Disjoint (MD1.image fun d => s(z1, d)) ((MC1.erase z1).image fun c => s(c, zp1)) := by
   rw [Finset.disjoint_left]; intro e h1 h2
   simp only [Finset.mem_image, Finset.mem_erase] at h1 h2
   rcases h1 with ⟨d, hd, rfl⟩; rcases h2 with ⟨c, ⟨hcz, hc⟩, heq⟩
   rw [Sym2.eq_iff] at heq
   rcases heq with ⟨rfl, rfl⟩ | ⟨_, h2'⟩
   ·exact hcz rfl
   ·exact hcol_ne (congrArg s h2'.symm)
  have hU1_eq : U1 = (MD1.image fun d => s(z1, d)) ∪ ((MC1.erase z1).image fun c => s(c, zp1)) := by
   ext e; simp only [U1, E1, flagEdges, Finset.mem_inter, Finset.mem_union, Finset.mem_image, Finset.mem_erase, MD1, MC1, Finset.mem_filter]
   constructor
   ·rintro ⟨heU, ⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩⟩
    ·exact Or.inl ⟨d, ⟨hd, heU⟩, rfl⟩
    ·by_cases hcz : c = z1
     ·subst hcz; exact Or.inl ⟨zp1, ⟨hf1.2.2.1, heU⟩, rfl⟩
     ·exact Or.inr ⟨c, ⟨hcz, hc, heU⟩, rfl⟩
   ·rintro (⟨d, ⟨hd, heU⟩, rfl⟩ | ⟨c, ⟨_, hc, heU⟩, rfl⟩)
    ·exact ⟨heU, Or.inl ⟨d, hd, rfl⟩⟩
    ·exact ⟨heU, Or.inr ⟨c, hc, rfl⟩⟩
  rw [hU1_eq, Finset.card_union_of_disjoint hdisj,
   Finset.card_image_of_injective _ (fun a b h => by rw [Sym2.eq_iff] at h; rcases h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl),
   Finset.card_image_of_injective _ (fun a b h => by rw [Sym2.eq_iff] at h; rcases h with ⟨rfl, _⟩ | ⟨rfl, rfl⟩ <;> rfl)]
 have hU2_card : U2.card = MD2.card + (MC2.erase z2).card := by
  have hdisj : Disjoint (MD2.image fun d => s(z2, d)) ((MC2.erase z2).image fun c => s(c, zp2)) := by
   rw [Finset.disjoint_left]; intro e h1 h2
   simp only [Finset.mem_image, Finset.mem_erase] at h1 h2
   rcases h1 with ⟨d, hd, rfl⟩; rcases h2 with ⟨c, ⟨hcz, hc⟩, heq⟩
   rw [Sym2.eq_iff] at heq
   rcases heq with ⟨rfl, rfl⟩ | ⟨_, h2'⟩
   ·exact hcz rfl
   ·exact hbip z2 zp2 hf2.1 (congrArg s h2'.symm)
  have hU2_eq : U2 = (MD2.image fun d => s(z2, d)) ∪ ((MC2.erase z2).image fun c => s(c, zp2)) := by
   ext e; simp only [U2, E2, flagEdges, Finset.mem_inter, Finset.mem_union, Finset.mem_image, Finset.mem_erase, MD2, MC2, Finset.mem_filter]
   constructor
   ·rintro ⟨heU, ⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩⟩
    ·exact Or.inl ⟨d, ⟨hd, heU⟩, rfl⟩
    ·by_cases hcz : c = z2
     ·subst hcz; exact Or.inl ⟨zp2, ⟨hf2.2.2.1, heU⟩, rfl⟩
     ·exact Or.inr ⟨c, ⟨hcz, hc, heU⟩, rfl⟩
   ·rintro (⟨d, ⟨hd, heU⟩, rfl⟩ | ⟨c, ⟨_, hc, heU⟩, rfl⟩)
    ·exact ⟨heU, Or.inl ⟨d, hd, rfl⟩⟩
    ·exact ⟨heU, Or.inr ⟨c, hc, rfl⟩⟩
  rw [hU2_eq, Finset.card_union_of_disjoint hdisj,
   Finset.card_image_of_injective _ (fun a b h => by rw [Sym2.eq_iff] at h; rcases h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl),
   Finset.card_image_of_injective _ (fun a b h => by rw [Sym2.eq_iff] at h; rcases h with ⟨rfl, _⟩ | ⟨rfl, rfl⟩ <;> rfl)]
 set loss1 : ℕ := if MC1 = C1 ∧ MD1 = D1 then 1 else 0
 set loss2 : ℕ := if MC2 = C2 ∧ MD2 = D2 then 1 else 0
 have hU1_fac : U1.card ≤ FacC1.card + FacD1.card + loss1 := by
  rw [hU1_card]
  by_cases hzM : z1 ∈ MC1
  ·rw [Finset.card_erase_of_mem hzM]
   have hzpM : zp1 ∈ MD1 := Finset.mem_filter.mpr ⟨hf1.2.2.1, (Finset.mem_filter.mp hzM).2⟩
   have hC1_1 : MC1.card ≤ FacC1.card + 1 := hFC1_b.1 ⟨z1, hzM⟩
   have hD1_1 : MD1.card ≤ FacD1.card + 1 := hFD1_b.1 ⟨zp1, hzpM⟩
   by_cases hfull : MC1 = C1 ∧ MD1 = D1
   ·simp only [loss1, if_pos hfull]; omega
   ·simp only [loss1, if_neg hfull]
    by_cases hCeq : MC1 = C1
    ·have hDne : MD1 ≠ D1 := fun h => hfull ⟨hCeq, h⟩
     have hex : ∃ r ∈ D1, r ∉ MD1 := by by_contra h; push Not at h; exact hDne (Finset.Subset.antisymm (Finset.filter_subset _ _) h)
     have hD1_0 : MD1.card ≤ FacD1.card := hFD1_b.2 hex; omega
    ·have hex : ∃ r ∈ C1, r ∉ MC1 := by by_contra h; push Not at h; exact hCeq (Finset.Subset.antisymm (Finset.filter_subset _ _) h)
     have hC1_0 : MC1.card ≤ FacC1.card := hFC1_b.2 hex; have hpos := Finset.card_pos.mpr ⟨z1, hzM⟩; omega
  ·rw [Finset.erase_eq_of_notMem hzM]
   have hzpM : zp1 ∉ MD1 := fun h => hzM (Finset.mem_filter.mpr ⟨hf1.2.1, (Finset.mem_filter.mp h).2⟩)
   have hC1_0 : MC1.card ≤ FacC1.card := hFC1_b.2 ⟨z1, hf1.2.1, hzM⟩
   have hD1_0 : MD1.card ≤ FacD1.card := hFD1_b.2 ⟨zp1, hf1.2.2.1, hzpM⟩
   omega
 have hU2_fac : U2.card ≤ FacC2.card + FacD2.card + loss2 := by
  rw [hU2_card]
  by_cases hzM : z2 ∈ MC2
  ·rw [Finset.card_erase_of_mem hzM]
   have hzpM : zp2 ∈ MD2 := Finset.mem_filter.mpr ⟨hf2.2.2.1, (Finset.mem_filter.mp hzM).2⟩
   have hC2_1 : MC2.card ≤ FacC2.card + 1 := hFC2_b.1 ⟨z2, hzM⟩
   have hD2_1 : MD2.card ≤ FacD2.card + 1 := hFD2_b.1 ⟨zp2, hzpM⟩
   by_cases hfull : MC2 = C2 ∧ MD2 = D2
   ·simp only [loss2, if_pos hfull]; omega
   ·simp only [loss2, if_neg hfull]
    by_cases hCeq : MC2 = C2
    ·have hDne : MD2 ≠ D2 := fun h => hfull ⟨hCeq, h⟩
     have hex : ∃ r ∈ D2, r ∉ MD2 := by by_contra h; push Not at h; exact hDne (Finset.Subset.antisymm (Finset.filter_subset _ _) h)
     have hD2_0 : MD2.card ≤ FacD2.card := hFD2_b.2 hex; omega
    ·have hex : ∃ r ∈ C2, r ∉ MC2 := by by_contra h; push Not at h; exact hCeq (Finset.Subset.antisymm (Finset.filter_subset _ _) h)
     have hC2_0 : MC2.card ≤ FacC2.card := hFC2_b.2 hex; have hpos := Finset.card_pos.mpr ⟨z2, hzM⟩; omega
  ·rw [Finset.erase_eq_of_notMem hzM]
   have hzpM : zp2 ∉ MD2 := fun h => hzM (Finset.mem_filter.mpr ⟨hf2.2.1, (Finset.mem_filter.mp h).2⟩)
   have hC2_0 : MC2.card ≤ FacC2.card := hFC2_b.2 ⟨z2, hf2.2.1, hzM⟩
   have hD2_0 : MD2.card ≤ FacD2.card := hFD2_b.2 ⟨zp2, hf2.2.2.1, hzpM⟩
   omega
 let isOwn : Fin n → Prop := fun v => ∃ a ∈ tops G C \ centreless G C, topOwner C s z1 g1 g2 a = v
 set MD1_ns := MD1.erase zp1
 set MC1_ns := MC1.erase z1
 set MD2_ns := (D2.erase zp2).filter (fun d => s(z2, d) ∈ U2 \ U1)
 set MC2_ns := (C2.erase z2).filter (fun c => s(c, zp2) ∈ U2 \ U1)
 let e1_to_z1 : Prop := MD1_ns.Nonempty ∨ isOwn z1 ∨ ¬ MC1_ns.Nonempty
 let e2_to_z2 : Prop := MD2_ns.Nonempty ∨ isOwn z2 ∨ ¬ MC2_ns.Nonempty
 let L : Fin n → Finset (Fin n) := fun v =>
  if v = z1 then (if s(z1, zp1) ∈ U1 ∧ e1_to_z1 then insert zp1 MD1_ns else MD1_ns)
  else if v = zp1 then (if s(z1, zp1) ∈ U1 ∧ ¬ e1_to_z1 then insert z1 MC1_ns else MC1_ns)
  else if v = z2 then (if s(z2, zp2) ∈ U2 ∧ e2_to_z2 then insert zp2 MD2_ns else MD2_ns)
  else if v = zp2 then (if s(z2, zp2) ∈ U2 ∧ ¬ e2_to_z2 then insert z2 MC2_ns else MC2_ns)
  else ∅
 have hLz1 : L z1 = if s(z1, zp1) ∈ U1 ∧ e1_to_z1 then insert zp1 MD1_ns else MD1_ns := by simp [L]
 have hLzp1 : L zp1 = if s(z1, zp1) ∈ U1 ∧ ¬ e1_to_z1 then insert z1 MC1_ns else MC1_ns := by simp [L, hz1_zp1.symm]
 have hLz2 : L z2 = if s(z2, zp2) ∈ U2 ∧ e2_to_z2 then insert zp2 MD2_ns else MD2_ns := by simp [L, hz12.symm, hz2_zp1]
 have hLzp2 : L zp2 = if s(z2, zp2) ∈ U2 ∧ ¬ e2_to_z2 then insert z2 MC2_ns else MC2_ns := by simp [L, hz1_zp2.symm, hzp12.symm, hz2_zp2.symm]
 have hZ4_card : ({z1, zp1, z2, zp2} : Finset (Fin n)).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hz1_zp1, hz12, hz1_zp2]),
   Finset.card_insert_of_notMem (by simp [hz2_zp1.symm, hzp12]), Finset.card_pair hz2_zp2]
 set Zact := ({z1, zp1, z2, zp2} : Finset (Fin n)).filter (fun v => (L v).Nonempty)
 set Zhas := Zact.filter isOwn
 set Znew := Zact \ Zhas
 have he2_nU1 : s(z2, zp2) ∉ U1 := by
  intro h
  have hE1 := (Finset.mem_inter.mp h).2
  simp only [E1, flagEdges, Finset.mem_union, Finset.mem_image, Sym2.eq_iff] at hE1
  rcases hE1 with ⟨d, hd, ⟨h1, _⟩ | ⟨h1, _⟩⟩ | ⟨c, hc, ⟨_, h2⟩ | ⟨h1, _⟩⟩
  ·exact hz12 h1
  ·exact hcol_ne (by rw [h1, ← hszp])
  ·exact hzp12 h2
  ·exact hcol_ne ((flag_color_C hbip hf1 hc).symm.trans (by rw [h1]; exact hszp.symm))
 have hcov : ∀ e ∈ Ustar G C, ∃ v ∈ Zact, ∃ u ∈ L v, e = s(v, u) := by
  intro e he
  rw [hUstar_eq, Finset.mem_union] at he
  by_cases he1 : e ∈ U1
  ·have hE1 := (Finset.mem_inter.mp he1).2
   have heU := (Finset.mem_inter.mp he1).1
   simp only [E1, flagEdges, Finset.mem_union, Finset.mem_image] at hE1
   rcases hE1 with ⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩
   ·by_cases hdzp : d = zp1
    ·rw [hdzp] at he1 ⊢
     by_cases hdir : e1_to_z1
     ·refine ⟨z1, Finset.mem_filter.mpr ⟨by simp, ⟨zp1, by rw [hLz1, if_pos ⟨he1, hdir⟩]; simp⟩⟩,
       zp1, by rw [hLz1, if_pos ⟨he1, hdir⟩]; simp, rfl⟩
     ·refine ⟨zp1, Finset.mem_filter.mpr ⟨by simp, ⟨z1, by rw [hLzp1, if_pos ⟨he1, hdir⟩]; simp⟩⟩,
       z1, by rw [hLzp1, if_pos ⟨he1, hdir⟩]; simp, Sym2.eq_swap⟩
    ·have hd_ns : d ∈ MD1_ns := Finset.mem_erase.mpr ⟨hdzp, Finset.mem_filter.mpr ⟨hd, heU⟩⟩
     have hdL : d ∈ L z1 := by rw [hLz1]; split_ifs; exact Finset.mem_insert_of_mem hd_ns; exact hd_ns
     exact ⟨z1, Finset.mem_filter.mpr ⟨by simp, ⟨d, hdL⟩⟩, d, hdL, rfl⟩
   ·by_cases hcz : c = z1
    ·rw [hcz] at he1 ⊢
     by_cases hdir : e1_to_z1
     ·refine ⟨z1, Finset.mem_filter.mpr ⟨by simp, ⟨zp1, by rw [hLz1, if_pos ⟨he1, hdir⟩]; simp⟩⟩,
       zp1, by rw [hLz1, if_pos ⟨he1, hdir⟩]; simp, rfl⟩
     ·refine ⟨zp1, Finset.mem_filter.mpr ⟨by simp, ⟨z1, by rw [hLzp1, if_pos ⟨he1, hdir⟩]; simp⟩⟩,
       z1, by rw [hLzp1, if_pos ⟨he1, hdir⟩]; simp, Sym2.eq_swap⟩
    ·have hc_ns : c ∈ MC1_ns := Finset.mem_erase.mpr ⟨hcz, Finset.mem_filter.mpr ⟨hc, heU⟩⟩
     have hcL : c ∈ L zp1 := by rw [hLzp1]; split_ifs; exact Finset.mem_insert_of_mem hc_ns; exact hc_ns
     exact ⟨zp1, Finset.mem_filter.mpr ⟨by simp, ⟨c, hcL⟩⟩, c, hcL, Sym2.eq_swap⟩
  ·have he2 : e ∈ U2 := he.resolve_left he1
   have he2d : e ∈ U2 \ U1 := Finset.mem_sdiff.mpr ⟨he2, he1⟩
   have hE2 := (Finset.mem_inter.mp he2).2
   simp only [E2, flagEdges, Finset.mem_union, Finset.mem_image] at hE2
   rcases hE2 with ⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩
   ·by_cases hdzp : d = zp2
    ·rw [hdzp] at he2 ⊢
     by_cases hdir : e2_to_z2
     ·refine ⟨z2, Finset.mem_filter.mpr ⟨by simp, ⟨zp2, by rw [hLz2, if_pos ⟨he2, hdir⟩]; simp⟩⟩,
       zp2, by rw [hLz2, if_pos ⟨he2, hdir⟩]; simp, rfl⟩
     ·refine ⟨zp2, Finset.mem_filter.mpr ⟨by simp, ⟨z2, by rw [hLzp2, if_pos ⟨he2, hdir⟩]; simp⟩⟩,
       z2, by rw [hLzp2, if_pos ⟨he2, hdir⟩]; simp, Sym2.eq_swap⟩
    ·have hd_ns : d ∈ MD2_ns := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hdzp, hd⟩, he2d⟩
     have hdL : d ∈ L z2 := by rw [hLz2]; split_ifs; exact Finset.mem_insert_of_mem hd_ns; exact hd_ns
     exact ⟨z2, Finset.mem_filter.mpr ⟨by simp, ⟨d, hdL⟩⟩, d, hdL, rfl⟩
   ·by_cases hcz : c = z2
    ·rw [hcz] at he2 ⊢
     by_cases hdir : e2_to_z2
     ·refine ⟨z2, Finset.mem_filter.mpr ⟨by simp, ⟨zp2, by rw [hLz2, if_pos ⟨he2, hdir⟩]; simp⟩⟩,
       zp2, by rw [hLz2, if_pos ⟨he2, hdir⟩]; simp, rfl⟩
     ·refine ⟨zp2, Finset.mem_filter.mpr ⟨by simp, ⟨z2, by rw [hLzp2, if_pos ⟨he2, hdir⟩]; simp⟩⟩,
       z2, by rw [hLzp2, if_pos ⟨he2, hdir⟩]; simp, Sym2.eq_swap⟩
    ·have hc_ns : c ∈ MC2_ns := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hcz, hc⟩, he2d⟩
     have hcL : c ∈ L zp2 := by rw [hLzp2]; split_ifs; exact Finset.mem_insert_of_mem hc_ns; exact hc_ns
     exact ⟨zp2, Finset.mem_filter.mpr ⟨by simp, ⟨c, hcL⟩⟩, c, hcL, Sym2.eq_swap⟩
 have hsum1 : (L z1).card + (L zp1).card = U1.card := by
  rw [hU1_card, hLz1, hLzp1]
  have hzp_n : zp1 ∉ MD1_ns := Finset.notMem_erase _ _
  have hz_n : z1 ∉ MC1_ns := Finset.notMem_erase _ _
  by_cases he1 : s(z1, zp1) ∈ U1
  ·have hzpM : zp1 ∈ MD1 := Finset.mem_filter.mpr ⟨hf1.2.2.1, (Finset.mem_inter.mp he1).1⟩
   have hMD1_er : MD1_ns.card + 1 = MD1.card := by
    rw [Finset.card_erase_of_mem hzpM]; have := Finset.card_pos.mpr ⟨zp1, hzpM⟩; omega
   by_cases hdir : e1_to_z1 <;> simp [he1, hdir, hzp_n, hz_n] <;> omega
  ·have hzpM : zp1 ∉ MD1 := fun h => he1 (Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp h).2,
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hf1.2.2.1)⟩)
   have hMD1_er : MD1_ns = MD1 := Finset.erase_eq_of_notMem hzpM
   simp [he1, hMD1_er]
 have hsum2 : (L z2).card + (L zp2).card = (U2 \ U1).card := by
  have hU2d_eq : U2 \ U1 = (MD2_ns.image fun d => s(z2, d)) ∪ (MC2_ns.image fun c => s(c, zp2)) ∪
    (if s(z2, zp2) ∈ U2 then {s(z2, zp2)} else ∅) := by
   ext e; simp only [Finset.mem_union, Finset.mem_image, MD2_ns, MC2_ns, Finset.mem_filter, Finset.mem_erase]
   constructor
   ·intro he
    have he2 := (Finset.mem_sdiff.mp he).1
    have hE2 := (Finset.mem_inter.mp he2).2
    simp only [E2, flagEdges, Finset.mem_union, Finset.mem_image] at hE2
    rcases hE2 with ⟨d, hd, rfl⟩ | ⟨c, hc, rfl⟩
    ·by_cases hdzp : d = zp2
     ·subst hdzp; right; rw [if_pos he2]; exact Finset.mem_singleton_self _
     ·left; left; exact ⟨d, ⟨⟨hdzp, hd⟩, he⟩, rfl⟩
    ·by_cases hcz : c = z2
     ·subst hcz; right; rw [if_pos he2]; exact Finset.mem_singleton_self _
     ·left; right; exact ⟨c, ⟨⟨hcz, hc⟩, he⟩, rfl⟩
   ·rintro ((⟨d, ⟨_, he⟩, rfl⟩ | ⟨c, ⟨_, he⟩, rfl⟩) | hsp)
    ·exact he
    ·exact he
    ·split_ifs at hsp with he2
     ·rw [Finset.mem_singleton] at hsp; subst hsp; exact Finset.mem_sdiff.mpr ⟨he2, he2_nU1⟩
     ·exact absurd hsp (Finset.notMem_empty _)
  have hd12 : Disjoint (MD2_ns.image fun d => s(z2, d)) (MC2_ns.image fun c => s(c, zp2)) := by
   rw [Finset.disjoint_left]; intro e h1 h2
   simp only [Finset.mem_image, MD2_ns, MC2_ns, Finset.mem_filter, Finset.mem_erase] at h1 h2
   rcases h1 with ⟨d, ⟨⟨hdzp, hd⟩, _⟩, rfl⟩; rcases h2 with ⟨c, ⟨⟨hcz, hc⟩, _⟩, heq⟩
   rw [Sym2.eq_iff] at heq
   rcases heq with ⟨rfl, rfl⟩ | ⟨_, h2'⟩
   ·exact hcz rfl
   ·exact hbip z2 zp2 hf2.1 (congrArg s h2'.symm)
  have hd3 : Disjoint ((MD2_ns.image fun d => s(z2, d)) ∪ (MC2_ns.image fun c => s(c, zp2)))
    (if s(z2, zp2) ∈ U2 then {s(z2, zp2)} else ∅) := by
   rw [Finset.disjoint_right]; intro e he hU
   split_ifs at he with he2
   ·rw [Finset.mem_singleton] at he; subst he
    simp only [Finset.mem_union, Finset.mem_image, MD2_ns, MC2_ns, Finset.mem_filter, Finset.mem_erase, Sym2.eq_iff] at hU
    rcases hU with ⟨d, ⟨⟨hdzp, _⟩, _⟩, ⟨_, h⟩ | ⟨h, _⟩⟩ | ⟨c, ⟨⟨hcz, _⟩, _⟩, ⟨h, _⟩ | ⟨_, h⟩⟩
    ·exact hdzp h
    ·exact hz2_zp2 h
    ·exact hcz h
    ·exact hz2_zp2 h.symm
   ·exact absurd he (Finset.notMem_empty _)
  have hU2d_card : (U2 \ U1).card = MD2_ns.card + MC2_ns.card + (if s(z2, zp2) ∈ U2 then 1 else 0) := by
   rw [hU2d_eq, Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd12,
    Finset.card_image_of_injective _ (fun a b h => by rw [Sym2.eq_iff] at h; rcases h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl),
    Finset.card_image_of_injective _ (fun a b h => by rw [Sym2.eq_iff] at h; rcases h with ⟨rfl, _⟩ | ⟨rfl, rfl⟩ <;> rfl)]
   split_ifs <;> simp
  rw [hU2d_card, hLz2, hLzp2]
  have hzp_n : zp2 ∉ MD2_ns := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
  have hz_n : z2 ∉ MC2_ns := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
  by_cases he2 : s(z2, zp2) ∈ U2 <;> by_cases hdir : e2_to_z2 <;>
   simp [he2, hdir, hzp_n, hz_n] <;> omega
 have hsum_L : (∑ v ∈ Zact, (L v).card) ≤ (Ustar G C).card := by
  have hle1 : ∑ v ∈ Zact, (L v).card ≤ ∑ v ∈ ({z1, zp1, z2, zp2} : Finset (Fin n)), (L v).card :=
   Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hsum4 : ∑ v ∈ ({z1, zp1, z2, zp2} : Finset (Fin n)), (L v).card =
    (L z1).card + (L zp1).card + (L z2).card + (L zp2).card := by
   rw [Finset.sum_insert (by simp [hz1_zp1, hz12, hz1_zp2]),
    Finset.sum_insert (by simp [hz2_zp1.symm, hzp12]), Finset.sum_pair hz2_zp2]; omega
  have hUcard : (Ustar G C).card = U1.card + (U2 \ U1).card := by
   have hdisj : Disjoint U1 (U2 \ U1) := Finset.disjoint_sdiff
   rw [show Ustar G C = U1 ∪ (U2 \ U1) by rw [hUstar_eq, Finset.union_sdiff_self_eq_union],
    Finset.card_union_of_disjoint hdisj]
  omega
 let topOf : Fin n → ℕ := fun v => if h : isOwn v then Classical.choose h else 0
 have hsurg := master_surgery_bound hL hLift h4 hg12 hjunk hne Zact Zhas L topOf
  (Finset.filter_subset _ _)
  (fun v hv => (Finset.mem_filter.mp hv).2)
  (fun v hv u hu => by
   have hv' := (Finset.mem_filter.mp hv).1
   simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
   rcases hv' with rfl | rfl | rfl | rfl
   ·rw [hLz1] at hu; split_ifs at hu
    ·rcases Finset.mem_insert.mp hu with rfl | hu
     ·exact hf1.1
     ·exact (hf1.2.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm
    ·exact (hf1.2.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm
   ·rw [hLzp1] at hu; split_ifs at hu
    ·rcases Finset.mem_insert.mp hu with rfl | hu
     ·exact hf1.1.symm
     ·exact (hf1.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm
    ·exact (hf1.2.2.2.1 u (Finset.mem_filter.mp (Finset.mem_of_mem_erase hu)).1).symm
   ·rw [hLz2] at hu; split_ifs at hu
    ·rcases Finset.mem_insert.mp hu with rfl | hu
     ·exact hf2.1
     ·exact (hf2.2.2.2.2.1 u (Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1)).symm
    ·exact (hf2.2.2.2.2.1 u (Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1)).symm
   ·rw [hLzp2] at hu; split_ifs at hu
    ·rcases Finset.mem_insert.mp hu with rfl | hu
     ·exact hf2.1.symm
     ·exact (hf2.2.2.2.1 u (Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1)).symm
    ·exact (hf2.2.2.2.1 u (Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1)).symm)
  hcov
  (fun v hv => by have h := (Finset.mem_filter.mp hv).2; simp only [topOf, dif_pos h]; exact (Classical.choose_spec h).1)
  (fun v hv => by
   have h := (Finset.mem_filter.mp hv).2; simp only [topOf, dif_pos h]
   have hsp := Classical.choose_spec h
   have hside := topOwner_side hL.1 h4 s z1 g1 g2 hsp.1
   rwa [hsp.2] at hside)
  (fun v1 hv1 v2 hv2 heq => by
   have h1 := (Finset.mem_filter.mp hv1).2; have h2 := (Finset.mem_filter.mp hv2).2
   simp only [topOf, dif_pos h1, dif_pos h2] at heq
   have hsp1 := Classical.choose_spec h1; have hsp2 := Classical.choose_spec h2
   rw [← hsp1.2, heq, hsp2.2])
 have hU_inc_exc : (Ustar G C).card + U12.card = U1.card + U2.card := by
  rw [hUstar_eq]; exact Finset.card_union_add_card_inter U1 U2
 have hbase : 2 * (centreless G C).card + Extra.card + U12.card + 2 ≤ Znew.card + loss1 + loss2 := by
  have hsurg' : 2 * (centreless G C).card + (orN G C \ lam G C).card + 2 ≤
    (∑ v ∈ Zact, (L v).card) + Znew.card := hsurg
  omega
 let A1_edge : Fin n → Prop := fun v =>
  (v = z1 ∧ ∃ d ∈ D1.erase zp1, s(z1, d) ∈ U1 \ E2) ∨
  (v = zp1 ∧ ∃ c ∈ C1.erase z1, s(c, zp1) ∈ U1 \ E2)
 let A2_edge : Fin n → Prop := fun v =>
  (v = z2 ∧ ∃ d ∈ D2.erase zp2, s(z2, d) ∈ U2 \ E1) ∨
  (v = zp2 ∧ ∃ c ∈ C2.erase z2, s(c, zp2) ∈ U2 \ E1)
 set A1 := (Znew ∩ {z1, zp1}).filter (fun v =>
  A1_edge v ∧ ∃ a ∈ centreless G C, ∃ b : Fin 2, side (n := n) C a b = ∅ ∧ OrReaches n C (opnd C a b) g1 ∧ v ∈ side (n := n) C a (1 - b))
 set A2 := (Znew ∩ {z2, zp2}).filter (fun v =>
  A2_edge v ∧ ∃ a ∈ centreless G C, ∃ b : Fin 2, side (n := n) C a b = ∅ ∧ OrReaches n C (opnd C a b) g2 ∧ v ∈ side (n := n) C a (1 - b))
 set Zconf := (Znew \ (A1 ∪ A2)).filter (fun v =>
  s v = s zp1 ∧ ∃ mv ∈ Extra, orIn n C (n + mv) = {v} ∧
   ∃ u' : Fin n, s u' = s z1 ∧ ∃ mu ∈ Extra, orIn n C (n + mu) = {u'})
 have hgold_1 : ∀ v ∈ Znew ∩ {z1, zp1}, A1_edge v → v ∈ A1 ∨ v ∈ Zconf := by
  intro v hv hedge
  have hv_new : v ∈ Znew := (Finset.mem_inter.mp hv).1
  have hv_nown : ¬ isOwn v := fun ho => (Finset.mem_sdiff.mp hv_new).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv_new).1, ho⟩)
  rcases hedge with ⟨hv_eq, d, hd, hzd⟩ | ⟨hv_eq, c, hc, hczp⟩
  ·rw [hv_eq] at hv hv_new hv_nown ⊢
   have hdzp : d ≠ zp1 := (Finset.mem_erase.mp hd).1
   have hdD1 : d ∈ D1 := Finset.mem_of_mem_erase hd
   have hzdU : s(z1, d) ∈ Ustar G C := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hzd).1).1
   have hzd_nE2 : s(z1, d) ∉ E2 := (Finset.mem_sdiff.mp hzd).2
   have hg2f : gateVal n C g2 (pairInput z1 d) = false := by
    rw [Bool.eq_false_iff, ne_eq, flag_pair_edge_iff hbip h4 hf2 (hf1.2.2.2.2.1 d hdD1).symm]; exact hzd_nE2
   have hnw :
     (gateVal n C g1 (pairInput z1 d) = true →
      (¬ ∀ x, gateVal n C g1 x = true → x d = true → graphFun G ∅ x = true) ∧
      (∀ w : Fin n, s w = s z1 → (∀ x, gateVal n C g1 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w d)) ∧
     (gateVal n C g2 (pairInput z1 d) = true →
      (¬ ∀ x, gateVal n C g2 x = true → x d = true → graphFun G ∅ x = true) ∧
      (∀ w : Fin n, s w = s z1 → (∀ x, gateVal n C g2 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w d)) :=
    ⟨fun _ => ⟨flag_wmax_not_D_other h4 hf1 hdD1 hdzp, fun w hsw hw => flag_wmax_adj_D hbip h4 hf1 hw hsw hdD1 hdzp⟩,
     fun h2 => (by rw [hg2f] at h2; cases h2)⟩
   rcases golden_edge_cover hbip h4 hL hLift hjunk hf1 hf2 hsz hszp hzdU hnw
     (fun h => by rw [hg2f] at h; cases h.2.1) with
    hA | ⟨a, haC, b, g, hg, hgv, hemp, hrb, hzs⟩ | ⟨hcol, _⟩
   ·exact absurd hA hv_nown
   ·have hgeq : g = g1 := hg.resolve_right (fun h => by rw [h, hg2f] at hgv; cases hgv)
    rw [hgeq] at hrb
    exact Or.inl (Finset.mem_filter.mpr ⟨hv, Or.inl ⟨rfl, d, hd, hzd⟩, a, haC, b, hemp, hrb, hzs⟩)
   ·exact absurd hcol hcol_ne
  ·rw [hv_eq] at hv hv_new hv_nown ⊢
   have hcz1 : c ≠ z1 := (Finset.mem_erase.mp hc).1
   have hcC1 : c ∈ C1 := Finset.mem_of_mem_erase hc
   have hczpU : s(zp1, c) ∈ Ustar G C := by rw [Sym2.eq_swap]; exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hczp).1).1
   have hczp_nE2 : s(zp1, c) ∉ E2 := by rw [Sym2.eq_swap]; exact (Finset.mem_sdiff.mp hczp).2
   have hg2f : gateVal n C g2 (pairInput zp1 c) = false := by
    rw [Bool.eq_false_iff, ne_eq, flag_pair_edge_iff hbip h4 hf2 (hf1.2.2.2.1 c hcC1).symm]; exact hczp_nE2
   have hnw :
     (gateVal n C g1 (pairInput zp1 c) = true →
      (¬ ∀ x, gateVal n C g1 x = true → x c = true → graphFun G ∅ x = true) ∧
      (∀ w : Fin n, s w = s zp1 → (∀ x, gateVal n C g1 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w c)) ∧
     (gateVal n C g2 (pairInput zp1 c) = true →
      (¬ ∀ x, gateVal n C g2 x = true → x c = true → graphFun G ∅ x = true) ∧
      (∀ w : Fin n, s w = s zp1 → (∀ x, gateVal n C g2 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w c)) :=
    ⟨fun _ => ⟨flag_wmax_not_C_other h4 hf1 hcC1 hcz1, fun w hsw hw => flag_wmax_adj_C hbip h4 hf1 hw hsw hcC1 hcz1⟩,
     fun h2 => (by rw [hg2f] at h2; cases h2)⟩
   rcases golden_edge_cover hbip h4 hL hLift hjunk hf1 hf2 hsz hszp hczpU hnw
     (fun h => by rw [hg2f] at h; cases h.2.1) with
    hA | ⟨a, haC, b, g, hg, hgv, hemp, hrb, hzs⟩ | ⟨hsv, _, _, _, g, hg, hgv, _, _, g', hg', _, _, mv, hmv, hmv_g', hmv_orIn, u', _, hsu', mu, hmu, hmu_g, hmu_orIn⟩
   ·exact absurd hA hv_nown
   ·have hgeq : g = g1 := hg.resolve_right (fun h => by rw [h, hg2f] at hgv; cases hgv)
    rw [hgeq] at hrb
    exact Or.inl (Finset.mem_filter.mpr ⟨hv, Or.inr ⟨rfl, c, hc, hczp⟩, a, haC, b, hemp, hrb, hzs⟩)
   ·by_cases hA1 : zp1 ∈ A1
    ·exact Or.inl hA1
    ·right
     have hnA2 : zp1 ∉ A2 := fun h => by
      have := (Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      exact this.elim hz2_zp1.symm hzp12
     have hmv_E : mv ∈ Extra := hExtra_of_reach mv hmv (hg'.imp (fun h => by rwa [← h]) (fun h => by rwa [← h]))
     have hmu_E : mu ∈ Extra := hExtra_of_reach mu hmu (hg.imp (fun h => by rwa [← h]) (fun h => by rwa [← h]))
     exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hv_new, fun h => (Finset.mem_union.mp h).elim hA1 hnA2⟩,
      hsv, mv, hmv_E, hmv_orIn, u', hsu', mu, hmu_E, hmu_orIn⟩
 have hgold_2 : ∀ v ∈ Znew ∩ {z2, zp2}, A2_edge v → v ∈ A2 ∨ v ∈ Zconf := by
  intro v hv hedge
  have hv_new : v ∈ Znew := (Finset.mem_inter.mp hv).1
  have hv_nown : ¬ isOwn v := fun ho => (Finset.mem_sdiff.mp hv_new).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv_new).1, ho⟩)
  rcases hedge with ⟨hv_eq, d, hd, hzd⟩ | ⟨hv_eq, c, hc, hczp⟩
  ·rw [hv_eq] at hv hv_new hv_nown ⊢
   have hdzp : d ≠ zp2 := (Finset.mem_erase.mp hd).1
   have hdD2 : d ∈ D2 := Finset.mem_of_mem_erase hd
   have hzdU : s(z2, d) ∈ Ustar G C := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hzd).1).1
   have hzd_nE1 : s(z2, d) ∉ E1 := (Finset.mem_sdiff.mp hzd).2
   have hg1f : gateVal n C g1 (pairInput z2 d) = false := by
    rw [Bool.eq_false_iff, ne_eq, flag_pair_edge_iff hbip h4 hf1 (hf2.2.2.2.2.1 d hdD2).symm]; exact hzd_nE1
   have hnw :
     (gateVal n C g1 (pairInput z2 d) = true →
      (¬ ∀ x, gateVal n C g1 x = true → x d = true → graphFun G ∅ x = true) ∧
      (∀ w : Fin n, s w = s z2 → (∀ x, gateVal n C g1 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w d)) ∧
     (gateVal n C g2 (pairInput z2 d) = true →
      (¬ ∀ x, gateVal n C g2 x = true → x d = true → graphFun G ∅ x = true) ∧
      (∀ w : Fin n, s w = s z2 → (∀ x, gateVal n C g2 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w d)) :=
    ⟨fun h1 => (by rw [hg1f] at h1; cases h1),
     fun _ => ⟨flag_wmax_not_D_other h4 hf2 hdD2 hdzp, fun w hsw hw => flag_wmax_adj_D hbip h4 hf2 hw hsw hdD2 hdzp⟩⟩
   rcases golden_edge_cover hbip h4 hL hLift hjunk hf1 hf2 hsz hszp hzdU hnw
     (fun h => by rw [hg1f] at h; cases h.1) with
    hA | ⟨a, haC, b, g, hg, hgv, hemp, hrb, hzs⟩ | ⟨hcol, _⟩
   ·exact absurd hA hv_nown
   ·have hgeq : g = g2 := hg.resolve_left (fun h => by rw [h, hg1f] at hgv; cases hgv)
    rw [hgeq] at hrb
    exact Or.inl (Finset.mem_filter.mpr ⟨hv, Or.inl ⟨rfl, d, hd, hzd⟩, a, haC, b, hemp, hrb, hzs⟩)
   ·exact absurd (hsz.trans hcol) hcol_ne
  ·rw [hv_eq] at hv hv_new hv_nown ⊢
   have hcz2 : c ≠ z2 := (Finset.mem_erase.mp hc).1
   have hcC2 : c ∈ C2 := Finset.mem_of_mem_erase hc
   have hczpU : s(zp2, c) ∈ Ustar G C := by rw [Sym2.eq_swap]; exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hczp).1).1
   have hczp_nE1 : s(zp2, c) ∉ E1 := by rw [Sym2.eq_swap]; exact (Finset.mem_sdiff.mp hczp).2
   have hg1f : gateVal n C g1 (pairInput zp2 c) = false := by
    rw [Bool.eq_false_iff, ne_eq, flag_pair_edge_iff hbip h4 hf1 (hf2.2.2.2.1 c hcC2).symm]; exact hczp_nE1
   have hnw :
     (gateVal n C g1 (pairInput zp2 c) = true →
      (¬ ∀ x, gateVal n C g1 x = true → x c = true → graphFun G ∅ x = true) ∧
      (∀ w : Fin n, s w = s zp2 → (∀ x, gateVal n C g1 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w c)) ∧
     (gateVal n C g2 (pairInput zp2 c) = true →
      (¬ ∀ x, gateVal n C g2 x = true → x c = true → graphFun G ∅ x = true) ∧
      (∀ w : Fin n, s w = s zp2 → (∀ x, gateVal n C g2 x = true → x w = true → graphFun G ∅ x = true) → G.Adj w c)) :=
    ⟨fun h1 => (by rw [hg1f] at h1; cases h1),
     fun _ => ⟨flag_wmax_not_C_other h4 hf2 hcC2 hcz2, fun w hsw hw => flag_wmax_adj_C hbip h4 hf2 hw hsw hcC2 hcz2⟩⟩
   rcases golden_edge_cover hbip h4 hL hLift hjunk hf1 hf2 hsz hszp hczpU hnw
     (fun h => by rw [hg1f] at h; cases h.1) with
    hA | ⟨a, haC, b, g, hg, hgv, hemp, hrb, hzs⟩ | ⟨hsv, _, _, _, g, hg, hgv, _, _, g', hg', _, _, mv, hmv, hmv_g', hmv_orIn, u', _, hsu', mu, hmu, hmu_g, hmu_orIn⟩
   ·exact absurd hA hv_nown
   ·have hgeq : g = g2 := hg.resolve_left (fun h => by rw [h, hg1f] at hgv; cases hgv)
    rw [hgeq] at hrb
    exact Or.inl (Finset.mem_filter.mpr ⟨hv, Or.inr ⟨rfl, c, hc, hczp⟩, a, haC, b, hemp, hrb, hzs⟩)
   ·by_cases hA2 : zp2 ∈ A2
    ·exact Or.inl hA2
    ·right
     have hnA1 : zp2 ∉ A1 := fun h => by
      have := (Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      exact this.elim hz1_zp2.symm hzp12.symm
     have hmv_E : mv ∈ Extra := hExtra_of_reach mv hmv (hg'.imp (fun h => by rwa [← h]) (fun h => by rwa [← h]))
     have hmu_E : mu ∈ Extra := hExtra_of_reach mu hmu (hg.imp (fun h => by rwa [← h]) (fun h => by rwa [← h]))
     exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hv_new, fun h => (Finset.mem_union.mp h).elim hnA1 hA2⟩,
      hsv, mv, hmv_E, hmv_orIn, u', hsu', mu, hmu_E, hmu_orIn⟩
 have h1_bound : (Znew ∩ {z1, zp1}).card + loss1 ≤ A1.card + (Zconf ∩ {zp1}).card + 1 + U12.card := by
  have hsub1 : A1 ∪ (Zconf ∩ {zp1}) ⊆ Znew ∩ {z1, zp1} := by
   refine Finset.union_subset (Finset.filter_subset _ _) ?_
   intro v hv; have h1 := (Finset.mem_inter.mp hv).1; have h2 := (Finset.mem_inter.mp hv).2
   rw [Finset.mem_singleton] at h2; subst h2
   exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_filter.mp h1).1).1, by simp⟩
  have hdisj1 : Disjoint A1 (Zconf ∩ {zp1}) := by
   rw [Finset.disjoint_left]; intro v hv1 hv2
   exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hv2).1).1).2 (Finset.mem_union_left _ hv1)
  have hcard_U : (A1 ∪ (Zconf ∩ {zp1})).card = A1.card + (Zconf ∩ {zp1}).card :=
   Finset.card_union_of_disjoint hdisj1
  have h_z1_in : z1 ∈ Znew → (∃ d ∈ MD1_ns, s(z1, d) ∉ E2) → z1 ∈ A1 ∪ (Zconf ∩ {zp1}) := by
   intro hz1n ⟨d, hd, hne2⟩
   have hd_er := Finset.mem_erase.mp hd
   have hd_f := Finset.mem_filter.mp hd_er.2
   have hU1 : s(z1, d) ∈ U1 := Finset.mem_inter.mpr ⟨hd_f.2, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hd_f.1)⟩
   rcases hgold_1 z1 (Finset.mem_inter.mpr ⟨hz1n, by simp⟩)
     (Or.inl ⟨rfl, d, Finset.mem_erase.mpr ⟨hd_er.1, hd_f.1⟩, Finset.mem_sdiff.mpr ⟨hU1, hne2⟩⟩) with hA | hC
   ·exact Finset.mem_union_left _ hA
   ·exact absurd (Finset.mem_filter.mp hC).2.1 hcol_ne
  have h_zp1_in : zp1 ∈ Znew → (∃ c ∈ MC1_ns, s(c, zp1) ∉ E2) → zp1 ∈ A1 ∪ (Zconf ∩ {zp1}) := by
   intro hzp1n ⟨c, hc, hne2⟩
   have hc_er := Finset.mem_erase.mp hc
   have hc_f := Finset.mem_filter.mp hc_er.2
   have hU1 : s(c, zp1) ∈ U1 := Finset.mem_inter.mpr ⟨hc_f.2, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc_f.1)⟩
   rcases hgold_1 zp1 (Finset.mem_inter.mpr ⟨hzp1n, by simp⟩)
     (Or.inr ⟨rfl, c, Finset.mem_erase.mpr ⟨hc_er.1, hc_f.1⟩, Finset.mem_sdiff.mpr ⟨hU1, hne2⟩⟩) with hA | hC
   ·exact Finset.mem_union_left _ hA
   ·exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hC, by simp⟩)
  have hrem : ((Znew ∩ {z1, zp1}) \ (A1 ∪ (Zconf ∩ {zp1}))).card + loss1 ≤ 1 + U12.card := by
   set R := (Znew ∩ {z1, zp1}) \ (A1 ∪ (Zconf ∩ {zp1}))
   have hRsub : R ⊆ {z1, zp1} := Finset.Subset.trans Finset.sdiff_subset Finset.inter_subset_right
   have hRle2 : R.card ≤ 2 := (Finset.card_le_card hRsub).trans (by rw [Finset.card_pair hz1_zp1])
   have hz1_R_no_edge : z1 ∈ R → ∀ d ∈ MD1_ns, s(z1, d) ∈ U12 := by
    intro hR d hd
    have hd_f := Finset.mem_filter.mp (Finset.mem_of_mem_erase hd)
    have hU1 : s(z1, d) ∈ U1 := Finset.mem_inter.mpr ⟨hd_f.2, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hd_f.1)⟩
    by_contra hnu
    have hne2 : s(z1, d) ∉ E2 := fun h => hnu (Finset.mem_inter.mpr ⟨hU1, Finset.mem_inter.mpr ⟨hd_f.2, h⟩⟩)
    exact (Finset.mem_sdiff.mp hR).2 (h_z1_in (Finset.mem_inter.mp (Finset.mem_sdiff.mp hR).1).1 ⟨d, hd, hne2⟩)
   have hzp1_R_no_edge : zp1 ∈ R → ∀ c ∈ MC1_ns, s(c, zp1) ∈ U12 := by
    intro hR c hc
    have hc_f := Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)
    have hU1 : s(c, zp1) ∈ U1 := Finset.mem_inter.mpr ⟨hc_f.2, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc_f.1)⟩
    by_contra hnu
    have hne2 : s(c, zp1) ∉ E2 := fun h => hnu (Finset.mem_inter.mpr ⟨hU1, Finset.mem_inter.mpr ⟨hc_f.2, h⟩⟩)
    exact (Finset.mem_sdiff.mp hR).2 (h_zp1_in (Finset.mem_inter.mp (Finset.mem_sdiff.mp hR).1).1 ⟨c, hc, hne2⟩)
   have hzp1_ne_ns : zp1 ∈ Znew → MC1_ns.Nonempty := by
    intro hzp1n
    have hLne : (L zp1).Nonempty := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzp1n).1).2
    by_contra hemp
    have hdir : e1_to_z1 := Or.inr (Or.inr hemp)
    rw [hLzp1, if_neg (fun h => h.2 hdir)] at hLne
    exact hemp hLne
   have hnot_both_R : ¬ (z1 ∈ R ∧ zp1 ∈ R) := by
    rintro ⟨hz1R, hzp1R⟩
    have hzp1n : zp1 ∈ Znew := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hzp1R).1).1
    have hz1n : z1 ∈ Znew := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hz1R).1).1
    obtain ⟨c, hc⟩ := hzp1_ne_ns hzp1n
    have hMD1_ne : MD1_ns.Nonempty := by
     have hLne : (L z1).Nonempty := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz1n).1).2
     by_contra hemp
     have hnown : ¬ isOwn z1 := fun ho => (Finset.mem_sdiff.mp hz1n).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz1n).1, ho⟩)
     have hndir : ¬ e1_to_z1 := fun h => h.elim hemp (fun h => h.elim hnown (fun h => h ⟨c, hc⟩))
     rw [hLz1, if_neg (fun h => hndir h.2)] at hLne
     exact hemp hLne
    obtain ⟨d, hd⟩ := hMD1_ne
    have he1 := hz1_R_no_edge hz1R d hd
    have he2 := hzp1_R_no_edge hzp1R c hc
    have hne_e : s(z1, d) ≠ s(c, zp1) := by
     intro heq; rw [Sym2.eq_iff] at heq
     rcases heq with ⟨rfl, _⟩ | ⟨_, h2'⟩
     ·exact (Finset.mem_erase.mp hc).1 rfl
     ·exact hcol_ne ((flag_color_C hbip hf1 (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)).1).symm.trans
       (by rw [← h2']; exact flag_color_D hbip hf1 (Finset.mem_filter.mp (Finset.mem_of_mem_erase hd)).1))
    have hle := Finset.card_le_card (Finset.insert_subset he1 (Finset.singleton_subset_iff.mpr he2))
    rw [Finset.card_pair hne_e] at hle; omega
   have hRle1 : R.card ≤ 1 := by
    by_contra hgt; push Not at hgt
    have hReq : R = {z1, zp1} := Finset.eq_of_subset_of_card_le hRsub (by rw [Finset.card_pair hz1_zp1]; omega)
    exact hnot_both_R ⟨by rw [hReq]; simp, by rw [hReq]; simp⟩
   by_cases hloss : MC1 = C1 ∧ MD1 = D1
   ·simp only [loss1, if_pos hloss]
    by_cases hR0 : R.card = 0
    ·omega
    ·
     obtain ⟨v, hvR⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
     have hU12_pos : 1 ≤ U12.card := by
      have hv := hRsub hvR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv_eq | hv_eq
      ·rw [hv_eq] at hvR
       obtain ⟨d, hd, hdzp⟩ := flag_exists_other_D hf1
       have hd_ns : d ∈ MD1_ns := Finset.mem_erase.mpr ⟨hdzp, by rw [hloss.2]; exact hd⟩
       exact Finset.card_pos.mpr ⟨s(z1, d), hz1_R_no_edge hvR d hd_ns⟩
      ·rw [hv_eq] at hvR
       obtain ⟨c, hc, hcz⟩ := flag_exists_other_C hf1
       have hc_ns : c ∈ MC1_ns := Finset.mem_erase.mpr ⟨hcz, by rw [hloss.1]; exact hc⟩
       exact Finset.card_pos.mpr ⟨s(c, zp1), hzp1_R_no_edge hvR c hc_ns⟩
     omega
   ·simp only [loss1, if_neg hloss]; omega
  have hle_sub := Finset.card_le_card hsub1
  have hsdiff := card_sdiff_eq hsub1
  omega
 have h2_bound : (Znew ∩ {z2, zp2}).card + loss2 ≤ A2.card + (Zconf ∩ {zp2}).card + 1 := by
  have hsub2 : A2 ∪ (Zconf ∩ {zp2}) ⊆ Znew ∩ {z2, zp2} := by
   refine Finset.union_subset (Finset.filter_subset _ _) ?_
   intro v hv; have h1 := (Finset.mem_inter.mp hv).1; have h2 := (Finset.mem_inter.mp hv).2
   rw [Finset.mem_singleton] at h2; subst h2
   exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_filter.mp h1).1).1, by simp⟩
  have hdisj2 : Disjoint A2 (Zconf ∩ {zp2}) := by
   rw [Finset.disjoint_left]; intro v hv1 hv2
   exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_inter.mp hv2).1).1).2 (Finset.mem_union_right _ hv1)
  have hcard_U : (A2 ∪ (Zconf ∩ {zp2})).card = A2.card + (Zconf ∩ {zp2}).card :=
   Finset.card_union_of_disjoint hdisj2
  set R := (Znew ∩ {z2, zp2}) \ (A2 ∪ (Zconf ∩ {zp2}))
  have hRsub : R ⊆ {z2, zp2} := Finset.Subset.trans Finset.sdiff_subset Finset.inter_subset_right
  have hzp2_nR : zp2 ∉ R := by
   intro hR
   have hzp2n : zp2 ∈ Znew := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hR).1).1
   have hMC2_ne : MC2_ns.Nonempty := by
    have hLne : (L zp2).Nonempty := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzp2n).1).2
    by_contra hemp
    have hdir : e2_to_z2 := Or.inr (Or.inr hemp)
    rw [hLzp2, if_neg (fun h => h.2 hdir)] at hLne
    exact hemp hLne
   obtain ⟨c, hc⟩ := hMC2_ne
   have hc_f := Finset.mem_filter.mp hc
   have hU2_nE1 : s(c, zp2) ∈ U2 \ E1 := Finset.mem_sdiff.mpr
    ⟨(Finset.mem_sdiff.mp hc_f.2).1, fun hE1 => (Finset.mem_sdiff.mp hc_f.2).2
     (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp hc_f.2).1).1, hE1⟩)⟩
   rcases hgold_2 zp2 (Finset.mem_inter.mpr ⟨hzp2n, by simp⟩) (Or.inr ⟨rfl, c, hc_f.1, hU2_nE1⟩) with hA | hC
   ·exact (Finset.mem_sdiff.mp hR).2 (Finset.mem_union_left _ hA)
   ·exact (Finset.mem_sdiff.mp hR).2 (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hC, by simp⟩))
  have hRsub_z2 : R ⊆ {z2} := by
   intro v hv
   have hv' := hRsub hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv' ⊢
   exact hv'.resolve_right (fun h => hzp2_nR (h ▸ hv))
  have hRle1 : R.card ≤ 1 := (Finset.card_le_card hRsub_z2).trans (by simp)
  have hR_loss : R.card + loss2 ≤ 1 := by
   by_cases hz2R : z2 ∈ R
   ·have hz2n : z2 ∈ Znew := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hz2R).1).1
    have hMD2_emp : ¬ MD2_ns.Nonempty := by
     rintro ⟨d, hd⟩
     have hd_f := Finset.mem_filter.mp hd
     have hU2_nE1 : s(z2, d) ∈ U2 \ E1 := Finset.mem_sdiff.mpr
      ⟨(Finset.mem_sdiff.mp hd_f.2).1, fun hE1 => (Finset.mem_sdiff.mp hd_f.2).2
       (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp hd_f.2).1).1, hE1⟩)⟩
     rcases hgold_2 z2 (Finset.mem_inter.mpr ⟨hz2n, by simp⟩) (Or.inl ⟨rfl, d, hd_f.1, hU2_nE1⟩) with hA | hC
     ·exact (Finset.mem_sdiff.mp hz2R).2 (Finset.mem_union_left _ hA)
     ·exact absurd (hsz.trans (Finset.mem_filter.mp hC).2.1) hcol_ne
    have hMC2_emp : ¬ MC2_ns.Nonempty := by
     intro hMC2_ne
     have hLne : (L z2).Nonempty := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hz2n).1).2
     have hnown : ¬ isOwn z2 := fun ho => (Finset.mem_sdiff.mp hz2n).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz2n).1, ho⟩)
     have hndir : ¬ e2_to_z2 := fun h => h.elim hMD2_emp (fun h => h.elim hnown (fun h => h hMC2_ne))
     rw [hLz2, if_neg (fun h => hndir h.2)] at hLne
     exact hMD2_emp hLne
    have hloss0 : loss2 = 0 := by
     simp only [loss2, ite_eq_right_iff]; rintro ⟨hCeq, hDeq⟩
     exfalso
     obtain ⟨c, hc, hcz⟩ := flag_exists_other_C hf2
     obtain ⟨d, hd, hdzp⟩ := flag_exists_other_D hf2
     have he_c : s(c, zp2) ∈ U2 := Finset.mem_inter.mpr
      ⟨(Finset.mem_filter.mp (by rw [hCeq]; exact hc : c ∈ MC2)).2, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)⟩
     have he_d : s(z2, d) ∈ U2 := Finset.mem_inter.mpr
      ⟨(Finset.mem_filter.mp (by rw [hDeq]; exact hd : d ∈ MD2)).2, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hd)⟩
     have hc_U1 : s(c, zp2) ∈ U1 := by
      by_contra hnu; exact hMC2_emp ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hcz, hc⟩, Finset.mem_sdiff.mpr ⟨he_c, hnu⟩⟩⟩
     have hd_U1 : s(z2, d) ∈ U1 := by
      by_contra hnu; exact hMD2_emp ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hdzp, hd⟩, Finset.mem_sdiff.mpr ⟨he_d, hnu⟩⟩⟩
     have hne_cd : s(c, zp2) ≠ s(z2, d) := by
      intro heq; rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, _⟩ | ⟨h1', _⟩
      ·exact hcz rfl
      ·exact hbip z2 zp2 hf2.1 ((flag_color_C hbip hf2 hc).symm.trans (by rw [h1']; exact flag_color_D hbip hf2 hd))
     have hle : ({s(c, zp2), s(z2, d)} : Finset (Sym2 (Fin n))).card ≤ U12.card :=
      Finset.card_le_card (Finset.insert_subset (Finset.mem_inter.mpr ⟨hc_U1, he_c⟩)
       (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hd_U1, he_d⟩)))
     rw [Finset.card_pair hne_cd] at hle; omega
    omega
   ·have hR0 : R = ∅ := by
     ext v; simp only [Finset.notMem_empty, iff_false]; intro hv
     exact hz2R ((Finset.mem_singleton.mp (hRsub_z2 hv)) ▸ hv)
    rw [hR0, Finset.card_empty]; simp [loss2]; split_ifs <;> omega
  have hle_sub := Finset.card_le_card hsub2
  have hsdiff : R.card = (Znew ∩ {z2, zp2}).card - (A2 ∪ (Zconf ∩ {zp2})).card := card_sdiff_eq hsub2
  omega
 have hZnew_split : Znew.card = (Znew ∩ {z1, zp1}).card + (Znew ∩ {z2, zp2}).card := by
  have hU : Znew = (Znew ∩ {z1, zp1}) ∪ (Znew ∩ {z2, zp2}) := by
   ext v; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
   constructor
   ·intro hv
    have hv4 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv4
    rcases hv4 with rfl | rfl | rfl | rfl
    ·exact Or.inl ⟨hv, Or.inl rfl⟩
    ·exact Or.inl ⟨hv, Or.inr rfl⟩
    ·exact Or.inr ⟨hv, Or.inl rfl⟩
    ·exact Or.inr ⟨hv, Or.inr rfl⟩
   ·rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
  have hd : Disjoint (Znew ∩ {z1, zp1}) (Znew ∩ {z2, zp2}) := by
   rw [Finset.disjoint_left]; intro v h1 h2
   have hv1 := (Finset.mem_inter.mp h1).2; have hv2 := (Finset.mem_inter.mp h2).2
   simp only [Finset.mem_insert, Finset.mem_singleton] at hv1 hv2
   rcases hv1 with rfl | rfl <;> rcases hv2 with h | h
   ·exact hz12 h
   ·exact hz1_zp2 h
   ·exact hz2_zp1 h.symm
   ·exact hzp12 h
  conv_lhs => rw [hU]
  exact Finset.card_union_of_disjoint hd
 have hZconf_split : Zconf.card = (Zconf ∩ {zp1}).card + (Zconf ∩ {zp2}).card := by
  have hsub : Zconf ⊆ {zp1, zp2} := by
   intro v hv
   have hvf := Finset.mem_filter.mp hv
   have hv4 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hvf.1).1).1).1
   simp only [Finset.mem_insert, Finset.mem_singleton] at hv4 ⊢
   rcases hv4 with rfl | rfl | rfl | rfl
   ·exact absurd hvf.2.1 hcol_ne
   ·exact Or.inl rfl
   ·exact absurd (hsz.trans hvf.2.1) hcol_ne
   ·exact Or.inr rfl
  have hU : Zconf = (Zconf ∩ {zp1}) ∪ (Zconf ∩ {zp2}) := by
   ext v; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_singleton]
   constructor
   ·intro hv
    have := hsub hv; simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl
    ·exact Or.inl ⟨hv, rfl⟩
    ·exact Or.inr ⟨hv, rfl⟩
   ·rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
  have hd : Disjoint (Zconf ∩ {zp1}) (Zconf ∩ {zp2}) := by
   rw [Finset.disjoint_left]; intro v h1 h2
   have hv1 := Finset.mem_singleton.mp (Finset.mem_inter.mp h1).2
   have hv2 := Finset.mem_singleton.mp (Finset.mem_inter.mp h2).2
   exact hzp12 (hv1.symm.trans hv2)
  conv_lhs => rw [hU]
  exact Finset.card_union_of_disjoint hd
 have hmaster : 2 * (centreless G C).card + Extra.card ≤ A1.card + A2.card + Zconf.card := by omega
 have hDisj_A1A2 : Disjoint A1 A2 := by
  rw [Finset.disjoint_left]; intro v h1 h2
  have hv1 := (Finset.mem_inter.mp (Finset.mem_filter.mp h1).1).2
  have hv2 := (Finset.mem_inter.mp (Finset.mem_filter.mp h2).1).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv1 hv2
  rcases hv1 with rfl | rfl <;> rcases hv2 with h | h
  ·exact hz12 h
  ·exact hz1_zp2 h
  ·exact hz2_zp1 h.symm
  ·exact hzp12 h
 have hDisj_AZ : Disjoint (A1 ∪ A2) Zconf := by
  rw [Finset.disjoint_left]; intro v hA hZ
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hZ).1).2 hA
 have htot_le4 : A1.card + A2.card + Zconf.card ≤ 4 := by
  have hsub : (A1 ∪ A2) ∪ Zconf ⊆ {z1, zp1, z2, zp2} := by
   intro v hv
   have hvZ : v ∈ Znew := by
    rcases Finset.mem_union.mp hv with hA | hZ
    ·rcases Finset.mem_union.mp hA with h1 | h2
     ·exact (Finset.mem_inter.mp (Finset.mem_filter.mp h1).1).1
     ·exact (Finset.mem_inter.mp (Finset.mem_filter.mp h2).1).1
    ·exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hZ).1).1
   exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hvZ).1).1
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hDisj_AZ, Finset.card_union_of_disjoint hDisj_A1A2, hZ4_card] at hle
  exact hle
 let mixGate : Fin n → ℕ := fun v =>
  if h : ∃ mv ∈ Extra, orIn n C (n + mv) = {v} then Classical.choose h else 0
 set SingleMix := Zconf.image mixGate
 have hSingleMix_sub : SingleMix ⊆ Extra := by
  intro k hk; simp only [SingleMix, Finset.mem_image] at hk
  rcases hk with ⟨v, hv, rfl⟩
  have hex : ∃ mv ∈ Extra, orIn n C (n + mv) = {v} := by
   rcases (Finset.mem_filter.mp hv).2.2 with ⟨mv, hmv, hor, _⟩; exact ⟨mv, hmv, hor⟩
  simp only [mixGate, dif_pos hex]; exact (Classical.choose_spec hex).1
 have hSingleMix_orIn : ∀ k ∈ SingleMix, ∃ v ∈ Zconf, orIn n C (n + k) = {v} := by
  intro k hk; simp only [SingleMix, Finset.mem_image] at hk
  rcases hk with ⟨v, hv, rfl⟩
  have hex : ∃ mv ∈ Extra, orIn n C (n + mv) = {v} := by
   rcases (Finset.mem_filter.mp hv).2.2 with ⟨mv, hmv, hor, _⟩; exact ⟨mv, hmv, hor⟩
  simp only [mixGate, dif_pos hex]; exact ⟨v, hv, (Classical.choose_spec hex).2⟩
 have hSingleMix_card : SingleMix.card = Zconf.card := by
  apply Finset.card_image_of_injOn
  intro v1 hv1 v2 hv2 heq
  have hex1 : ∃ mv ∈ Extra, orIn n C (n + mv) = {v1} := by
   rcases (Finset.mem_filter.mp hv1).2.2 with ⟨mv, hmv, hor, _⟩; exact ⟨mv, hmv, hor⟩
  have hex2 : ∃ mv ∈ Extra, orIn n C (n + mv) = {v2} := by
   rcases (Finset.mem_filter.mp hv2).2.2 with ⟨mv, hmv, hor, _⟩; exact ⟨mv, hmv, hor⟩
  simp only [mixGate, dif_pos hex1, dif_pos hex2] at heq
  have h1 := (Classical.choose_spec hex1).2
  have h2 := (Classical.choose_spec hex2).2
  rw [heq] at h1
  exact Finset.singleton_injective (h1.symm.trans h2)
 have hW_bound : ∀ a ∈ centreless G C, ∀ b : Fin 2, side (n := n) C a b = ∅ →
   ∀ A' : Finset (Fin n), A'.Nonempty → A' ⊆ A1 ∪ A2 → A' ⊆ side (n := n) C a (1 - b) →
   let HW := Extra.filter (fun k => 2 ≤ (orIn n C (n + k)).card)
   A'.card ≤ HW.card + 1 := by
  intro a haC b hemp A' hAne hA'sub hA'side HW
  have ha_top : a ∈ tops G C := (Finset.mem_filter.mp haC).1
  have ha' := mem_tops_iff.mp ha_top
  have hreach_b : OrReaches n C (opnd C a b) g1 ∨ OrReaches n C (opnd C a b) g2 := by
   have hall := (not_belowF_wval_eq hL hLift hne hjunk (opnd C a b)
    (by have := opnd_lt hL.1 ha'.1 b; omega) (top_opnd_not_belowF hL hne ha_top b) (fun _ => true)).mp
    (wval_allTrue hL.1 (opnd C a b) (by have := opnd_lt hL.1 ha'.1 b; omega))
   rcases hall with ⟨u, hu, _⟩ | ⟨hr, _⟩ | ⟨hr, _⟩
   ·rw [show orIn n C (opnd C a b) = ∅ from hemp] at hu; exact absurd hu (Finset.notMem_empty _)
   ·exact Or.inl hr
   ·exact Or.inr hr
  have hno_pair : ∀ k, OrReaches n C (opnd C a (1 - b)) k → k ∈ lam G C ∪ FacAll →
    (orIn n C (n + k) ∩ A').card ≤ 1 := by
   intro k _ hk
   by_contra hgt; push Not at hgt
   obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hgt
   have hu' := Finset.mem_inter.mp hu; have hv' := Finset.mem_inter.mp hv
   have hsame_col : s u = s v := by
    rcases Finset.mem_union.mp hk with hlam | hfac
    ·rcases (Finset.mem_filter.mp hlam).2.2.2 with ⟨atp, hatp, btp, hcard1, hrt⟩
     obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
     have hsub := orIn_subset_of_orReaches hrt
     have hwm : w ∈ side (n := n) C atp (1 - btp) := by rw [hw]; simp
     have hau : G.Adj w u := by fin_cases btp; exact (top_sides_adj hL.1 hatp (hsub hu'.1) hwm).symm; exact top_sides_adj hL.1 hatp hwm (hsub hu'.1)
     have hav : G.Adj w v := by fin_cases btp; exact (top_sides_adj hL.1 hatp (hsub hv'.1) hwm).symm; exact top_sides_adj hL.1 hatp hwm (hsub hv'.1)
     exact bool_eq_of_ne_ne (hbip w u hau).symm (hbip w v hav).symm
    ·simp only [FacAll, Finset.mem_union] at hfac
     rcases hfac with (h | h) | (h | h)
     ·exact (flag_color_C hbip hf1 ((hFC1_p k h).2.2.1 hu'.1)).trans (flag_color_C hbip hf1 ((hFC1_p k h).2.2.1 hv'.1)).symm
     ·exact (flag_color_D hbip hf1 ((hFD1_p k h).2.2.1 hu'.1)).trans (flag_color_D hbip hf1 ((hFD1_p k h).2.2.1 hv'.1)).symm
     ·exact (flag_color_C hbip hf2 ((hFC2_p k h).2.2.1 hu'.1)).trans (flag_color_C hbip hf2 ((hFC2_p k h).2.2.1 hv'.1)).symm
     ·exact (flag_color_D hbip hf2 ((hFD2_p k h).2.2.1 hu'.1)).trans (flag_color_D hbip hf2 ((hFD2_p k h).2.2.1 hv'.1)).symm
   have hpair_cases : ((u = z1 ∧ v = z2) ∨ (u = z2 ∧ v = z1)) ∨
     ((u = zp1 ∧ v = zp2) ∨ (u = zp2 ∧ v = zp1)) := by
    have hmem4 : ∀ x ∈ A', x = z1 ∨ x = zp1 ∨ x = z2 ∨ x = zp2 := fun x hx => by
     rcases Finset.mem_union.mp (hA'sub hx) with h1 | h2
     ·have := (Finset.mem_inter.mp (Finset.mem_filter.mp h1).1).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl; exact Or.inl rfl; exact Or.inr (Or.inl rfl)
     ·have := (Finset.mem_inter.mp (Finset.mem_filter.mp h2).1).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl; exact Or.inr (Or.inr (Or.inl rfl)); exact Or.inr (Or.inr (Or.inr rfl))
    rcases hmem4 u hu'.2 with rfl | rfl | rfl | rfl <;> rcases hmem4 v hv'.2 with rfl | rfl | rfl | rfl
    ·exact absurd rfl huv
    ·exact absurd hsame_col hcol_ne
    ·exact Or.inl (Or.inl ⟨rfl, rfl⟩)
    ·exact absurd (hsame_col.trans hszp.symm) hcol_ne
    ·exact absurd hsame_col.symm hcol_ne
    ·exact absurd rfl huv
    ·exact absurd (hsz.trans hsame_col.symm) hcol_ne
    ·exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    ·exact Or.inl (Or.inr ⟨rfl, rfl⟩)
    ·exact absurd (hsz.trans hsame_col) hcol_ne
    ·exact absurd rfl huv
    ·exact absurd (hsz.trans (hsame_col.trans hszp.symm)) hcol_ne
    ·exact absurd (hsame_col.symm.trans hszp.symm) hcol_ne
    ·exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    ·exact absurd (hsz.trans (hsame_col.symm.trans hszp.symm)) hcol_ne
    ·exact absurd rfl huv
   have hkill_z : z1 ∈ orIn n C (n + k) → z2 ∈ orIn n C (n + k) → z1 ∈ A' → z2 ∈ A' → False := by
    intro hz1k hz2k hz1A hz2A
    have hz1_A1 : z1 ∈ A1 := (Finset.mem_union.mp (hA'sub hz1A)).resolve_right (fun h => by
     have := (Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2; simp [hz12, hz1_zp2] at this)
    have hz2_A2 : z2 ∈ A2 := (Finset.mem_union.mp (hA'sub hz2A)).resolve_left (fun h => by
     have := (Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2; simp [hz12.symm, hz2_zp1] at this)
    rcases hreach_b with hrg1 | hrg2
    ·
     obtain ⟨d1, hd1, hzd1⟩ : ∃ d1 ∈ D1.erase zp1, s(z1, d1) ∈ U1 \ E2 := by
      rcases (Finset.mem_filter.mp hz1_A1).2.1 with ⟨_, h⟩ | ⟨heq, _⟩
      ·exact h
      ·exact absurd heq hz1_zp1
     have hd1zp : d1 ≠ zp1 := (Finset.mem_erase.mp hd1).1
     have hd1D : d1 ∈ D1 := Finset.mem_of_mem_erase hd1
     have hwmax := top_reaches_flag_wmax hL.1 ha_top b hrg1 (hA'side hz2A)
     have hadj_z2d1 : G.Adj z2 d1 := flag_wmax_adj_D hbip h4 hf1 hwmax hsz.symm hd1D hd1zp
     have hadj_z1d1 : G.Adj z1 d1 := (hf1.2.2.2.2.1 d1 hd1D).symm
     rcases Finset.mem_union.mp hk with hlam | hfac
     ·rcases (Finset.mem_filter.mp hlam).2.2.2 with ⟨atp, hatp, btp, hcard1, hrt⟩
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      have hsub := orIn_subset_of_orReaches hrt
      have hwm : w ∈ side (n := n) C atp (1 - btp) := by rw [hw]; simp
      have haz1 : G.Adj z1 w := by fin_cases btp; exact top_sides_adj hL.1 hatp (hsub hz1k) hwm; exact (top_sides_adj hL.1 hatp hwm (hsub hz1k)).symm
      have haz2 : G.Adj z2 w := by fin_cases btp; exact top_sides_adj hL.1 hatp (hsub hz2k) hwm; exact (top_sides_adj hL.1 hatp hwm (hsub hz2k)).symm
      have hweq : w = d1 := noFourCycle_unique h4 hz12 haz1 haz2 hadj_z1d1 hadj_z2d1
      subst hweq
      have hstar : s(z1, w) ∈ starEdges G C := by
       simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
       fin_cases btp
       ·exact ⟨atp, hatp, (z1, w), ⟨hsub hz1k, hwm⟩, rfl⟩
       ·exact ⟨atp, hatp, (w, z1), ⟨hwm, hsub hz1k⟩, Sym2.eq_swap⟩
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp hzd1).1).1).2 hstar
     ·simp only [FacAll, Finset.mem_union] at hfac
      rcases hfac with (h | h) | (h | h)
      ·have hsub := (hFC1_p k h).2.2.1
       have heq := noFourCycle_unique h4 hz12 (hf1.2.2.2.1 z1 (hsub hz1k)) (hf1.2.2.2.1 z2 (hsub hz2k)) hadj_z1d1 hadj_z2d1
       exact hd1zp heq.symm
      ·exact hcol_ne (flag_color_D hbip hf1 ((hFD1_p k h).2.2.1 hz1k))
      ·have hsub := (hFC2_p k h).2.2.1
       have heq := noFourCycle_unique h4 hz12 (hf2.2.2.2.1 z1 (hsub hz1k)) (hf2.2.2.2.1 z2 (hsub hz2k)) hadj_z1d1 hadj_z2d1
       subst heq
       exact (Finset.mem_sdiff.mp hzd1).2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hsub hz1k)))
      ·exact hcol_ne ((flag_color_D hbip hf2 ((hFD2_p k h).2.2.1 hz1k)).trans hszp.symm)
    ·
     obtain ⟨d2, hd2, hzd2⟩ : ∃ d2 ∈ D2.erase zp2, s(z2, d2) ∈ U2 \ E1 := by
      rcases (Finset.mem_filter.mp hz2_A2).2.1 with ⟨_, h⟩ | ⟨heq, _⟩
      ·exact h
      ·exact absurd heq hz2_zp2
     have hd2zp : d2 ≠ zp2 := (Finset.mem_erase.mp hd2).1
     have hd2D : d2 ∈ D2 := Finset.mem_of_mem_erase hd2
     have hwmax := top_reaches_flag_wmax hL.1 ha_top b hrg2 (hA'side hz1A)
     have hadj_z1d2 : G.Adj z1 d2 := flag_wmax_adj_D hbip h4 hf2 hwmax hsz hd2D hd2zp
     have hadj_z2d2 : G.Adj z2 d2 := (hf2.2.2.2.2.1 d2 hd2D).symm
     rcases Finset.mem_union.mp hk with hlam | hfac
     ·rcases (Finset.mem_filter.mp hlam).2.2.2 with ⟨atp, hatp, btp, hcard1, hrt⟩
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      have hsub := orIn_subset_of_orReaches hrt
      have hwm : w ∈ side (n := n) C atp (1 - btp) := by rw [hw]; simp
      have haz1 : G.Adj z1 w := by fin_cases btp; exact top_sides_adj hL.1 hatp (hsub hz1k) hwm; exact (top_sides_adj hL.1 hatp hwm (hsub hz1k)).symm
      have haz2 : G.Adj z2 w := by fin_cases btp; exact top_sides_adj hL.1 hatp (hsub hz2k) hwm; exact (top_sides_adj hL.1 hatp hwm (hsub hz2k)).symm
      have hweq : w = d2 := noFourCycle_unique h4 hz12 haz1 haz2 hadj_z1d2 hadj_z2d2
      subst hweq
      have hstar : s(z2, w) ∈ starEdges G C := by
       simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
       fin_cases btp
       ·exact ⟨atp, hatp, (z2, w), ⟨hsub hz2k, hwm⟩, rfl⟩
       ·exact ⟨atp, hatp, (w, z2), ⟨hwm, hsub hz2k⟩, Sym2.eq_swap⟩
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp hzd2).1).1).2 hstar
     ·simp only [FacAll, Finset.mem_union] at hfac
      rcases hfac with (h | h) | (h | h)
      ·have hsub := (hFC1_p k h).2.2.1
       have heq := noFourCycle_unique h4 hz12 (hf1.2.2.2.1 z1 (hsub hz1k)) (hf1.2.2.2.1 z2 (hsub hz2k)) hadj_z1d2 hadj_z2d2
       subst heq
       exact (Finset.mem_sdiff.mp hzd2).2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hsub hz2k)))
      ·exact hcol_ne (flag_color_D hbip hf1 ((hFD1_p k h).2.2.1 hz1k))
      ·have hsub := (hFC2_p k h).2.2.1
       have heq := noFourCycle_unique h4 hz12 (hf2.2.2.2.1 z1 (hsub hz1k)) (hf2.2.2.2.1 z2 (hsub hz2k)) hadj_z1d2 hadj_z2d2
       exact hd2zp heq.symm
      ·exact hcol_ne ((flag_color_D hbip hf2 ((hFD2_p k h).2.2.1 hz1k)).trans hszp.symm)
   have hkill_zp : zp1 ∈ orIn n C (n + k) → zp2 ∈ orIn n C (n + k) → zp1 ∈ A' → zp2 ∈ A' → False := by
    intro hzp1k hzp2k hzp1A hzp2A
    have hzp1_A1 : zp1 ∈ A1 := (Finset.mem_union.mp (hA'sub hzp1A)).resolve_right (fun h => by
     have := (Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2; simp [hz2_zp1.symm, hzp12] at this)
    have hzp2_A2 : zp2 ∈ A2 := (Finset.mem_union.mp (hA'sub hzp2A)).resolve_left (fun h => by
     have := (Finset.mem_inter.mp (Finset.mem_filter.mp h).1).2; simp [hz1_zp2.symm, hzp12.symm] at this)
    rcases hreach_b with hrg1 | hrg2
    ·obtain ⟨c1, hc1, hczp1⟩ : ∃ c1 ∈ C1.erase z1, s(c1, zp1) ∈ U1 \ E2 := by
      rcases (Finset.mem_filter.mp hzp1_A1).2.1 with ⟨heq, _⟩ | ⟨_, h⟩
      ·exact absurd heq hz1_zp1.symm
      ·exact h
     have hc1z : c1 ≠ z1 := (Finset.mem_erase.mp hc1).1
     have hc1C : c1 ∈ C1 := Finset.mem_of_mem_erase hc1
     have hwmax := top_reaches_flag_wmax hL.1 ha_top b hrg1 (hA'side hzp2A)
     have hadj_zp2c1 : G.Adj zp2 c1 := flag_wmax_adj_C hbip h4 hf1 hwmax hszp.symm hc1C hc1z
     have hadj_zp1c1 : G.Adj zp1 c1 := (hf1.2.2.2.1 c1 hc1C).symm
     rcases Finset.mem_union.mp hk with hlam | hfac
     ·rcases (Finset.mem_filter.mp hlam).2.2.2 with ⟨atp, hatp, btp, hcard1, hrt⟩
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      have hsub := orIn_subset_of_orReaches hrt
      have hwm : w ∈ side (n := n) C atp (1 - btp) := by rw [hw]; simp
      have haz1 : G.Adj zp1 w := by fin_cases btp; exact top_sides_adj hL.1 hatp (hsub hzp1k) hwm; exact (top_sides_adj hL.1 hatp hwm (hsub hzp1k)).symm
      have haz2 : G.Adj zp2 w := by fin_cases btp; exact top_sides_adj hL.1 hatp (hsub hzp2k) hwm; exact (top_sides_adj hL.1 hatp hwm (hsub hzp2k)).symm
      have hweq : w = c1 := noFourCycle_unique h4 hzp12 haz1 haz2 hadj_zp1c1 hadj_zp2c1
      subst hweq
      have hstar : s(w, zp1) ∈ starEdges G C := by
       simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
       fin_cases btp
       ·exact ⟨atp, hatp, (zp1, w), ⟨hsub hzp1k, hwm⟩, Sym2.eq_swap⟩
       ·exact ⟨atp, hatp, (w, zp1), ⟨hwm, hsub hzp1k⟩, rfl⟩
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp hczp1).1).1).2 hstar
     ·simp only [FacAll, Finset.mem_union] at hfac
      rcases hfac with (h | h) | (h | h)
      ·exact hcol_ne.symm (flag_color_C hbip hf1 ((hFC1_p k h).2.2.1 hzp1k))
      ·have hsub := (hFD1_p k h).2.2.1
       have heq := noFourCycle_unique h4 hzp12 (hf1.2.2.2.2.1 zp1 (hsub hzp1k)) (hf1.2.2.2.2.1 zp2 (hsub hzp2k)) hadj_zp1c1 hadj_zp2c1
       exact hc1z heq.symm
      ·exact hcol_ne.symm ((flag_color_C hbip hf2 ((hFC2_p k h).2.2.1 hzp1k)).trans hsz.symm)
      ·have hsub := (hFD2_p k h).2.2.1
       have heq := noFourCycle_unique h4 hzp12 (hf2.2.2.2.2.1 zp1 (hsub hzp1k)) (hf2.2.2.2.2.1 zp2 (hsub hzp2k)) hadj_zp1c1 hadj_zp2c1
       subst heq
       exact (Finset.mem_sdiff.mp hczp1).2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hsub hzp1k)))
    ·obtain ⟨c2, hc2, hczp2⟩ : ∃ c2 ∈ C2.erase z2, s(c2, zp2) ∈ U2 \ E1 := by
      rcases (Finset.mem_filter.mp hzp2_A2).2.1 with ⟨heq, _⟩ | ⟨_, h⟩
      ·exact absurd heq hz2_zp2.symm
      ·exact h
     have hc2z : c2 ≠ z2 := (Finset.mem_erase.mp hc2).1
     have hc2C : c2 ∈ C2 := Finset.mem_of_mem_erase hc2
     have hwmax := top_reaches_flag_wmax hL.1 ha_top b hrg2 (hA'side hzp1A)
     have hadj_zp1c2 : G.Adj zp1 c2 := flag_wmax_adj_C hbip h4 hf2 hwmax hszp hc2C hc2z
     have hadj_zp2c2 : G.Adj zp2 c2 := (hf2.2.2.2.1 c2 hc2C).symm
     rcases Finset.mem_union.mp hk with hlam | hfac
     ·rcases (Finset.mem_filter.mp hlam).2.2.2 with ⟨atp, hatp, btp, hcard1, hrt⟩
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      have hsub := orIn_subset_of_orReaches hrt
      have hwm : w ∈ side (n := n) C atp (1 - btp) := by rw [hw]; simp
      have haz1 : G.Adj zp1 w := by fin_cases btp; exact top_sides_adj hL.1 hatp (hsub hzp1k) hwm; exact (top_sides_adj hL.1 hatp hwm (hsub hzp1k)).symm
      have haz2 : G.Adj zp2 w := by fin_cases btp; exact top_sides_adj hL.1 hatp (hsub hzp2k) hwm; exact (top_sides_adj hL.1 hatp hwm (hsub hzp2k)).symm
      have hweq : w = c2 := noFourCycle_unique h4 hzp12 haz1 haz2 hadj_zp1c2 hadj_zp2c2
      subst hweq
      have hstar : s(w, zp2) ∈ starEdges G C := by
       simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
       fin_cases btp
       ·exact ⟨atp, hatp, (zp2, w), ⟨hsub hzp2k, hwm⟩, Sym2.eq_swap⟩
       ·exact ⟨atp, hatp, (w, zp2), ⟨hwm, hsub hzp2k⟩, rfl⟩
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_sdiff.mp hczp2).1).1).2 hstar
     ·simp only [FacAll, Finset.mem_union] at hfac
      rcases hfac with (h | h) | (h | h)
      ·exact hcol_ne.symm (flag_color_C hbip hf1 ((hFC1_p k h).2.2.1 hzp1k))
      ·have hsub := (hFD1_p k h).2.2.1
       have heq := noFourCycle_unique h4 hzp12 (hf1.2.2.2.2.1 zp1 (hsub hzp1k)) (hf1.2.2.2.2.1 zp2 (hsub hzp2k)) hadj_zp1c2 hadj_zp2c2
       subst heq
       exact (Finset.mem_sdiff.mp hczp2).2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hsub hzp2k)))
      ·exact hcol_ne.symm ((flag_color_C hbip hf2 ((hFC2_p k h).2.2.1 hzp1k)).trans hsz.symm)
      ·have hsub := (hFD2_p k h).2.2.1
       have heq := noFourCycle_unique h4 hzp12 (hf2.2.2.2.2.1 zp1 (hsub hzp1k)) (hf2.2.2.2.2.1 zp2 (hsub hzp2k)) hadj_zp1c2 hadj_zp2c2
       exact hc2z heq.symm
   rcases hpair_cases with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
   ·exact hkill_z hu'.1 hv'.1 hu'.2 hv'.2
   ·exact hkill_z hv'.1 hu'.1 hv'.2 hu'.2
   ·exact hkill_zp hu'.1 hv'.1 hu'.2 hv'.2
   ·exact hkill_zp hv'.1 hu'.1 hv'.2 hu'.2
  have hwb := w_merge_bound hL hLift hne hjunk
   (by have := opnd_lt hL.1 ha'.1 (1 - b); omega) (top_opnd_not_belowF hL hne ha_top (1 - b))
   A' hAne hA'side FacAll hno_pair
  have hsub_HW : (orN G C \ lam G C).filter (fun k =>
    OrReaches n C (opnd C a (1 - b)) k ∧ k ∉ FacAll ∧ 2 ≤ (orIn n C (n + k) ∩ A').card) ⊆ HW := by
   intro k hk
   have hkf := Finset.mem_filter.mp hk
   exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hkf.1, hkf.2.2.1⟩,
    le_trans hkf.2.2.2 (Finset.card_le_card Finset.inter_subset_left)⟩
  have hle_HW := Finset.card_le_card hsub_HW
  omega
 by_cases hcent3 : 3 ≤ (centreless G C).card
 ·omega
 ·by_cases hcent0 : (centreless G C).card = 0
  ·have hcent_emp : centreless G C = ∅ := Finset.card_eq_zero.mp hcent0
   have hA1_0 : A1 = ∅ := by
    ext v; simp only [Finset.notMem_empty, iff_false]; intro hv
    rcases (Finset.mem_filter.mp hv).2.2 with ⟨a, haC, _⟩
    rw [hcent_emp] at haC; exact Finset.notMem_empty _ haC
   have hA2_0 : A2 = ∅ := by
    ext v; simp only [Finset.notMem_empty, iff_false]; intro hv
    rcases (Finset.mem_filter.mp hv).2.2 with ⟨a, haC, _⟩
    rw [hcent_emp] at haC; exact Finset.notMem_empty _ haC
   rw [hA1_0, hA2_0, Finset.card_empty] at hmaster
   by_cases hZc0 : Zconf = ∅
   ·obtain ⟨m0, hm0, hm0_gt⟩ := exists_mixing_gt_g2 hL hLift hne hlt12 hjunk hcent_emp
    have hm0_E : m0 ∈ Extra := Finset.mem_sdiff.mpr ⟨hm0, fun hkf => by
     have : m0 < g2 := by
      simp only [FacAll, Finset.mem_union] at hkf
      rcases hkf with (h | h) | (h | h)
      ·have := orReaches_le (Finset.mem_filter.mp h).2; have := opnd_lt hL.1 hg1j.1 b1; omega
      ·have := orReaches_le (Finset.mem_filter.mp h).2; have := opnd_lt hL.1 hg1j.1 (1 - b1); omega
      ·have := orReaches_le (Finset.mem_filter.mp h).2; have := opnd_lt hL.1 hg2j.1 b2; omega
      ·have := orReaches_le (Finset.mem_filter.mp h).2; have := opnd_lt hL.1 hg2j.1 (1 - b2); omega
     omega⟩
    have hEpos : 1 ≤ Extra.card := Finset.card_pos.mpr ⟨m0, hm0_E⟩
    rw [hZc0, Finset.card_empty] at hmaster; omega
   ·obtain ⟨v0, hv0⟩ := Finset.nonempty_iff_ne_empty.mpr hZc0
    obtain ⟨_, _, _, u', hsu', mu, hmu_E, hmu_orIn⟩ := (Finset.mem_filter.mp hv0).2.2
    have hmu_nSM : mu ∉ SingleMix := by
     intro hsm
     obtain ⟨v, hv, hor⟩ := hSingleMix_orIn mu hsm
     rw [hmu_orIn] at hor
     have hu'eq : u' = v := Finset.singleton_injective hor
     have hsv := (Finset.mem_filter.mp hv).2.1
     exact hcol_ne (hsu'.symm.trans ((congrArg s hu'eq).trans hsv))
    have hle := Finset.card_le_card (Finset.insert_subset hmu_E hSingleMix_sub)
    rw [Finset.card_insert_of_notMem hmu_nSM, hSingleMix_card] at hle
    omega
  ·by_cases hcent1 : (centreless G C).card = 1
   ·obtain ⟨a0, ha0⟩ := Finset.card_eq_one.mp hcent1
    have ha0C : a0 ∈ centreless G C := by rw [ha0]; simp
    by_cases hA_emp : A1 ∪ A2 = ∅
    ·have hA1_0 : A1 = ∅ := (Finset.union_eq_empty.mp hA_emp).1
     have hA2_0 : A2 = ∅ := (Finset.union_eq_empty.mp hA_emp).2
     have hle := Finset.card_le_card hSingleMix_sub
     rw [hSingleMix_card] at hle
     rw [hA1_0, hA2_0, Finset.card_empty] at hmaster
     omega
    ·obtain ⟨v0, hv0⟩ := Finset.nonempty_iff_ne_empty.mpr hA_emp
     obtain ⟨b0, hemp0, hv0s⟩ : ∃ b0 : Fin 2, side (n := n) C a0 b0 = ∅ ∧ v0 ∈ side (n := n) C a0 (1 - b0) := by
      rcases Finset.mem_union.mp hv0 with h1 | h2
      ·rcases (Finset.mem_filter.mp h1).2.2 with ⟨a, haC, b, hemp, _, hvs⟩
       have haeq : a = a0 := Finset.mem_singleton.mp (ha0 ▸ haC); subst haeq
       exact ⟨b, hemp, hvs⟩
      ·rcases (Finset.mem_filter.mp h2).2.2 with ⟨a, haC, b, hemp, _, hvs⟩
       have haeq : a = a0 := Finset.mem_singleton.mp (ha0 ▸ haC); subst haeq
       exact ⟨b, hemp, hvs⟩
     have hA_side : A1 ∪ A2 ⊆ side (n := n) C a0 (1 - b0) := by
      intro v hv
      obtain ⟨b, hemp, hvs⟩ : ∃ b : Fin 2, side (n := n) C a0 b = ∅ ∧ v ∈ side (n := n) C a0 (1 - b) := by
       rcases Finset.mem_union.mp hv with h1 | h2
       ·rcases (Finset.mem_filter.mp h1).2.2 with ⟨a, haC, b, hemp, _, hvs⟩
        have haeq : a = a0 := Finset.mem_singleton.mp (ha0 ▸ haC); subst haeq
        exact ⟨b, hemp, hvs⟩
       ·rcases (Finset.mem_filter.mp h2).2.2 with ⟨a, haC, b, hemp, _, hvs⟩
        have haeq : a = a0 := Finset.mem_singleton.mp (ha0 ▸ haC); subst haeq
        exact ⟨b, hemp, hvs⟩
      have hbe : b = b0 := by
       by_contra hne_b
       have h1mb : 1 - b0 = b := fin2_sub_eq (Ne.symm hne_b)
       rw [h1mb, hemp] at hv0s; exact Finset.notMem_empty _ hv0s
      rwa [← hbe]
     set HW := Extra.filter (fun k => 2 ≤ (orIn n C (n + k)).card)
     have hW_le := hW_bound a0 ha0C b0 hemp0 (A1 ∪ A2) ⟨v0, hv0⟩ (Finset.Subset.refl _) hA_side
     have hDisj_SM_HW : Disjoint SingleMix HW := by
      rw [Finset.disjoint_left]; intro k hk1 hk2
      obtain ⟨v, _, hor⟩ := hSingleMix_orIn k hk1
      have hc := (Finset.mem_filter.mp hk2).2
      rw [hor, Finset.card_singleton] at hc; omega
     have hE_ge := Finset.card_le_card (Finset.union_subset hSingleMix_sub (Finset.filter_subset _ _ : HW ⊆ Extra))
     rw [Finset.card_union_of_disjoint hDisj_SM_HW, hSingleMix_card] at hE_ge
     rw [Finset.card_union_of_disjoint hDisj_A1A2] at hW_le
     omega
   ·
    have hcent2 : (centreless G C).card = 2 := by omega
    by_cases hZpos : 1 ≤ Zconf.card
    ·have hle := Finset.card_le_card hSingleMix_sub
     rw [hSingleMix_card] at hle
     omega
    ·by_cases htot3 : A1.card + A2.card + Zconf.card ≤ 3
     ·omega
     ·
      have hA_card4 : (A1 ∪ A2).card = 4 := by
       rw [Finset.card_union_of_disjoint hDisj_A1A2]; omega
      obtain ⟨a1, a2, ha12, hcent_eq⟩ := Finset.card_eq_two.mp hcent2
      have ha1C : a1 ∈ centreless G C := by rw [hcent_eq]; simp
      have ha2C : a2 ∈ centreless G C := by rw [hcent_eq]; simp
      let S1 := (A1 ∪ A2).filter (fun v => ∃ b : Fin 2, side (n := n) C a1 b = ∅ ∧ v ∈ side (n := n) C a1 (1 - b))
      let S2 := (A1 ∪ A2).filter (fun v => ∃ b : Fin 2, side (n := n) C a2 b = ∅ ∧ v ∈ side (n := n) C a2 (1 - b))
      have hU_S12 : A1 ∪ A2 ⊆ S1 ∪ S2 := by
       intro v hv
       obtain ⟨a, haC, b, hemp, hvs⟩ : ∃ a ∈ centreless G C, ∃ b : Fin 2, side (n := n) C a b = ∅ ∧ v ∈ side (n := n) C a (1 - b) := by
        rcases Finset.mem_union.mp hv with h1 | h2
        ·rcases (Finset.mem_filter.mp h1).2.2 with ⟨a, haC, b, hemp, _, hvs⟩; exact ⟨a, haC, b, hemp, hvs⟩
        ·rcases (Finset.mem_filter.mp h2).2.2 with ⟨a, haC, b, hemp, _, hvs⟩; exact ⟨a, haC, b, hemp, hvs⟩
       rw [hcent_eq, Finset.mem_insert, Finset.mem_singleton] at haC
       rcases haC with rfl | rfl
       ·exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, b, hemp, hvs⟩)
       ·exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, b, hemp, hvs⟩)
      have hle_sum : 4 ≤ S1.card + S2.card := by
       have h1 := Finset.card_le_card hU_S12
       have h2 := Finset.card_union_le S1 S2
       omega
      have hpick : ∃ a ∈ centreless G C, ∃ S' : Finset (Fin n), 2 ≤ S'.card ∧ S' ⊆ A1 ∪ A2 ∧
        ∃ b : Fin 2, side (n := n) C a b = ∅ ∧ S' ⊆ side (n := n) C a (1 - b) := by
       by_cases hS1 : 2 ≤ S1.card
       ·obtain ⟨v0, hv0⟩ := Finset.card_pos.mp (by omega : 0 < S1.card)
        obtain ⟨b0, hemp0, hv0s⟩ := (Finset.mem_filter.mp hv0).2
        refine ⟨a1, ha1C, S1, hS1, Finset.filter_subset _ _, b0, hemp0, fun v hv => ?_⟩
        obtain ⟨b, hemp, hvs⟩ := (Finset.mem_filter.mp hv).2
        have hbe : b = b0 := by
         by_contra hne_b
         have h1mb : 1 - b0 = b := fin2_sub_eq (Ne.symm hne_b)
         rw [h1mb, hemp] at hv0s; exact Finset.notMem_empty _ hv0s
        rwa [← hbe]
       ·have hS2 : 2 ≤ S2.card := by omega
        obtain ⟨v0, hv0⟩ := Finset.card_pos.mp (by omega : 0 < S2.card)
        obtain ⟨b0, hemp0, hv0s⟩ := (Finset.mem_filter.mp hv0).2
        refine ⟨a2, ha2C, S2, hS2, Finset.filter_subset _ _, b0, hemp0, fun v hv => ?_⟩
        obtain ⟨b, hemp, hvs⟩ := (Finset.mem_filter.mp hv).2
        have hbe : b = b0 := by
         by_contra hne_b
         have h1mb : 1 - b0 = b := fin2_sub_eq (Ne.symm hne_b)
         rw [h1mb, hemp] at hv0s; exact Finset.notMem_empty _ hv0s
        rwa [← hbe]
      obtain ⟨a, haC, S', hS'2, hS'sub, b, hemp, hS'side⟩ := hpick
      set HW := Extra.filter (fun k => 2 ≤ (orIn n C (n + k)).card)
      have hW_le : S'.card ≤ HW.card + 1 := hW_bound a haC b hemp S' (Finset.card_pos.mp (by omega)) hS'sub hS'side
      have hE_ge : HW.card ≤ Extra.card := Finset.card_le_card (Finset.filter_subset _ _)
      omega
lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
  (hbip : ∀ u v : Fin n, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
  (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) :
  ¬ ∃ g1 g2 : ℕ, g1 ≠ g2 ∧ (∀ k : ℕ, k ∈ junk G C ↔ k = g1 ∨ k = g2) ∧
   (∃ (Ci Di : Finset (Fin n)) (z zp : Fin n), G.Adj z zp ∧ z ∈ Ci ∧ zp ∈ Di ∧
    (∀ c ∈ Ci, G.Adj c zp) ∧ (∀ d ∈ Di, G.Adj d z) ∧ 2 ≤ Ci.card ∧ 2 ≤ Di.card ∧
    ∀ x : Fin n → Bool, gateVal n C g1 x = (decide (∃ c ∈ Ci, x c = true) && decide (∃ d ∈ Di, x d = true))) ∧
   (∃ (Ci Di : Finset (Fin n)) (z zp : Fin n), G.Adj z zp ∧ z ∈ Ci ∧ zp ∈ Di ∧
    (∀ c ∈ Ci, G.Adj c zp) ∧ (∀ d ∈ Di, G.Adj d z) ∧ 2 ≤ Ci.card ∧ 2 ≤ Di.card ∧
    ∀ x : Fin n → Bool, gateVal n C g2 x = (decide (∃ c ∈ Ci, x c = true) && decide (∃ d ∈ Di, x d = true))) := by
 have hsymm_flag : ∀ g Ci Di z zp, IsFlag G C g Ci Di z zp → IsFlag G C g Di Ci zp z := by
  intro g Ci Di z zp hf
  refine ⟨hf.1.symm, hf.2.2.1, hf.2.1, hf.2.2.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.2.1, hf.2.2.2.2.2.1, fun x => ?_⟩
  rw [hf.2.2.2.2.2.2.2 x, Bool.and_comm]
 have hordered : ∀ g1 g2, g1 < g2 → (∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2) →
   ∀ C1 D1 z1 zp1 C2 D2 z2 zp2,
   IsFlag G C g1 C1 D1 z1 zp1 → IsFlag G C g2 C2 D2 z2 zp2 → False := by
  intro g1 g2 hlt12 hjunk C1 D1 z1 zp1 C2 D2 z2 zp2 hf1 hf2
  have haligned : ∀ C2' D2' z2' zp2', IsFlag G C g2 C2' D2' z2' zp2' →
    s z1 = s z2' → s zp1 = s zp2' → False := by
   intro C2' D2' z2' zp2' hf2' hsz hszp
   by_cases hz : z1 = z2'
   ·subst hz
    by_cases hzp : zp1 = zp2'
    ·subst hzp; exact case_two_centers hbip h4 hL hLift hlt12 hjunk hf1 hf2'
    ·exact case_three_centers hbip h4 hL hLift hlt12 hjunk hzp hf1 hf2'
   ·by_cases hzp : zp1 = zp2'
    ·subst hzp
     exact case_three_centers hbip h4 hL hLift hlt12 hjunk hz
      (hsymm_flag g1 C1 D1 z1 zp1 hf1) (hsymm_flag g2 C2' D2' z2' zp1 hf2')
    ·exact case_four_centers hbip h4 hL hLift hlt12 hjunk hz hzp hsz hszp hf1 hf2'
  by_cases hsz : s z1 = s z2
  ·have hszp : s zp1 = s zp2 :=
    bool_eq_of_ne_ne (hbip z1 zp1 hf1.1).symm (by rw [hsz]; exact (hbip z2 zp2 hf2.1).symm)
   exact haligned C2 D2 z2 zp2 hf2 hsz hszp
  ·have hsz' : s z1 = s zp2 := bool_eq_of_ne_ne hsz (hbip z2 zp2 hf2.1).symm
   have hszp' : s zp1 = s z2 := bool_eq_of_ne_ne (hbip z1 zp1 hf1.1).symm (Ne.symm hsz)
   exact haligned D2 C2 zp2 z2 (hsymm_flag g2 C2 D2 z2 zp2 hf2) hsz' hszp'
 rintro ⟨g1, g2, hne12, hjunk, ⟨C1, D1, z1, zp1, hf1⟩, ⟨C2, D2, z2, zp2, hf2⟩⟩
 rcases Nat.lt_or_gt_of_ne hne12 with hlt | hgt
 ·exact hordered g1 g2 hlt hjunk C1 D1 z1 zp1 C2 D2 z2 zp2 hf1 hf2
 ·exact hordered g2 g1 hgt (fun k => by rw [hjunk k, or_comm]) C2 D2 z2 zp2 C1 D1 z1 zp1 hf2 hf1
end PEqualNP.Outside.L_meta_5012_apart_case.Flags
namespace PEqualNP.Outside.L_meta_5012_apart_case
namespace Lift
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
  (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
   acc.length + gs.length := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.foldl_wires_len <;> assumption
lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
  (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
   acc.getD i false := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.foldl_wires_getD_lt <;> assumption
lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
  (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
  (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
    (acc.length + j) false =
   gs[j].op.eval (gs[j].inputs.map fun k =>
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
     k false) := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.foldl_wires_getD_gate <;> assumption
lemma wires_length (C : Circuit) (x : List Bool) :
  (C.wires x).length = x.length + C.gates.length :=
 foldl_wires_len C.gates x
lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
  wval C x i = x ⟨i, hi⟩ := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.wval_input <;> assumption
lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
  gateVal n C j x = wval C x (n + j) := rfl
lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
  wval C x w = false := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.wval_ge_len <;> assumption
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
  gateAt C j = C.gates[j] := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.gateAt_eq <;> assumption
lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
  gateAt C j ∈ C.gates := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.gateAt_mem <;> assumption
lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
  (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.gate_inputs_eq <;> assumption
lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
  opnd C j b ∈ (gateAt C j).inputs := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.opnd_mem <;> assumption
lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
  opnd C j b < n + j :=
 hAO.2.1 j hj _ (opnd_mem hAO hj b)
lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
  {j : ℕ} (hj : j < C.gates.length) :
  wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.wval_gate_eval <;> assumption
lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
  {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
  wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.wval_gate_or <;> assumption
lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
  (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.foldl_cones_len <;> assumption
lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
  (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.foldl_cones_getD_lt <;> assumption
lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.cones_length <;> assumption
lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
  (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
   (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
    (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.foldl_cones_getD_gate <;> assumption
lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.inCone_lt_len <;> assumption
lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
  InCone n C i j ↔
   ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.inCone_iff <;> assumption
lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.inCone_lt <;> assumption
lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
  InCone n C i k := by
 induction k using Nat.strong_induction_on with
 | ind k ih =>
  have hk := inCone_lt_len h2
  rw [inCone_iff hk] at h2 ⊢
  rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
  ·exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
  ·exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩
lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
  graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.graphFun_iff <;> assumption
lemma graphFun_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
  graphFun G ∅ (fun w => decide (w = v)) = false := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.graphFun_unit_false <;> assumption
lemma input_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
  {w : ℕ} (hw : w < n) :
  ¬ ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.input_not_belowF <;> assumption
lemma below_wire_contains_top {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {C : Circuit} (hAO : IsAO2 n C) (w : ℕ) (hw : w < n + C.gates.length)
  (hb : ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true) :
  ∃ r, r < C.gates.length ∧ (gateAt C r).op = GateOp.and ∧ BelowF G C r ∧
   (r = w - n ∨ InCone n C r (w - n)) := by
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  have hn : n ≤ w := by
   by_contra h
   exact input_not_belowF (by omega : w < n) hb
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hj : j < C.gates.length := by omega
  have hjb : BelowF G C j := hb
  rcases hAO.1 _ (gateAt_mem hj) with hand | hor
  ·exact ⟨j, hj, hand, hjb, Or.inl (by omega)⟩
  ·have hwb : ∀ x : Fin n → Bool, wval C x (opnd C j 0) = true → graphFun G ∅ x = true := by
    intro x hx
    apply hjb x
    rw [gateVal_eq_wval, wval_gate_or hAO x hj hor, Bool.or_eq_true]
    exact Or.inl hx
   have hlt := opnd_lt hAO hj 0
   have hn0 : n ≤ opnd C j 0 := by
    by_contra h
    exact input_not_belowF (by omega : opnd C j 0 < n) hwb
   obtain ⟨r, hr, hro, hrb, hrc⟩ := ih (opnd C j 0) hlt (by omega) hwb
   refine ⟨r, hr, hro, hrb, Or.inr ?_⟩
   simp only [Nat.add_sub_cancel_left]
   exact (inCone_iff hj).mpr ⟨opnd C j 0, opnd_mem hAO hj 0, hn0, hlt, hrc⟩
lemma cone_propagates_through_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
  {i j : ℕ} (hcone : InCone n C i j)
  (hor : ∀ k, InCone n C i k → (gateAt C k).op = GateOp.or)
  (x : Fin n → Bool) (hi : gateVal n C i x = true) : gateVal n C j x = true := by
 induction j using Nat.strong_induction_on with
 | ind j ih =>
  have hj := inCone_lt_len hcone
  have hop := hor j hcone
  obtain ⟨w, hw, hnw, hwj, hsub⟩ := (inCone_iff hj).mp hcone
  have hwv : wval C x w = true := by
   rcases hsub with he | hsub
   ·rw [he, gateVal_eq_wval, Nat.add_sub_of_le hnw] at hi
    exact hi
   ·have hg := ih (w - n) (by omega) hsub
    rw [gateVal_eq_wval, Nat.add_sub_of_le hnw] at hg
    exact hg
  rw [gateVal_eq_wval, wval_gate_or hAO x hj hop, Bool.or_eq_true]
  rw [gate_inputs_eq hAO hj] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  ·exact Or.inl hwv
  ·exact Or.inr hwv
lemma topForm_isLiftFixedPoint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
  (hT : TopForm G C) : IsLiftFixedPoint G C := by
 rintro ⟨h, hh, b, hLive, _, hNot, hImp⟩
 have hwlt := opnd_lt hAO hh b
 obtain ⟨r, hr, hro, hrb, hrc⟩ :=
  below_wire_contains_top hAO (opnd C h b) (by omega) hImp.1
 have hwn : n ≤ opnd C h b := by
  by_contra hlt
  exact input_not_belowF (by omega : opnd C h b < n) hImp.1
 have hrh : InCone n C r h :=
  (inCone_iff hh).mpr ⟨opnd C h b, opnd_mem hAO hh b, hwn, hwlt, hrc⟩
 have hor : ∀ k, InCone n C h k → (gateAt C k).op = GateOp.or := by
  intro k hk
  have hkl := inCone_lt_len hk
  rcases hAO.1 _ (gateAt_mem hkl) with hand | hkor
  ·exact False.elim (hT r hr k hkl hro hrb hand (inCone_trans hrh hk))
  ·exact hkor
 apply hNot
 intro x hx
 have hout : wval C x C.output = true := by
  rcases hLive.2 with hout | ⟨houtn, hcone⟩
  ·rw [hout]
   exact hx
  ·have hc := cone_propagates_through_or hAO hcone hor x hx
   rw [gateVal_eq_wval, Nat.add_sub_of_le houtn] at hc
   exact hc
 change circuitFun n C x = true at hout
 rwa [hF] at hout
end Lift
namespace Patch
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
open Lift
def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩
lemma patch_length (C : Circuit) (j : ℕ) (g : Gate) :
  (patch C j g).gates.length = C.gates.length := by
 simp [patch]
lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
  gateAt (patch C j g) k = gateAt C k := by
 simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]
lemma gateAt_patch_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) :
  gateAt (patch C j g) j = g := by
 simp [patch, gateAt, List.getD_eq_getElem?_getD, hj]
lemma patch_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (j : ℕ) (g : Gate)
  (hOp : g.op = GateOp.and ∨ g.op = GateOp.or) (hLen : g.inputs.length = 2)
  (hBack : ∀ w ∈ g.inputs, w < n + j) : IsAO2 n (patch C j g) := by
 refine ⟨?_, ?_, ?_⟩
 ·intro k hk
  change k ∈ C.gates.set j g at hk
  rcases List.mem_or_eq_of_mem_set hk with hk | rfl
  ·exact hAO.1 k hk
  ·exact hOp
 ·intro k hk w hw
  have hkC : k < C.gates.length := by simpa only [patch_length] using hk
  by_cases hkj : k = j
  ·subst k
   rw [gateAt_patch_eq hkC] at hw
   exact hBack w hw
  ·rw [gateAt_patch_ne C j k g (Ne.symm hkj)] at hw
   exact hAO.2.1 k hkC w hw
 ·intro k hk
  change k ∈ C.gates.set j g at hk
  rcases List.mem_or_eq_of_mem_set hk with hk | rfl
  ·exact hAO.2.2 k hk
  ·exact hLen
lemma patch_gateVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
  (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C j g)) (k : ℕ)
  (hne : j ≠ k) (hCone : ¬ InCone n C j k) (x : Fin n → Bool) :
  gateVal n (patch C j g) k x = gateVal n C k x := by
 induction k using Nat.strong_induction_on with
 | ind k ih =>
  by_cases hk : k < C.gates.length
  ·have hk' : k < (patch C j g).gates.length := by simpa only [patch_length] using hk
   have hgate := gateAt_patch_ne C j k g hne
   have hopnd (b : Fin 2) : opnd (patch C j g) k b = opnd C k b := by
    unfold opnd
    rw [hgate]
   have hval (b : Fin 2) : wval (patch C j g) x (opnd C k b) =
     wval C x (opnd C k b) := by
    by_cases hw : opnd C k b < n
    ·rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
    ·have hw' : n ≤ opnd C k b := by omega
     have hlt := opnd_lt hAO hk b
     have hsub_ne : j ≠ opnd C k b - n := by
      intro he
      apply hCone
      exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inl he⟩
     have hsub_cone : ¬ InCone n C j (opnd C k b - n) := by
      intro he
      apply hCone
      exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inr he⟩
     have hv := ih (opnd C k b - n) (by omega) hsub_ne hsub_cone
     rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hw'] at hv
     exact hv
   rw [gateVal_eq_wval, gateVal_eq_wval, wval_gate_eval hAO' x hk',
    wval_gate_eval hAO x hk, hgate, hopnd 0, hopnd 1, hval 0, hval 1]
  ·rw [gateVal_eq_wval, gateVal_eq_wval, wval_ge_len _ _ (by rw [patch_length]; omega),
    wval_ge_len _ _ (by omega)]
lemma patch_size (C : Circuit) (j : ℕ) (g : Gate) : (patch C j g).size = C.size := by
 simp [Circuit.size, patch_length]
lemma patch_isLeastAO {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {C : Circuit} {j : ℕ} {g : Gate} (hL : IsLeastAO G C)
  (hAO' : IsAO2 n (patch C j g)) (hF' : circuitFun n (patch C j g) = graphFun G ∅) :
  IsLeastAO G (patch C j g) := by
 refine ⟨hAO', hF', ?_⟩
 intro D hD hDF
 rw [patch_size]
 exact hL.2.2 D hD hDF
lemma patch_junk_mem_iff_of_not_inCone {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {C : Circuit} {j : ℕ} {g : Gate} (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C j g))
  {k : ℕ} (hne : j ≠ k) (hCone : ¬ InCone n C j k) :
  k ∈ junk G (patch C j g) ↔ k ∈ junk G C := by
 change (k ∈ (Finset.range (patch C j g).gates.length).filter (fun i => IsDirtyAnd n G (patch C j g) i)) ↔
  k ∈ (Finset.range C.gates.length).filter (fun i => IsDirtyAnd n G C i)
 rw [Finset.mem_filter, Finset.mem_filter]
 simp only [Finset.mem_range, IsDirtyAnd, IsDirty, patch_length,
  gateAt_patch_ne C j k g hne, patch_gateVal_eq_of_not_inCone hAO hAO' k hne hCone]
end Patch
namespace SoleReader
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
open Lift
end SoleReader
namespace IndependentDescent
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
def product {n : ℕ} (P Q : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
 decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)
def Safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (P Q : Finset (Fin n)) (w : Fin n) : Prop :=
 ∀ x : Fin n → Bool, product P Q x = true → x w = true → graphFun G ∅ x = true
def leftCenters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (P Q : Finset (Fin n)) : Finset (Fin n) :=
 P.filter fun p => ∀ q ∈ Q, G.Adj p q
def rightCenters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (P Q : Finset (Fin n)) : Finset (Fin n) :=
 Q.filter fun q => ∀ p ∈ P, G.Adj p q
def Useful {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (P Q : Finset (Fin n)) (u v : Fin n) : Prop :=
 G.Adj u v ∧ product P Q (pairInput u v) = true ∧
  (Safe G P Q u ∨ Safe G P Q v)
lemma product_true {n : ℕ} (P Q : Finset (Fin n)) (x : Fin n → Bool) :
  product P Q x = true ↔ (∃ p ∈ P, x p = true) ∧ ∃ q ∈ Q, x q = true := by
 simp [product]
lemma wmax_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ) (P Q : Finset (Fin n))
  (heval : ∀ x : Fin n → Bool, gateVal n C g x = product P Q x) (w : Fin n) :
  w ∈ wmax G C g ↔ Safe G P Q w := by
 simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and, Safe]
 simp_rw [heval]
lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
  graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
 simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
  Bool.false_or, decide_eq_true_eq, pairInput]
 constructor
 ·rintro ⟨a, b, hab, ha, hb⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  ·exact (G.irrefl hab).elim
  ·exact hab
  ·exact hab.symm
  ·exact (G.irrefl hab).elim
 ·intro h
  exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma safe_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (P Q : Finset (Fin n)) {z : Fin n} (hz : z ∈ P) :
  Safe G P Q z ↔ ∀ q ∈ Q, G.Adj z q := by
 constructor
 ·intro hs q hq
  apply (graph_pair G z q).mp
  apply hs
  ·exact (product_true P Q _).mpr ⟨⟨z, hz, by simp [pairInput]⟩,
    q, hq, by simp [pairInput]⟩
  ·simp [pairInput]
 ·intro hadj x hp hxz
  obtain ⟨_, q, hq, hxq⟩ := (product_true P Q x).mp hp
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
   Bool.false_or, decide_eq_true_eq]
  exact ⟨z, q, hadj q hq, hxz, hxq⟩
lemma safe_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (P Q : Finset (Fin n)) {z : Fin n} (hz : z ∈ Q) :
  Safe G P Q z ↔ ∀ p ∈ P, G.Adj p z := by
 constructor
 ·intro hs p hp
  apply (graph_pair G p z).mp
  apply hs
  ·exact (product_true P Q _).mpr ⟨⟨p, hp, by simp [pairInput]⟩,
    z, hz, by simp [pairInput]⟩
  ·simp [pairInput]
 ·intro hadj x hp hxz
  obtain ⟨⟨p, hp, hxp⟩, _⟩ := (product_true P Q x).mp hp
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
   Bool.false_or, decide_eq_true_eq]
  exact ⟨p, z, hadj p hp, hxp, hxz⟩
lemma left_centers_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (P Q : Finset (Fin n)) (h4 : NoFourCycle G) (hQ : 2 ≤ Q.card) :
  (leftCenters G P Q).card ≤ 1 := by
 apply Finset.card_le_one.mpr
 intro u hu v hv
 by_contra hne
 obtain ⟨_, huQ⟩ := Finset.mem_filter.mp hu
 obtain ⟨_, hvQ⟩ := Finset.mem_filter.mp hv
 have hsub : Q ⊆ Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w := by
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huQ w hw, hvQ w hw⟩
 have hc := (Finset.card_le_card hsub).trans (h4 u v hne)
 omega
lemma right_centers_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (P Q : Finset (Fin n)) (h4 : NoFourCycle G) (hP : 2 ≤ P.card) :
  (rightCenters G P Q).card ≤ 1 := by
 apply Finset.card_le_one.mpr
 intro u hu v hv
 by_contra hne
 obtain ⟨_, huP⟩ := Finset.mem_filter.mp hu
 obtain ⟨_, hvP⟩ := Finset.mem_filter.mp hv
 have hsub : P ⊆ Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w := by
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (huP w hw).symm, (hvP w hw).symm⟩
 have hc := (Finset.card_le_card hsub).trans (h4 u v hne)
 omega
lemma pair_cross {n : ℕ} (P Q : Finset (Fin n)) (hdis : Disjoint P Q)
  (u v : Fin n) (hprod : product P Q (pairInput u v) = true) :
  (u ∈ P ∧ v ∈ Q) ∨ (v ∈ P ∧ u ∈ Q) := by
 obtain ⟨⟨p, hp, hxp⟩, q, hq, hxq⟩ := (product_true P Q _).mp hprod
 simp only [pairInput, decide_eq_true_eq] at hxp hxq
 rcases hxp with rfl | rfl <;> rcases hxq with rfl | rfl
 ·exact (Finset.disjoint_left.mp hdis hp hq).elim
 ·exact Or.inl ⟨hp, hq⟩
 ·exact Or.inr ⟨hp, hq⟩
 ·exact (Finset.disjoint_left.mp hdis hp hq).elim
lemma useful_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (P Q : Finset (Fin n)) (hdis : Disjoint P Q) (u v : Fin n)
  (huv : Useful G P Q u v) :
  ∃ z, (z = u ∨ z = v) ∧
   (z ∈ leftCenters G P Q ∨ z ∈ rightCenters G P Q) := by
 obtain ⟨_, hp, hu | hv⟩ := huv
 ·rcases pair_cross P Q hdis u v hp with ⟨hup, hvq⟩ | ⟨hvp, huq⟩
  ·exact ⟨u, Or.inl rfl, Or.inl (Finset.mem_filter.mpr
    ⟨hup, (safe_left G P Q hup).mp hu⟩)⟩
  ·exact ⟨u, Or.inl rfl, Or.inr (Finset.mem_filter.mpr
    ⟨huq, (safe_right G P Q huq).mp hu⟩)⟩
 ·rcases pair_cross P Q hdis u v hp with ⟨hup, hvq⟩ | ⟨hvp, huq⟩
  ·exact ⟨v, Or.inr rfl, Or.inr (Finset.mem_filter.mpr
    ⟨hvq, (safe_right G P Q hvq).mp hv⟩)⟩
  ·exact ⟨v, Or.inr rfl, Or.inl (Finset.mem_filter.mpr
    ⟨hvp, (safe_left G P Q hvp).mp hv⟩)⟩
lemma decomposition {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (P Q : Finset (Fin n)) (h4 : NoFourCycle G) (hdis : Disjoint P Q)
  (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card) :
  (∃ z ∈ P, ∃ zp ∈ Q, G.Adj z zp ∧
   (∀ p ∈ P, G.Adj p zp) ∧ (∀ q ∈ Q, G.Adj z q)) ∨
  (∃ z ∈ P, (∀ q ∈ Q, G.Adj z q) ∧
   ∀ u v, Useful G P Q u v → pairInput u v z = true) ∨
  (∃ z ∈ Q, (∀ p ∈ P, G.Adj p z) ∧
   ∀ u v, Useful G P Q u v → pairInput u v z = true) ∨
  (∀ u v, ¬ Useful G P Q u v) := by
 classical
 by_cases hL : (leftCenters G P Q).Nonempty
 ·obtain ⟨z, hz⟩ := hL
  obtain ⟨hzP, hzQ⟩ := Finset.mem_filter.mp hz
  by_cases hR : (rightCenters G P Q).Nonempty
  ·obtain ⟨zp, hzp⟩ := hR
   obtain ⟨hzpQ, hzpP⟩ := Finset.mem_filter.mp hzp
   exact Or.inl ⟨z, hzP, zp, hzpQ, hzQ zp hzpQ, hzpP, hzQ⟩
  ·refine Or.inr (Or.inl ⟨z, hzP, hzQ, ?_⟩)
   intro u v huv
   obtain ⟨w, hw, hwL | hwR⟩ := useful_center G P Q hdis u v huv
   ·have heq : w = z := Finset.card_le_one.mp (left_centers_card G P Q h4 hQ) w hwL z hz
    subst w
    simpa [pairInput] using hw
   ·exact (hR ⟨w, hwR⟩).elim
 ·by_cases hR : (rightCenters G P Q).Nonempty
  ·obtain ⟨z, hz⟩ := hR
   obtain ⟨hzQ, hzP⟩ := Finset.mem_filter.mp hz
   refine Or.inr (Or.inr (Or.inl ⟨z, hzQ, hzP, ?_⟩))
   intro u v huv
   obtain ⟨w, hw, hwL | hwR⟩ := useful_center G P Q hdis u v huv
   ·exact (hL ⟨w, hwL⟩).elim
   ·have heq : w = z := Finset.card_le_one.mp (right_centers_card G P Q h4 hP) w hwR z hz
    subst w
    simpa [pairInput] using hw
  ·refine Or.inr (Or.inr (Or.inr ?_))
   intro u v huv
   obtain ⟨w, _, hwL | hwR⟩ := useful_center G P Q hdis u v huv
   ·exact hL ⟨w, hwL⟩
   ·exact hR ⟨w, hwR⟩
lemma clean_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (P Q : Finset (Fin n)) (z : Fin n) (hzP : z ∈ P)
  (hzQ : ∀ q ∈ Q, G.Adj z q) :
  (∀ x, product {z} Q x = true → product P Q x = true) ∧
  (∀ x, product {z} Q x = true → graphFun G ∅ x = true) ∧
  (∀ u v, product P Q (pairInput u v) = true → pairInput u v z = true →
   product {z} Q (pairInput u v) = true) := by
 have hf : ∀ x, product {z} Q x = true ↔ x z = true ∧ ∃ q ∈ Q, x q = true := by
  intro x
  simp [product_true]
 refine ⟨?_, ?_, ?_⟩
 ·intro x hx
  obtain ⟨hxz, hq⟩ := (hf x).mp hx
  exact (product_true P Q x).mpr ⟨⟨z, hzP, hxz⟩, hq⟩
 ·intro x hx
  obtain ⟨hxz, q, hq, hxq⟩ := (hf x).mp hx
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
   Bool.false_or, decide_eq_true_eq]
  exact ⟨z, q, hzQ q hq, hxz, hxq⟩
 ·intro u v hp hz
  exact (hf _).mpr ⟨hz, ((product_true P Q _).mp hp).2⟩
lemma clean_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (P Q : Finset (Fin n)) (z : Fin n) (hzQ : z ∈ Q)
  (hzP : ∀ p ∈ P, G.Adj p z) :
  (∀ x, product P {z} x = true → product P Q x = true) ∧
  (∀ x, product P {z} x = true → graphFun G ∅ x = true) ∧
  (∀ u v, product P Q (pairInput u v) = true → pairInput u v z = true →
   product P {z} (pairInput u v) = true) := by
 have hf : ∀ x, product P {z} x = true ↔ (∃ p ∈ P, x p = true) ∧ x z = true := by
  intro x
  simp [product_true]
 refine ⟨?_, ?_, ?_⟩
 ·intro x hx
  obtain ⟨hp, hxz⟩ := (hf x).mp hx
  exact (product_true P Q x).mpr ⟨hp, z, hzQ, hxz⟩
 ·intro x hx
  obtain ⟨⟨p, hp, hxp⟩, hxz⟩ := (hf x).mp hx
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
   Bool.false_or, decide_eq_true_eq]
  exact ⟨p, z, hzP p hp, hxp, hxz⟩
 ·intro u v hp hz
  exact (hf _).mpr ⟨((product_true P Q _).mp hp).1, hz⟩
end IndependentDescent
namespace IndependentObstruction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm
abbrev G : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 1), (2, 3)]
def C : Circuit :=
 {gates :=
   [ ⟨GateOp.or, [3, 0]⟩,
    ⟨GateOp.or, [3, 1]⟩,
    ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.and, [4, 7]⟩,
    ⟨GateOp.and, [2, 6]⟩,
    ⟨GateOp.and, [1, 8]⟩,
    ⟨GateOp.or, [9, 10]⟩ ],
  output := 11 }
def D : Circuit := { C with output := 9 }
end IndependentObstruction
namespace Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
def wireStep (w : List Bool) (g : Gate) : List Bool :=
 w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
  (gs.foldl wireStep acc).length = acc.length + gs.length := by
 induction gs generalizing acc with
 | nil => simp
 | cons g gs ih =>
  simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
  omega
lemma wires_length (C : Circuit) (x : List Bool) :
  (C.wires x).length = x.length + C.gates.length := by
 exact foldl_wireStep_length C.gates x
lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
  gateAt C k = C.gates[k] := by
 unfold gateAt
 rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
 rfl
lemma foldl_coneStep_length (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
  (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
 induction gs generalizing acc with
 | nil => simp
 | cons g gs ih =>
  simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
  omega
lemma foldl_coneStep_prefix (n : ℕ) (gs : List Gate) (acc : List (List ℕ))
  (j : ℕ) (hj : j < acc.length) :
  (gs.foldl (coneStep n) acc).getD j [] = acc.getD j [] := by
 induction gs generalizing acc with
 | nil => rfl
 | cons g gs ih =>
  have hj' : j < (coneStep n acc g).length := by
   simp only [coneStep, List.length_append, List.length_singleton]
   omega
  rw [List.foldl_cons, ih (coneStep n acc g) hj']
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp only [coneStep, List.getElem?_append_left hj]
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
  InCone n C i j ↔
   ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
 have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
  have h1 := List.take_append_drop j C.gates
  have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
  rw [h2] at h1
  simp only [List.append_assoc, List.singleton_append, h1]
 set acc := (C.gates.take j).foldl (coneStep n) [] with hacc
 have hacc_len : acc.length = j := by
  rw [hacc, foldl_coneStep_length, List.length_nil, List.length_take]
  omega
 have hpref : ∀ k < j, (cones n C).getD k [] = acc.getD k [] := by
  intro k hk
  unfold cones
  conv_lhs => rw [← List.take_append_drop j C.gates]
  rw [List.foldl_append, ← hacc]
  exact foldl_coneStep_prefix n (C.gates.drop j) acc k (by omega)
 have hstep : (cones n C).getD j [] =
   ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
    (fun w => (w - n) :: acc.getD (w - n) []) := by
  unfold cones
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
  have hlen : j < (coneStep n acc C.gates[j]).length := by
   simp only [coneStep, List.length_append, List.length_singleton]
   omega
  rw [foldl_coneStep_prefix n (C.gates.drop (j + 1)) (coneStep n acc C.gates[j]) j hlen]
  rw [List.getD_eq_getElem?_getD]
  simp only [coneStep, List.getElem?_append_right (by omega : acc.length ≤ j),
   hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
   gateAt_eq_getElem C j hj]
 unfold InCone
 rw [hstep, List.mem_flatMap]
 constructor
 ·rintro ⟨w, hw, hi⟩
  rw [List.mem_filter] at hw
  have hbounds : n ≤ w ∧ w < n + j := by simpa using hw.2
  rw [List.mem_cons] at hi
  refine ⟨w, hw.1, hbounds.1, hbounds.2, ?_⟩
  rcases hi with rfl | hi
  ·exact Or.inl rfl
  ·right
   rw [hpref (w - n) (by omega)]
   exact hi
 ·rintro ⟨w, hw, hnw, hlt, hi⟩
  refine ⟨w, ?_, ?_⟩
  ·rw [List.mem_filter]
   exact ⟨hw, by simpa using And.intro hnw hlt⟩
  ·rw [List.mem_cons]
   rcases hi with rfl | hi
   ·exact Or.inl rfl
   ·right
    rw [← hpref (w - n) (by omega)]
    exact hi
end Normalize
namespace Cases
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core
lemma edge_nonempty_of_junk_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C : Circuit) (hL : IsLeastAO G C) (hJ : (junk G C).Nonempty) :
  G.edgeFinset.Nonempty := by
 by_contra hE
 have hnone : ∀ u v : Fin n, ¬ G.Adj u v := by
  intro u v huv
  exact hE ⟨s(u,v), by simpa using huv⟩
 let D : Circuit := ⟨[], n⟩
 have hD : IsAO2 n D := by simp [IsAO2, AndOrOnly, ReadsBack, D]
 have hDF : circuitFun n D = graphFun G ∅ := by
  funext x
  simp [circuitFun, Circuit.eval, Circuit.wires, D, graphFun, hnone]
 have hsize := hL.2.2 D hD hDF
 obtain ⟨j, hj⟩ := hJ
 have hjlt : j < C.gates.length := by
  exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
 simp only [Circuit.size, D, List.length_nil] at hsize
 omega
end Cases
namespace CleanReplacement
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
 PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
 PEqualNP.CleanedNonEdge PEqualNP.TopForm
def gateBit (w : List Bool) (g : Gate) : Bool :=
 g.op.eval (g.inputs.map fun i => w.getD i false)
def stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]
def WiresLE (w z : List Bool) : Prop :=
 w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true
def IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or
lemma monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
  IsMonoGate g := by
 simpa [IsMonoGate] using (hC g hg).1
lemma bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
  (hw : gateBit w g = true) : gateBit z g = true := by
 rcases hg with hop | hop
 ·simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
   Function.comp_apply, id_eq] at hw ⊢
  exact fun i hi => h.2 i (hw i hi)
 ·simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
   Function.comp_apply, id_eq] at hw ⊢
  obtain ⟨i, hi, hv⟩ := hw
  exact ⟨i, hi, h.2 i hv⟩
lemma append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
  (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
 refine ⟨by simp [h.1], ?_⟩
 intro i hi
 rw [List.getD_eq_getElem?_getD] at hi ⊢
 by_cases hlt : i < w.length
 ·rw [List.getElem?_append_left hlt] at hi
  rw [List.getElem?_append_left (by rwa [← h.1])]
  simpa only [List.getD_eq_getElem?_getD] using h.2 i
   (by simpa only [List.getD_eq_getElem?_getD] using hi)
 ·rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
  rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
  cases hd : i - w.length with
  | zero =>
   simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
   exact hab hi
  | succ k => simp [hd] at hi
lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
  {w z : List Bool} (h : WiresLE w z) :
  WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
 induction gs generalizing w z with
 | nil => exact h
 | cons g gs ih =>
  exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
   (append_mono h (bit_mono h (hg g (by simp))))
lemma fold_length (gs : List Gate) (w : List Bool) :
  (gs.foldl stepWire w).length = w.length + gs.length := by
 induction gs generalizing w with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons, ih]
  simp [stepWire]
  omega
lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
  (gs.foldl stepWire w).getD i false = w.getD i false := by
 induction gs generalizing w with
 | nil => rfl
 | cons g gs ih =>
  simp only [List.foldl_cons]
  rw [ih (stepWire w g) (by simp [stepWire]; omega)]
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
  (List.ofFn x).getD u.val false = x u := by
 simp [List.getD_eq_getElem?_getD]
lemma ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
  WiresLE (List.ofFn x) (List.ofFn y) := by
 refine ⟨by simp, ?_⟩
 intro i hi
 by_cases hlt : i < n
 ·rw [ofFn_getD y ⟨i, hlt⟩]
  exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
 ·rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
  cases hi
def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩
def earlierWires (C : Circuit) (j : ℕ) (w : List Bool) : List Bool :=
 (C.gates.take j).foldl stepWire w
def off : Gate := ⟨GateOp.or, []⟩
def edgeGate {n : ℕ} (u v : Fin n) : Gate := ⟨GateOp.and, [u.val, v.val]⟩
lemma off_bit (w : List Bool) : gateBit w off = false := rfl
lemma edge_bit {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (u v : Fin n) :
  gateBit (earlierWires C j (List.ofFn x)) (edgeGate u v) = (x u && x v) := by
 simp only [gateBit, edgeGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
  List.all_nil, id_eq, Bool.and_true]
 unfold earlierWires
 rw [fold_getD_lt _ _ _ (by simp), fold_getD_lt _ _ _ (by simp),
  ofFn_getD, ofFn_getD]
lemma wires_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) (w : List Bool) :
  (patch C j g).wires w = (C.gates.drop (j + 1)).foldl stepWire (stepWire (earlierWires C j w) g) := by
 change (C.gates.set j g).foldl stepWire w = _
 rw [List.set_eq_take_append_cons_drop, ite_eq_left hj, List.foldl_append, List.foldl_cons]
 rfl
lemma original_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
  patch C j C.gates[j] = C := by
 cases C with
 | mk gates output =>
  change Circuit.mk (gates.set j gates[j]) output = Circuit.mk gates output
  congr 1
  exact List.set_getElem_self hj
lemma patch_mono {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j < C.gates.length)
  (g h : Gate) (w : List Bool)
  (hbit : gateBit (earlierWires C j w) g = true → gateBit (earlierWires C j w) h = true) :
  WiresLE ((patch C j g).wires w) ((patch C j h).wires w) := by
 rw [wires_patch hj, wires_patch hj]
 apply fold_mono _ (fun k hk => monoGate_of_mem hC (List.mem_of_mem_drop hk))
 exact append_mono ⟨rfl, fun _ h => h⟩ hbit
lemma patch_bit {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
  (g : Gate) (x : Fin n → Bool) :
  gateVal n (patch C j g) j x = gateBit (earlierWires C j (List.ofFn x)) g := by
 have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
  unfold earlierWires
  rw [fold_length]
  simp [Nat.min_eq_left (Nat.le_of_lt hj)]
 unfold gateVal
 rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]), ← hlen]
 simp [stepWire, List.getD_eq_getElem?_getD]
lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
  gateAt (patch C j g) k = gateAt C k := by
 simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]
lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (x : Fin n → Bool) :
  graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
 simp [graphFun]
lemma pair_le {n : ℕ} {x : Fin n → Bool} {u v : Fin n}
  (hu : x u = true) (hv : x v = true) (k : Fin n) :
  pairInput u v k = true → x k = true := by
 simp only [pairInput, decide_eq_true_eq]
 rintro (rfl | rfl)
 ·exact hu
 ·exact hv
lemma circuit_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
  (hxy : ∀ u, x u = true → y u = true) :
  circuitFun n C x = true → circuitFun n C y = true :=
 (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 C.output
lemma mem_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j : ℕ} :
  j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
 unfold junk gatesWhere
 rw [Finset.mem_filter, Finset.mem_range]
lemma ao2_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
 intro g hg
 exact ⟨by simpa using hAO.1 g hg, Nat.le_of_eq (hAO.2.2 g hg)⟩
lemma no_clean_independent_replacement {n : ℕ} (G : SimpleGraph (Fin n))
  [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
  (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
  {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
  (hCone : ¬ InCone n C j k) (R : Gate)
  (hOp : R.op = GateOp.and ∨ R.op = GateOp.or)
  (hLen : R.inputs.length = 2) (hBack : ∀ w ∈ R.inputs, w < n + j)
  (hClean : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
   gateBit (earlierWires C j (List.ofFn x)) R = false)
  (hCover : ∀ u v : Fin n, G.Adj u v →
   circuitFun n (patch C j off) (pairInput u v) = false →
   gateBit (earlierWires C j (List.ofFn (pairInput u v))) R = true) : False := by
 have hjmem : j ∈ junk G C := by rw [hJ]; simp
 have hkmem : k ∈ junk G C := by rw [hJ]; simp
 have hj : j < C.gates.length := (mem_junk.mp hjmem).1
 have hmono : Monotone2 C := ao2_mono hL.1
 let D := patch C j R
 have hDAO : IsAO2 n D := Patch.patch_isAO2 hL.1 j R hOp hLen hBack
 have hDM : Monotone2 D := ao2_mono hDAO
 have hnegative (x : Fin n → Bool) (hf : graphFun G ∅ x = false) :
   WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
  have h := patch_mono hmono hj R C.gates[j] (List.ofFn x)
   (by intro hh; rw [hClean x hf] at hh; cases hh)
  rwa [original_patch hj] at h
 have hEdges (u v : Fin n) (huv : G.Adj u v) :
   circuitFun n D (pairInput u v) = true := by
  have hF : circuitFun n C (pairInput u v) = true := by
   rw [hL.2.1]
   exact (graph_true G _).mpr ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩
  cases hCut : circuitFun n (patch C j off) (pairInput u v) with
  | false =>
   have h := patch_mono hmono hj C.gates[j] R (List.ofFn (pairInput u v))
    (fun _ => hCover u v huv hCut)
   rw [original_patch hj] at h
   exact h.2 C.output hF
  | true =>
   exact (patch_mono hmono hj off R (List.ofFn (pairInput u v))
    (by intro hh; simp [off_bit] at hh)).2 C.output hCut
 have hDF : circuitFun n D = graphFun G ∅ := by
  funext x
  cases hf : graphFun G ∅ x with
  | false =>
   cases hd : circuitFun n D x with
   | false => rfl
   | true =>
    have hh : circuitFun n C x = true := (hnegative x hf).2 C.output hd
    rw [hL.2.1,hf] at hh
    cases hh
  | true =>
   obtain ⟨u,v,huv,hu,hv⟩ := (graph_true G x).mp hf
   exact circuit_mono hDM (pair_le hu hv) (hEdges u v huv)
 have hNoJ : j ∉ junk G D := by
  intro hmem
  obtain ⟨_,_,_,x,hx,hf⟩ := mem_junk.mp hmem
  change gateVal n (patch C j R) j x = true at hx
  rw [patch_bit hj, hClean x hf] at hx
  cases hx
 have hSub : junk G D ⊆ junk G C := by
  intro a ha
  have hja : j ≠ a := by intro he; exact hNoJ (he.symm ▸ ha)
  obtain ⟨haLen,haAnd,_,x,hx,hf⟩ := mem_junk.mp ha
  have haC : a < C.gates.length := by simpa [D,patch] using haLen
  have haOp : (gateAt C a).op = GateOp.and := by
   change (gateAt (patch C j R) a).op = GateOp.and at haAnd
   rwa [gateAt_patch_ne C j a R hja] at haAnd
  exact mem_junk.mpr ⟨haC,haOp,haC,x,(hnegative x hf).2 (n+a) hx,hf⟩
 have hkD : k ∈ junk G D :=
  (Patch.patch_junk_mem_iff_of_not_inCone hL.1 hDAO hne hCone).mpr hkmem
 have hJD : junk G D = {k} := by
  apply Finset.ext
  intro a
  constructor
  ·intro ha
   have hao := hSub ha
   rw [hJ] at hao
   simp only [Finset.mem_insert,Finset.mem_singleton] at hao ⊢
   rcases hao with rfl | he
   ·exact (hNoJ ha).elim
   ·exact he
  ·intro ha
   have he := Finset.mem_singleton.mp ha
   exact he ▸ hkD
 have hDL : IsLeastAO G D := Patch.patch_isLeastAO hL hDAO hDF
 exact hOne D hDL (by rw [hJD]; simp)
end CleanReplacement
namespace FlagReduction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
open CleanReplacement IndependentDescent
lemma earlier_wire_eq {n : ℕ} (C : Circuit) (j : ℕ) (hj : j ≤ C.gates.length)
  (x : Fin n → Bool) {w : ℕ} (hw : w < n + j) :
  (earlierWires C j (List.ofFn x)).getD w false = wval C x w := by
 have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
  unfold earlierWires
  rw [fold_length]
  simp [Nat.min_eq_left hj]
 have hsplit : C.wires (List.ofFn x) =
   (C.gates.drop j).foldl stepWire (earlierWires C j (List.ofFn x)) := by
  change C.gates.foldl stepWire _ = _
  conv_lhs => rw [← List.take_append_drop j C.gates, List.foldl_append]
  rfl
 unfold wval
 rw [hsplit, fold_getD_lt _ _ _ (by omega)]
lemma star_gate_bit {n : ℕ} (C : Circuit) (j : ℕ) (hj : j ≤ C.gates.length)
  (z : Fin n) (w : ℕ) (hw : w < n + j) (x : Fin n → Bool) :
  gateBit (earlierWires C j (List.ofFn x)) ⟨GateOp.and,[z.val,w]⟩ =
   (x z && wval C x w) := by
 simp only [gateBit, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
  List.all_nil, id_eq, Bool.and_true]
 rw [earlier_wire_eq C j hj x (by have := z.isLt; omega),
  earlier_wire_eq C j hj x hw, Lift.wval_input C x z.val z.isLt]
lemma filtered_independent_is_cross_star {n : ℕ} (G : SimpleGraph (Fin n))
  [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C)
  (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
  {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
  (hCone : ¬ InCone n C j k) (P Q : Finset (Fin n))
  (h4 : NoFourCycle G) (hdis : Disjoint P Q) (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card)
  (hRawP : ∀ x : Fin n → Bool,
   wval C x (opnd C j 0) = decide (∃ p ∈ P, x p = true))
  (hRawQ : ∀ x : Fin n → Bool,
   wval C x (opnd C j 1) = decide (∃ q ∈ Q, x q = true))
  (hCritical : ∀ u v : Fin n, G.Adj u v →
   circuitFun n (patch C j off) (pairInput u v) = false → Useful G P Q u v) :
  ∃ z ∈ P, ∃ zp ∈ Q, G.Adj z zp ∧
   (∀ p ∈ P, G.Adj p zp) ∧ (∀ q ∈ Q, G.Adj z q) := by
 have hjmem : j ∈ junk G C := by rw [hJ]; simp
 have hj : j < C.gates.length := (mem_junk.mp hjmem).1
 have hOpnd (b : Fin 2) : opnd C j b < n + j := Lift.opnd_lt hL.1 hj b
 rcases decomposition G P Q h4 hdis hP hQ with
  hFlag | ⟨z,hzP,hzQ,hzCover⟩ | ⟨z,hzQ,hzP,hzCover⟩ | hNone
 ·exact hFlag
 ·exfalso
  apply no_clean_independent_replacement G C hL hOne hne hJ hCone
   ⟨GateOp.and,[z.val,opnd C j 1]⟩ (Or.inl rfl) rfl
  ·intro w hw
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
   rcases hw with rfl | rfl
   ·have := z.isLt; omega
   ·exact hOpnd 1
  ·intro x hf
   rw [star_gate_bit C j (Nat.le_of_lt hj) z _ (hOpnd 1) x, hRawQ x]
   apply Bool.eq_false_iff.mpr
   intro ht
   have hc := (clean_left G P Q z hzP hzQ).2.1 x
   have hp : product {z} Q x = true := by simpa [product] using ht
   have := hc hp
   rw [hf] at this
   cases this
  ·intro u v huv hCut
   have hUse := hCritical u v huv hCut
   rw [star_gate_bit C j (Nat.le_of_lt hj) z _ (hOpnd 1) _, hRawQ]
   have hp := (clean_left G P Q z hzP hzQ).2.2 u v hUse.2.1 (hzCover u v hUse)
   simpa [product] using hp
 ·exfalso
  apply no_clean_independent_replacement G C hL hOne hne hJ hCone
   ⟨GateOp.and,[z.val,opnd C j 0]⟩ (Or.inl rfl) rfl
  ·intro w hw
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
   rcases hw with rfl | rfl
   ·have := z.isLt; omega
   ·exact hOpnd 0
  ·intro x hf
   rw [star_gate_bit C j (Nat.le_of_lt hj) z _ (hOpnd 0) x, hRawP x]
   apply Bool.eq_false_iff.mpr
   intro ht
   have hc := (clean_right G P Q z hzQ hzP).2.1 x
   have hp : product P {z} x = true := by simpa [product,Bool.and_comm] using ht
   have := hc hp
   rw [hf] at this
   cases this
  ·intro u v huv hCut
   have hUse := hCritical u v huv hCut
   rw [star_gate_bit C j (Nat.le_of_lt hj) z _ (hOpnd 0) _, hRawP]
   have hp := (clean_right G P Q z hzQ hzP).2.2 u v hUse.2.1 (hzCover u v hUse)
   simpa [product,Bool.and_comm] using hp
 ·exfalso
  obtain ⟨e,he⟩ := Cases.edge_nonempty_of_junk_nonempty G C hL ⟨j,hjmem⟩
  obtain ⟨u,v,huv⟩ : ∃ u v : Fin n, G.Adj u v := by
   revert he
   refine Sym2.inductionOn e ?_
   intro u v he
   exact ⟨u,v,by simpa using he⟩
  apply no_clean_independent_replacement G C hL hOne hne hJ hCone
   (edgeGate u v) (Or.inl rfl) rfl
  ·intro w hw
   simp only [edgeGate,List.mem_cons,List.not_mem_nil,or_false] at hw
   rcases hw with rfl | rfl <;> omega
  ·intro x hf
   rw [edge_bit]
   apply Bool.eq_false_iff.mpr
   intro ht
   simp only [Bool.and_eq_true] at ht
   obtain ⟨hu,hv⟩ := ht
   have := (graph_true G x).mpr ⟨u,v,huv,hu,hv⟩
   rw [hf] at this
   cases this
  ·intro a b hab hCut
   exact (hNone a b (hCritical a b hab hCut)).elim
end FlagReduction
namespace RawOperands
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def stepWire (w : List Bool) (g : Gate) : List Bool :=
 w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
  C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
  (gs.foldl stepWire w).length = w.length + gs.length := by
 induction gs generalizing w with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons, ih]
  simp [stepWire]
  omega
lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
  (gs.foldl stepWire w).getD i false = w.getD i false := by
 induction gs generalizing w with
 | nil => rfl
 | cons g gs ih =>
  simp only [List.foldl_cons]
  have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
  rw [ih (stepWire w g) hlt]
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
  w.getD i false = false := by
 simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
  (C.wires (List.ofFn x)).length = n + C.gates.length := by
 rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
  ∃ (pre post : List Gate) (gj : Gate),
   gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
 refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
 rw [List.cons_getElem_drop_succ, List.take_append_drop]
def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
 (C.wires (List.ofFn x)).getD u false
lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
 simp [gateAt, List.getD_eq_getElem?_getD, hk]
lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
  W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
   if i < n + k then W n C x i else false) := by
 obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
 have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
 rw [hga]
 let w0 := pre.foldl stepWire (List.ofFn x)
 have hw0_len : w0.length = n + k := by
  simp [w0, foldl_stepWire_length, hpre_len]
 have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
  simp only [W]
  rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
  rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
  simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
 rw [hCj]
 congr 1
 refine List.map_congr_left fun i _ => ?_
 by_cases hi : i < n + k
 ·simp only [hi, ↓reduceIte]
  simp only [W]
  rw [wires_eq_foldl, hgs, List.foldl_append]
  exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
 ·simp only [hi, ↓reduceIte]
  exact getD_ge_length w0 i (by omega)
lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
  W n C x u = x ⟨u, hu⟩ := by
 simp only [W]
 rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
 simp [List.getD_eq_getElem?_getD, hu]
open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
  (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
 induction gs generalizing cs with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons, ih]
  simp [orStep]
  omega
open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
  x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
   ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
 by_cases h : g.op = GateOp.or
 ·simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
   ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
   List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  constructor
  ·rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
   ·exact Or.inl h1
   ·exact Or.inr ⟨w, hw, hn, hlt, hx⟩
  ·rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
   ·exact Or.inl h1
   ·exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
 ·simp [orStep, List.getD_eq_getElem?_getD, h]
open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
  (orStep n cs g).getD m [] = cs.getD m [] := by
 simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
  (hk : k < cs.length) :
  (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
 induction gs generalizing cs with
 | nil => rfl
 | cons g gs ih =>
  simp only [List.foldl_cons]
  rw [ih (orStep n cs g) (by simp [orStep]; omega)]
  exact orStep_getD_lt n cs g k hk
open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
  x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
   ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
 obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
 have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
 rw [hga]
 have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
  simp only [orSets]
  rw [hgs, List.foldl_append, List.foldl_cons]
 have hl0 : (pre.foldl (orStep n) []).length = k := by
  rw [orFold_length]; simp [hpre_len]
 have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
  simp [orStep, hl0]
 have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
  rw [hc, orFold_getD_lt n post _ k (by omega)]
 have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
  intro m hm
  rw [hc, orFold_getD_lt n post _ m (by omega)]
  exact orStep_getD_lt n _ gk m (by omega)
 have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
 rw [hl0] at h3
 rw [h1, h3]
 constructor
 ·rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
  ·exact Or.inl h
  ·exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
 ·rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
  ·exact Or.inl h
  ·exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩
lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
  (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
  (hlt : i < n + r) (hv : W n C x i = true) : W n C x (n + r) = true := by
 rw [W_gate n C x r hr, hop]
 simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
 exact ⟨i, hi, by rw [ite_eq_left hlt]; exact hv⟩
open PEqualNP.CleanedNonEdge in
lemma reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
  (hv : W n C x (n + g) = true) :
  ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → W n C x (n + k) = true := by
 intro k
 induction k using Nat.strong_induction_on with
 | _ k ih =>
  intro hk hmem
  rcases (orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
  ·rw [← h]; exact hv
  ·have h3 := ih (w - n) (by omega) (by omega) hx
   have e : n + (w - n) = w := by omega
   rw [e] at h3
   exact W_or n C x k hk hop w hw hlt h3
open PEqualNP.CleanedNonEdge in
lemma reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
  (h : OrReaches n C w g) (hv : W n C x (n + g) = true) : W n C x w = true := by
 obtain ⟨hn, hmem⟩ := h
 by_cases hk : w - n < C.gates.length
 ·have h3 := reach_val n C x g hv (w - n) hk hmem
  have e : n + (w - n) = w := by omega
  rw [e] at h3
  exact h3
 ·exfalso
  have hlen : (orSets n C).length = C.gates.length := by
   unfold orSets; rw [orFold_length]; simp
  have hge : (orSets n C).length ≤ w - n := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
  simp at hmem
lemma mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
  (h : a ∈ @Finset.filter α p d s) : p a :=
 ((@Finset.mem_filter α p d s a).mp h).2
lemma side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
  (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
  W n C x (PEqualNP.TopForm.opnd C j b) = true := by
 unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
 have hi2 := mem_filter_gen _ _ _ _ hi
 rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
 ·rw [← h, W_input n C x i.val i.isLt]; exact hx
 ·have hk1 : W n C x (n + k) = true := by
   apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
   rw [W_input n C x i.val i.isLt]; exact hx
  exact reach_up n C x _ k hreach hk1
open PEqualNP.EdgeOwnership in
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
  (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
 induction gs generalizing cs with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons, ih]
  simp [coneStep]
  omega
open PEqualNP.EdgeOwnership in
lemma cones_char (n : ℕ) (gs : List Gate) :
  ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
   j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
    (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
 induction gs using List.reverseRecOn with
 | nil => intro i j; simp
 | append_singleton gs g ih =>
  intro i j
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
   rw [cones_len]; simp
  have key : ∀ k, k < gs.length →
    (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
     (gs.foldl (coneStep n) []).getD k [] := by
   intro k hk
   simp only [coneStep, List.getD_eq_getElem?_getD]
   rw [List.getElem?_append_left (by omega)]
  rcases Nat.lt_trichotomy j gs.length with h | h | h
  ·have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h]
   rw [key j h, ih i j, e1]
   constructor
   ·rintro ⟨_, w, hw, h1, h2, h3⟩
    refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
    rw [key (w - n) (by omega)]
    exact h3
   ·rintro ⟨_, w, hw, h1, h2, h3⟩
    refine ⟨h, w, hw, h1, h2, ?_⟩
    rw [key (w - n) (by omega)] at h3
    exact h3
  ·subst h
   have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
   have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
     (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
      (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
    simp only [coneStep, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]
   rw [e2, e1]
   simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
   constructor
   ·rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
    refine ⟨by simp, w, hw, h1, h2, ?_⟩
    rw [key (w - n) (by omega)]
    exact h3
   ·rintro ⟨_, w, hw, h1, h2, h3⟩
    rw [key (w - n) (by omega)] at h3
    exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
  ·have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
    simp only [coneStep, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl
   rw [e0]
   constructor
   ·intro h0; simp at h0
   ·rintro ⟨h0, _⟩
    simp at h0
    omega
open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
  InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
   (i = k ∨ InCone n C i k) := by
 have h := cones_char n C.gates i j
 unfold InCone cones gateAt
 rw [h]
 constructor
 ·rintro ⟨h0, w, hw, h1, h2, h3⟩
  refine ⟨h0, w - n, by omega, ?_, h3⟩
  have : n + (w - n) = w := by omega
  rw [this]
  exact hw
 ·rintro ⟨h0, k, hk, hw, h3⟩
  refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
  have : n + k - n = k := by omega
  rw [this]
  exact h3
lemma gateAt_mem' (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
 rw [gateAt_eq C j hj]; exact List.getElem_mem hj
open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
 intro j
 induction j using Nat.strong_induction_on with
 | _ j ih =>
  intro i h
  obtain ⟨_, k, hk, _, h3⟩ := (inCone_iff n C i j).mp h
  rcases h3 with h3 | h3
  ·omega
  ·have := ih k hk i h3; omega
open PEqualNP.CleanedNonEdge in
lemma orReach_trans (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
  (hop : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
  (hlt : w < n + k) (g : ℕ) (h : OrReaches n C w g) : OrReaches n C (n + k) g := by
 obtain ⟨hn, hmem⟩ := h
 refine ⟨by omega, ?_⟩
 have e : n + k - n = k := by omega
 rw [e]
 exact (orSets_mem_iff n C k g hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hmem⟩)
open PEqualNP.CleanedNonEdge in
lemma orReach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
  OrReaches n C (n + k) k := by
 refine ⟨by omega, ?_⟩
 have e : n + k - n = k := by omega
 rw [e]
 exact (orSets_mem_iff n C k k hk).mpr (Or.inl rfl)
lemma orIn_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
  i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
   PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
    (i : ℕ) ∈ (gateAt C k).inputs) := by
 unfold PEqualNP.TopForm.orIn
 simp only [Finset.mem_filter, Finset.mem_univ, true_and]
open PEqualNP.CleanedNonEdge in
lemma down (n : ℕ) (C : Circuit) (x : Fin n → Bool)
  (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
  ∀ w, W n C x w = true → (∃ i : Fin n, i ∈ PEqualNP.TopForm.orIn n C w ∧ x i = true) ∨
   ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
    W n C x (n + k) = true := by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro hv
  by_cases hwn : w < n
  ·left
   refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
   rw [← W_input n C x w hwn]; exact hv
  ·by_cases hk : w - n < C.gates.length
   ·have hw : w = n + (w - n) := by omega
    set k := w - n with hkdef
    rcases hAO k hk with hop | hop
    ·right
     refine ⟨k, hk, ?_, hop, ?_⟩
     ·rw [hw]; exact orReach_self n C k hk
     ·rw [← hw]; exact hv
    ·have hv2 := hv
     rw [hw, W_gate n C x k hk, hop] at hv2
     simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
     obtain ⟨i, hi, hiv⟩ := hv2
     split_ifs at hiv with hlt
     rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
     ·left
      refine ⟨j, ?_, hxj⟩
      rw [orIn_mem] at hj ⊢
      right
      rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
      ·refine ⟨k, hk, ?_, hop, ?_⟩
       ·rw [hw]; exact orReach_self n C k hk
       ·rw [hj]; exact hi
      ·refine ⟨k'', hk'', ?_, hop'', hin⟩
       rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
     ·right
      refine ⟨k', hk', ?_, hop', hv'⟩
      rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
   ·exfalso
    have hl := wires_length n C x
    have : W n C x w = false := getD_ge_length _ w (by omega)
    rw [this] at hv; exact Bool.false_ne_true hv
open PEqualNP.EdgeOwnership in
lemma orSets_cone (n : ℕ) (C : Circuit) : ∀ m, m < C.gates.length → ∀ k,
  k ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD m [] → k = m ∨ InCone n C k m := by
 intro m
 induction m using Nat.strong_induction_on with
 | _ m ih =>
  intro hm k hk
  rcases (orSets_mem_iff n C m k hm).mp hk with h | ⟨_, w, hw, hn, hlt, hx⟩
  ·exact Or.inl h
  ·right
   have h2 := ih (w - n) (by omega) (by omega) k hx
   have e : n + (w - n) = w := by omega
   exact (inCone_iff n C k m).mpr ⟨hm, w - n, by omega, by rw [e]; exact hw, h2⟩
open PEqualNP.EdgeOwnership in
lemma reach_cone (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (o : ℕ)
  (ho : o ∈ (gateAt C j).inputs) (hlt : o < n + j) (k : ℕ)
  (h : PEqualNP.CleanedNonEdge.OrReaches n C o k) : InCone n C k j := by
 obtain ⟨hn, hmem⟩ := h
 have h2 := orSets_cone n C (o - n) (by omega) k hmem
 have e : n + (o - n) = o := by omega
 exact (inCone_iff n C k j).mpr ⟨hj, o - n, by omega, by rw [e]; exact ho, h2⟩
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
lemma junk_data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C : Circuit) (j : ℕ) (hj : j ∈ junk G C) :
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
 obtain ⟨hjl, hja, _⟩ := Finset.mem_filter.mp hj
 exact ⟨Finset.mem_range.mp hjl, hja⟩
lemma operand_mem {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
  (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) :
  opnd C j b ∈ (gateAt C j).inputs := by
 have hlen := hAO.2.2 _ (gateAt_mem' C j hj)
 unfold opnd
 rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
 exact List.getElem_mem _
lemma raw_operand_of_no_junk_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
  (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
  (hno : ∀ k ∈ junk G C, ¬ InCone n C k j) (b : Fin 2) (x : Fin n → Bool) :
  PEqualNP.ReadTwo.wval C x (opnd C j b) =
   decide (∃ u ∈ side (n := n) C j b, x u = true) := by
 have hm := operand_mem C hAO j hj b
 have hlt := hAO.2.1 j hj _ hm
 have hi : W n C x (opnd C j b) = true ↔
   ∃ u ∈ side (n := n) C j b, x u = true := by
  constructor
  ·intro hv
   have hops : ∀ k < C.gates.length,
     (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or :=
    fun k hk => hAO.1 _ (gateAt_mem' C k hk)
   rcases down n C x hops _ hv with hraw | ⟨k, hk, hr, hop, _⟩
   ·exact hraw
   ·have hc := reach_cone n C j hj _ hm hlt k hr
    have hnb : ¬ BelowF G C k := fun hb => hTop k hk j hj hop hb hand hc
    have hd : ∃ y : Fin n → Bool, gateVal n C k y = true ∧ graphFun G ∅ y = false := by
     by_contra hn
     apply hnb
     intro y hy
     by_contra hf
     exact hn ⟨y, hy, Bool.eq_false_iff.mpr hf⟩
    have hkj : k ∈ junk G C :=
     Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, hk, hd⟩
    exact (hno k hkj hc).elim
  ·rintro ⟨u, hu, hxu⟩
   exact side_val n C x j b u hu hxu
 change W n C x (opnd C j b) = _
 by_cases hv : W n C x (opnd C j b) = true
 ·simp [hv, hi.mp hv]
 ·have hn : ¬ ∃ u ∈ side (n := n) C j b, x u = true := fun h => hv (hi.mpr h)
  simp [Bool.eq_false_iff.mpr hv, hn]
lemma independent_no_junk_ancestors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C : Circuit) (g h : ℕ) (hJ : junk G C = {g, h})
  (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
  (j : ℕ) (hj : j = g ∨ j = h) :
  ∀ k ∈ junk G C, ¬ InCone n C k j := by
 intro k hk hc
 have hkm : k = g ∨ k = h := by simpa [hJ] using hk
 rcases hj with rfl | rfl <;> rcases hkm with rfl | rfl
 ·have := inCone_lt n C _ _ hc
  omega
 ·exact hhg hc
 ·exact hgh hc
 ·have := inCone_lt n C _ _ hc
  omega
lemma independent_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
  (g h : ℕ) (hJ : junk G C = {g, h})
  (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
  (j : ℕ) (hj : j = g ∨ j = h) (b : Fin 2) (x : Fin n → Bool) :
  PEqualNP.ReadTwo.wval C x (opnd C j b) =
   decide (∃ u ∈ side (n := n) C j b, x u = true) := by
 have hjm : j ∈ junk G C := by simpa [hJ] using hj
 obtain ⟨hjl, hja⟩ := junk_data G C j hjm
 exact raw_operand_of_no_junk_cone G C hAO hTop j hjl hja
  (independent_no_junk_ancestors G C g h hJ hgh hhg j hj) b x
lemma and_gate_eq {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
  (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
  (x : Fin n → Bool) :
  gateVal n C j x =
   (PEqualNP.ReadTwo.wval C x (opnd C j 0) && PEqualNP.ReadTwo.wval C x (opnd C j 1)) := by
 obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C j hj))
 have ham : a ∈ (gateAt C j).inputs := by simp [hab]
 have hbm : b ∈ (gateAt C j).inputs := by simp [hab]
 have hba := hAO.2.1 j hj a ham
 have hbb := hAO.2.1 j hj b hbm
 change W n C x (n + j) = _
 rw [W_gate n C x j hj, hand, hab]
 simp [GateOp.eval, opnd, hab, hba, hbb, W, PEqualNP.ReadTwo.wval]
lemma independent_product {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
  (g h : ℕ) (hJ : junk G C = {g, h})
  (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
  (j : ℕ) (hj : j = g ∨ j = h) (x : Fin n → Bool) :
  gateVal n C j x =
   (decide (∃ u ∈ side (n := n) C j 0, x u = true) &&
    decide (∃ u ∈ side (n := n) C j 1, x u = true)) := by
 have hjm : j ∈ junk G C := by simpa [hJ] using hj
 obtain ⟨hjl, hja⟩ := junk_data G C j hjm
 rw [and_gate_eq C hAO j hjl hja x,
  independent_operand G C hAO hTop g h hJ hgh hhg j hj 0 x,
  independent_operand G C hAO hTop g h hJ hgh hhg j hj 1 x]
end RawOperands
namespace Critical.Base
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
def stepWire (w : List Bool) (g : Gate) : List Bool :=
 w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
  C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_length (gs : List Gate) (w : List Bool) :
  (gs.foldl stepWire w).length = w.length + gs.length := by
 induction gs generalizing w with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons, ih]
  simp [stepWire]
  omega
lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
  (gs.foldl stepWire w).getD i false = w.getD i false := by
 induction gs generalizing w with
 | nil => rfl
 | cons g gs ih =>
  simp only [List.foldl_cons]
  have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
  rw [ih (stepWire w g) hlt]
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
 simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
  (gs.foldl stepWire w).getD (w.length + j) false =
   (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
    if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
 induction gs generalizing w j with
 | nil => simp at hj
 | cons g gs ih =>
  rw [List.foldl_cons]
  cases j with
  | zero =>
   have h1 : w.length < (stepWire w g).length := by simp [stepWire]
   rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
   simp only [List.getElem_cons_zero]
   have h2 : (stepWire w g).getD w.length false =
     g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp [stepWire, List.getD_eq_getElem?_getD]
   rw [h2]
   congr 1
   apply List.map_congr_left
   intro i _
   by_cases hi : i < w.length
   ·rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
   ·rw [ite_eq_right hi]; exact getD_ge w i (by omega)
  | succ j =>
   have hj' : j < gs.length := by simpa using hj
   have key := ih (stepWire w g) j hj'
   have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
   rw [hl] at key
   have e : w.length + (j + 1) = w.length + 1 + j := by omega
   simp only [List.getElem_cons_succ]
   rw [e]
   exact key
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
 simp [gateAt, List.getD_eq_getElem?_getD, hj]
lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.gateAt_mem <;> assumption
lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
  val C x u = x.getD u false := by
 unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)
lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
  (hu : n + C.gates.length ≤ u) : val C x u = false := by
 unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega
lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
  (hj : j < C.gates.length) :
  val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
   if i < n + j then val C x i else false) := by
 subst hx
 rw [gateAt_eq hj]
 exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
  (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
  val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
 rw [val_gate hx hr, hop]
 simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
 constructor
 ·rintro ⟨i, hi, h⟩
  by_cases hlt : i < n + r
  ·rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
  ·rw [ite_eq_right hlt] at h; cases h
 ·rintro ⟨i, hi, hlt, h⟩
  exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩
lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
  (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
  val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
 rw [val_gate hx hr, hop]
 simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
 constructor
 ·intro h i hi
  have h' := h i hi
  by_cases hlt : i < n + r
  ·rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
  ·rw [ite_eq_right hlt] at h'; cases h'
 ·intro h i hi
  rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
  val C (List.ofFn x) u.val = x u := by
 rw [val_input (n := n) (by simp) u.isLt]
 simp [List.getD_eq_getElem?_getD]
lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
  PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl
def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
 ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
  w' ∈ (gateAt C k).inputs ∧ w' < n + k
lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
  (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
  val C x w = true := by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl => exact hv
 | head hstep _ ih =>
  obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
  exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩
lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
  ∀ w : ℕ, val C x w = true →
   ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
    (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro hv
  by_cases hw : w < n
  ·exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
  ·by_cases hlen : n + C.gates.length ≤ w
   ·rw [val_ge hx hlen] at hv; cases hv
   ·obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    by_cases hop : (gateAt C k).op = GateOp.or
    ·obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
     obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
     exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
    ·exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
 simp [pairInput]
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
 simp [pairInput]
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
  graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
 simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
  Bool.false_or, decide_eq_true_eq, pairInput_true]
 constructor
 ·rintro ⟨a, b, hab, ha, hb⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  ·exact (G.irrefl hab).elim
  ·exact hab
  ·exact hab.symm
  ·exact (G.irrefl hab).elim
 ·intro h
  exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
  (hv : val C (List.ofFn (pairInput u v)) p = true) :
  (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
  (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
   Relation.ReflTransGen (OrStep n C) p (n + h) ∧
   val C (List.ofFn (pairInput u v)) (n + h) = true) := by
 obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
  (by simp) p hv
 rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
 ·left
  refine ⟨⟨w', hlt⟩, ?_, hr⟩
  have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
  rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
  exact (pairInput_true u v _).mp h1.symm
 ·right
  exact ⟨h, hh, hop, hr, hv'⟩
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
  (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
  val C (List.ofFn x) p = true :=
 orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
  (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
  (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
  (u v : Fin n) (huv : F (pairInput u v) = true) :
  ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
   Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
   val C (List.ofFn (pairInput u v)) (n + a) = true := by
 rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
  ⟨t, _, hr⟩ | h
 ·exfalso
  have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
  rw [hout] at h1
  exact G.irrefl (hF t t h1)
 ·exact h
lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
  (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
  (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
  (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
 rw [← hout]
 exact orStep_up (n := n) (by simp) hr hv
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
  (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
 induction gs generalizing cs with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons, ih]
  simp [coneStep]
  omega
lemma cones_char (n : ℕ) (gs : List Gate) :
  ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
   j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
    (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
 induction gs using List.reverseRecOn with
 | nil => intro i j; simp
 | append_singleton gs g ih =>
  intro i j
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
   rw [cones_len]; simp
  have key : ∀ k, k < gs.length →
    (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
     (gs.foldl (coneStep n) []).getD k [] := by
   intro k hk
   simp only [coneStep, List.getD_eq_getElem?_getD]
   rw [List.getElem?_append_left (by omega)]
  rcases Nat.lt_trichotomy j gs.length with h | h | h
  ·have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h]
   rw [key j h, ih i j, e1]
   constructor
   ·rintro ⟨_, w, hw, h1, h2, h3⟩
    refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
    rw [key (w - n) (by omega)]
    exact h3
   ·rintro ⟨_, w, hw, h1, h2, h3⟩
    refine ⟨h, w, hw, h1, h2, ?_⟩
    rw [key (w - n) (by omega)] at h3
    exact h3
  ·subst h
   have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
   have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
     (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
      (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
    simp only [coneStep, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]
   rw [e2, e1]
   simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
   constructor
   ·rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
    refine ⟨by simp, w, hw, h1, h2, ?_⟩
    rw [key (w - n) (by omega)]
    exact h3
   ·rintro ⟨_, w, hw, h1, h2, h3⟩
    rw [key (w - n) (by omega)] at h3
    exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
  ·have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
    simp only [coneStep, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl
   rw [e0]
   constructor
   ·intro h0; simp at h0
   ·rintro ⟨h0, _⟩
    simp at h0
    omega
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
  InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
   (i = k ∨ InCone n C i k) := by
 have h := cones_char n C.gates i j
 unfold InCone cones gateAt
 rw [h]
 constructor
 ·rintro ⟨h0, w, hw, h1, h2, h3⟩
  refine ⟨h0, w - n, by omega, ?_, h3⟩
  have : n + (w - n) = w := by omega
  rw [this]
  exact hw
 ·rintro ⟨h0, k, hk, hw, h3⟩
  refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
  have : n + k - n = k := by omega
  rw [this]
  exact h3
lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
  (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl => exact le_rfl
 | head hstep _ ih =>
  obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
  omega
lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
  (h : Relation.ReflTransGen (OrStep n C) w w') :
  ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl => intro k h' h1 h2; left; omega
 | @head a c hstep hrest ih =>
  intro k h' h1 h2
  obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
  have hk : k0 = k := by omega
  subst hk
  have hle := orStep_le hrest
  obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
  subst hk1
  right
  rw [inCone_iff]
  exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩
lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
  (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
  (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
 have hle := orStep_le hr
 obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
 rw [inCone_iff]
 exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
  (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
 induction gs generalizing cs with
 | nil => simp
 | cons g gs ih =>
  rw [List.foldl_cons, ih]
  simp [orStep]
  omega
lemma orSets_char (n : ℕ) (gs : List Gate) :
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
   rw [orSets_len]; simp
  have key : ∀ k, k < gs.length →
    (orStep n (gs.foldl (orStep n) []) g).getD k [] =
     (gs.foldl (orStep n) []).getD k [] := by
   intro k hk
   simp only [orStep, List.getD_eq_getElem?_getD]
   rw [List.getElem?_append_left (by omega)]
  rcases Nat.lt_trichotomy j gs.length with h | h | h
  ·have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h]
   rw [key j h, ih i j, e1]
   constructor
   ·rintro ⟨_, h3⟩
    refine ⟨by simp; omega, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    ·exact Or.inl h3
    ·refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
     rw [key (w - n) (by omega)]
     exact h3
   ·rintro ⟨_, h3⟩
    refine ⟨h, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    ·exact Or.inl h3
    ·rw [key (w - n) (by omega)] at h3
     exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
  ·subst h
   have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
   rw [e1]
   by_cases hop : g.op = GateOp.or
   ·have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
      gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
       (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
     simp only [orStep, List.getD_eq_getElem?_getD]
     rw [List.getElem?_append_right (by omega)]
     simp [hlen, hop]
    rw [e2]
    simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    ·rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
     ·exact ⟨by simp, Or.inl h3⟩
     ·refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
      rw [key (w - n) (by omega)]
      exact h3
    ·rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
     ·exact Or.inl h3
     ·rw [key (w - n) (by omega)] at h3
      exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
   ·have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
     simp only [orStep, List.getD_eq_getElem?_getD]
     rw [List.getElem?_append_right (by omega)]
     simp [hlen, hop]
    rw [e2]
    simp only [List.mem_singleton]
    constructor
    ·intro h3
     exact ⟨by simp, Or.inl h3⟩
    ·rintro ⟨_, h3 | ⟨hop2, _⟩⟩
     ·exact h3
     ·exact (hop hop2).elim
  ·have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
    simp only [orStep, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl
   rw [e0]
   constructor
   ·intro h0; simp at h0
   ·rintro ⟨h0, _⟩
    simp at h0
    omega
lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
  OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
   ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
 have h := orSets_char n C.gates g k
 unfold OrReaches orSets gateAt
 have e : n + k - n = k := by omega
 rw [e, h]
 constructor
 ·rintro ⟨_, hk, h3⟩
  refine ⟨hk, ?_⟩
  rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
  ·exact Or.inl h3
  ·exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
 ·rintro ⟨hk, h3⟩
  refine ⟨by omega, hk, ?_⟩
  rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
  ·exact Or.inl h3
  ·exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
  (h : Relation.ReflTransGen (OrStep n C) w w2) :
  ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl =>
  intro g h1 hg
  subst h1
  exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
 | @head a c hstep hrest ih =>
  intro g h1 hg
  obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
  exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩
lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
  ∀ w, OrReaches n C w g →
   Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
 intro w
 induction w using Nat.strong_induction_on with
 | _ w ih =>
  intro h
  have hnw : n ≤ w := h.1
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
  rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
  ·exact ⟨Relation.ReflTransGen.refl, hk⟩
  ·obtain ⟨hr2, hg⟩ := ih i hlt hr
   exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩
lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
  (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
  Relation.ReflTransGen (OrStep n C) p u.val := by
 simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
 rcases hu with h | ⟨k, hk, hr, hop, hin⟩
 ·rw [h]
 ·exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩
lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
  (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
  u ∈ PEqualNP.TopForm.orIn n C p := by
 simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
 rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
 ·exact Or.inl h
 ·obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
  exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma topData {a : ℕ} (ha : a ∈ tops G C) :
  a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
 simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
lemma junkData {a : ℕ} (ha : a ∈ junk G C) :
  a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
   ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
 rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
 exact ⟨hal, hop, hd⟩
lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
  ∃ p q, (gateAt C a).inputs = [p, q] :=
 List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
  opnd C a b ∈ (gateAt C a).inputs := by
 obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
 fin_cases b <;> simp [opnd, hpq]
lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
  opnd C a b < n + a :=
 hAO.2.1 a ha _ (opndMem hAO ha b)
lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
  (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
  gateVal n C a x = true ↔
   val C (List.ofFn x) (opnd C a 0) = true ∧
   val C (List.ofFn x) (opnd C a 1) = true := by
 rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
 constructor
 ·intro h
  exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
 ·intro h i hi
  refine ⟨hAO.2.1 a ha i hi, ?_⟩
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
  ·simpa [opnd, hpq] using h.1
  ·have e : i = q := List.mem_singleton.mp hq
   subst i
   simpa [opnd, hpq] using h.2
lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
  (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
  gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
 rw [andValBoth hAO ha hop]
 constructor
 ·intro h b
  fin_cases b
  ·exact h.1
  ·exact h.2
 ·intro h
  exact ⟨h 0, h 1⟩
lemma operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
  {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
  InCone n C h a :=
 operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
  (orReaches_reach h _ hr).1
lemma operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
  (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
  {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
  (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
 have hlen := (orReaches_reach h _ hr).2
 have hnb : ¬ BelowF G C h :=
  fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
 have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
  by_contra hne
  apply hnb
  intro x hx
  by_contra hf
  exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
 exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
lemma reachVal {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
  (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
 orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hh
lemma eitherOperand (b c : Fin 2) : c = b ∨ c = 1 - b := by
 fin_cases b <;> fin_cases c <;> decide
lemma oppositeSideWmax (hAO : IsAO2 n C) {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
  (hr : OrReaches n C (opnd C a b) j) :
  side (n := n) C a (1 - b) ⊆ wmax G C j := by
 intro t ht
 obtain ⟨hal, hao, hab⟩ := topData ha
 simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
 intro x hj hx
 apply hab x
 apply (andValOperands hAO hal hao x).mpr
 intro c
 rcases eitherOperand b c with rfl | rfl
 ·exact reachVal hr hj
 ·exact reach_var_val x _ t (mem_orIn_reach t ht) hx
lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
  (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
  {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
  (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
   ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
    gateVal n C j (pairInput u v) = true := by
 rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
 ·exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
 ·have hr' := reach_orReaches hr j rfl hj
  exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
   ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩
lemma memJunkPair {j k a : ℕ} (hs : junk G C = {j,k}) (ha : a ∈ junk G C) :
  a = j ∨ a = k := by
 simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using ha
end Critical.Base
namespace Critical.Patch
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
  (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
   acc.length + gs.length := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.foldl_wires_len <;> assumption
lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
  (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
   acc.getD i false := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.foldl_wires_getD_lt <;> assumption
lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
  (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
  (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
    (acc.length + j) false =
   gs[j].op.eval (gs[j].inputs.map fun k =>
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
     k false) := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.foldl_wires_getD_gate <;> assumption
lemma wires_length (C : Circuit) (x : List Bool) :
  (C.wires x).length = x.length + C.gates.length :=
 foldl_wires_len C.gates x
lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
  wval C x i = x ⟨i, hi⟩ := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.wval_input <;> assumption
lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
  gateVal n C j x = wval C x (n + j) := rfl
lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
  wval C x w = false := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.wval_ge_len <;> assumption
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
  gateAt C j = C.gates[j] := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.gateAt_eq <;> assumption
lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
  gateAt C j ∈ C.gates := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.gateAt_mem <;> assumption
lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
  (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.gate_inputs_eq <;> assumption
lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
  opnd C j b ∈ (gateAt C j).inputs := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.opnd_mem <;> assumption
lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
  opnd C j b < n + j :=
 hAO.2.1 j hj _ (opnd_mem hAO hj b)
lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
  {j : ℕ} (hj : j < C.gates.length) :
  wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.wval_gate_eval <;> assumption
lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
  {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
  wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.wval_gate_or <;> assumption
lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
  (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.foldl_cones_len <;> assumption
lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
  (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.foldl_cones_getD_lt <;> assumption
lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.cones_length <;> assumption
lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
  (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
   (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
    (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.foldl_cones_getD_gate <;> assumption
lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.inCone_lt_len <;> assumption
lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
  InCone n C i j ↔
   ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.inCone_iff <;> assumption
lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.inCone_lt <;> assumption
lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
  InCone n C i k := by
 induction k using Nat.strong_induction_on with
 | ind k ih =>
  have hk := inCone_lt_len h2
  rw [inCone_iff hk] at h2 ⊢
  rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
  ·exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
  ·exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩
def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩
lemma patch_length (C : Circuit) (j : ℕ) (g : Gate) :
  (patch C j g).gates.length = C.gates.length := by
 simp [patch]
lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
  gateAt (patch C j g) k = gateAt C k := by
 simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]
lemma gateAt_patch_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) :
  gateAt (patch C j g) j = g := by
 simp [patch, gateAt, List.getD_eq_getElem?_getD, hj]
lemma patch_wval_gate_eval {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
  (hAO : IsAO2 n C) (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length)
  (hne : j ≠ k) :
  wval (patch C j g) x (n + k) = (gateAt C k).op.eval
   [wval (patch C j g) x (opnd C k 0), wval (patch C j g) x (opnd C k 1)] := by
 have hk' : k < (patch C j g).gates.length := by simpa only [patch_length] using hk
 have hgate := gateAt_patch_ne C j k g hne
 have hlen : (List.ofFn x).length = n := List.length_ofFn
 have hback : ∀ w ∈ (patch C j g).gates[k].inputs, w < (List.ofFn x).length + k := by
  intro w hw
  rw [← gateAt_eq hk', hgate] at hw
  rw [hlen]
  exact hAO.2.1 k hk w hw
 have heval := foldl_wires_getD_gate (patch C j g).gates (List.ofFn x) k hk' hback
 rw [hlen, ← gateAt_eq hk', hgate, gate_inputs_eq hAO hk] at heval
 simpa only [wval, Circuit.wires, List.map_cons, List.map_nil] using heval
lemma patch_gateVal_eq_of_not_inCone {n : ℕ} {C : Circuit} {j : ℕ} {g : Gate}
  (hAO : IsAO2 n C) (k : ℕ) (hne : j ≠ k) (hCone : ¬ InCone n C j k)
  (x : Fin n → Bool) : gateVal n (patch C j g) k x = gateVal n C k x := by
 induction k using Nat.strong_induction_on with
 | ind k ih =>
  by_cases hk : k < C.gates.length
  ·have hval (b : Fin 2) : wval (patch C j g) x (opnd C k b) =
     wval C x (opnd C k b) := by
    by_cases hw : opnd C k b < n
    ·rw [wval_input _ _ _ hw, wval_input _ _ _ hw]
    ·have hw' : n ≤ opnd C k b := by omega
     have hlt := opnd_lt hAO hk b
     have hsub_ne : j ≠ opnd C k b - n := by
      intro he
      apply hCone
      exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inl he⟩
     have hsub_cone : ¬ InCone n C j (opnd C k b - n) := by
      intro he
      apply hCone
      exact (inCone_iff hk).mpr ⟨opnd C k b, opnd_mem hAO hk b, hw', hlt, Or.inr he⟩
     have hv := ih (opnd C k b - n) (by omega) hsub_ne hsub_cone
     rw [gateVal_eq_wval, gateVal_eq_wval, Nat.add_sub_of_le hw'] at hv
     exact hv
   rw [gateVal_eq_wval, gateVal_eq_wval, patch_wval_gate_eval hAO x hk hne,
    wval_gate_eval hAO x hk, hval 0, hval 1]
  ·rw [gateVal_eq_wval, gateVal_eq_wval, wval_ge_len _ _ (by rw [patch_length]; omega),
    wval_ge_len _ _ (by omega)]
end Critical.Patch
namespace Critical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
def offPatch (C : Circuit) (h : ℕ) : Circuit := ⟨C.gates.set h ⟨GateOp.or, []⟩, C.output⟩
lemma offPatch_length (C : Circuit) (h : ℕ) : (offPatch C h).gates.length = C.gates.length := by
 simp [offPatch]
lemma gateAt_offPatch_ne (C : Circuit) (h k : ℕ) (hne : h ≠ k) :
  gateAt (offPatch C h) k = gateAt C k := by
 simp [offPatch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]
lemma orStep_offPatch {n : ℕ} {C : Circuit} {h w w' : ℕ}
  (hAnd : (gateAt C h).op = GateOp.and) (hs : Base.OrStep n C w w') :
  Base.OrStep n (offPatch C h) w w' := by
 obtain ⟨k, hk, rfl, hOr, hi, hb⟩ := hs
 have hne : h ≠ k := by
  intro he
  rw [← he, hAnd] at hOr
  cases hOr
 refine ⟨k, by simpa only [offPatch_length] using hk, rfl, ?_, ?_, hb⟩
 ·simpa only [gateAt_offPatch_ne C h k hne] using hOr
 ·simpa only [gateAt_offPatch_ne C h k hne] using hi
lemma orPath_offPatch {n : ℕ} {C : Circuit} {h w w' : ℕ}
  (hAnd : (gateAt C h).op = GateOp.and)
  (hs : Relation.ReflTransGen (Base.OrStep n C) w w') :
  Relation.ReflTransGen (Base.OrStep n (offPatch C h)) w w' := by
 induction hs using Relation.ReflTransGen.head_induction_on with
 | refl => exact Relation.ReflTransGen.refl
 | head hs _ ih => exact Relation.ReflTransGen.head (orStep_offPatch hAnd hs) ih
lemma offPatch_difference_trace {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
  {h : ℕ} (hAnd : (gateAt C h).op = GateOp.and) (x : Fin n → Bool) :
  ∀ w, Base.val C (List.ofFn x) w = true → Base.val (offPatch C h) (List.ofFn x) w = false →
  ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ OrReaches n C w j ∧
   gateVal n C j x = true ∧ gateVal n (offPatch C h) j x = false := by
 intro w
 induction w using Nat.strong_induction_on with
 | ind w ih =>
  intro hw hw'
  by_cases hwInput : w < n
  ·rw [Base.val_input (n := n) (by simp) hwInput] at hw hw'
   rw [hw] at hw'
   cases hw'
  ·by_cases hwLarge : n + C.gates.length ≤ w
   ·rw [Base.val_ge (n := n) (by simp) hwLarge] at hw
    cases hw
   ·obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    by_cases hOr : (gateAt C k).op = GateOp.or
    ·have hne : h ≠ k := by
      intro he
      rw [← he, hAnd] at hOr
      cases hOr
     obtain ⟨v, hvMem, hvLt, hv⟩ := (Base.val_or (n := n) (by simp) hk hOr).mp hw
     have hv' : Base.val (offPatch C h) (List.ofFn x) v = false := by
      cases hv' : Base.val (offPatch C h) (List.ofFn x) v
      ·rfl
      ·have hk' : k < (offPatch C h).gates.length := by simpa only [offPatch_length] using hk
       have hOr' : (gateAt (offPatch C h) k).op = GateOp.or := by
        simpa only [gateAt_offPatch_ne C h k hne] using hOr
       have hMem' : v ∈ (gateAt (offPatch C h) k).inputs := by
        simpa only [gateAt_offPatch_ne C h k hne] using hvMem
       have ht := (Base.val_or (n := n) (by simp) hk' hOr').mpr ⟨v, hMem', hvLt, hv'⟩
       rw [hw'] at ht
       cases ht
     obtain ⟨j, hj, hjAnd, hReach, hjv, hjv'⟩ := ih v hvLt hv hv'
     refine ⟨j, hj, hjAnd, ?_, hjv, hjv'⟩
     exact (Base.orReaches_iff n C k j).mpr ⟨hk, Or.inr ⟨hOr, v, hvMem, hvLt, hReach⟩⟩
    ·have hAndK : (gateAt C k).op = GateOp.and := (hAO.1 _ (Base.gateAt_mem hk)).resolve_right hOr
     exact ⟨k, hk, hAndK, (Base.orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hw, hw'⟩
lemma critical_edge_useful {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
  (hT : TopForm G C) {g h : ℕ} (hJ : junk G C = {g, h}) (hne : g ≠ h)
  (hIndependent : ¬ InCone n C h g)
  (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
   OrReaches n C (opnd C a b) h → ¬ OrReaches n C (opnd C a (1 - b)) g)
  (u v : Fin n) (hAdj : G.Adj u v)
  (hLost : circuitFun n (offPatch C h) (pairInput u v) = false) :
  gateVal n C h (pairInput u v) = true ∧ (u ∈ wmax G C h ∨ v ∈ wmax G C h) := by
 have hhJ : h ∈ junk G C := by rw [hJ]; simp
 obtain ⟨hhLen, hhAnd, hx, hhx, hFx⟩ := Base.junkData hhJ
 have hout (x : Fin n → Bool) : Base.val C (List.ofFn x) C.output = graphFun G ∅ x :=
  congrFun hF x
 obtain ⟨a, haLen, haNotOr, haPath, haVal⟩ :=
  Base.edge_trace G (graphFun G ∅) (fun x y hxy => (Base.graphFun_pair G x y).mp hxy)
   hout u v ((Base.graphFun_pair G u v).mpr hAdj)
 have haAnd : (gateAt C a).op = GateOp.and :=
  (hAO.1 _ (Base.gateAt_mem haLen)).resolve_right haNotOr
 have haBelow : BelowF G C a := fun x hv =>
  Base.below_of_reach (graphFun G ∅) hout a haPath x hv
 have haTop : a ∈ tops G C := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
   And.intro haLen (And.intro haAnd haBelow)
 have hha : h ≠ a := by
  intro he
  subst a
  have ht := haBelow hx hhx
  rw [hFx] at ht
  cases ht
 have haOff : gateVal n (offPatch C h) a (pairInput u v) = false := by
  cases hc : gateVal n (offPatch C h) a (pairInput u v)
  ·rfl
  ·have ho := Base.orStep_up (n := n) (by simp) (orPath_offPatch hhAnd haPath) hc
   change circuitFun n (offPatch C h) (pairInput u v) = true at ho
   rw [hLost] at ho
   cases ho
 have hEval : gateVal n (offPatch C h) a (pairInput u v) =
   (Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0) &&
    Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 1)) := by
  have he := Patch.patch_wval_gate_eval (j := h) (g := ⟨GateOp.or, []⟩) hAO (pairInput u v) haLen hha
  change gateVal n (offPatch C h) a (pairInput u v) = (gateAt C a).op.eval
   [Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0),
    Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 1)] at he
  simpa only [haAnd, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true] using he
 obtain ⟨b, hbOff⟩ : ∃ b : Fin 2,
   Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a b) = false := by
  by_cases h0 : Base.val (offPatch C h) (List.ofFn (pairInput u v)) (opnd C a 0) = false
  ·exact ⟨0, h0⟩
  ·have h0t := Bool.eq_true_of_not_eq_false h0
   refine ⟨1, ?_⟩
   rw [haOff, h0t, Bool.true_and] at hEval
   exact hEval.symm
 have hbVal := ((Base.andValOperands hAO haLen haAnd (pairInput u v)).mp haVal) b
 obtain ⟨j, hjLen, hjAnd, hjReach, hjVal, hjOff⟩ :=
  offPatch_difference_trace hAO hhAnd (pairInput u v) (opnd C a b) hbVal hbOff
 have hjJ := Base.operandOrAndJunk hAO hT haLen haAnd hjReach hjAnd
 have hjh : j = h := by
  rcases Base.memJunkPair hJ hjJ with hjg | hjh
  ·subst j
   have he := Patch.patch_gateVal_eq_of_not_inCone (j := h) (g := ⟨GateOp.or, []⟩)
    hAO g (Ne.symm hne) hIndependent (pairInput u v)
   change gateVal n (offPatch C h) g (pairInput u v) = gateVal n C g (pairInput u v) at he
   rw [he, hjVal] at hjOff
   cases hjOff
  ·exact hjh
 subst j
 refine ⟨hjVal, ?_⟩
 have hoVal := ((Base.andValOperands hAO haLen haAnd (pairInput u v)).mp haVal) (1 - b)
 rcases Base.operandSupport hAO hT haLen haAnd hoVal with ⟨t, ht, htu⟩ | ⟨k, hkJ, hkReach, _⟩
 ·have htw := Base.oppositeSideWmax hAO haTop hjReach ht
  rcases htu with rfl | rfl
  ·exact Or.inl htw
  ·exact Or.inr htw
 ·rcases Base.memJunkPair hJ hkJ with hkg | hkh
  ·subst k
   exact False.elim (hNoCommon a haTop b hjReach hkReach)
  ·subst k
   have ht : gateVal n C a hx = true := by
    apply (Base.andValOperands hAO haLen haAnd hx).mpr
    intro c
    rcases Base.eitherOperand b c with rfl | rfl
    ·exact Base.reachVal hjReach hhx
    ·exact Base.reachVal hkReach hhx
   have hf := haBelow hx ht
   rw [hFx] at hf
   cases hf
end Critical
namespace ApartFlags
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
 PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
lemma one_flag {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C : Circuit) (hL : IsLeastAO G C)
  (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
  (hT : TopForm G C) {j k : ℕ} (hne : j ≠ k) (hJ : junk G C = {j,k})
  (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
  (hNoCommon : ∀ a ∈ tops G C, ∀ b : Fin 2,
   OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k)
  (h4 : NoFourCycle G)
  (hdis : Disjoint (side (n := n) C j 0) (side (n := n) C j 1))
  (hP : 2 ≤ (side (n := n) C j 0).card) (hQ : 2 ≤ (side (n := n) C j 1).card) :
  ∃ z ∈ side (n := n) C j 0, ∃ zp ∈ side (n := n) C j 1,
   G.Adj z zp ∧ (∀ p ∈ side (n := n) C j 0, G.Adj p zp) ∧
    (∀ q ∈ side (n := n) C j 1, G.Adj z q) := by
 apply FlagReduction.filtered_independent_is_cross_star G C hL hOne hne hJ hjk
  (side (n := n) C j 0) (side (n := n) C j 1) h4 hdis hP hQ
 ·exact RawOperands.independent_operand G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) 0
 ·exact RawOperands.independent_operand G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl) 1
 ·intro u v huv hLost
  have hJ' : junk G C = {k,j} := by rw [hJ,Finset.pair_comm]
  obtain ⟨hjv,hFilter⟩ := Critical.critical_edge_useful hL.1 hL.2.1 hT hJ'
   (Ne.symm hne) hjk hNoCommon u v huv hLost
  have heval : ∀ x : Fin n → Bool, gateVal n C j x =
    IndependentDescent.product (side (n := n) C j 0) (side (n := n) C j 1) x :=
   RawOperands.independent_product G C hL.1 hT j k hJ hjk hkj j (Or.inl rfl)
  refine ⟨huv,(heval _).symm.trans hjv,?_⟩
  rcases hFilter with hu | hv
  ·exact Or.inl ((IndependentDescent.wmax_iff G C j _ _ heval u).mp hu)
  ·exact Or.inr ((IndependentDescent.wmax_iff G C j _ _ heval v).mp hv)
lemma reaches_operand_cone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
  {a g : ℕ} (ha : a < C.gates.length) (b : Fin 2)
  (hr : OrReaches n C (opnd C a b) g) : InCone n C g a := by
 exact Critical.Base.operand_cone ha (Lift.opnd_mem hAO ha b) (Lift.opnd_lt hAO ha b)
  (Critical.Base.orReaches_reach g _ hr).1
lemma two_flags_no_joint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C : Circuit) (hL : IsLeastAO G C)
  (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
  (hT : TopForm G C) {g h : ℕ} (hne : g ≠ h) (hJ : junk G C = {g,h})
  (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
  (hApart : ∀ a ∈ tops G C, ∀ b : Fin 2,
   OrReaches n C (opnd C a b) g → ¬ OrReaches n C (opnd C a (1-b)) h)
  (h4 : NoFourCycle G)
  (hdis : ∀ j ∈ junk G C, Disjoint (side (n := n) C j 0) (side (n := n) C j 1))
  (hlarge : ∀ j ∈ junk G C, ∀ b : Fin 2, 2 ≤ (side (n := n) C j b).card) :
  ∀ j ∈ junk G C, ∃ (P Q : Finset (Fin n)) (z zp : Fin n),
   G.Adj z zp ∧ z ∈ P ∧ zp ∈ Q ∧ (∀ p ∈ P, G.Adj p zp) ∧
   (∀ q ∈ Q, G.Adj q z) ∧ 2 ≤ P.card ∧ 2 ≤ Q.card ∧
   ∀ x : Fin n → Bool, gateVal n C j x =
    (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)) := by
 classical
 have hFlag (j k : ℕ) (hne' : j ≠ k) (hJ' : junk G C = {j,k})
   (hjk : ¬ InCone n C j k) (hkj : ¬ InCone n C k j)
   (hApart' : ∀ a ∈ tops G C, ∀ b : Fin 2,
    OrReaches n C (opnd C a b) j → ¬ OrReaches n C (opnd C a (1-b)) k) :
   ∃ z ∈ side (n := n) C j 0, ∃ zp ∈ side (n := n) C j 1,
    G.Adj z zp ∧ (∀ p ∈ side (n := n) C j 0, G.Adj p zp) ∧
     (∀ q ∈ side (n := n) C j 1, G.Adj z q) := by
  have hjmem : j ∈ junk G C := by rw [hJ']; simp
  exact one_flag G C hL hOne hT hne' hJ' hjk hkj hApart' h4
   (hdis j hjmem) (hlarge j hjmem 0) (hlarge j hjmem 1)
 intro j hj
 have hjcases : j = g ∨ j = h := by simpa [hJ] using hj
 have heval := RawOperands.independent_product G C hL.1 hT g h hJ hgh hhg j hjcases
 have hz : ∃ z ∈ side (n := n) C j 0, ∃ zp ∈ side (n := n) C j 1,
   G.Adj z zp ∧ (∀ p ∈ side (n := n) C j 0, G.Adj p zp) ∧
    (∀ q ∈ side (n := n) C j 1, G.Adj z q) := by
  rcases hjcases with hjg | hjh
  ·rw [hjg]
   exact hFlag g h hne hJ hgh hhg hApart
  ·rw [hjh]
   exact hFlag h g (Ne.symm hne) (by rw [hJ,Finset.pair_comm]) hhg hgh
    (by
     intro a ha b hhr hgr
     apply hApart a ha (1-b) hgr
     have hb : (1 : Fin 2) - (1-b) = b := by fin_cases b <;> decide
     simpa only [hb] using hhr)
 obtain ⟨z,hz,zp,hzp,hzzp,hP,hQ⟩ := hz
 exact ⟨side (n := n) C j 0,side (n := n) C j 1,z,zp,hzzp,hz,hzp,hP,
  fun q hq => (hQ q hq).symm,hlarge j hj 0,hlarge j hj 1,heval⟩
end ApartFlags
end PEqualNP.Outside.L_meta_5012_apart_case
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadTwo
theorem PEqualNP.Outside.L_meta_5012_apart_case
  {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (C : Circuit) (s : Fin n → Bool)
  (hbip : ∀ u v : Fin n, G.Adj u v → s u ≠ s v)
  (h4 : NoFourCycle G) (hL : IsLeastAO G C)
  (hOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
  (hT : TopForm G C) {g h : ℕ} (hne : g ≠ h)
  (hJ : junk G C = {g,h})
  (hgh : ¬ InCone n C g h) (hhg : ¬ InCone n C h g)
  (hApart : ∀ a ∈ tops G C, ∀ b : Fin 2,
   OrReaches n C (opnd C a b) g → ¬ OrReaches n C (opnd C a (1-b)) h)
  (hdis : ∀ j ∈ junk G C, Disjoint (side (n := n) C j 0) (side (n := n) C j 1))
  (hlarge : ∀ j ∈ junk G C, ∀ b : Fin 2, 2 ≤ (side (n := n) C j b).card) : False := by
 classical
 have hflags := PEqualNP.Outside.L_meta_5012_apart_case.ApartFlags.two_flags_no_joint G C hL hOne hT
  hne hJ hgh hhg hApart h4 hdis hlarge
 have hLift := PEqualNP.Outside.L_meta_5012_apart_case.Lift.topForm_isLiftFixedPoint hL.1 hL.2.1 hT
 apply PEqualNP.Outside.L_meta_5012_apart_case.Flags.main n G C s hbip h4 hL hLift
 refine ⟨g,h,hne,?_,hflags g ?_,hflags h ?_⟩
 ·intro k
  simp [hJ]
 ·simp [hJ]
 ·simp [hJ]

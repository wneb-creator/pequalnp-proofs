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

lemma and_of_pure_cone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hpure : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ InCone n C k j) :
    ∃ A B : Finset (Fin n), A.Nonempty ∧ B.Nonempty ∧
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
  refine ⟨A, B, hA, hB, ?_⟩
  intro x
  rw [gateVal_eq_wval, wval_gate_and hAO x hj hand, ha x, hb x]

lemma stopped_wire_support {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g : ℕ) :
    ∀ w < n + C.gates.length,
      (∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
        w = n + k ∨ (n ≤ w ∧ InCone n C k (w - n)) → False) →
      ∃ (S : Finset (Fin n)) (b : Bool),
        ∀ x : Fin n → Bool, wval C x w =
          (decide (∃ u ∈ S, x u = true) || (b && gateVal n C g x)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hno
    by_cases hwg : w = n + g
    · refine ⟨∅, true, ?_⟩
      intro x
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.true_and,
        Bool.false_or, gateVal_eq_wval, hwg]
    · by_cases hwn : w < n
      · refine ⟨{⟨w, hwn⟩}, false, ?_⟩
        intro x
        rw [wval_input C x w hwn]
        simp
      · have hj : w - n < C.gates.length := by omega
        have hw_eq : w = n + (w - n) := by omega
        have hor : (gateAt C (w - n)).op = GateOp.or := by
          rcases hAO.1 _ (gateAt_mem hj) with hand | hor
          · exact False.elim (hno (w - n) hj hand (by omega) (Or.inl hw_eq))
          · exact hor
        have child : ∀ b : Fin 2,
            ∃ (S : Finset (Fin n)) (d : Bool),
              ∀ x : Fin n → Bool, wval C x (opnd C (w - n) b) =
                (decide (∃ u ∈ S, x u = true) || (d && gateVal n C g x)) := by
          intro b
          have hlt : opnd C (w - n) b < w := by
            have := opnd_lt hAO hj b
            omega
          refine ih _ hlt (by omega) ?_
          intro k hk hand hkg hkc
          apply hno k hk hand hkg
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
        obtain ⟨S, bS, hs⟩ := child 0
        obtain ⟨T, bT, ht⟩ := child 1
        refine ⟨S ∪ T, bS || bT, ?_⟩
        intro x
        rw [hw_eq, wval_gate_or hAO x hj hor, hs x, ht x]
        simp only [Finset.mem_union, or_and_right, exists_or, Bool.decide_or]
        cases bS <;> cases bT <;> cases hg : gateVal n C g x <;>
          simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

lemma and_of_one_and_cone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (g : ℕ) {j : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hcone : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → InCone n C k j → k = g) :
    ∃ (A B : Finset (Fin n)) (a b : Bool),
      ∀ x : Fin n → Bool, gateVal n C j x =
        ((decide (∃ u ∈ A, x u = true) || (a && gateVal n C g x)) &&
         (decide (∃ u ∈ B, x u = true) || (b && gateVal n C g x))) := by
  have child : ∀ b : Fin 2,
      ∃ (S : Finset (Fin n)) (d : Bool),
        ∀ x : Fin n → Bool, wval C x (opnd C j b) =
          (decide (∃ u ∈ S, x u = true) || (d && gateVal n C g x)) := by
    intro b
    apply stopped_wire_support hAO g (opnd C j b) (by have := opnd_lt hAO hj b; omega)
    intro k hk hop hkg hkc
    apply hkg
    apply hcone k hk hop
    rcases hkc with heq | ⟨hnc, hc⟩
    · apply (inCone_iff hj).mpr
      refine ⟨opnd C j b, opnd_mem hAO hj b, by omega, opnd_lt hAO hj b, ?_⟩
      left
      omega
    · apply inCone_trans hc
      apply (inCone_iff hj).mpr
      exact ⟨opnd C j b, opnd_mem hAO hj b, hnc, opnd_lt hAO hj b, Or.inl rfl⟩
  obtain ⟨A, a, ha⟩ := child 0
  obtain ⟨B, b, hb⟩ := child 1
  refine ⟨A, B, a, b, ?_⟩
  intro x
  rw [gateVal_eq_wval, wval_gate_and hAO x hj hand, ha x, hb x]


def MarkedBelow (n : ℕ) (C : Circuit) (g w : ℕ) : Prop :=
  w = n + g ∨ (n ≤ w ∧ InCone n C g (w - n))

lemma inCone_inputs_iff {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {g j : ℕ} (hj : j < C.gates.length) :
    InCone n C g j ↔
      MarkedBelow n C g (opnd C j 0) ∨ MarkedBelow n C g (opnd C j 1) := by
  have child : ∀ b : Fin 2, MarkedBelow n C g (opnd C j b) → InCone n C g j := by
    intro b h
    apply (inCone_iff hj).mpr
    refine ⟨opnd C j b, opnd_mem hAO hj b, ?_, opnd_lt hAO hj b, ?_⟩
    · rcases h with h | h <;> omega
    · rcases h with h | h
      · left; omega
      · exact Or.inr h.2
  constructor
  · intro h
    obtain ⟨w, hw, hnw, hlt, hwg⟩ := (inCone_iff hj).mp h
    have hwmarked : MarkedBelow n C g w := by
      rcases hwg with h | h
      · left; omega
      · exact Or.inr ⟨hnw, h⟩
    rw [gate_inputs_eq hAO hj] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hwmarked
    · exact Or.inr hwmarked
  · rintro (h | h)
    · exact child 0 h
    · exact child 1 h

lemma stopped_wire_support_marked {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (g : ℕ) :
    ∀ w < n + C.gates.length,
      (∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
        w = n + k ∨ (n ≤ w ∧ InCone n C k (w - n)) → False) →
      ∃ (S : Finset (Fin n)) (b : Bool),
        (b = true ↔ MarkedBelow n C g w) ∧
        ∀ x : Fin n → Bool, wval C x w =
          (decide (∃ u ∈ S, x u = true) || (b && gateVal n C g x)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hno
    by_cases hwg : w = n + g
    · refine ⟨∅, true, ?_, ?_⟩
      · simp [MarkedBelow, hwg]
      · intro x
        simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.true_and,
          Bool.false_or, gateVal_eq_wval, hwg]
    · by_cases hwn : w < n
      · refine ⟨{⟨w, hwn⟩}, false, ?_, ?_⟩
        · simp only [Bool.false_eq_true, false_iff, MarkedBelow]
          rintro (h | h) <;> omega
        · intro x
          rw [wval_input C x w hwn]
          simp
      · have hj : w - n < C.gates.length := by omega
        have hw_eq : w = n + (w - n) := by omega
        have hor : (gateAt C (w - n)).op = GateOp.or := by
          rcases hAO.1 _ (gateAt_mem hj) with hand | hor
          · exact False.elim (hno (w - n) hj hand (by omega) (Or.inl hw_eq))
          · exact hor
        have child : ∀ b : Fin 2,
            ∃ (S : Finset (Fin n)) (d : Bool),
              (d = true ↔ MarkedBelow n C g (opnd C (w - n) b)) ∧
              ∀ x : Fin n → Bool, wval C x (opnd C (w - n) b) =
                (decide (∃ u ∈ S, x u = true) || (d && gateVal n C g x)) := by
          intro b
          have hlt : opnd C (w - n) b < w := by
            have := opnd_lt hAO hj b
            omega
          refine ih _ hlt (by omega) ?_
          intro k hk hand hkg hkc
          apply hno k hk hand hkg
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
        obtain ⟨S, bS, hflagS, hs⟩ := child 0
        obtain ⟨T, bT, hflagT, ht⟩ := child 1
        refine ⟨S ∪ T, bS || bT, ?_, ?_⟩
        · rw [Bool.or_eq_true, hflagS, hflagT, ← inCone_inputs_iff hAO hj]
          simp only [MarkedBelow, hwg, false_or, Nat.le_of_not_gt hwn, true_and]
        · intro x
          rw [hw_eq, wval_gate_or hAO x hj hor, hs x, ht x]
          simp only [Finset.mem_union, or_and_right, exists_or, Bool.decide_or]
          cases bS <;> cases bT <;> cases hg : gateVal n C g x <;>
            simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

lemma and_of_one_and_cone_marked {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (g : ℕ) {j : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hcone : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → InCone n C k j → k = g) :
    ∃ (A B : Finset (Fin n)) (a b : Bool),
      ((a = true ∨ b = true) ↔ InCone n C g j) ∧
      ∀ x : Fin n → Bool, gateVal n C j x =
        ((decide (∃ u ∈ A, x u = true) || (a && gateVal n C g x)) &&
         (decide (∃ u ∈ B, x u = true) || (b && gateVal n C g x))) := by
  have child : ∀ b : Fin 2,
      ∃ (S : Finset (Fin n)) (d : Bool),
        (d = true ↔ MarkedBelow n C g (opnd C j b)) ∧
        ∀ x : Fin n → Bool, wval C x (opnd C j b) =
          (decide (∃ u ∈ S, x u = true) || (d && gateVal n C g x)) := by
    intro b
    apply stopped_wire_support_marked hAO g (opnd C j b) (by have := opnd_lt hAO hj b; omega)
    intro k hk hop hkg hkc
    apply hkg
    apply hcone k hk hop
    rcases hkc with heq | ⟨hnc, hc⟩
    · apply (inCone_iff hj).mpr
      refine ⟨opnd C j b, opnd_mem hAO hj b, by omega, opnd_lt hAO hj b, ?_⟩
      left
      omega
    · apply inCone_trans hc
      apply (inCone_iff hj).mpr
      exact ⟨opnd C j b, opnd_mem hAO hj b, hnc, opnd_lt hAO hj b, Or.inl rfl⟩
  obtain ⟨A, a, hflagA, ha⟩ := child 0
  obtain ⟨B, b, hflagB, hb⟩ := child 1
  refine ⟨A, B, a, b, ?_, ?_⟩
  · rw [hflagA, hflagB, ← inCone_inputs_iff hAO hj]
  · intro x
    rw [gateVal_eq_wval, wval_gate_and hAO x hj hand, ha x, hb x]

end PEqualNP.Outside.L_meta_5012.StructuralSemantics


namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma coneStep_order (n : ℕ) (cs : List (List ℕ)) (g : Gate)
    (hc : ∀ i j : ℕ, i ∈ cs.getD j [] → i < j) :
    ∀ i j : ℕ, i ∈ (coneStep n cs g).getD j [] → i < j := by
  intro i j hi
  unfold coneStep at hi
  rcases Nat.lt_trichotomy j cs.length with hj | hj | hj
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj] at hi
    exact hc i j hi
  · subst j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
    obtain ⟨w, hw, hi⟩ := List.mem_flatMap.mp hi
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    rcases List.mem_cons.mp hi with hi | hi
    · omega
    · have := hc i (w - n) hi
      omega
  · have hj' : (cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])]).length ≤ j := by
      simp only [List.length_append, List.length_singleton]
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj'] at hi
    exact False.elim (List.not_mem_nil hi)

lemma cones_fold_order (n : ℕ) (gs : List Gate) (cs : List (List ℕ))
    (hc : ∀ i j : ℕ, i ∈ cs.getD j [] → i < j) :
    ∀ i j : ℕ, i ∈ (gs.foldl (coneStep n) cs).getD j [] → i < j := by
  induction gs generalizing cs with
  | nil => exact hc
  | cons g gs ih =>
    exact ih (coneStep n cs g) (coneStep_order n cs g hc)

lemma cone_index_lt {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : i < j := by
  exact cones_fold_order n C.gates [] (by simp) i j h

lemma two_junk_ordered {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hj : (junk G C).card = 2) :
    ∃ g h : ℕ, g < h ∧ junk G C = {g, h} ∧
      (∀ k ∈ junk G C, ¬ InCone n C k g) ∧ ¬ InCone n C h g := by
  obtain ⟨a, b, hab, hjab⟩ := Finset.card_eq_two.mp hj
  have arrange : ∀ a b : ℕ, a < b → junk G C = {a, b} →
      ∃ g h : ℕ, g < h ∧ junk G C = {g, h} ∧
        (∀ k ∈ junk G C, ¬ InCone n C k g) ∧ ¬ InCone n C h g := by
    intro a b hab hjab
    refine ⟨a, b, hab, hjab, ?_, ?_⟩
    · intro k hk hcone
      have hlt := cone_index_lt hcone
      rw [hjab] at hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      omega
    · intro hcone
      have hlt := cone_index_lt hcone
      omega
  rcases Nat.lt_or_gt_of_ne hab with hab | hba
  · exact arrange a b hab hjab
  · exact arrange b a hba (by rw [hjab, Finset.pair_comm])

lemma mem_junk_characterization {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) :
    j ∈ junk G C ↔ j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty BelowF
  constructor
  · rintro ⟨hj, hop, _, x, hx, hf⟩
    refine ⟨hj, hop, ?_⟩
    intro hb
    have := hb x hx
    simp_all
  · rintro ⟨hj, hop, hb⟩
    push Not at hb
    obtain ⟨x, hx, hf⟩ := hb
    refine ⟨hj, hop, hj, x, hx, ?_⟩
    cases h : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x <;> simp_all

lemma two_junk_nested_or_pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ht : TopForm G C) (hj : (junk G C).card = 2) :
    ∃ g h : ℕ, g < h ∧ junk G C = {g, h} ∧
      (∀ k < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and → ¬ InCone n C k g) ∧
      (InCone n C g h ∨ ∀ k < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and → ¬ InCone n C k h) := by
  obtain ⟨g, h, hgh, hjs, hmin, _⟩ := two_junk_ordered G C hj
  have hgm : g ∈ junk G C := by rw [hjs]; simp
  have hhm : h ∈ junk G C := by rw [hjs]; simp
  have hgp := (mem_junk_characterization G C g).mp hgm
  have hhp := (mem_junk_characterization G C h).mp hhm
  refine ⟨g, h, hgh, hjs, ?_, ?_⟩
  · intro k hk hop hc
    by_cases hb : BelowF G C k
    · exact ht k hk g hgp.1 hop hb hgp.2.1 hc
    · exact hmin k ((mem_junk_characterization G C k).mpr ⟨hk, hop, hb⟩) hc
  · by_cases hc : InCone n C g h
    · exact Or.inl hc
    · right
      intro k hk hop hkh
      by_cases hb : BelowF G C k
      · exact ht k hk h hhp.1 hop hb hhp.2.1 hkh
      · have hkm := (mem_junk_characterization G C k).mpr ⟨hk, hop, hb⟩
        rw [hjs] at hkm
        simp only [Finset.mem_insert, Finset.mem_singleton] at hkm
        rcases hkm with rfl | rfl
        · exact hc hkh
        · have := cone_index_lt hkh
          omega

end PEqualNP.Outside.L_meta_5012


namespace PEqualNP.Outside.L_meta_5012.NestedJoint

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

lemma nested_joint_guarded {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (g h : ℕ) (R S : Finset (Fin n)) (a b : Bool)
    (hsem : ∀ x : Fin n → Bool, gateVal n C h x =
      ((decide (∃ r ∈ R, x r = true) || (a && gateVal n C g x)) &&
        (decide (∃ s ∈ S, x s = true) || (b && gateVal n C g x))))
    (hjoint : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C h x = true → graphFun G ∅ x = true)
    (hused : a = true ∨ b = true) (u v : Fin n)
    (hguv : gateVal n C g (pairInput u v) = true)
    (hhuv : gateVal n C h (pairInput u v) = true) :
    u ∈ wmax G C g ∨ v ∈ wmax G C g := by
  have hR (ha : a = false) (hb : b = true) (r : Fin n) (hr : r ∈ R) :
      r ∈ wmax G C g := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ r, ?_⟩
    intro x hgx hrx
    apply hjoint x hgx
    rw [hsem]
    have hRx : decide (∃ r ∈ R, x r = true) = true := decide_eq_true ⟨r, hr, hrx⟩
    simp [ha, hb, hgx, hRx]
  have hS (ha : a = true) (hb : b = false) (s : Fin n) (hs : s ∈ S) :
      s ∈ wmax G C g := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ s, ?_⟩
    intro x hgx hsx
    apply hjoint x hgx
    rw [hsem]
    have hSx : decide (∃ s ∈ S, x s = true) = true := decide_eq_true ⟨s, hs, hsx⟩
    simp [ha, hb, hgx, hSx]
  cases ha : a with
  | false =>
    have hb : b = true := hused.resolve_left (by simp [ha])
    have hh := hhuv
    rw [hsem] at hh
    simp only [ha, hb, hguv, Bool.false_and, Bool.or_false, Bool.true_and,
      Bool.or_true, Bool.and_true, decide_eq_true_eq] at hh
    obtain ⟨r, hr, hrv⟩ := hh
    have hrw := hR ha hb r hr
    simp only [pairInput, decide_eq_true_eq] at hrv
    rcases hrv with rfl | rfl <;> simp [hrw]
  | true =>
    cases hb : b with
    | false =>
      have hh := hhuv
      rw [hsem] at hh
      simp only [ha, hb, hguv, Bool.false_and, Bool.or_false, Bool.true_and,
        Bool.or_true, decide_eq_true_eq] at hh
      obtain ⟨s, hs, hsv⟩ := hh
      have hsw := hS ha hb s hs
      simp only [pairInput, decide_eq_true_eq] at hsv
      rcases hsv with rfl | rfl <;> simp [hsw]
    | true =>
      left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ u, ?_⟩
      intro x hgx _
      apply hjoint x hgx
      rw [hsem]
      simp [ha, hb, hgx]

lemma nested_joint_unguarded_coefficients {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (g h : ℕ) (R S : Finset (Fin n)) (a b : Bool)
    (hsem : ∀ x : Fin n → Bool, gateVal n C h x =
      ((decide (∃ r ∈ R, x r = true) || (a && gateVal n C g x)) &&
        (decide (∃ s ∈ S, x s = true) || (b && gateVal n C g x))))
    (hjoint : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C h x = true → graphFun G ∅ x = true)
    (u v : Fin n) (hguv : gateVal n C g (pairInput u v) = true)
    (hhuv : gateVal n C h (pairInput u v) = true)
    (hfree : u ∉ wmax G C g ∧ v ∉ wmax G C g) : a = false ∧ b = false := by
  have hnot : ¬ (a = true ∨ b = true) := by
    intro hused
    exact (nested_joint_guarded g h R S a b hsem hjoint hused u v hguv hhuv).elim
      hfree.1 hfree.2
  cases a <;> cases b <;> simp_all

end PEqualNP.Outside.L_meta_5012.NestedJoint

namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma two_junk_normal_form_marked {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) (hJ : (junk G C).card = 2) :
    ∃ g h : ℕ, g < h ∧ junk G C = {g, h} ∧
      ∃ (A B R S : Finset (Fin n)) (a b : Bool), A.Nonempty ∧ B.Nonempty ∧
        ((a = true ∨ b = true) ↔ InCone n C g h) ∧
        (∀ x : Fin n → Bool, gateVal n C g x =
          (decide (∃ u ∈ A, x u = true) && decide (∃ u ∈ B, x u = true))) ∧
        (∀ x : Fin n → Bool, gateVal n C h x =
          ((decide (∃ u ∈ R, x u = true) || (a && gateVal n C g x)) &&
           (decide (∃ u ∈ S, x u = true) || (b && gateVal n C g x)))) := by
  obtain ⟨g, h, hgh, hjs, hgpure, _⟩ := two_junk_nested_or_pure G C hT hJ
  have hgm : g ∈ junk G C := by rw [hjs]; simp
  have hhm : h ∈ junk G C := by rw [hjs]; simp
  have hgp := (mem_junk_characterization G C g).mp hgm
  have hhp := (mem_junk_characterization G C h).mp hhm
  have hhcone : ∀ k < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and →
      InCone n C k h → k = g := by
    intro k hk hop hkh
    by_cases hb : BelowF G C k
    · exact False.elim (hT k hk h hhp.1 hop hb hhp.2.1 hkh)
    · have hkm := (mem_junk_characterization G C k).mpr ⟨hk, hop, hb⟩
      rw [hjs] at hkm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hkm
      rcases hkm with hkg | rfl
      · exact hkg
      · have := cone_index_lt hkh
        omega
  obtain ⟨A, B, hA, hB, hgfun⟩ :=
    StructuralSemantics.and_of_pure_cone hAO hgp.1 hgp.2.1 hgpure
  obtain ⟨R, S, a, b, hmarked, hhfun⟩ :=
    StructuralSemantics.and_of_one_and_cone_marked hAO g hhp.1 hhp.2.1 hhcone
  exact ⟨g, h, hgh, hjs, A, B, R, S, a, b, hA, hB, hmarked, hgfun, hhfun⟩

end PEqualNP.Outside.L_meta_5012


namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma nested_two_junk_joint_guarded {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) {g h : ℕ}
    (hjs : junk G C = {g, h}) (hnested : InCone n C g h)
    (hjoint : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C h x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
    (u v : Fin n) (hguv : gateVal n C g (pairInput u v) = true)
    (hhuv : gateVal n C h (pairInput u v) = true) :
    u ∈ wmax G C g ∨ v ∈ wmax G C g := by
  have hhm : h ∈ junk G C := by rw [hjs]; simp
  have hhp := (mem_junk_characterization G C h).mp hhm
  have hhcone : ∀ k < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and →
      InCone n C k h → k = g := by
    intro k hk hop hkh
    by_cases hb : BelowF G C k
    · exact False.elim (hT k hk h hhp.1 hop hb hhp.2.1 hkh)
    · have hkm := (mem_junk_characterization G C k).mpr ⟨hk, hop, hb⟩
      rw [hjs] at hkm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hkm
      rcases hkm with hkg | rfl
      · exact hkg
      · have := cone_index_lt hkh
        omega
  obtain ⟨R, S, a, b, hmarked, hsem⟩ :=
    StructuralSemantics.and_of_one_and_cone_marked hAO g hhp.1 hhp.2.1 hhcone
  exact NestedJoint.nested_joint_guarded g h R S a b hsem hjoint
    (hmarked.mpr hnested) u v hguv hhuv

lemma unguarded_two_junk_not_nested {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hT : TopForm G C) {g h : ℕ}
    (hjs : junk G C = {g, h})
    (hjoint : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C h x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)
    (u v : Fin n) (hguv : gateVal n C g (pairInput u v) = true)
    (hhuv : gateVal n C h (pairInput u v) = true)
    (hfree : u ∉ wmax G C g ∧ v ∉ wmax G C g) : ¬ InCone n C g h := by
  intro hnest
  exact (nested_two_junk_joint_guarded G C hAO hT hjs hnest hjoint u v hguv hhuv).elim
    hfree.1 hfree.2

end PEqualNP.Outside.L_meta_5012

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


namespace PEqualNP.Outside.L_meta_5012.MutualBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
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
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
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

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

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
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
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
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
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
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
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
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

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
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
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
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
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

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
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
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
theorem junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
theorem binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
theorem opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
theorem opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
theorem andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
theorem andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
theorem operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
theorem operandReachLt (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) : h < a := by
  have hle := orStep_le (orReaches_reach h _ hr).1
  have hb := opndBound hAO ha b
  omega
theorem operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
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
theorem reachVal {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
    (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
  orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hh
theorem eitherOperand (b c : Fin 2) : c = b ∨ c = 1 - b := by
  fin_cases b <;> fin_cases c <;> decide
theorem oppositeSideWmax (hAO : IsAO2 n C) {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
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
  · exact reachVal hr hj
  · exact reach_var_val x _ t (mem_orIn_reach t ht) hx
theorem orInTrans {w z : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w z) :
    orIn n C z ⊆ orIn n C w :=
  fun x hx => reach_mem_orIn x (hr.trans (mem_orIn_reach x hx))
theorem orStepOpnd (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.or) (b : Fin 2) :
    OrStep n C (n + m) (opnd C m b) :=
  ⟨m, hm, rfl, hop, opndMem hAO hm b, opndBound hAO hm b⟩
theorem inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
theorem orNOfRaw {m : ℕ} (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hn : (orIn n C (n + m)).Nonempty) : m ∈ orN G C := by
  obtain ⟨t, ht⟩ := hn
  simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
  refine ⟨hm, hop, ?_⟩
  intro hb
  have hv : gateVal n C m (pairInput t t) = true :=
    reach_var_val (pairInput t t) _ t (mem_orIn_reach t ht) (pairInput_left t t)
  exact G.irrefl ((graphFun_pair G t t).mp (hb _ hv))
theorem lamAvoidsUstar {m : ℕ} (hm : m ∈ lam G C)
    (hstar : ∀ a ∈ tops G C, ∀ x ∈ side (n := n) C a 0, ∀ y ∈ side C a 1, G.Adj x y) :
    ∃ t : Fin n, ∀ x ∈ orIn n C (n + m), G.Adj t x ∧ s(t, x) ∉ Ustar G C := by
  obtain ⟨_, _, _, a, ha, b, hcard, hr⟩ := Finset.mem_filter.mp hm
  have hsub : orIn n C (n + m) ⊆ side (n := n) C a b :=
    orInTrans (orReaches_reach m _ hr).1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
  refine ⟨t, fun x hx => ?_⟩
  have hts : t ∈ side (n := n) C a (1 - b) := by simp [ht]
  have hstar' : s(t, x) ∈ starEdges G C := by
    unfold starEdges
    refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ?_⟩
    fin_cases b
    · exact ⟨(x, t), Finset.mem_product.mpr ⟨hsub hx, hts⟩, Sym2.eq_swap⟩
    · exact ⟨(t, x), Finset.mem_product.mpr ⟨hts, hsub hx⟩, rfl⟩
  refine ⟨?_, fun he => (Finset.mem_sdiff.mp he).2 hstar'⟩
  fin_cases b
  · exact (hstar a ha x (hsub hx) t hts).symm
  · exact hstar a ha t hts x (hsub hx)

lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩

def coveredByJunk (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Finset (Sym2 (Fin n)) :=
  (junk G C).biUnion fun j => (gammaE G C j).filter fun e =>
    ¬ Disjoint e.toFinset (wmax G C j)

def Joint (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j k : ℕ) : Prop :=
  ∀ x : Fin n → Bool, gateVal n C j x = true → gateVal n C k x = true →
    graphFun G ∅ x = true

lemma joint_comm {j k : ℕ} (h : Joint G C j k) : Joint G C k j :=
  fun x hk hj => h x hj hk

lemma freeOfWmax {u v : Fin n} (he : s(u,v) ∈ Ustar G C \ coveredByJunk G C)
    {j : ℕ} (hj : j ∈ junk G C) (hval : gateVal n C j (pairInput u v) = true)
    {t : Fin n} (ht : t = u ∨ t = v) : t ∉ wmax G C j := by
  intro hw
  apply (Finset.mem_sdiff.mp he).2
  refine Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1,
      u, v, rfl, hval⟩
  · intro hd
    exact (Finset.disjoint_left.mp hd) (by simpa using ht) hw

lemma memJunkPair {j k a : ℕ} (hs : junk G C = {j,k}) (ha : a ∈ junk G C) :
    a = j ∨ a = k := by
  simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using ha

lemma residualJoint (hL : IsLeastAO G C) (hT : TopForm G C) {j k : ℕ}
    (hs : junk G C = {j,k}) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C \ coveredByJunk G C) :
    Joint G C j k ∧ gateVal n C j (pairInput u v) = true ∧
      gateVal n C k (pairInput u v) = true := by
  have hU := (Finset.mem_sdiff.mp he).1
  have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1
  obtain ⟨a, ha, hv⟩ := acceptedTop hL hadj
  obtain ⟨hl, ho, hb⟩ := topData ha
  have traces (b : Fin 2) := operandSupport hL.1 hT hl ho
    ((andValOperands hL.1 hl ho (pairInput u v)).mp hv b)
  have mixed {b : Fin 2} {t : Fin n} {g : ℕ}
      (ht : t ∈ side (n := n) C a (1-b)) (het : t = u ∨ t = v)
      (hg : g ∈ junk G C) (hr : OrReaches n C (opnd C a b) g)
      (hgval : gateVal n C g (pairInput u v) = true) : False :=
    freeOfWmax he hg hgval het (oppositeSideWmax hL.1 ha hr ht)
  rcases traces 0 with ⟨x,hx,hxe⟩ | ⟨g,hg,hrg,hvg⟩ <;>
    rcases traces 1 with ⟨y,hy,hye⟩ | ⟨g',hg',hrg',hvg'⟩
  · have hxy := G.ne_of_adj (topAdj hL.1 ha hx hy)
    have eq : s(u,v) = s(x,y) := by
      rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    exact ((Finset.mem_sdiff.mp hU).2 (eq ▸ Finset.mem_biUnion.mpr ⟨a,ha,
      Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, rfl⟩⟩)).elim
  · exact (mixed (b := 1) (by exact hx) hxe hg' hrg' hvg').elim
  · exact (mixed (b := 0) (by exact hy) hye hg hrg hvg).elim
  · have pair : Joint G C g g' := fun x xv yv =>
      hb x ((andValBoth hL.1 hl ho x).mpr ⟨reachVal hrg xv, reachVal hrg' yv⟩)
    have ne : g ≠ g' := by
      rintro rfl
      obtain ⟨_,_,x,hx,hfx⟩ := junkData hg
      exact Bool.false_ne_true (hfx.symm.trans (pair x hx hx))
    rcases memJunkPair hs hg with eg | eg <;> rcases memJunkPair hs hg' with eg' | eg'
    · exact (ne (eg.trans eg'.symm)).elim
    · simpa only [eg, eg'] using And.intro pair (And.intro hvg hvg')
    · simpa only [eg, eg'] using And.intro (joint_comm pair) (And.intro hvg' hvg)
    · exact (ne (eg.trans eg'.symm)).elim


end PEqualNP.Outside.L_meta_5012.MutualBudget


namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover

lemma residual_nonempty_forces_independent {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    {g h : ℕ} (hjs : junk G C = {g, h})
    (hR : (Ustar G C \ MutualBudget.coveredByJunk G C).Nonempty) :
    ¬ InCone n C g h ∧ ¬ InCone n C h g := by
  have hgmem : g ∈ junk G C := by rw [hjs]; simp
  have hhmem : h ∈ junk G C := by rw [hjs]; simp
  obtain ⟨e, he⟩ := hR
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨hjoint, hgv, hhv⟩ := MutualBudget.residualJoint hL hT hjs he
    have hfreeg : u ∉ wmax G C g ∧ v ∉ wmax G C g :=
      ⟨MutualBudget.freeOfWmax he hgmem hgv (Or.inl rfl),
       MutualBudget.freeOfWmax he hgmem hgv (Or.inr rfl)⟩
    have hfreeh : u ∉ wmax G C h ∧ v ∉ wmax G C h :=
      ⟨MutualBudget.freeOfWmax he hhmem hhv (Or.inl rfl),
       MutualBudget.freeOfWmax he hhmem hhv (Or.inr rfl)⟩
    constructor
    · exact unguarded_two_junk_not_nested G C hL.1 hT hjs hjoint u v hgv hhv hfreeg
    · have hswap : junk G C = {h, g} := hjs.trans (Finset.pair_comm _ _)
      exact unguarded_two_junk_not_nested G C hL.1 hT hswap
        (MutualBudget.joint_comm hjoint) u v hhv hgv hfreeh

lemma junk_pure_of_independent {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hT : TopForm G C)
    {g h : ℕ} (hjs : junk G C = {g, h}) (hind : ¬ InCone n C h g) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ InCone n C k g := by
  have hgm : g ∈ junk G C := by rw [hjs]; simp
  have hgp := (mem_junk_characterization G C g).mp hgm
  intro k hk hand hkg
  by_cases hclean : BelowF G C k
  · exact hT k hk g hgp.1 hand hclean hgp.2.1 hkg
  · have hkm := (mem_junk_characterization G C k).mpr ⟨hk, hand, hclean⟩
    rw [hjs] at hkm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hkm
    rcases hkm with rfl | rfl
    · exact (Nat.lt_irrefl _) (cone_index_lt hkg)
    · exact hind hkg

lemma residual_two_pure_products {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    {g h : ℕ} (hjs : junk G C = {g, h})
    (hR : (Ustar G C \ MutualBudget.coveredByJunk G C).Nonempty) :
    ∃ P Q R S : Finset (Fin n), P.Nonempty ∧ Q.Nonempty ∧ R.Nonempty ∧ S.Nonempty ∧
      (∀ x : Fin n → Bool, gateVal n C g x =
        (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true))) ∧
      (∀ x : Fin n → Bool, gateVal n C h x =
        (decide (∃ r ∈ R, x r = true) && decide (∃ s ∈ S, x s = true))) := by
  have hgmem : g ∈ junk G C := by rw [hjs]; simp
  have hhmem : h ∈ junk G C := by rw [hjs]; simp
  have hgp := (mem_junk_characterization G C g).mp hgmem
  have hhp := (mem_junk_characterization G C h).mp hhmem
  obtain ⟨hngh, hnhg⟩ := residual_nonempty_forces_independent G C hL hT hjs hR
  have hswap : junk G C = {h, g} := hjs.trans (Finset.pair_comm _ _)
  obtain ⟨P, Q, hP, hQ, hgfun⟩ := StructuralSemantics.and_of_pure_cone hL.1
    hgp.1 hgp.2.1 (junk_pure_of_independent G C hT hjs hnhg)
  obtain ⟨R, S, hR, hS, hhfun⟩ := StructuralSemantics.and_of_pure_cone hL.1
    hhp.1 hhp.2.1 (junk_pure_of_independent G C hT hswap hngh)
  exact ⟨P, Q, R, S, hP, hQ, hR, hS, hgfun, hhfun⟩

end PEqualNP.Outside.L_meta_5012

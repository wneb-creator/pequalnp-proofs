import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5226

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Part 1: Generic append-only foldl lemmas

lemma foldl_append_spec {α β : Type} (f : List α → β → α) :
    ∀ (l : List β) (acc : List α),
      (l.foldl (fun w b => w ++ [f w b]) acc).length = acc.length + l.length ∧
      (∀ i < acc.length, (l.foldl (fun w b => w ++ [f w b]) acc)[i]? = acc[i]?) ∧
      (∀ (j : ℕ) (b : β), l[j]? = some b →
        (l.foldl (fun w b => w ++ [f w b]) acc)[acc.length + j]? =
          some (f ((l.take j).foldl (fun w x => w ++ [f w x]) acc) b)) := by
  intro l
  induction l with
  | nil =>
    intro acc
    refine ⟨by simp, fun i _ => rfl, fun j b h => by simp at h⟩
  | cons a t ih =>
    intro acc
    have h1 := ih (acc ++ [f acc a])
    refine ⟨?_, ?_, ?_⟩
    · rw [List.foldl_cons, h1.1, List.length_append, List.length_singleton, List.length_cons]
      omega
    · intro i hi
      simp only [List.foldl_cons]
      have hi' : i < (acc ++ [f acc a]).length := by simp; omega
      rw [h1.2.1 i hi', List.getElem?_append_left hi]
    · intro j b hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [List.foldl_cons, Nat.add_zero, List.take_zero, List.foldl_nil]
        have hi' : acc.length < (acc ++ [f acc a]).length := by simp
        rw [h1.2.1 acc.length hi', List.getElem?_append_right (le_refl _)]
        simp
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        simp only [List.foldl_cons, List.take_succ_cons]
        have hstep := h1.2.2 j' b hj
        simp only [List.length_append, List.length_singleton] at hstep
        have heq : acc.length + (j' + 1) = acc.length + 1 + j' := by omega
        rw [heq]
        exact hstep

lemma foldl_append_take_getD {α β : Type} (f : List α → β → α) (d : α)
    (l : List β) (acc : List α) (k i : ℕ) (hi : i < acc.length + k) (hk : k ≤ l.length) :
    ((l.take k).foldl (fun w x => w ++ [f w x]) acc).getD i d =
      (l.foldl (fun w x => w ++ [f w x]) acc).getD i d := by
  have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hlen : ((l.take k).foldl (fun w x => w ++ [f w x]) acc).length = acc.length + k := by
    rw [(foldl_append_spec f (l.take k) acc).1, List.length_take, Nat.min_eq_left hk]
  have hget := (foldl_append_spec f (l.drop k) ((l.take k).foldl (fun w x => w ++ [f w x]) acc)).2.1 i (by omega)
  simp only [List.getD_eq_getElem?_getD, hget]

-- Part 2: wires, cones, orSets unfolding lemmas

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wireVal n C i.val x = x i := by
  unfold wireVal Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hi : i.val < (List.ofFn x).length := by omega
  have hget := (foldl_append_spec (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
    C.gates (List.ofFn x)).2.1 i.val hi
  rw [List.getD_eq_getElem?_getD, hget, List.getElem?_ofFn]
  simp [i.isLt]

lemma gateVal_eq_wireVal (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wireVal n C (n + j) x := rfl

lemma isAO2_inputs (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have hget : C.gates[j]? = some (gateAt C j) := by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hmem : gateAt C j ∈ C.gates := List.mem_of_getElem? hget
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) hmem
  rcases h_eq : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · simp [h_eq] at hlen
  · simp [h_eq] at hlen
  · have h0 : opnd C j 0 = a := by simp [opnd, h_eq]
    have h1 : opnd C j 1 = b := by simp [opnd, h_eq]
    rw [h0, h1]
    refine ⟨rfl, hAO.2.1 j hj a (by simp [h_eq]), hAO.2.1 j hj b (by simp [h_eq]), hAO.1 (gateAt C j) hmem⟩
  · simp [h_eq] at hlen

lemma gateVal_eval_ao2 (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    gateVal n C j x =
      (gateAt C j).op.eval [wireVal n C (opnd C j 0) x, wireVal n C (opnd C j 1) x] := by
  obtain ⟨hinp, h0, h1, _⟩ := isAO2_inputs n C hAO j hj
  have hgetg : C.gates[j]? = some (gateAt C j) := by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  unfold gateVal Circuit.wires
  have hstep := (foldl_append_spec (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
    C.gates (List.ofFn x)).2.2 j (gateAt C j) hgetg
  rw [List.length_ofFn] at hstep
  rw [List.getD_eq_getElem?_getD, hstep, Option.getD_some, hinp, List.map_cons, List.map_cons, List.map_nil]
  have hw0 := foldl_append_take_getD (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
    false C.gates (List.ofFn x) j (opnd C j 0) (by rw [List.length_ofFn]; exact h0) (Nat.le_of_lt hj)
  have hw1 := foldl_append_take_getD (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
    false C.gates (List.ofFn x) j (opnd C j 1) (by rw [List.length_ofFn]; exact h1) (Nat.le_of_lt hj)
  rw [hw0, hw1]
  rfl

lemma gateVal_and_iff (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C j x = true ↔ wireVal n C (opnd C j 0) x = true ∧ wireVal n C (opnd C j 1) x = true := by
  rw [gateVal_eval_ao2 n C hAO j hj x, hop]
  simp [GateOp.eval]

lemma gateVal_or_iff (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    gateVal n C j x = true ↔ wireVal n C (opnd C j 0) x = true ∨ wireVal n C (opnd C j 1) x = true := by
  rw [gateVal_eval_ao2 n C hAO j hj x, hop]
  simp [GateOp.eval]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones
  have h := (foldl_append_spec (fun cs g =>
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])) C.gates []).1
  change (C.gates.foldl (fun cs g => cs ++ [((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) []))]) []).length = C.gates.length
  rw [h]
  simp

lemma cones_getD_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  have hgetg : C.gates[j]? = some (gateAt C j) := by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  let f : List (List ℕ) → Gate → List ℕ := fun cs g =>
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])
  have hstep := (foldl_append_spec f C.gates []).2.2 j (gateAt C j) hgetg
  have hlen : ((C.gates.take j).foldl (fun w x => w ++ [f w x]) []).length = j := by
    rw [(foldl_append_spec f (C.gates.take j) []).1, List.length_nil, Nat.zero_add,
      List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  change (C.gates.foldl (fun w x => w ++ [f w x]) []).getD j [] = _
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [List.getD_eq_getElem?_getD, hstep, Option.getD_some]
  dsimp only [f]
  rw [hlen]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  congr 1
  exact foldl_append_take_getD f [] C.gates [] j (w - n) (by simp; omega) (Nat.le_of_lt hj)

lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro i hij
    by_cases hj : j < C.gates.length
    · unfold InCone at hij
      rw [cones_getD_eq n C j hj, List.mem_flatMap] at hij
      obtain ⟨w, hw, hmem⟩ := hij
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · omega
      · have hlt := ih (w - n) (by omega) i hmem
        omega
    · unfold InCone at hij
      have hlen : (cones n C).length = C.gates.length := cones_length n C
      have hnone : (cones n C)[j]? = none := List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, hnone] at hij

lemma inCone_of_input (n : ℕ) (C : Circuit) (k j : ℕ) (hj : j < C.gates.length)
    (hk : k < j) (hmem : n + k ∈ (gateAt C j).inputs) : InCone n C k j := by
  unfold InCone
  rw [cones_getD_eq n C j hj, List.mem_flatMap]
  refine ⟨n + k, ?_, ?_⟩
  · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hmem, by omega, by omega⟩
  · simp

lemma inCone_trans_of_input (n : ℕ) (C : Circuit) (i k j : ℕ) (hj : j < C.gates.length)
    (hk : k < j) (hmem : n + k ∈ (gateAt C j).inputs) (hik : InCone n C i k) : InCone n C i j := by
  unfold InCone at hik ⊢
  rw [cones_getD_eq n C j hj, List.mem_flatMap]
  refine ⟨n + k, ?_, ?_⟩
  · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hmem, by omega, by omega⟩
  · simp only [List.mem_cons, Nat.add_sub_cancel_left]; exact Or.inr hik

lemma inCone_trans (n : ℕ) (C : Circuit) :
    ∀ k i j, InCone n C i j → InCone n C j k → InCone n C i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro i j hij hjk
    by_cases hk : k < C.gates.length
    · unfold InCone at hjk
      rw [cones_getD_eq n C k hk, List.mem_flatMap] at hjk
      obtain ⟨w, hw, hmem⟩ := hjk
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      simp only [List.mem_cons] at hmem
      have hweq : w = n + (w - n) := by omega
      rcases hmem with rfl | hmem
      · exact inCone_trans_of_input n C i (w - n) k hk (by omega) (by rw [← hweq]; exact hw.1) hij
      · have hrec : InCone n C i (w - n) := ih (w - n) (by omega) i j hij hmem
        exact inCone_trans_of_input n C i (w - n) k hk (by omega) (by rw [← hweq]; exact hw.1) hrec
    · unfold InCone at hjk
      have hlen : (cones n C).length = C.gates.length := cones_length n C
      have hnone : (cones n C)[k]? = none := List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, hnone] at hjk

def orStepElem (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  cs.length :: match g.op with
    | GateOp.or =>
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
    | _ => []

lemma orStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    orStep n cs g = cs ++ [orStepElem n cs g] := by
  unfold orStep orStepElem
  cases g.op <;> rfl

lemma orSets_eq_foldl (n : ℕ) (C : Circuit) :
    orSets n C = C.gates.foldl (fun cs g => cs ++ [orStepElem n cs g]) [] := by
  unfold orSets
  have hfn : orStep n = fun cs g => cs ++ [orStepElem n cs g] := by
    funext cs g; exact orStep_eq n cs g
  rw [hfn]

lemma orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  rw [orSets_eq_foldl]
  have h := (foldl_append_spec (orStepElem n) C.gates []).1
  simpa using h

lemma orSets_getD_eq (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    (orSets n C).getD k [] =
      k :: match (gateAt C k).op with
        | GateOp.or =>
          ((gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
            (fun w => (orSets n C).getD (w - n) [])
        | _ => [] := by
  have hgetg : C.gates[k]? = some (gateAt C k) := by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  have hstep := (foldl_append_spec (orStepElem n) C.gates []).2.2 k (gateAt C k) hgetg
  have hlen : ((C.gates.take k).foldl (fun w x => w ++ [orStepElem n w x]) []).length = k := by
    rw [(foldl_append_spec (orStepElem n) (C.gates.take k) []).1, List.length_nil, Nat.zero_add,
      List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [orSets_eq_foldl, List.getD_eq_getElem?_getD, hstep, Option.getD_some]
  generalize hacc : (C.gates.take k).foldl (fun w x => w ++ [orStepElem n w x]) [] = acc
  rw [hacc] at hlen
  dsimp only [orStepElem]
  rw [hlen]
  congr 1
  cases (gateAt C k).op <;> try rfl
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  rw [← hacc]
  exact foldl_append_take_getD (orStepElem n) [] C.gates [] k (w - n) (by simp; omega) (Nat.le_of_lt hk)

lemma orReaches_lt_len (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    w - n < C.gates.length := by
  by_contra hge
  have hlen := orSets_length n C
  have hnone : (orSets n C)[w - n]? = none := List.getElem?_eq_none (by omega)
  have hm := h.2
  simp [List.getD_eq_getElem?_getD, hnone] at hm

lemma orReaches_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := by
  refine ⟨by omega, ?_⟩
  rw [Nat.add_sub_cancel_left, orSets_getD_eq n C k hk]
  simp

lemma orReaches_iff_gate (n : ℕ) (C : Circuit) (k g : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔
      g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ u ∈ (gateAt C k).inputs, u < n + k ∧ OrReaches n C u g) := by
  unfold OrReaches
  rw [Nat.add_sub_cancel_left, orSets_getD_eq n C k hk]
  constructor
  · rintro ⟨_, hmem⟩
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · cases hop : (gateAt C k).op <;> rw [hop] at hmem
      · simp at hmem
      · rw [List.mem_flatMap] at hmem
        obtain ⟨u, hu, hgu⟩ := hmem
        simp only [List.mem_filter, decide_eq_true_eq] at hu
        exact Or.inr ⟨rfl, u, hu.1, hu.2.2, hu.2.1, hgu⟩
      · simp at hmem
      · simp at hmem
      · simp at hmem
  · rintro (rfl | ⟨hop, u, hu, hult, hge, hgu⟩)
    · exact ⟨by omega, by simp⟩
    · refine ⟨by omega, ?_⟩
      rw [hop]
      simp only [List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨u, by simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hu, hge, hult⟩, hgu⟩

lemma orReaches_trans (n : ℕ) (C : Circuit) :
    ∀ k m g, OrReaches n C (n + k) m → OrReaches n C (n + m) g → OrReaches n C (n + k) g := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro m g hkm hmg
    have hk : k < C.gates.length := by
      have := orReaches_lt_len n C (n + k) m hkm; omega
    rw [orReaches_iff_gate n C k m hk] at hkm
    rcases hkm with rfl | ⟨hop, u, hu, hult, hge, hgu⟩
    · exact hmg
    · rw [orReaches_iff_gate n C k g hk]
      refine Or.inr ⟨hop, u, hu, hult, ?_⟩
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq]
      exact ih (u - n) (by omega) m g (by rw [← hu_eq]; exact ⟨hge, hgu⟩) hmg

lemma orReaches_trans_wire (n : ℕ) (C : Circuit) (w m g : ℕ)
    (hwm : OrReaches n C w m) (hmg : OrReaches n C (n + m) g) : OrReaches n C w g := by
  have hge := hwm.1
  have hweq : w = n + (w - n) := by omega
  rw [hweq]
  exact orReaches_trans n C (w - n) m g (by rwa [← hweq]) hmg

lemma orReaches_inCone_or_eq (n : ℕ) (C : Circuit) :
    ∀ k g, OrReaches n C (n + k) g → g = k ∨ InCone n C g k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro g hg
    have hk : k < C.gates.length := by
      have := orReaches_lt_len n C (n + k) g hg; omega
    rw [orReaches_iff_gate n C k g hk] at hg
    rcases hg with rfl | ⟨_, u, hu, hult, hge, hgu⟩
    · exact Or.inl rfl
    · have hu_eq : u = n + (u - n) := by omega
      have hrec := ih (u - n) (by omega) g (by rw [← hu_eq]; exact ⟨hge, hgu⟩)
      rcases hrec with rfl | hcone
      · exact Or.inr (inCone_of_input n C (u - n) k hk (by omega) (by rwa [← hu_eq]))
      · exact Or.inr (inCone_trans_of_input n C g (u - n) k hk (by omega) (by rwa [← hu_eq]) hcone)

lemma orReaches_imp_inCone_parent (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (t : ℕ)
    (ht : t < C.gates.length) (b : Fin 2) (g : ℕ) (hr : OrReaches n C (opnd C t b) g) :
    InCone n C g t := by
  obtain ⟨hinp, h0, h1, _⟩ := isAO2_inputs n C hAO t ht
  have hwlt : opnd C t b < n + t := by fin_cases b <;> assumption
  have hwmem : opnd C t b ∈ (gateAt C t).inputs := by rw [hinp]; fin_cases b <;> simp
  have hge : n ≤ opnd C t b := hr.1
  have hweq : opnd C t b = n + (opnd C t b - n) := by omega
  have hr' : OrReaches n C (n + (opnd C t b - n)) g := by rwa [← hweq]
  rcases orReaches_inCone_or_eq n C (opnd C t b - n) g hr' with rfl | hc
  · exact inCone_of_input n C (opnd C t b - n) t ht (by omega) (by rwa [← hweq])
  · exact inCone_trans_of_input n C g (opnd C t b - n) t ht (by omega) (by rwa [← hweq]) hc

lemma orReaches_val_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool) :
    ∀ k g, OrReaches n C (n + k) g → gateVal n C g x = true → gateVal n C k x = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro g hg hval
    have hk : k < C.gates.length := by
      have := orReaches_lt_len n C (n + k) g hg; omega
    rw [orReaches_iff_gate n C k g hk] at hg
    rcases hg with rfl | ⟨hop, u, hu, hult, hge, hgu⟩
    · exact hval
    · obtain ⟨hinp, _, _, _⟩ := isAO2_inputs n C hAO k hk
      rw [gateVal_or_iff n C hAO k hk hop x]
      have hu_eq : u = n + (u - n) := by omega
      have hgv := ih (u - n) (by omega) g (by rw [← hu_eq]; exact ⟨hge, hgu⟩) hval
      rw [hinp] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact Or.inl (by rw [hu_eq]; exact hgv)
      · exact Or.inr (by rw [hu_eq]; exact hgv)

lemma orReaches_wireVal_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool)
    (w g : ℕ) (hr : OrReaches n C w g) (hval : gateVal n C g x = true) :
    wireVal n C w x = true := by
  have hge := hr.1
  have hweq : w = n + (w - n) := by omega
  rw [hweq]
  exact orReaches_val_true n C hAO x (w - n) g (by rwa [← hweq]) hval

lemma orIn_wireVal_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool)
    (w : ℕ) (u : Fin n) (hu : u ∈ orIn n C w) (hxu : x u = true) :
    wireVal n C w x = true := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with heq | ⟨k, hk, hr, hop, hmem⟩
  · rw [← heq, wireVal_input]; exact hxu
  · have hgv : gateVal n C k x = true := by
      obtain ⟨hinp, _, _, _⟩ := isAO2_inputs n C hAO k hk
      rw [gateVal_or_iff n C hAO k hk hop x]
      rw [hinp] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with heq0 | heq1
      · left; rw [← heq0, wireVal_input]; exact hxu
      · right; rw [← heq1, wireVal_input]; exact hxu
    exact orReaches_wireVal_true n C hAO x w k hr hgv

lemma orIn_subset_of_orReaches (n : ℕ) (C : Circuit) (w g : ℕ) (hr : OrReaches n C w g) :
    orIn n C (n + g) ⊆ orIn n C w := by
  intro v hv
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rcases hv with heq | ⟨k, hk, hgk, hopk, hmemk⟩
  · exfalso; have := v.isLt; omega
  · exact Or.inr ⟨k, hk, orReaches_trans_wire n C w g k hr hgk, hopk, hmemk⟩

lemma orIn_subset_of_input_or (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (u : ℕ) (hu : u ∈ (gateAt C k).inputs) (hult : u < n + k) :
    orIn n C u ⊆ orIn n C (n + k) := by
  intro v hv
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rcases hv with heq | ⟨m, hm, hr, hopm, hmemm⟩
  · exact Or.inr ⟨k, hk, orReaches_self n C k hk, hop, by rwa [heq]⟩
  · refine Or.inr ⟨m, hm, ?_, hopm, hmemm⟩
    rw [orReaches_iff_gate n C k m hk]
    exact Or.inr ⟨hop, u, hu, hult, hr⟩

lemma pure_or_wireVal_imp_orIn (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w < n + C.gates.length,
      (∀ g, OrReaches n C w g → (gateAt C g).op ≠ GateOp.and) →
      wireVal n C w x = true → ∃ u ∈ orIn n C w, x u = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwlt hnoand hval
    by_cases hwn : w < n
    · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · simp [orIn]
      · rw [← wireVal_input n C x ⟨w, hwn⟩]; exact hval
    · let k := w - n
      have hweq : w = n + k := by omega
      have hk : k < C.gates.length := by omega
      have hne_and : (gateAt C k).op ≠ GateOp.and :=
        hnoand k (by rw [hweq]; exact orReaches_self n C k hk)
      obtain ⟨hinp, h0, h1, hor⟩ := isAO2_inputs n C hAO k hk
      have hop : (gateAt C k).op = GateOp.or := by
        rcases hor with ha | ho
        · exact (hne_and ha).elim
        · exact ho
      have hgv : gateVal n C k x = true := by rwa [gateVal_eq_wireVal, ← hweq]
      rw [gateVal_or_iff n C hAO k hk hop x] at hgv
      have hsub : ∀ b : Fin 2,
          (∀ g, OrReaches n C (opnd C k b) g → (gateAt C g).op ≠ GateOp.and) := by
        intro b g hrg
        apply hnoand g
        rw [hweq, orReaches_iff_gate n C k g hk]
        refine Or.inr ⟨hop, opnd C k b, ?_, ?_, hrg⟩
        · rw [hinp]; fin_cases b <;> simp
        · fin_cases b <;> assumption
      rcases hgv with hv0 | hv1
      · obtain ⟨u, hu, hxu⟩ := ih (opnd C k 0) (by omega) (by omega) (hsub 0) hv0
        have hinc := orIn_subset_of_input_or n C k hk hop (opnd C k 0) (by rw [hinp]; simp) h0
        exact ⟨u, by rw [hweq]; exact hinc hu, hxu⟩
      · obtain ⟨u, hu, hxu⟩ := ih (opnd C k 1) (by omega) (by omega) (hsub 1) hv1
        have hinc := orIn_subset_of_input_or n C k hk hop (opnd C k 1) (by rw [hinp]; simp) h1
        exact ⟨u, by rw [hweq]; exact hinc hu, hxu⟩

lemma orIn_and_eq_empty (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) : orIn n C (n + j) = ∅ := by
  ext v
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
    not_or, not_exists, not_and]
  refine ⟨by omega, fun k _ hr hopk _ => ?_⟩
  rw [orReaches_iff_gate n C j k hj] at hr
  rcases hr with rfl | ⟨hor, _⟩
  · rw [hop] at hopk; cases hopk
  · rw [hop] at hor; cases hor

lemma orIn_input_eq_singleton (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    orIn n C w = {⟨w, hw⟩} := by
  ext v
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (heq | ⟨k, _, hr, _, _⟩)
    · exact Fin.ext heq
    · have := hr.1; omega
  · intro heq; subst heq; exact Or.inl rfl

-- Part 3: Structural TopForm lemmas

lemma graphFun_empty_pairInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true → G.Adj u v := by
  intro h
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and,
    exists_false, false_or] at h
  obtain ⟨a, b, hab, ha, hb⟩ := h
  simp only [pairInput, decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (G.loopless.irrefl _ hab).elim
  · exact hab
  · exact hab.symm
  · exact (G.loopless.irrefl _ hab).elim

lemma graphFun_empty_oneHot_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    graphFun G ∅ (fun v => decide (v = u)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and,
    exists_false, false_or] at h
  obtain ⟨a, b, hab, rfl, rfl⟩ := h
  exact G.loopless.irrefl _ hab

lemma orN_witness_of_non_centreless {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (t : ℕ) (ht : t ∈ tops G C) (hnc : t ∉ centreless G C) (b : Fin 2)
    (j : ℕ) (hj : j ∈ junk G C) (hr : OrReaches n C (opnd C t b) j) :
    ∃ m ∈ orN G C \ lam G C, OrReaches n C (opnd C t b) m ∧ OrReaches n C (n + m) j := by
  have hjmem : j ∈ junk G C := hj
  unfold junk gatesWhere at hjmem
  rw [Finset.mem_filter, Finset.mem_range] at hjmem
  unfold IsDirtyAnd IsDirty at hjmem
  have hjlt : j < C.gates.length := hjmem.1
  have hjop : (gateAt C j).op = GateOp.and := hjmem.2.1
  obtain ⟨xd, hjxd, hfxd⟩ := hjmem.2.2.2
  have hside_ne : side (n := n) C t b ≠ ∅ := by
    intro hemp
    apply hnc
    simp only [centreless, Finset.mem_filter]
    refine ⟨ht, ?_⟩
    fin_cases b
    · exact Or.inl hemp
    · exact Or.inr hemp
  have hwn : n ≤ opnd C t b := hr.1
  let k0 := opnd C t b - n
  have hk0_eq : opnd C t b = n + k0 := by omega
  have hk0_lt : k0 < C.gates.length := orReaches_lt_len n C (opnd C t b) j hr
  have hk0_ne : k0 ≠ j := by
    intro heq; subst heq
    apply hside_ne
    change orIn n C (opnd C t b) = ∅
    rw [hk0_eq]
    exact orIn_and_eq_empty n C k0 hk0_lt hjop
  have hk0_or : (gateAt C k0).op = GateOp.or := by
    have hr0 : OrReaches n C (n + k0) j := by rwa [← hk0_eq]
    rw [orReaches_iff_gate n C k0 j hk0_lt] at hr0
    rcases hr0 with rfl | ⟨hop, _⟩
    · exact (hk0_ne rfl).elim
    · exact hop
  let P : ℕ → Prop := fun m =>
    m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
      OrReaches n C (opnd C t b) m ∧ OrReaches n C (n + m) j
  have hex : ∃ m, P m := ⟨k0, hk0_lt, hk0_or, by rw [hk0_eq]; exact orReaches_self n C k0 hk0_lt,
    by rwa [← hk0_eq]⟩
  classical
  let m := Nat.find hex
  have hm : P m := Nat.find_spec hex
  have hm_min : ∀ m' < m, ¬ P m' := fun m' hlt => Nat.find_min hex hlt
  obtain ⟨hmlt, hmop, hrm1, hrm2⟩ := hm
  have hm_ne_j : m ≠ j := by
    intro heq; rw [heq, hjop] at hmop; cases hmop
  rw [orReaches_iff_gate n C m j hmlt] at hrm2
  rcases hrm2 with heq | ⟨_, u, hu, hult, hru⟩
  · exact (hm_ne_j heq.symm).elim
  · have hu_eq : u = n + (u - n) := by have := hru.1; omega
    have hu_is_j : u - n = j := by
      by_contra hne
      have hult_c : u - n < C.gates.length := orReaches_lt_len n C u j hru
      have hru' : OrReaches n C (n + (u - n)) j := by rwa [← hu_eq]
      rw [orReaches_iff_gate n C (u - n) j hult_c] at hru'
      rcases hru' with heq | ⟨huop, _⟩
      · exact hne heq.symm
      · have hrm_u : OrReaches n C (opnd C t b) (u - n) := by
          rw [hk0_eq]
          apply orReaches_trans n C k0 m (u - n) (by rwa [← hk0_eq])
          rw [orReaches_iff_gate n C m (u - n) hmlt]
          have hself : OrReaches n C u (u - n) := by
            have h1 := orReaches_self n C (u - n) hult_c
            rwa [← hu_eq] at h1
          exact Or.inr ⟨hmop, u, hu, hult, hself⟩
        exact hm_min (u - n) (by omega) ⟨hult_c, huop, hrm_u, by rwa [← hu_eq]⟩
    have hu_val : u = n + j := by omega
    have hm_orN : m ∈ orN G C := by
      simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
      refine ⟨hmlt, hmop, fun hbf => ?_⟩
      have hrmj : OrReaches n C (n + m) j := by
        rw [orReaches_iff_gate n C m j hmlt]
        exact Or.inr ⟨hmop, u, hu, hult, hru⟩
      have hgm := orReaches_val_true n C hAO xd m j hrmj hjxd
      have hft := hbf xd hgm
      rw [hfxd] at hft; cases hft
    have hm_not_lam : m ∉ lam G C := by
      simp only [lam, Finset.mem_filter]
      rintro ⟨_, hne0, hne1, _⟩
      obtain ⟨hinp, _, _, _⟩ := isAO2_inputs n C hAO m hmlt
      rw [hinp] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      have hemp := orIn_and_eq_empty n C j hjlt hjop
      rcases hu with heq0 | heq1
      · rw [← heq0, hu_val, hemp] at hne0; exact Finset.not_nonempty_empty hne0
      · rw [← heq1, hu_val, hemp] at hne1; exact Finset.not_nonempty_empty hne1
    have hrmj : OrReaches n C (n + m) j := by
      rw [orReaches_iff_gate n C m j hmlt]
      exact Or.inr ⟨hmop, u, hu, hult, hru⟩
    exact ⟨m, Finset.mem_sdiff.mpr ⟨hm_orN, hm_not_lam⟩, hrm1, hrmj⟩

-- Part 4: Finite G11 Combinatorics over Fin 2048

def g11List : List (ℕ × ℕ) :=
  [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
   (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

def g11Graph : SimpleGraph (Fin 11) := edgeGraph 11 g11List

def maskBit (m : Fin 2048) (v : Fin 11) : Bool :=
  m.val.testBit v.val

def maskCard (m : Fin 2048) : ℕ :=
  (List.finRange 11).countP (fun v => maskBit m v)

def adjB (u v : ℕ) : Bool :=
  u != v && ((u, v) ∈ g11List || (v, u) ∈ g11List)

def uncovList (m : Fin 2048) : List (ℕ × ℕ) :=
  g11List.filter (fun e => !(m.val.testBit e.1) && !(m.val.testBit e.2))

def noCrossPair (e1 e2 : ℕ × ℕ) : Bool :=
  e1.1 != e2.1 && e1.1 != e2.2 && e1.2 != e2.1 && e1.2 != e2.2 &&
  !adjB e1.1 e2.1 && !adjB e1.1 e2.2 && !adjB e1.2 e2.1 && !adjB e1.2 e2.2

def allPairsNoCross : List (ℕ × ℕ) → Bool
  | [] => true
  | e :: rest => rest.all (fun e' => noCrossPair e e') && allPairsNoCross rest

def hasCommonInT (m : Fin 2048) (x y : ℕ) : Bool :=
  (List.range 11).any (fun z => m.val.testBit z && adjB z x && adjB z y)

def checkOrient (m : Fin 2048) (p1 q1 p2 q2 : ℕ) : Bool :=
  !(hasCommonInT m p1 q2 && hasCommonInT m q1 p2 && hasCommonInT m q1 q2) ||
  (List.range 11).all (fun z => !(m.val.testBit z && adjB z p1) || adjB z q2)

def checkTripleForList (m : Fin 2048) : List (ℕ × ℕ) → Bool
  | [e1, e2] =>
    checkOrient m e1.1 e1.2 e2.1 e2.2 &&
    checkOrient m e1.1 e1.2 e2.2 e2.1 &&
    checkOrient m e1.2 e1.1 e2.1 e2.2 &&
    checkOrient m e1.2 e1.1 e2.2 e2.1
  | _ => true

def checkG11Mask (m : Fin 2048) : Bool :=
  let tc := maskCard m
  let ul := uncovList m
  (7 ≤ tc + ul.length) &&
  (!(tc + ul.length == 7) || (4 ≤ tc && allPairsNoCross ul)) &&
  (!(tc == 5 && ul.length == 2) || checkTripleForList m ul)

lemma g11_all_masks_ok_split :
    ∀ a : Fin 64, ∀ b : Fin 32, checkG11Mask ⟨a.val * 32 + b.val, by omega⟩ = true := by decide

lemma g11_all_masks_ok : ∀ m : Fin 2048, checkG11Mask m = true := by
  intro m
  have h := g11_all_masks_ok_split ⟨m.val / 32, by omega⟩ ⟨m.val % 32, by omega⟩
  have heq : (⟨m.val / 32 * 32 + m.val % 32, by omega⟩ : Fin 2048) = m := by
    ext; dsimp only; omega
  rwa [heq] at h

def finsetToMaskNat (T : Finset (Fin 11)) : List (Fin 11) → ℕ
  | [] => 0
  | v :: vs => (if v ∈ T then 2 ^ v.val else 0) ||| finsetToMaskNat T vs

lemma finsetToMaskNat_lt (T : Finset (Fin 11)) : ∀ l : List (Fin 11), finsetToMaskNat T l < 2048
  | [] => by simp [finsetToMaskNat]
  | v :: vs => by
    unfold finsetToMaskNat
    have hvs := finsetToMaskNat_lt T vs
    have hv : (if v ∈ T then 2 ^ v.val else 0) < 2 ^ 11 := by
      split_ifs
      · exact Nat.pow_lt_pow_right (by omega) v.isLt
      · omega
    exact Nat.or_lt_two_pow hv hvs

lemma finsetToMaskNat_testBit (T : Finset (Fin 11)) (u : Fin 11) :
    ∀ l : List (Fin 11), (finsetToMaskNat T l).testBit u.val = decide (u ∈ l ∧ u ∈ T)
  | [] => by simp [finsetToMaskNat]
  | v :: vs => by
    unfold finsetToMaskNat
    rw [Nat.testBit_or, finsetToMaskNat_testBit T u vs]
    by_cases hvT : v ∈ T
    · simp only [hvT, ↓reduceIte, Nat.testBit_two_pow]
      by_cases huv : v = u
      · subst huv; simp [hvT]
      · have hne : v.val ≠ u.val := fun h => huv (Fin.ext h)
        simp [hne, Ne.symm huv]
    · simp only [hvT, ↓reduceIte, Nat.zero_testBit, Bool.false_or]
      by_cases huv : u = v
      · subst huv; simp [hvT]
      · simp [huv]

def finsetToMask (T : Finset (Fin 11)) : Fin 2048 :=
  ⟨finsetToMaskNat T (List.finRange 11), finsetToMaskNat_lt T (List.finRange 11)⟩

lemma maskBit_finsetToMask (T : Finset (Fin 11)) (u : Fin 11) :
    maskBit (finsetToMask T) u = decide (u ∈ T) := by
  unfold maskBit finsetToMask
  rw [finsetToMaskNat_testBit]
  simp [List.mem_finRange]

lemma maskCard_finsetToMask (T : Finset (Fin 11)) :
    maskCard (finsetToMask T) = T.card := by
  unfold maskCard
  have heq : (List.finRange 11).countP (fun v => maskBit (finsetToMask T) v) =
      (List.finRange 11).countP (fun v => decide (v ∈ T)) := by
    congr 1; funext v; exact maskBit_finsetToMask T v
  rw [heq, List.countP_eq_length_filter]
  have hnodup : ((List.finRange 11).filter (fun v => decide (v ∈ T))).Nodup :=
    (List.nodup_finRange 11).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  congr 1
  ext v
  simp

lemma g11List_valid_nodup :
    g11List.Nodup ∧
    (∀ e ∈ g11List, e.1 < 11 ∧ e.2 < 11 ∧ e.1 < e.2) := by decide

lemma g11Graph_adj_iff_adjB (u v : Fin 11) :
    g11Graph.Adj u v ↔ adjB u.val v.val = true := by
  unfold g11Graph edgeGraph adjB
  simp only [Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hne, hmem⟩
    exact ⟨fun h => hne (Fin.ext h), hmem⟩
  · rintro ⟨hne, hmem⟩
    exact ⟨fun h => hne (congrArg Fin.val h), hmem⟩

lemma allPairsNoCross_spec : ∀ l : List (ℕ × ℕ), allPairsNoCross l = true →
    ∀ e1 ∈ l, ∀ e2 ∈ l, e1 ≠ e2 → noCrossPair e1 e2 = true ∨ noCrossPair e2 e1 = true := by
  intro l
  induction l with
  | nil => intro _ _ h; simp at h
  | cons a t ih =>
    intro h e1 he1 e2 he2 hne
    simp only [allPairsNoCross, Bool.and_eq_true, List.all_eq_true] at h
    simp only [List.mem_cons] at he1 he2
    rcases he1 with rfl | he1 <;> rcases he2 with rfl | he2
    · exact (hne rfl).elim
    · exact Or.inl (h.1 e2 he2)
    · exact Or.inr (h.1 e1 he1)
    · exact ih h.2 e1 he1 e2 he2 hne

lemma uncovList_card_le_and_mem (T : Finset (Fin 11)) (F : Finset (Sym2 (Fin 11)))
    (hcov : (g11Graph.deleteEdges (F : Set (Sym2 (Fin 11)))).IsVertexCover (T : Set (Fin 11))) :
    (uncovList (finsetToMask T)).length ≤ F.card ∧
    ∀ e ∈ uncovList (finsetToMask T), ∃ h1 : e.1 < 11, ∃ h2 : e.2 < 11,
      e.1 < e.2 ∧
      (⟨e.1, h1⟩ : Fin 11) ∉ T ∧
      (⟨e.2, h2⟩ : Fin 11) ∉ T ∧
      s((⟨e.1, h1⟩ : Fin 11), (⟨e.2, h2⟩ : Fin 11)) ∈ F := by
  have hmemF : ∀ e ∈ uncovList (finsetToMask T), ∃ h1 : e.1 < 11, ∃ h2 : e.2 < 11,
      e.1 < e.2 ∧
      (⟨e.1, h1⟩ : Fin 11) ∉ T ∧
      (⟨e.2, h2⟩ : Fin 11) ∉ T ∧
      s((⟨e.1, h1⟩ : Fin 11), (⟨e.2, h2⟩ : Fin 11)) ∈ F := by
    intro e he
    simp only [uncovList, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at he
    have hvalid := g11List_valid_nodup.2 e he.1
    let u : Fin 11 := ⟨e.1, hvalid.1⟩
    let v : Fin 11 := ⟨e.2, hvalid.2.1⟩
    have hu : u ∉ T := by
      intro huT
      have hmb := maskBit_finsetToMask T u
      simp only [huT, decide_true] at hmb
      unfold maskBit at hmb
      rw [hmb] at he
      cases he.2.1
    have hv : v ∉ T := by
      intro hvT
      have hmb := maskBit_finsetToMask T v
      simp only [hvT, decide_true] at hmb
      unfold maskBit at hmb
      rw [hmb] at he
      cases he.2.2
    refine ⟨hvalid.1, hvalid.2.1, hvalid.2.2, hu, hv, ?_⟩
    by_contra hnotF
    have hadj : (g11Graph.deleteEdges (F : Set (Sym2 (Fin 11)))).Adj u v := by
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨⟨?_, Or.inl he.1⟩, hnotF⟩
      intro heq
      have : e.1 = e.2 := congrArg Fin.val heq
      omega
    have := hcov hadj
    rcases this with h1 | h2
    · exact hu h1
    · exact hv h2
  refine ⟨?_, hmemF⟩
  let U := uncovList (finsetToMask T)
  have hnodupU : U.Nodup := g11List_valid_nodup.1.filter _
  let emb : ℕ × ℕ → Sym2 (Fin 11) := fun e => s(Fin.ofNat 11 e.1, Fin.ofNat 11 e.2)
  have hmap_nodup : (U.map emb).Nodup := by
    rw [List.nodup_map_iff_inj_on hnodupU]
    intro a ha b hb heq
    have ha' := g11List_valid_nodup.2 a (List.mem_of_mem_filter ha)
    have hb' := g11List_valid_nodup.2 b (List.mem_of_mem_filter hb)
    simp only [emb, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at heq
    have hf : ∀ x < 11, (Fin.ofNat 11 x).val = x := fun x hx => by
      simp [Fin.ofNat, Nat.mod_eq_of_lt hx]
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
      rw [hf a.1 ha'.1, hf b.1 hb'.1] at e1
      rw [hf a.2 ha'.2.1, hf b.2 hb'.2.1] at e2
      exact Prod.ext e1 e2
    · have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
      rw [hf a.1 ha'.1, hf b.2 hb'.2.1] at e1
      rw [hf a.2 ha'.2.1, hf b.1 hb'.1] at e2
      omega
  have hsub : (U.map emb).toFinset ⊆ F := by
    intro s hs
    simp only [List.mem_toFinset, List.mem_map] at hs
    obtain ⟨e, he, rfl⟩ := hs
    obtain ⟨h1, h2, _, _, _, hF⟩ := hmemF e he
    have hf1 : Fin.ofNat 11 e.1 = ⟨e.1, h1⟩ := by ext; simp [Fin.ofNat, Nat.mod_eq_of_lt h1]
    have hf2 : Fin.ofNat 11 e.2 = ⟨e.2, h2⟩ := by ext; simp [Fin.ofNat, Nat.mod_eq_of_lt h2]
    dsimp only [emb]
    rw [hf1, hf2]
    exact hF
  calc U.length = (U.map emb).length := (List.length_map emb).symm
    _ = (U.map emb).toFinset.card := (List.toFinset_card_of_nodup hmap_nodup).symm
    _ ≤ F.card := Finset.card_le_card hsub

lemma noCrossPair_imp_graph (e1 e2 : ℕ × ℕ)
    (h1 : e1.1 < 11 ∧ e1.2 < 11) (h2 : e2.1 < 11 ∧ e2.2 < 11)
    (hnc : noCrossPair e1 e2 = true ∨ noCrossPair e2 e1 = true) :
    let u1 : Fin 11 := ⟨e1.1, h1.1⟩
    let v1 : Fin 11 := ⟨e1.2, h1.2⟩
    let u2 : Fin 11 := ⟨e2.1, h2.1⟩
    let v2 : Fin 11 := ⟨e2.2, h2.2⟩
    (u1 ≠ u2 ∧ u1 ≠ v2 ∧ v1 ≠ u2 ∧ v1 ≠ v2) ∧
    (¬g11Graph.Adj u1 u2 ∧ ¬g11Graph.Adj u1 v2 ∧ ¬g11Graph.Adj v1 u2 ∧ ¬g11Graph.Adj v1 v2) := by
  have hnotadj : ∀ a b : Fin 11, adjB a.val b.val = false → ¬g11Graph.Adj a b := by
    intro a b hab hG
    rw [g11Graph_adj_iff_adjB, hab] at hG
    cases hG
  have hsym : ∀ a b : Fin 11, adjB a.val b.val = adjB b.val a.val := by
    intro a b; unfold adjB
    by_cases h : a.val = b.val
    · simp [h]
    · have h1' : (a.val != b.val) = true := by simp [h]
      have h2' : (b.val != a.val) = true := by simp [Ne.symm h]
      simp [h1', h2', Bool.or_comm]
  have hneq : ∀ a b : Fin 11, (a.val != b.val) = true → a ≠ b := by
    intro a b h heq; subst heq; simp at h
  rcases hnc with h | h
  · simp only [noCrossPair, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨⟨hneq _ _ h.1.1.1.1.1.1.1, hneq _ _ h.1.1.1.1.1.1.2,
            hneq _ _ h.1.1.1.1.1.2, hneq _ _ h.1.1.1.1.2⟩,
           ⟨hnotadj _ _ h.1.1.1.2, hnotadj _ _ h.1.1.2, hnotadj _ _ h.1.2, hnotadj _ _ h.2⟩⟩
  · simp only [noCrossPair, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨⟨(hneq _ _ h.1.1.1.1.1.1.1).symm, (hneq _ _ h.1.1.1.1.1.2).symm,
            (hneq _ _ h.1.1.1.1.1.1.2).symm, (hneq _ _ h.1.1.1.1.2).symm⟩,
           ⟨hnotadj _ _ (by rw [hsym]; exact h.1.1.1.2),
            hnotadj _ _ (by rw [hsym]; exact h.1.2),
            hnotadj _ _ (by rw [hsym]; exact h.1.1.2),
            hnotadj _ _ (by rw [hsym]; exact h.2)⟩⟩

lemma hasCommonInT_of_exists (T : Finset (Fin 11)) (x y z : Fin 11)
    (hz : z ∈ T) (h1 : g11Graph.Adj z x) (h2 : g11Graph.Adj z y) :
    hasCommonInT (finsetToMask T) x.val y.val = true := by
  unfold hasCommonInT
  rw [List.any_eq_true]
  refine ⟨z.val, List.mem_range.mpr z.isLt, ?_⟩
  simp only [Bool.and_eq_true]
  have hmb : (finsetToMask T).val.testBit z.val = true := by
    have := maskBit_finsetToMask T z
    unfold maskBit at this
    rw [this, decide_eq_true hz]
  exact ⟨⟨hmb, (g11Graph_adj_iff_adjB z x).mp h1⟩, (g11Graph_adj_iff_adjB z y).mp h2⟩

lemma checkOrient_spec (T : Finset (Fin 11)) (p1 q1 p2 q2 : Fin 11)
    (hco : checkOrient (finsetToMask T) p1.val q1.val p2.val q2.val = true)
    (hz1 : ∃ z ∈ T, g11Graph.Adj z p1 ∧ g11Graph.Adj z q2)
    (hz2 : ∃ z ∈ T, g11Graph.Adj z q1 ∧ g11Graph.Adj z p2)
    (hz3 : ∃ z ∈ T, g11Graph.Adj z q1 ∧ g11Graph.Adj z q2) :
    ∀ z ∈ T, g11Graph.Adj z p1 → g11Graph.Adj z q2 := by
  obtain ⟨z1, hz1T, h1a, h1b⟩ := hz1
  obtain ⟨z2, hz2T, h2a, h2b⟩ := hz2
  obtain ⟨z3, hz3T, h3a, h3b⟩ := hz3
  have hc1 := hasCommonInT_of_exists T p1 q2 z1 hz1T h1a h1b
  have hc2 := hasCommonInT_of_exists T q1 p2 z2 hz2T h2a h2b
  have hc3 := hasCommonInT_of_exists T q1 q2 z3 hz3T h3a h3b
  unfold checkOrient at hco
  rw [hc1, hc2, hc3] at hco
  simp only [Bool.and_true, Bool.not_true, Bool.false_or, List.all_eq_true] at hco
  intro z hzT hzp1
  have hzspec := hco z.val (List.mem_range.mpr z.isLt)
  have hmb : (finsetToMask T).val.testBit z.val = true := by
    have := maskBit_finsetToMask T z
    unfold maskBit at this
    rw [this, decide_eq_true hzT]
  have hadj1 : adjB z.val p1.val = true := (g11Graph_adj_iff_adjB z p1).mp hzp1
  rw [hmb, hadj1] at hzspec
  simp only [Bool.and_true, Bool.not_true, Bool.false_or] at hzspec
  exact (g11Graph_adj_iff_adjB z q2).mpr hzspec

-- Part 5: Generic induced-matching contradiction for a 2-sided junk gate

lemma no_induced_matching_two_sides {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (A B : Finset (Fin n))
    (hj_iff : ∀ x, gateVal n C j x = true ↔ (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true))
    (u1 v1 u2 v2 : Fin n)
    (hcross : ¬G.Adj u1 u2 ∧ ¬G.Adj u1 v2 ∧ ¬G.Adj v1 u2 ∧ ¬G.Adj v1 v2)
    (t1 : ℕ) (ht1 : t1 ∈ tops G C) (b1 : Fin 2)
    (hr1 : OrReaches n C (opnd C t1 b1) j)
    (hj1 : gateVal n C j (pairInput u1 v1) = true)
    (w1 : Fin n) (hw1 : w1 ∈ side (n := n) C t1 (1 - b1)) (hpw1 : w1 = u1 ∨ w1 = v1)
    (t2 : ℕ) (ht2 : t2 ∈ tops G C) (b2 : Fin 2)
    (hr2 : OrReaches n C (opnd C t2 b2) j)
    (hj2 : gateVal n C j (pairInput u2 v2) = true)
    (w2 : Fin n) (hw2 : w2 ∈ side (n := n) C t2 (1 - b2)) (hpw2 : w2 = u2 ∨ w2 = v2) : False := by
  obtain ⟨⟨a1, ha1, hpa1⟩, ⟨c1, hc1, hpc1⟩⟩ := (hj_iff (pairInput u1 v1)).mp hj1
  obtain ⟨⟨a2, ha2, hpa2⟩, ⟨c2, hc2, hpc2⟩⟩ := (hj_iff (pairInput u2 v2)).mp hj2
  simp only [pairInput, decide_eq_true_eq] at hpa1 hpc1 hpa2 hpc2
  have fire : ∀ (t : ℕ) (ht : t ∈ tops G C) (b : Fin 2) (p q : Fin n),
      OrReaches n C (opnd C t b) j →
      (∃ a ∈ A, a = p ∨ a = q) →
      (∃ c ∈ B, c = p ∨ c = q) →
      (∃ w ∈ side (n := n) C t (1 - b), w = p ∨ w = q) →
      G.Adj p q := by
    intro t ht b p q hr ⟨a, ha, hapq⟩ ⟨c, hc, hcpq⟩ ⟨w, hw, hwpq⟩
    have htmem := ht
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htmem
    have hjv : gateVal n C j (pairInput p q) = true := by
      rw [hj_iff (pairInput p q)]
      exact ⟨⟨a, ha, by simp [pairInput, hapq]⟩, ⟨c, hc, by simp [pairInput, hcpq]⟩⟩
    have hv1 := orReaches_wireVal_true n C hAO (pairInput p q) (opnd C t b) j hr hjv
    have hv2 := orIn_wireVal_true n C hAO (pairInput p q) (opnd C t (1 - b)) w hw
      (by simp [pairInput, hwpq])
    have htv : gateVal n C t (pairInput p q) = true := by
      rw [gateVal_and_iff n C hAO t htmem.1 htmem.2.1 (pairInput p q)]
      fin_cases b
      · exact ⟨hv1, hv2⟩
      · exact ⟨hv2, hv1⟩
    exact graphFun_empty_pairInput G p q (htmem.2.2 (pairInput p q) htv)
  have hno : ∀ p q : Fin n, (p = u1 ∨ p = v1) → (q = u2 ∨ q = v2) → ¬G.Adj p q := by
    rintro p q (rfl | rfl) (rfl | rfl)
    · exact hcross.1
    · exact hcross.2.1
    · exact hcross.2.2.1
    · exact hcross.2.2.2
  by_cases heq : a1 = c1
  · have hadj := fire t2 ht2 b2 a1 w2 hr2
      ⟨a1, ha1, Or.inl rfl⟩ ⟨c1, hc1, Or.inl heq.symm⟩ ⟨w2, hw2, Or.inr rfl⟩
    exact hno a1 w2 hpa1 hpw2 hadj
  · have hw_cases : w1 = a1 ∨ w1 = c1 := by
      rcases hpa1 with rfl | rfl <;> rcases hpc1 with rfl | rfl <;> rcases hpw1 with rfl | rfl <;>
        first | exact Or.inl rfl | exact Or.inr rfl | exact (heq rfl).elim
    rcases hw_cases with rfl | rfl
    · have hadj := fire t1 ht1 b1 w1 c2 hr1
        ⟨w1, ha1, Or.inl rfl⟩ ⟨c2, hc2, Or.inr rfl⟩ ⟨w1, hw1, Or.inl rfl⟩
      exact hno w1 c2 hpa1 hpc2 hadj
    · have hadj := fire t1 ht1 b1 w1 a2 hr1
        ⟨a2, ha2, Or.inr rfl⟩ ⟨w1, hc1, Or.inl rfl⟩ ⟨w1, hw1, Or.inl rfl⟩
      exact hno w1 a2 hpc1 hpa2 hadj

lemma mem_orN_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ orN G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ ¬BelowF G C k := by
  simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]

-- Part 6: Main Proof of L_meta_5226

lemma main_proof (x1 : SimpleGraph (Fin 11)) [DecidableRel x1.Adj]
    (C : Circuit) (x4 x5 : ℕ)
    (hx1 : x1 = g11Graph)
    (hLeast : IsLeastAO x1 C)
    (hTF : TopForm x1 C)
    (h45 : x4 < x5)
    (hjunk : junk x1 C = {x4, x5})
    (hcone45 : InCone 11 C x4 x5)
    (htop_star : ∀ t ∈ tops x1 C,
      (∀ u ∈ side (n := 11) C t 0, ∀ v ∈ side (n := 11) C t 1, x1.Adj u v) ∧
      ((side (n := 11) C t 0).card ≤ 1 ∨ (side (n := 11) C t 1).card ≤ 1))
    (hcard5 : (tops x1 C \ centreless x1 C).card = 5)
    (hcent : centreless x1 C = ∅)
    (hustar2 : (Ustar x1 C).card = 2)
    (hwit : ∃ (m j : ℕ),
      orN x1 C \ lam x1 C = {m} ∧
      j ∈ junk x1 C ∧
      11 + j ∈ (gateAt C m).inputs ∧
      ∀ (u v : Fin 11), s(u, v) ∈ Ustar x1 C →
        ∃ t ∈ tops x1 C, ∃ b : Fin 2,
          gateVal 11 C t (pairInput u v) = true ∧
          OrReaches 11 C (opnd C t b) m ∧
          gateVal 11 C j (pairInput u v) = true) : False := by
  subst hx1
  classical
  have hAO : IsAO2 11 C := hLeast.1
  set x12 := Ustar g11Graph C
  set x14 := orN g11Graph C \ lam g11Graph C
  set x15 := tops g11Graph C
  have hcard_tops : x15.card = 5 := by
    have hdiff : x15 \ centreless g11Graph C = x15 := by rw [hcent, Finset.sdiff_empty]
    rwa [hdiff] at hcard5
  -- Step 1: Define center : tops -> Fin 11 and extract 5-vertex cover T
  have htop_side_card : ∀ t ∈ x15,
      (side (n := 11) C t 0).card = 1 ∨ (side (n := 11) C t 1).card = 1 := by
    intro t ht
    have hnc : t ∉ centreless g11Graph C := by rw [hcent]; simp
    have hne0 : side (n := 11) C t 0 ≠ ∅ := by
      intro h0; apply hnc; simp only [centreless, Finset.mem_filter]; exact ⟨ht, Or.inl h0⟩
    have hne1 : side (n := 11) C t 1 ≠ ∅ := by
      intro h1; apply hnc; simp only [centreless, Finset.mem_filter]; exact ⟨ht, Or.inr h1⟩
    have hc0 : 1 ≤ (side (n := 11) C t 0).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne0)
    have hc1 : 1 ≤ (side (n := 11) C t 1).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne1)
    rcases (htop_star t ht).2 with hle0 | hle1
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  let center : ℕ → Fin 11 := fun t =>
    if h0 : (side (n := 11) C t 0).card = 1 then (Finset.card_eq_one.mp h0).choose
    else if h1 : (side (n := 11) C t 1).card = 1 then (Finset.card_eq_one.mp h1).choose
    else ⟨0, by omega⟩
  have hcenter_spec : ∀ t ∈ x15,
      side (n := 11) C t 0 = {center t} ∨ side (n := 11) C t 1 = {center t} := by
    intro t ht
    dsimp only [center]
    split_ifs with h0 h1
    · exact Or.inl (Finset.card_eq_one.mp h0).choose_spec
    · exact Or.inr (Finset.card_eq_one.mp h1).choose_spec
    · rcases htop_side_card t ht with h | h
      · exact (h0 h).elim
      · exact (h1 h).elim
  have hcenter_other_singleton : ∀ t ∈ x15, ∀ b : Fin 2, ∀ p : Fin 11,
      p ∈ side (n := 11) C t (1 - b) → p ≠ center t → side (n := 11) C t b = {center t} := by
    intro t ht b p hp hne
    rcases hcenter_spec t ht with h0 | h1
    · fin_cases b
      · exact h0
      · change p ∈ side (n := 11) C t 0 at hp
        rw [h0, Finset.mem_singleton] at hp
        exact (hne hp).elim
    · fin_cases b
      · change p ∈ side (n := 11) C t 1 at hp
        rw [h1, Finset.mem_singleton] at hp
        exact (hne hp).elim
      · exact h1
  have hcenter_unique_singleton : ∀ t ∈ x15, ∀ b : Fin 2, ∀ z : Fin 11,
      side (n := 11) C t (1 - b) = {z} → 2 ≤ (side (n := 11) C t b).card → z = center t := by
    intro t ht b z hz hge2
    rcases hcenter_spec t ht with h0 | h1
    · fin_cases b
      · change 2 ≤ (side (n := 11) C t 0).card at hge2
        rw [h0] at hge2; simp at hge2
      · change side (n := 11) C t 0 = {z} at hz
        rw [h0, Finset.singleton_inj] at hz
        exact hz.symm
    · fin_cases b
      · change side (n := 11) C t 1 = {z} at hz
        rw [h1, Finset.singleton_inj] at hz
        exact hz.symm
      · change 2 ≤ (side (n := 11) C t 1).card at hge2
        rw [h1] at hge2; simp at hge2
  let T : Finset (Fin 11) := x15.image center
  have hTle5 : T.card ≤ 5 := by
    calc T.card ≤ x15.card := Finset.card_image_le
      _ = 5 := hcard_tops
  have hTcov : (g11Graph.deleteEdges (x12 : Set (Sym2 (Fin 11)))).IsVertexCover (T : Set (Fin 11)) := by
    intro u v hadj
    rw [SimpleGraph.deleteEdges_adj] at hadj
    have hedge : s(u, v) ∈ g11Graph.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hadj.1
    have hnotu : s(u, v) ∉ x12 := hadj.2
    have hstar : s(u, v) ∈ starEdges g11Graph C := by
      by_contra hns
      exact hnotu (Finset.mem_sdiff.mpr ⟨hedge, hns⟩)
    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at hstar
    obtain ⟨t, ht, ⟨a, b⟩, ⟨ha, hb⟩, hs⟩ := hstar
    have hc_ab : center t = a ∨ center t = b := by
      rcases hcenter_spec t ht with h0 | h1
      · rw [h0, Finset.mem_singleton] at ha; exact Or.inl ha.symm
      · rw [h1, Finset.mem_singleton] at hb; exact Or.inr hb.symm
    have hcT : center t ∈ T := Finset.mem_image.mpr ⟨t, ht, rfl⟩
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hs
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hc_ab with heq | heq
    · exact Or.inl (heq ▸ hcT)
    · exact Or.inr (heq ▸ hcT)
    · exact Or.inr (heq ▸ hcT)
    · exact Or.inl (heq ▸ hcT)
  have hm := g11_all_masks_ok (finsetToMask T)
  unfold checkG11Mask at hm
  simp only [maskCard_finsetToMask, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, decide_eq_true_eq] at hm
  obtain ⟨⟨hsum7, hcase7⟩, htriple⟩ := hm
  obtain ⟨hulen, humem⟩ := uncovList_card_le_and_mem T x12 hTcov
  have hTcard5 : T.card = 5 := by omega
  have hulen2 : (uncovList (finsetToMask T)).length = 2 := by omega
  have hnc_all : allPairsNoCross (uncovList (finsetToMask T)) = true := by
    rcases hcase7 with hne | ⟨_, hnc⟩
    · exact (hne (by omega)).elim
    · exact hnc
  have htriple_ok : checkTripleForList (finsetToMask T) (uncovList (finsetToMask T)) = true := by
    rcases htriple with hne | hok
    · simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne] at hne
      rcases hne with h1 | h2
      · exact (h1 hTcard5).elim
      · exact (h2 hulen2).elim
    · exact hok
  have hcenter_inj : Set.InjOn center (x15 : Set ℕ) := by
    rw [← Finset.card_image_iff]
    change T.card = x15.card
    omega
  -- Extract the 2 uncovered edges e1, e2
  rcases hul_eq : uncovList (finsetToMask T) with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩
  · simp [hul_eq] at hulen2
  · simp [hul_eq] at hulen2
  · have hnd : (uncovList (finsetToMask T)).Nodup := g11List_valid_nodup.1.filter _
    rw [hul_eq] at hnd htriple_ok
    have hne12 : e1 ≠ e2 := by simp at hnd; exact hnd
    have he1_mem : e1 ∈ uncovList (finsetToMask T) := by rw [hul_eq]; simp
    have he2_mem : e2 ∈ uncovList (finsetToMask T) := by rw [hul_eq]; simp
    obtain ⟨h11, h12, h1lt, hu1nT, hv1nT, he1F⟩ := humem e1 he1_mem
    obtain ⟨h21, h22, h2lt, hu2nT, hv2nT, he2F⟩ := humem e2 he2_mem
    let u1 : Fin 11 := ⟨e1.1, h11⟩
    let v1 : Fin 11 := ⟨e1.2, h12⟩
    let u2 : Fin 11 := ⟨e2.1, h21⟩
    let v2 : Fin 11 := ⟨e2.2, h22⟩
    have huv1_ne : u1 ≠ v1 := fun h => by have := congrArg Fin.val h; dsimp [u1, v1] at this; omega
    have huv2_ne : u2 ≠ v2 := fun h => by have := congrArg Fin.val h; dsimp [u2, v2] at this; omega
    obtain ⟨hdisj_pts, hcross⟩ := noCrossPair_imp_graph e1 e2 ⟨h11, h12⟩ ⟨h21, h22⟩
      (allPairsNoCross_spec _ hnc_all e1 he1_mem e2 he2_mem hne12)
    have hs12_ne : s(u1, v1) ≠ s(u2, v2) := by
      intro h
      simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h
      rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hdisj_pts.1 h1
      · exact hdisj_pts.2.1 h1
    have hx12_eq : x12 = {s(u1, v1), s(u2, v2)} := by
      apply (Finset.eq_of_subset_of_card_le _ _).symm
      · intro s hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · exact he1F
        · exact he2F
      · rw [Finset.card_pair hs12_ne, hustar2]
    -- Step 2: Unpack witness (m, j) and prove Claim 1
    obtain ⟨m, j, hx14m, hjjunk, hjm_in, hall⟩ := hwit
    have hm_orN : m ∈ orN g11Graph C := by
      have hm14 : m ∈ x14 := by rw [hx14m]; simp
      exact (Finset.mem_sdiff.mp hm14).1
    have hmlt : m < C.gates.length := ((mem_orN_iff g11Graph C m).mp hm_orN).1
    have hmop : (gateAt C m).op = GateOp.or := ((mem_orN_iff g11Graph C m).mp hm_orN).2.1
    have hjm_lt : j < m := by
      have hrb := hAO.2.1 m hmlt (11 + j) hjm_in
      omega
    have hj_mem : j ∈ junk g11Graph C := hjjunk
    unfold junk gatesWhere at hj_mem
    rw [Finset.mem_filter, Finset.mem_range] at hj_mem
    unfold IsDirtyAnd IsDirty at hj_mem
    have hjlt : j < C.gates.length := hj_mem.1
    have hjop : (gateAt C j).op = GateOp.and := hj_mem.2.1
    obtain ⟨xjd, hjxd, hfxd⟩ := hj_mem.2.2.2
    have hrmj : OrReaches 11 C (11 + m) j := by
      rw [orReaches_iff_gate 11 C m j hmlt]
      exact Or.inr ⟨hmop, 11 + j, hjm_in, by omega, orReaches_self 11 C j hjlt⟩
    -- Claim 1: if OrReaches (opnd t b) m for t in tops, then opnd t (1-b) has no AND gate
    have hclaim1 : ∀ t ∈ x15, ∀ b : Fin 2, OrReaches 11 C (opnd C t b) m →
        ∀ g, OrReaches 11 C (opnd C t (1 - b)) g → (gateAt C g).op ≠ GateOp.and := by
      intro t ht b hrtm g hrg hgop
      have htmem := ht
      simp only [x15, tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htmem
      have hgt : InCone 11 C g t := orReaches_imp_inCone_parent 11 C hAO t htmem.1 (1 - b) g hrg
      have hglt : g < t := inCone_lt 11 C t g hgt
      by_cases hbf : BelowF g11Graph C g
      · exact hTF g (by omega) t htmem.1 hgop hbf htmem.2.1 hgt
      · have hgjunk : g ∈ junk g11Graph C := by
          unfold junk gatesWhere
          rw [Finset.mem_filter, Finset.mem_range]
          unfold IsDirtyAnd IsDirty
          refine ⟨by omega, hgop, by omega, ?_⟩
          unfold BelowF at hbf; push Not at hbf
          obtain ⟨x, hx1, hx2⟩ := hbf
          exact ⟨x, hx1, Bool.eq_false_iff.mpr hx2⟩
        have hntc : t ∉ centreless g11Graph C := by rw [hcent]; simp
        obtain ⟨m', hm'14, hrm'1, _⟩ :=
          orN_witness_of_non_centreless g11Graph C hAO t ht hntc (1 - b) g hgjunk hrg
        have hm'eq : m' = m := by
          change m' ∈ x14 at hm'14
          rw [hx14m, Finset.mem_singleton] at hm'14
          exact hm'14
        rw [hm'eq] at hrm'1
        have hr1j : OrReaches 11 C (opnd C t b) j := orReaches_trans_wire 11 C _ m j hrtm hrmj
        have hr2j : OrReaches 11 C (opnd C t (1 - b)) j := orReaches_trans_wire 11 C _ m j hrm'1 hrmj
        have hv1 := orReaches_wireVal_true 11 C hAO xjd (opnd C t b) j hr1j hjxd
        have hv2 := orReaches_wireVal_true 11 C hAO xjd (opnd C t (1 - b)) j hr2j hjxd
        have htv : gateVal 11 C t xjd = true := by
          rw [gateVal_and_iff 11 C hAO t htmem.1 htmem.2.1 xjd]
          fin_cases b
          · exact ⟨hv1, hv2⟩
          · exact ⟨hv2, hv1⟩
        have hft := htmem.2.2 xjd htv
        rw [hfxd] at hft; cases hft
    -- Extract witnesses for e1 and e2
    obtain ⟨t1, ht1, b1, ht1v, hrt1m, hj1v⟩ := hall u1 v1 he1F
    obtain ⟨t2, ht2, b2, ht2v, hrt2m, hj2v⟩ := hall u2 v2 he2F
    have hrt1j : OrReaches 11 C (opnd C t1 b1) j := orReaches_trans_wire 11 C _ m j hrt1m hrmj
    have hrt2j : OrReaches 11 C (opnd C t2 b2) j := orReaches_trans_wire 11 C _ m j hrt2m hrmj
    have get_w : ∀ (t : ℕ) (ht : t ∈ x15) (b : Fin 2) (u v : Fin 11),
        gateVal 11 C t (pairInput u v) = true → OrReaches 11 C (opnd C t b) m →
        ∃ w ∈ side (n := 11) C t (1 - b), w = u ∨ w = v := by
      intro t ht b u v htv hrm
      have htmem := ht
      simp only [x15, tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htmem
      obtain ⟨_, h0, h1, _⟩ := isAO2_inputs 11 C hAO t htmem.1
      rw [gateVal_and_iff 11 C hAO t htmem.1 htmem.2.1 (pairInput u v)] at htv
      have hval : wireVal 11 C (opnd C t (1 - b)) (pairInput u v) = true := by
        fin_cases b
        · exact htv.2
        · exact htv.1
      have hlt : opnd C t (1 - b) < 11 + C.gates.length := by
        fin_cases b
        · change opnd C t 1 < 11 + C.gates.length; omega
        · change opnd C t 0 < 11 + C.gates.length; omega
      obtain ⟨w, hw, hpw⟩ := pure_or_wireVal_imp_orIn 11 C hAO (pairInput u v) (opnd C t (1 - b)) hlt
        (hclaim1 t ht b hrm) hval
      simp only [pairInput, decide_eq_true_eq] at hpw
      exact ⟨w, hw, hpw⟩
    obtain ⟨w1, hw1, hpw1⟩ := get_w t1 ht1 b1 u1 v1 ht1v hrt1m
    obtain ⟨w2, hw2, hpw2⟩ := get_w t2 ht2 b2 u2 v2 ht2v hrt2m
    -- Facts about x4 and x5 in junk
    have hx4_mem : x4 ∈ junk g11Graph C := by rw [hjunk]; simp
    have hx5_mem : x5 ∈ junk g11Graph C := by rw [hjunk]; simp
    unfold junk gatesWhere at hx4_mem hx5_mem
    rw [Finset.mem_filter, Finset.mem_range] at hx4_mem hx5_mem
    unfold IsDirtyAnd IsDirty at hx4_mem hx5_mem
    have hx4lt : x4 < C.gates.length := hx4_mem.1
    have hx4op : (gateAt C x4).op = GateOp.and := hx4_mem.2.1
    obtain ⟨x4d, hx4d_t, hx4d_f⟩ := hx4_mem.2.2.2
    have hx5lt : x5 < C.gates.length := hx5_mem.1
    have hx5op : (gateAt C x5).op = GateOp.and := hx5_mem.2.1
    -- x4 has no AND gate in either operand
    have hx4_noand : ∀ c : Fin 2, ∀ g, OrReaches 11 C (opnd C x4 c) g → (gateAt C g).op ≠ GateOp.and := by
      intro c g hrg hgop
      have hcone : InCone 11 C g x4 := orReaches_imp_inCone_parent 11 C hAO x4 hx4lt c g hrg
      have hglt : g < x4 := inCone_lt 11 C x4 g hcone
      by_cases hbf : BelowF g11Graph C g
      · exact hTF g (by omega) x4 hx4lt hgop hbf hx4op hcone
      · have hgj : g ∈ junk g11Graph C := by
          unfold junk gatesWhere
          rw [Finset.mem_filter, Finset.mem_range]
          unfold IsDirtyAnd IsDirty
          refine ⟨by omega, hgop, by omega, ?_⟩
          unfold BelowF at hbf; push Not at hbf
          obtain ⟨x, hx1, hx2⟩ := hbf
          exact ⟨x, hx1, Bool.eq_false_iff.mpr hx2⟩
        rw [hjunk] at hgj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hgj
        omega
    have hx4_iff : ∀ x, gateVal 11 C x4 x = true ↔
        (∃ a ∈ side (n := 11) C x4 0, x a = true) ∧ (∃ b ∈ side (n := 11) C x4 1, x b = true) := by
      intro x
      obtain ⟨_, h0, h1, _⟩ := isAO2_inputs 11 C hAO x4 hx4lt
      rw [gateVal_and_iff 11 C hAO x4 hx4lt hx4op x]
      constructor
      · rintro ⟨hv0, hv1⟩
        exact ⟨pure_or_wireVal_imp_orIn 11 C hAO x (opnd C x4 0) (by omega) (hx4_noand 0) hv0,
               pure_or_wireVal_imp_orIn 11 C hAO x (opnd C x4 1) (by omega) (hx4_noand 1) hv1⟩
      · rintro ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩
        exact ⟨orIn_wireVal_true 11 C hAO x (opnd C x4 0) a ha hxa,
               orIn_wireVal_true 11 C hAO x (opnd C x4 1) b hb hxb⟩
    -- Split on j = x4 vs j = x5
    have hj_cases : j = x4 ∨ j = x5 := by
      rw [hjunk] at hjjunk
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hjjunk
    rcases hj_cases with hj4 | hj5
    · -- Case 1: j = x4
      subst j
      exact no_induced_matching_two_sides g11Graph C hAO x4
        (side (n := 11) C x4 0) (side (n := 11) C x4 1) hx4_iff
        u1 v1 u2 v2 hcross t1 ht1 b1 hrt1j hj1v w1 hw1 hpw1 t2 ht2 b2 hrt2j hj2v w2 hw2 hpw2
    · -- Case 2: j = x5 (and x4 < x5 < m)
      subst j
      -- Claim 2: No OR gate k < x5 has OrReaches (11 + k) x4
      have hclaim2 : ∀ k < x5, (gateAt C k).op = GateOp.or → ¬OrReaches 11 C (11 + k) x4 := by
        intro k0 hk0lt hk0op hk0r
        let P : ℕ → Prop := fun k => k < x5 ∧ (gateAt C k).op = GateOp.or ∧ OrReaches 11 C (11 + k) x4
        have hex : ∃ k, P k := ⟨k0, hk0lt, hk0op, hk0r⟩
        let k := Nat.find hex
        have hk : P k := Nat.find_spec hex
        have hk_min : ∀ k' < k, ¬P k' := fun k' hlt => Nat.find_min hex hlt
        obtain ⟨hklt5, hkop, hkr⟩ := hk
        have hklt : k < C.gates.length := by omega
        have hk_ne4 : k ≠ x4 := by intro heq; rw [heq, hx4op] at hkop; cases hkop
        have hkr' := hkr
        rw [orReaches_iff_gate 11 C k x4 hklt] at hkr'
        rcases hkr' with heq | ⟨_, u, hu, hult, hru⟩
        · exact hk_ne4 heq.symm
        · have hu_eq : u = 11 + (u - 11) := by have := hru.1; omega
          have hu_is4 : u - 11 = x4 := by
            by_contra hne
            have hult_c : u - 11 < C.gates.length := orReaches_lt_len 11 C u x4 hru
            have hru' : OrReaches 11 C (11 + (u - 11)) x4 := by rwa [← hu_eq]
            rw [orReaches_iff_gate 11 C (u - 11) x4 hult_c] at hru'
            rcases hru' with heq | ⟨huop, _⟩
            · exact hne heq.symm
            · exact hk_min (u - 11) (by omega) ⟨by omega, huop, by rwa [← hu_eq]⟩
          have hu_val : u = 11 + x4 := by omega
          have hk_orN : k ∈ orN g11Graph C := by
            rw [mem_orN_iff]
            refine ⟨hklt, hkop, fun hbf => ?_⟩
            have hgk := orReaches_val_true 11 C hAO x4d k x4 hkr hx4d_t
            have hft := hbf x4d hgk
            rw [hx4d_f] at hft; cases hft
          have hk_not_lam : k ∉ lam g11Graph C := by
            simp only [lam, Finset.mem_filter]
            rintro ⟨_, hne0, hne1, _⟩
            obtain ⟨hinp, _, _, _⟩ := isAO2_inputs 11 C hAO k hklt
            rw [hinp] at hu
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            have hemp := orIn_and_eq_empty 11 C x4 hx4lt hx4op
            rcases hu with heq0 | heq1
            · rw [← heq0, hu_val, hemp] at hne0; exact Finset.not_nonempty_empty hne0
            · rw [← heq1, hu_val, hemp] at hne1; exact Finset.not_nonempty_empty hne1
          have hk14 : k ∈ x14 := Finset.mem_sdiff.mpr ⟨hk_orN, hk_not_lam⟩
          rw [hx14m, Finset.mem_singleton] at hk14
          omega
      -- Helper: any k < x5 with InCone k x5 and (k = x4 ∨ InCone x4 k) satisfies OrReaches (11 + k) x4
      have hcone_imp_orReaches : ∀ k, k < x5 → InCone 11 C k x5 →
          (k = x4 ∨ InCone 11 C x4 k) → OrReaches 11 C (11 + k) x4 := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro hklt5 hk5 h4k
          rcases h4k with hkeq | h4k
          · rw [hkeq]; exact orReaches_self 11 C x4 hx4lt
          · have h4lt : x4 < k := inCone_lt 11 C k x4 h4k
            have hklt : k < C.gates.length := by omega
            have hkop : (gateAt C k).op = GateOp.or := by
              obtain ⟨_, _, _, hor⟩ := isAO2_inputs 11 C hAO k hklt
              rcases hor with hand | hor
              · exfalso
                by_cases hbf : BelowF g11Graph C k
                · exact hTF k hklt x5 hx5lt hand hbf hx5op hk5
                · have hkj : k ∈ junk g11Graph C := by
                    unfold junk gatesWhere
                    rw [Finset.mem_filter, Finset.mem_range]
                    unfold IsDirtyAnd IsDirty
                    refine ⟨hklt, hand, hklt, ?_⟩
                    unfold BelowF at hbf; push Not at hbf
                    obtain ⟨x, hx1, hx2⟩ := hbf
                    exact ⟨x, hx1, Bool.eq_false_iff.mpr hx2⟩
                  rw [hjunk] at hkj
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hkj
                  omega
              · exact hor
            unfold InCone at h4k
            rw [cones_getD_eq 11 C k hklt, List.mem_flatMap] at h4k
            obtain ⟨u, hu, hmem⟩ := h4k
            simp only [List.mem_filter, decide_eq_true_eq] at hu
            simp only [List.mem_cons] at hmem
            have hu_eq : u = 11 + (u - 11) := by omega
            have huk : InCone 11 C (u - 11) k :=
              inCone_of_input 11 C (u - 11) k hklt (by omega) (by rw [← hu_eq]; exact hu.1)
            have hu5 : InCone 11 C (u - 11) x5 := inCone_trans 11 C x5 (u - 11) k huk hk5
            have hrec : OrReaches 11 C (11 + (u - 11)) x4 := by
              apply ih (u - 11) (by omega) (by omega) hu5
              rcases hmem with rfl | hmem
              · exact Or.inl rfl
              · exact Or.inr hmem
            rw [orReaches_iff_gate 11 C k x4 hklt]
            exact Or.inr ⟨hkop, u, hu.1, hu.2.2, by rwa [hu_eq]⟩
      -- Claim 3: 11 + x4 ∈ (gateAt C x5).inputs
      have hx4_in_x5 : 11 + x4 ∈ (gateAt C x5).inputs := by
        unfold InCone at hcone45
        rw [cones_getD_eq 11 C x5 hx5lt, List.mem_flatMap] at hcone45
        obtain ⟨w, hw, hmem⟩ := hcone45
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        simp only [List.mem_cons] at hmem
        have hw_eq : w = 11 + (w - 11) := by omega
        rcases hmem with h4eq | h4cone
        · have : 11 + x4 = w := by omega
          rw [this]; exact hw.1
        · exfalso
          have hklt5 : w - 11 < x5 := by omega
          have h4lt : x4 < w - 11 := inCone_lt 11 C (w - 11) x4 h4cone
          have hk5 : InCone 11 C (w - 11) x5 :=
            inCone_of_input 11 C (w - 11) x5 hx5lt hklt5 (by rw [← hw_eq]; exact hw.1)
          have hklt : w - 11 < C.gates.length := by omega
          have hkop : (gateAt C (w - 11)).op = GateOp.or := by
            obtain ⟨_, _, _, hor⟩ := isAO2_inputs 11 C hAO (w - 11) hklt
            rcases hor with hand | hor
            · exfalso
              by_cases hbf : BelowF g11Graph C (w - 11)
              · exact hTF (w - 11) hklt x5 hx5lt hand hbf hx5op hk5
              · have hkj : w - 11 ∈ junk g11Graph C := by
                  unfold junk gatesWhere
                  rw [Finset.mem_filter, Finset.mem_range]
                  unfold IsDirtyAnd IsDirty
                  refine ⟨hklt, hand, hklt, ?_⟩
                  unfold BelowF at hbf; push Not at hbf
                  obtain ⟨x, hx1, hx2⟩ := hbf
                  exact ⟨x, hx1, Bool.eq_false_iff.mpr hx2⟩
                rw [hjunk] at hkj
                simp only [Finset.mem_insert, Finset.mem_singleton] at hkj
                omega
            · exact hor
          exact hclaim2 (w - 11) hklt5 hkop (hcone_imp_orReaches (w - 11) hklt5 hk5 (Or.inr h4cone))
      obtain ⟨hinp5, h50, h51, _⟩ := isAO2_inputs 11 C hAO x5 hx5lt
      have hx5_opnd : opnd C x5 0 = 11 + x4 ∨ opnd C x5 1 = 11 + x4 := by
        rw [hinp5] at hx4_in_x5
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx4_in_x5
        rcases hx4_in_x5 with h | h
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      by_cases hboth : opnd C x5 0 = 11 + x4 ∧ opnd C x5 1 = 11 + x4
      · -- Subcase 2a: both operands of x5 are 11 + x4, so gateVal x5 = gateVal x4
        have hx5_iff : ∀ x, gateVal 11 C x5 x = true ↔
            (∃ a ∈ side (n := 11) C x4 0, x a = true) ∧ (∃ b ∈ side (n := 11) C x4 1, x b = true) := by
          intro x
          rw [gateVal_and_iff 11 C hAO x5 hx5lt hx5op x, hboth.1, hboth.2, and_self]
          exact hx4_iff x
        exact no_induced_matching_two_sides g11Graph C hAO x5
          (side (n := 11) C x4 0) (side (n := 11) C x4 1) hx5_iff
          u1 v1 u2 v2 hcross t1 ht1 b1 hrt1j hj1v w1 hw1 hpw1 t2 ht2 b2 hrt2j hj2v w2 hw2 hpw2
      · -- Subcase 2b: exactly one operand of x5 is 11 + x4
        have hex_c : ∃ c : Fin 2, opnd C x5 c = 11 + x4 ∧ opnd C x5 (1 - c) ≠ 11 + x4 := by
          rcases hx5_opnd with h0 | h1
          · exact ⟨0, h0, fun h1 => hboth ⟨h0, h1⟩⟩
          · exact ⟨1, h1, fun h0 => hboth ⟨h0, h1⟩⟩
        obtain ⟨c, hxc, hxnc⟩ := hex_c
        have hx5_other_lt : opnd C x5 (1 - c) < 11 + x5 := by
          fin_cases c
          · exact h51
          · exact h50
        have hx5_other_noand : ∀ g, OrReaches 11 C (opnd C x5 (1 - c)) g → (gateAt C g).op ≠ GateOp.and := by
          intro g hrg hgop
          have hcone : InCone 11 C g x5 := orReaches_imp_inCone_parent 11 C hAO x5 hx5lt (1 - c) g hrg
          have hglt : g < x5 := inCone_lt 11 C x5 g hcone
          have hg4 : g = x4 := by
            by_cases hbf : BelowF g11Graph C g
            · exact (hTF g (by omega) x5 hx5lt hgop hbf hx5op hcone).elim
            · have hgj : g ∈ junk g11Graph C := by
                unfold junk gatesWhere
                rw [Finset.mem_filter, Finset.mem_range]
                unfold IsDirtyAnd IsDirty
                refine ⟨by omega, hgop, by omega, ?_⟩
                unfold BelowF at hbf; push Not at hbf
                obtain ⟨x, hx1, hx2⟩ := hbf
                exact ⟨x, hx1, Bool.eq_false_iff.mpr hx2⟩
              rw [hjunk] at hgj
              simp only [Finset.mem_insert, Finset.mem_singleton] at hgj
              omega
          subst g
          have hwge : 11 ≤ opnd C x5 (1 - c) := hrg.1
          let k := opnd C x5 (1 - c) - 11
          have hkeq : opnd C x5 (1 - c) = 11 + k := by omega
          have hklt5 : k < x5 := by omega
          have hklt : k < C.gates.length := by omega
          have hkr : OrReaches 11 C (11 + k) x4 := by rwa [← hkeq]
          have hkr' := hkr
          rw [orReaches_iff_gate 11 C k x4 hklt] at hkr'
          rcases hkr' with h4k | ⟨hkop, _⟩
          · exact hxnc (by omega)
          · exact hclaim2 k hklt5 hkop hkr
        let A := side (n := 11) C x4 0
        let B := side (n := 11) C x4 1
        let D := side (n := 11) C x5 (1 - c)
        have hx5_iff : ∀ x, gateVal 11 C x5 x = true ↔
            (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true) ∧ (∃ d ∈ D, x d = true) := by
          intro x
          rw [gateVal_and_iff 11 C hAO x5 hx5lt hx5op x]
          have hcomm : (wireVal 11 C (opnd C x5 0) x = true ∧ wireVal 11 C (opnd C x5 1) x = true) ↔
              (wireVal 11 C (opnd C x5 c) x = true ∧ wireVal 11 C (opnd C x5 (1 - c)) x = true) := by
            fin_cases c
            · rfl
            · exact and_comm
          rw [hcomm, hxc]
          change (gateVal 11 C x4 x = true ∧ wireVal 11 C (opnd C x5 (1 - c)) x = true) ↔ _
          rw [hx4_iff x, and_assoc]
          refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
          constructor
          · exact pure_or_wireVal_imp_orIn 11 C hAO x (opnd C x5 (1 - c)) (by omega) hx5_other_noand
          · rintro ⟨d, hd, hxd⟩
            exact orIn_wireVal_true 11 C hAO x (opnd C x5 (1 - c)) d hd hxd
        -- Orient e1 as (p1, q1) and e2 as (p2, q2) with p1 = w1, p2 = w2
        let p1 : Fin 11 := w1
        let q1 : Fin 11 := if w1 = u1 then v1 else u1
        let p2 : Fin 11 := w2
        let q2 : Fin 11 := if w2 = u2 then v2 else u2
        have hpq1_or : (p1 = u1 ∧ q1 = v1) ∨ (p1 = v1 ∧ q1 = u1) := by
          dsimp only [p1, q1]
          rcases hpw1 with h | h
          · exact Or.inl ⟨h, by simp [h]⟩
          · exact Or.inr ⟨h, by simp [h, Ne.symm huv1_ne]⟩
        have hpq2_or : (p2 = u2 ∧ q2 = v2) ∨ (p2 = v2 ∧ q2 = u2) := by
          dsimp only [p2, q2]
          rcases hpw2 with h | h
          · exact Or.inl ⟨h, by simp [h]⟩
          · exact Or.inr ⟨h, by simp [h, Ne.symm huv2_ne]⟩
        have hpq1_nT : p1 ∉ T ∧ q1 ∉ T := by
          rcases hpq1_or with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
          · exact ⟨hu1nT, hv1nT⟩
          · exact ⟨hv1nT, hu1nT⟩
        have hpq2_nT : p2 ∉ T ∧ q2 ∉ T := by
          rcases hpq2_or with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
          · exact ⟨hu2nT, hv2nT⟩
          · exact ⟨hv2nT, hu2nT⟩
        have hpq_disj : p1 ≠ q2 ∧ q1 ≠ p2 ∧ q1 ≠ q2 := by
          rcases hpq1_or with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hpq2_or with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
            rw [h1, h2, h3, h4]
          · exact ⟨hdisj_pts.2.1, hdisj_pts.2.2.1, hdisj_pts.2.2.2⟩
          · exact ⟨hdisj_pts.1, hdisj_pts.2.2.2, hdisj_pts.2.2.1⟩
          · exact ⟨hdisj_pts.2.2.2, hdisj_pts.1, hdisj_pts.2.1⟩
          · exact ⟨hdisj_pts.2.2.1, hdisj_pts.2.1, hdisj_pts.1⟩
        have hpq_nocross : ∀ a b : Fin 11, (a = p1 ∨ a = q1) → (b = p2 ∨ b = q2) → ¬g11Graph.Adj a b := by
          intro a b ha hb
          have ha' : a = u1 ∨ a = v1 := by
            rcases hpq1_or with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ha with rfl | rfl
            · exact Or.inl h1
            · exact Or.inr h2
            · exact Or.inr h1
            · exact Or.inl h2
          have hb' : b = u2 ∨ b = v2 := by
            rcases hpq2_or with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hb with rfl | rfl
            · exact Or.inl h1
            · exact Or.inr h2
            · exact Or.inr h1
            · exact Or.inl h2
          rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
          · exact hcross.1
          · exact hcross.2.1
          · exact hcross.2.2.1
          · exact hcross.2.2.2
        -- Firing lemmas for t1 and t2
        have hno_fire1 : ∀ y : Fin 11, (y = p2 ∨ y = q2) →
            ¬((p1 ∈ A ∨ y ∈ A) ∧ (p1 ∈ B ∨ y ∈ B) ∧ (p1 ∈ D ∨ y ∈ D)) := by
          intro y hy ⟨hA, hB, hD⟩
          have hjv : gateVal 11 C x5 (pairInput p1 y) = true := by
            rw [hx5_iff (pairInput p1 y)]
            refine ⟨?_, ?_, ?_⟩
            · rcases hA with h | h
              · exact ⟨p1, h, by simp [pairInput]⟩
              · exact ⟨y, h, by simp [pairInput]⟩
            · rcases hB with h | h
              · exact ⟨p1, h, by simp [pairInput]⟩
              · exact ⟨y, h, by simp [pairInput]⟩
            · rcases hD with h | h
              · exact ⟨p1, h, by simp [pairInput]⟩
              · exact ⟨y, h, by simp [pairInput]⟩
          have ht1mem := ht1
          simp only [x15, tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ht1mem
          have hv1 := orReaches_wireVal_true 11 C hAO (pairInput p1 y) (opnd C t1 b1) x5 hrt1j hjv
          have hv2 := orIn_wireVal_true 11 C hAO (pairInput p1 y) (opnd C t1 (1 - b1)) p1 hw1
            (by simp [pairInput])
          have htv : gateVal 11 C t1 (pairInput p1 y) = true := by
            rw [gateVal_and_iff 11 C hAO t1 ht1mem.1 ht1mem.2.1 (pairInput p1 y)]
            fin_cases b1
            · exact ⟨hv1, hv2⟩
            · exact ⟨hv2, hv1⟩
          exact hpq_nocross p1 y (Or.inl rfl) hy (graphFun_empty_pairInput g11Graph p1 y (ht1mem.2.2 _ htv))
        have hno_fire2 : ∀ x : Fin 11, (x = p1 ∨ x = q1) →
            ¬((x ∈ A ∨ p2 ∈ A) ∧ (x ∈ B ∨ p2 ∈ B) ∧ (x ∈ D ∨ p2 ∈ D)) := by
          intro x hx ⟨hA, hB, hD⟩
          have hjv : gateVal 11 C x5 (pairInput x p2) = true := by
            rw [hx5_iff (pairInput x p2)]
            refine ⟨?_, ?_, ?_⟩
            · rcases hA with h | h
              · exact ⟨x, h, by simp [pairInput]⟩
              · exact ⟨p2, h, by simp [pairInput]⟩
            · rcases hB with h | h
              · exact ⟨x, h, by simp [pairInput]⟩
              · exact ⟨p2, h, by simp [pairInput]⟩
            · rcases hD with h | h
              · exact ⟨x, h, by simp [pairInput]⟩
              · exact ⟨p2, h, by simp [pairInput]⟩
          have ht2mem := ht2
          simp only [x15, tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ht2mem
          have hv1 := orReaches_wireVal_true 11 C hAO (pairInput x p2) (opnd C t2 b2) x5 hrt2j hjv
          have hv2 := orIn_wireVal_true 11 C hAO (pairInput x p2) (opnd C t2 (1 - b2)) p2 hw2
            (by simp [pairInput])
          have htv : gateVal 11 C t2 (pairInput x p2) = true := by
            rw [gateVal_and_iff 11 C hAO t2 ht2mem.1 ht2mem.2.1 (pairInput x p2)]
            fin_cases b2
            · exact ⟨hv1, hv2⟩
            · exact ⟨hv2, hv1⟩
          exact hpq_nocross x p2 hx (Or.inl rfl) (graphFun_empty_pairInput g11Graph x p2 (ht2mem.2.2 _ htv))
        -- Extract memberships in A, B, D for {p1, q1} and {p2, q2}
        have hmem1 : (p1 ∈ A ∨ q1 ∈ A) ∧ (p1 ∈ B ∨ q1 ∈ B) ∧ (p1 ∈ D ∨ q1 ∈ D) := by
          obtain ⟨⟨a, ha, hpa⟩, ⟨b, hb, hpb⟩, ⟨d, hd, hpd⟩⟩ := (hx5_iff (pairInput u1 v1)).mp hj1v
          simp only [pairInput, decide_eq_true_eq] at hpa hpb hpd
          rcases hpq1_or with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · refine ⟨?_, ?_, ?_⟩
            · rcases hpa with rfl | rfl <;> [exact Or.inl (h1.symm ▸ ha); exact Or.inr (h2.symm ▸ ha)]
            · rcases hpb with rfl | rfl <;> [exact Or.inl (h1.symm ▸ hb); exact Or.inr (h2.symm ▸ hb)]
            · rcases hpd with rfl | rfl <;> [exact Or.inl (h1.symm ▸ hd); exact Or.inr (h2.symm ▸ hd)]
          · refine ⟨?_, ?_, ?_⟩
            · rcases hpa with rfl | rfl <;> [exact Or.inr (h2.symm ▸ ha); exact Or.inl (h1.symm ▸ ha)]
            · rcases hpb with rfl | rfl <;> [exact Or.inr (h2.symm ▸ hb); exact Or.inl (h1.symm ▸ hb)]
            · rcases hpd with rfl | rfl <;> [exact Or.inr (h2.symm ▸ hd); exact Or.inl (h1.symm ▸ hd)]
        have hmem2 : (p2 ∈ A ∨ q2 ∈ A) ∧ (p2 ∈ B ∨ q2 ∈ B) ∧ (p2 ∈ D ∨ q2 ∈ D) := by
          obtain ⟨⟨a, ha, hpa⟩, ⟨b, hb, hpb⟩, ⟨d, hd, hpd⟩⟩ := (hx5_iff (pairInput u2 v2)).mp hj2v
          simp only [pairInput, decide_eq_true_eq] at hpa hpb hpd
          rcases hpq2_or with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · refine ⟨?_, ?_, ?_⟩
            · rcases hpa with rfl | rfl <;> [exact Or.inl (h1.symm ▸ ha); exact Or.inr (h2.symm ▸ ha)]
            · rcases hpb with rfl | rfl <;> [exact Or.inl (h1.symm ▸ hb); exact Or.inr (h2.symm ▸ hb)]
            · rcases hpd with rfl | rfl <;> [exact Or.inl (h1.symm ▸ hd); exact Or.inr (h2.symm ▸ hd)]
          · refine ⟨?_, ?_, ?_⟩
            · rcases hpa with rfl | rfl <;> [exact Or.inr (h2.symm ▸ ha); exact Or.inl (h1.symm ▸ ha)]
            · rcases hpb with rfl | rfl <;> [exact Or.inr (h2.symm ▸ hb); exact Or.inl (h1.symm ▸ hb)]
            · rcases hpd with rfl | rfl <;> [exact Or.inr (h2.symm ▸ hd); exact Or.inl (h1.symm ▸ hd)]
        -- Helper: wire w < 11 + x5 with no AND gate in OR-closure and 2 distinct elements in orIn gives common neighbor in T!
        have wire_common_T : ∀ (w : ℕ) (hwlt : w < 11 + x5),
            (∀ g, OrReaches 11 C w g → (gateAt C g).op ≠ GateOp.and) →
            ∀ x y : Fin 11, x ≠ y → x ∈ orIn 11 C w → y ∈ orIn 11 C w →
            ∃ z ∈ T, g11Graph.Adj z x ∧ g11Graph.Adj z y := by
          intro w hwlt hnoand x y hxy hx hy
          have hwge : 11 ≤ w := by
            by_contra hlt11
            push Not at hlt11
            have heq := orIn_input_eq_singleton 11 C w hlt11
            rw [heq, Finset.mem_singleton] at hx hy
            exact hxy (hx.trans hy.symm)
          let g := w - 11
          have hweq : w = 11 + g := by omega
          have hglt5 : g < x5 := by omega
          have hglt : g < C.gates.length := by omega
          have hgop : (gateAt C g).op = GateOp.or := by
            have hne := hnoand g (by rw [hweq]; exact orReaches_self 11 C g hglt)
            obtain ⟨_, _, _, hor⟩ := isAO2_inputs 11 C hAO g hglt
            rcases hor with ha | ho
            · exact (hne ha).elim
            · exact ho
          have hg_orN : g ∈ orN g11Graph C := by
            rw [mem_orN_iff]
            refine ⟨hglt, hgop, fun hbf => ?_⟩
            have hgx : gateVal 11 C g (fun v => decide (v = x)) = true := by
              rw [gateVal_eq_wireVal, ← hweq]
              exact orIn_wireVal_true 11 C hAO _ w x hx (by simp)
            have hfx := hbf _ hgx
            rw [graphFun_empty_oneHot_false g11Graph x] at hfx
            cases hfx
          have hg_lam : g ∈ lam g11Graph C := by
            by_contra hnl
            have hg14 : g ∈ x14 := Finset.mem_sdiff.mpr ⟨hg_orN, hnl⟩
            rw [hx14m, Finset.mem_singleton] at hg14
            omega
          simp only [lam, Finset.mem_filter] at hg_lam
          obtain ⟨_, _, _, t, ht, b, hsc1, hrtg⟩ := hg_lam
          have hsub : orIn 11 C (11 + g) ⊆ side (n := 11) C t b :=
            orIn_subset_of_orReaches 11 C (opnd C t b) g hrtg
          have hxt : x ∈ side (n := 11) C t b := hsub (by rwa [← hweq])
          have hyt : y ∈ side (n := 11) C t b := hsub (by rwa [← hweq])
          have hge2 : 2 ≤ (side (n := 11) C t b).card := by
            have hpair : ({x, y} : Finset (Fin 11)) ⊆ side (n := 11) C t b := by
              intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
              rcases hv with rfl | rfl <;> assumption
            have hc := Finset.card_le_card hpair
            rwa [Finset.card_pair hxy] at hc
          obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hsc1
          have hzc : z = center t := hcenter_unique_singleton t ht b z hz hge2
          have hzT : z ∈ T := by rw [hzc]; exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
          have hz_mem : z ∈ side (n := 11) C t (1 - b) := by rw [hz]; simp
          refine ⟨z, hzT, ?_, ?_⟩
          · fin_cases b
            · exact ((htop_star t ht).1 x hxt z hz_mem).symm
            · exact (htop_star t ht).1 z hz_mem x hxt
          · fin_cases b
            · exact ((htop_star t ht).1 y hyt z hz_mem).symm
            · exact (htop_star t ht).1 z hz_mem y hyt
        -- Wires corresponding to A, B, D
        have hwire_A : ∀ x y : Fin 11, x ≠ y → x ∈ A → y ∈ A →
            ∃ z ∈ T, g11Graph.Adj z x ∧ g11Graph.Adj z y := by
          obtain ⟨_, h40, _, _⟩ := isAO2_inputs 11 C hAO x4 hx4lt
          exact wire_common_T (opnd C x4 0) (by omega) (hx4_noand 0)
        have hwire_B : ∀ x y : Fin 11, x ≠ y → x ∈ B → y ∈ B →
            ∃ z ∈ T, g11Graph.Adj z x ∧ g11Graph.Adj z y := by
          obtain ⟨_, _, h41, _⟩ := isAO2_inputs 11 C hAO x4 hx4lt
          exact wire_common_T (opnd C x4 1) (by omega) (hx4_noand 1)
        have hwire_D : ∀ x y : Fin 11, x ≠ y → x ∈ D → y ∈ D →
            ∃ z ∈ T, g11Graph.Adj z x ∧ g11Graph.Adj z y :=
          wire_common_T (opnd C x5 (1 - c)) hx5_other_lt hx5_other_noand
        -- Deduce: {q1, q2} covers A, B, D, AND common neighbors exist for (p1, q2), (q1, p2), (q1, q2)!
        have htriples :
            ((q1 ∈ A ∨ q2 ∈ A) ∧ (q1 ∈ B ∨ q2 ∈ B) ∧ (q1 ∈ D ∨ q2 ∈ D)) ∧
            (∃ z ∈ T, g11Graph.Adj z p1 ∧ g11Graph.Adj z q2) ∧
            (∃ z ∈ T, g11Graph.Adj z q1 ∧ g11Graph.Adj z p2) ∧
            (∃ z ∈ T, g11Graph.Adj z q1 ∧ g11Graph.Adj z q2) := by
          -- Exclude pairs of {A, B, D} for p1
          have hnp1AB : ¬(p1 ∈ A ∧ p1 ∈ B) := by
            rintro ⟨h1, h2⟩
            rcases hmem2.2.2 with h3 | h3
            · exact hno_fire1 p2 (Or.inl rfl) ⟨Or.inl h1, Or.inl h2, Or.inr h3⟩
            · exact hno_fire1 q2 (Or.inr rfl) ⟨Or.inl h1, Or.inl h2, Or.inr h3⟩
          have hnp1AD : ¬(p1 ∈ A ∧ p1 ∈ D) := by
            rintro ⟨h1, h2⟩
            rcases hmem2.2.1 with h3 | h3
            · exact hno_fire1 p2 (Or.inl rfl) ⟨Or.inl h1, Or.inr h3, Or.inl h2⟩
            · exact hno_fire1 q2 (Or.inr rfl) ⟨Or.inl h1, Or.inr h3, Or.inl h2⟩
          have hnp1BD : ¬(p1 ∈ B ∧ p1 ∈ D) := by
            rintro ⟨h1, h2⟩
            rcases hmem2.1 with h3 | h3
            · exact hno_fire1 p2 (Or.inl rfl) ⟨Or.inr h3, Or.inl h1, Or.inl h2⟩
            · exact hno_fire1 q2 (Or.inr rfl) ⟨Or.inr h3, Or.inl h1, Or.inl h2⟩
          -- Exclude pairs of {A, B, D} for p2
          have hnp2AB : ¬(p2 ∈ A ∧ p2 ∈ B) := by
            rintro ⟨h1, h2⟩
            rcases hmem1.2.2 with h3 | h3
            · exact hno_fire2 p1 (Or.inl rfl) ⟨Or.inr h1, Or.inr h2, Or.inl h3⟩
            · exact hno_fire2 q1 (Or.inr rfl) ⟨Or.inr h1, Or.inr h2, Or.inl h3⟩
          have hnp2AD : ¬(p2 ∈ A ∧ p2 ∈ D) := by
            rintro ⟨h1, h2⟩
            rcases hmem1.2.1 with h3 | h3
            · exact hno_fire2 p1 (Or.inl rfl) ⟨Or.inr h1, Or.inl h3, Or.inr h2⟩
            · exact hno_fire2 q1 (Or.inr rfl) ⟨Or.inr h1, Or.inl h3, Or.inr h2⟩
          have hnp2BD : ¬(p2 ∈ B ∧ p2 ∈ D) := by
            rintro ⟨h1, h2⟩
            rcases hmem1.1 with h3 | h3
            · exact hno_fire2 p1 (Or.inl rfl) ⟨Or.inl h3, Or.inr h1, Or.inr h2⟩
            · exact hno_fire2 q1 (Or.inr rfl) ⟨Or.inl h3, Or.inr h1, Or.inr h2⟩
          -- p1 must be in at least one of A, B, D (else q1 in all 3 -> fire2 q1)
          have hp1_some : p1 ∈ A ∨ p1 ∈ B ∨ p1 ∈ D := by
            by_contra h
            push Not at h
            have hqA : q1 ∈ A := hmem1.1.resolve_left h.1
            have hqB : q1 ∈ B := hmem1.2.1.resolve_left h.2.1
            have hqD : q1 ∈ D := hmem1.2.2.resolve_left h.2.2
            exact hno_fire2 q1 (Or.inr rfl) ⟨Or.inl hqA, Or.inl hqB, Or.inl hqD⟩
          -- p2 must be in at least one of A, B, D (else q2 in all 3 -> fire1 q2)
          have hp2_some : p2 ∈ A ∨ p2 ∈ B ∨ p2 ∈ D := by
            by_contra h
            push Not at h
            have hqA : q2 ∈ A := hmem2.1.resolve_left h.1
            have hqB : q2 ∈ B := hmem2.2.1.resolve_left h.2.1
            have hqD : q2 ∈ D := hmem2.2.2.resolve_left h.2.2
            exact hno_fire1 q2 (Or.inr rfl) ⟨Or.inr hqA, Or.inr hqB, Or.inr hqD⟩
          rcases hp1_some with hp1A | hp1B | hp1D <;> rcases hp2_some with hp2A | hp2B | hp2D
          · -- p1 ∈ A, p2 ∈ A -> contradiction
            have hq2B : q2 ∈ B := hmem2.2.1.resolve_left (fun h => hnp2AB ⟨hp2A, h⟩)
            have hq2D : q2 ∈ D := hmem2.2.2.resolve_left (fun h => hnp2AD ⟨hp2A, h⟩)
            exact (hno_fire1 q2 (Or.inr rfl) ⟨Or.inl hp1A, Or.inr hq2B, Or.inr hq2D⟩).elim
          · -- p1 ∈ A, p2 ∈ B
            have hq1B : q1 ∈ B := hmem1.2.1.resolve_left (fun h => hnp1AB ⟨hp1A, h⟩)
            have hq1D : q1 ∈ D := hmem1.2.2.resolve_left (fun h => hnp1AD ⟨hp1A, h⟩)
            have hq2A : q2 ∈ A := hmem2.1.resolve_left (fun h => hnp2AB ⟨h, hp2B⟩)
            have hq2D : q2 ∈ D := hmem2.2.2.resolve_left (fun h => hnp2BD ⟨hp2B, h⟩)
            exact ⟨⟨Or.inr hq2A, Or.inl hq1B, Or.inl hq1D⟩,
              hwire_A p1 q2 hpq_disj.1 hp1A hq2A,
              hwire_B q1 p2 hpq_disj.2.1 hq1B hp2B,
              hwire_D q1 q2 hpq_disj.2.2 hq1D hq2D⟩
          · -- p1 ∈ A, p2 ∈ D
            have hq1B : q1 ∈ B := hmem1.2.1.resolve_left (fun h => hnp1AB ⟨hp1A, h⟩)
            have hq1D : q1 ∈ D := hmem1.2.2.resolve_left (fun h => hnp1AD ⟨hp1A, h⟩)
            have hq2A : q2 ∈ A := hmem2.1.resolve_left (fun h => hnp2AD ⟨h, hp2D⟩)
            have hq2B : q2 ∈ B := hmem2.2.1.resolve_left (fun h => hnp2BD ⟨h, hp2D⟩)
            exact ⟨⟨Or.inr hq2A, Or.inl hq1B, Or.inl hq1D⟩,
              hwire_A p1 q2 hpq_disj.1 hp1A hq2A,
              hwire_D q1 p2 hpq_disj.2.1 hq1D hp2D,
              hwire_B q1 q2 hpq_disj.2.2 hq1B hq2B⟩
          · -- p1 ∈ B, p2 ∈ A
            have hq1A : q1 ∈ A := hmem1.1.resolve_left (fun h => hnp1AB ⟨h, hp1B⟩)
            have hq1D : q1 ∈ D := hmem1.2.2.resolve_left (fun h => hnp1BD ⟨hp1B, h⟩)
            have hq2B : q2 ∈ B := hmem2.2.1.resolve_left (fun h => hnp2AB ⟨hp2A, h⟩)
            have hq2D : q2 ∈ D := hmem2.2.2.resolve_left (fun h => hnp2AD ⟨hp2A, h⟩)
            exact ⟨⟨Or.inl hq1A, Or.inr hq2B, Or.inl hq1D⟩,
              hwire_B p1 q2 hpq_disj.1 hp1B hq2B,
              hwire_A q1 p2 hpq_disj.2.1 hq1A hp2A,
              hwire_D q1 q2 hpq_disj.2.2 hq1D hq2D⟩
          · -- p1 ∈ B, p2 ∈ B -> contradiction
            have hq2A : q2 ∈ A := hmem2.1.resolve_left (fun h => hnp2AB ⟨h, hp2B⟩)
            have hq2D : q2 ∈ D := hmem2.2.2.resolve_left (fun h => hnp2BD ⟨hp2B, h⟩)
            exact (hno_fire1 q2 (Or.inr rfl) ⟨Or.inr hq2A, Or.inl hp1B, Or.inr hq2D⟩).elim
          · -- p1 ∈ B, p2 ∈ D
            have hq1A : q1 ∈ A := hmem1.1.resolve_left (fun h => hnp1AB ⟨h, hp1B⟩)
            have hq1D : q1 ∈ D := hmem1.2.2.resolve_left (fun h => hnp1BD ⟨hp1B, h⟩)
            have hq2A : q2 ∈ A := hmem2.1.resolve_left (fun h => hnp2AD ⟨h, hp2D⟩)
            have hq2B : q2 ∈ B := hmem2.2.1.resolve_left (fun h => hnp2BD ⟨h, hp2D⟩)
            exact ⟨⟨Or.inl hq1A, Or.inr hq2B, Or.inl hq1D⟩,
              hwire_B p1 q2 hpq_disj.1 hp1B hq2B,
              hwire_D q1 p2 hpq_disj.2.1 hq1D hp2D,
              hwire_A q1 q2 hpq_disj.2.2 hq1A hq2A⟩
          · -- p1 ∈ D, p2 ∈ A
            have hq1A : q1 ∈ A := hmem1.1.resolve_left (fun h => hnp1AD ⟨h, hp1D⟩)
            have hq1B : q1 ∈ B := hmem1.2.1.resolve_left (fun h => hnp1BD ⟨h, hp1D⟩)
            have hq2B : q2 ∈ B := hmem2.2.1.resolve_left (fun h => hnp2AB ⟨hp2A, h⟩)
            have hq2D : q2 ∈ D := hmem2.2.2.resolve_left (fun h => hnp2AD ⟨hp2A, h⟩)
            exact ⟨⟨Or.inl hq1A, Or.inl hq1B, Or.inr hq2D⟩,
              hwire_D p1 q2 hpq_disj.1 hp1D hq2D,
              hwire_A q1 p2 hpq_disj.2.1 hq1A hp2A,
              hwire_B q1 q2 hpq_disj.2.2 hq1B hq2B⟩
          · -- p1 ∈ D, p2 ∈ B
            have hq1A : q1 ∈ A := hmem1.1.resolve_left (fun h => hnp1AD ⟨h, hp1D⟩)
            have hq1B : q1 ∈ B := hmem1.2.1.resolve_left (fun h => hnp1BD ⟨h, hp1D⟩)
            have hq2A : q2 ∈ A := hmem2.1.resolve_left (fun h => hnp2AB ⟨h, hp2B⟩)
            have hq2D : q2 ∈ D := hmem2.2.2.resolve_left (fun h => hnp2BD ⟨hp2B, h⟩)
            exact ⟨⟨Or.inl hq1A, Or.inl hq1B, Or.inr hq2D⟩,
              hwire_D p1 q2 hpq_disj.1 hp1D hq2D,
              hwire_B q1 p2 hpq_disj.2.1 hq1B hp2B,
              hwire_A q1 q2 hpq_disj.2.2 hq1A hq2A⟩
          · -- p1 ∈ D, p2 ∈ D -> contradiction
            have hq2A : q2 ∈ A := hmem2.1.resolve_left (fun h => hnp2AD ⟨h, hp2D⟩)
            have hq2B : q2 ∈ B := hmem2.2.1.resolve_left (fun h => hnp2BD ⟨h, hp2D⟩)
            exact (hno_fire1 q2 (Or.inr rfl) ⟨Or.inr hq2A, Or.inr hq2B, Or.inl hp1D⟩).elim
        obtain ⟨hq12_cov, hz1, hz2, hz3⟩ := htriples
        -- Apply finite G11 lemma: every z ∈ T adjacent to p1 is also adjacent to q2!
        have hco_pq : checkOrient (finsetToMask T) p1.val q1.val p2.val q2.val = true := by
          unfold checkTripleForList at htriple_ok
          simp only [Bool.and_eq_true] at htriple_ok
          rcases hpq1_or with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hpq2_or with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
            rw [h1, h2, h3, h4]
          · exact htriple_ok.1.1.1
          · exact htriple_ok.1.1.2
          · exact htriple_ok.1.2
          · exact htriple_ok.2
        have htransfer : ∀ z ∈ T, g11Graph.Adj z p1 → g11Graph.Adj z q2 :=
          checkOrient_spec T p1 q1 p2 q2 hco_pq hz1 hz2 hz3
        -- Close the contradiction via t1 and center t1!
        let c1 := center t1
        have hc1T : c1 ∈ T := Finset.mem_image.mpr ⟨t1, ht1, rfl⟩
        have hp1_ne_c1 : p1 ≠ c1 := fun h => hpq1_nT.1 (h ▸ hc1T)
        have hside_t1_b1 : side (n := 11) C t1 b1 = {c1} :=
          hcenter_other_singleton t1 ht1 b1 p1 hw1 hp1_ne_c1
        have hc1_adj_p1 : g11Graph.Adj c1 p1 := by
          have hc1_mem : c1 ∈ side (n := 11) C t1 b1 := by rw [hside_t1_b1]; simp
          fin_cases b1
          · exact (htop_star t1 ht1).1 c1 hc1_mem p1 hw1
          · exact ((htop_star t1 ht1).1 p1 hw1 c1 hc1_mem).symm
        have hc1_adj_q2 : g11Graph.Adj c1 q2 := htransfer c1 hc1T hc1_adj_p1
        have hnot_x12 : s(c1, q2) ∉ x12 := by
          rw [hx12_eq]
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          constructor <;> intro hs <;>
            simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hs
          · rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact hu1nT (show u1 ∈ T from h1 ▸ hc1T)
            · exact hv1nT (show v1 ∈ T from h1 ▸ hc1T)
          · rcases hs with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact hu2nT (show u2 ∈ T from h1 ▸ hc1T)
            · exact hv2nT (show v2 ∈ T from h1 ▸ hc1T)
        have hstar_c1q2 : s(c1, q2) ∈ starEdges g11Graph C := by
          have hedge : s(c1, q2) ∈ g11Graph.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hc1_adj_q2
          by_contra hns
          exact hnot_x12 (Finset.mem_sdiff.mpr ⟨hedge, hns⟩)
        simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at hstar_c1q2
        obtain ⟨t', ht', ⟨a', b'⟩, ⟨ha', hb'⟩, hs'⟩ := hstar_c1q2
        have hct'_eq : center t' = c1 := by
          have hct'_ab : center t' = a' ∨ center t' = b' := by
            rcases hcenter_spec t' ht' with h0 | h1
            · rw [h0, Finset.mem_singleton] at ha'; exact Or.inl ha'.symm
            · rw [h1, Finset.mem_singleton] at hb'; exact Or.inr hb'.symm
          have hct'_T : center t' ∈ T := Finset.mem_image.mpr ⟨t', ht', rfl⟩
          simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hs'
          rcases hs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hct'_ab with heq | heq
          · exact heq
          · exact (hpq2_nT.2 (heq ▸ hct'_T)).elim
          · exact (hpq2_nT.2 (heq ▸ hct'_T)).elim
          · exact heq
        have ht'_eq : t' = t1 := hcenter_inj ht' ht1 hct'_eq
        subst t'
        have hq2_in_t1 : q2 ∈ side (n := 11) C t1 (1 - b1) := by
          have hq2_ne_c1 : q2 ≠ c1 := fun h => hpq2_nT.2 (h ▸ hc1T)
          simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at hs'
          fin_cases b1
          · change side (n := 11) C t1 0 = {c1} at hside_t1_b1
            rw [hside_t1_b1, Finset.mem_singleton] at ha'
            rcases hs' with ⟨_, rfl⟩ | ⟨h1, _⟩
            · exact hb'
            · exact (hq2_ne_c1 (h1.symm.trans ha')).elim
          · change side (n := 11) C t1 1 = {c1} at hside_t1_b1
            rw [hside_t1_b1, Finset.mem_singleton] at hb'
            rcases hs' with ⟨_, h2⟩ | ⟨rfl, _⟩
            · exact (hq2_ne_c1 (h2.symm.trans hb')).elim
            · exact ha'
        -- Evaluate t1 on pairInput q1 q2!
        have hjv_q1q2 : gateVal 11 C x5 (pairInput q1 q2) = true := by
          rw [hx5_iff (pairInput q1 q2)]
          refine ⟨?_, ?_, ?_⟩
          · rcases hq12_cov.1 with h | h
            · exact ⟨q1, h, by simp [pairInput]⟩
            · exact ⟨q2, h, by simp [pairInput]⟩
          · rcases hq12_cov.2.1 with h | h
            · exact ⟨q1, h, by simp [pairInput]⟩
            · exact ⟨q2, h, by simp [pairInput]⟩
          · rcases hq12_cov.2.2 with h | h
            · exact ⟨q1, h, by simp [pairInput]⟩
            · exact ⟨q2, h, by simp [pairInput]⟩
        have ht1mem := ht1
        simp only [x15, tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ht1mem
        have hv1 := orReaches_wireVal_true 11 C hAO (pairInput q1 q2) (opnd C t1 b1) x5 hrt1j hjv_q1q2
        have hv2 := orIn_wireVal_true 11 C hAO (pairInput q1 q2) (opnd C t1 (1 - b1)) q2 hq2_in_t1
          (by simp [pairInput])
        have htv : gateVal 11 C t1 (pairInput q1 q2) = true := by
          rw [gateVal_and_iff 11 C hAO t1 ht1mem.1 ht1mem.2.1 (pairInput q1 q2)]
          fin_cases b1
          · exact ⟨hv1, hv2⟩
          · exact ⟨hv2, hv1⟩
        exact hpq_nocross q1 q2 (Or.inr rfl) (Or.inr rfl)
          (graphFun_empty_pairInput g11Graph q1 q2 (ht1mem.2.2 _ htv))
  · simp [hul_eq] at hulen2

end PEqualNP.Outside.L_meta_5226

theorem PEqualNP.Outside.L_meta_5226 :
  ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x4 < x5 →           PEqualNP.TopForm.junk x1 x3 = {x4, x5} →             PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →               have x12 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;               have x13 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;               have x14 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;               have x15 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;               (∀ x16 ∈ x15,                   have x18 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x16;                   (∀ x19 ∈ x18 (0 : Fin (2 : ℕ)), ∀ x21 ∈ x18 (1 : Fin (2 : ℕ)), x1.Adj x19 x21) ∧ ((x18 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x18 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →                 x3.size = (21 : ℕ) → (x15 \ x13).card = (5 : ℕ) → x13 = ∅ → x12.card = (2 : ℕ) → (∀ x21 ∈ x12, ∀ x23 ∈ x12, x21 ≠ x23 → ∀ x26 ∈ x21, x26 ∉ x23) → (∃ (x22 : ℕ) (x23 : ℕ), x14 = {x22} ∧ x23 ∈ PEqualNP.TopForm.junk x1 x3 ∧ (11 : ℕ) + x23 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x22).inputs ∧ ∀ (x24 x25 : Fin (11 : ℕ)), s(x24, x25) ∈ x12 → ∃ x27 ∈ x15, ∃ (x28 : Fin (2 : ℕ)), PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x27 (PEqualNP.EdgeOwnership.pairInput x24 x25) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x27 x28) x22 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x23 (PEqualNP.EdgeOwnership.pairInput x24 x25) = Bool.true) → False := by
  intro x1 _ x3 x4 x5 hx1 hLeast hTF h45 hjunk hcone45
  dsimp only
  intro htop_star _ hcard5 hcent hustar2 _ hwit
  exact PEqualNP.Outside.L_meta_5226.main_proof x1 x3 x4 x5 hx1 hLeast hTF h45 hjunk hcone45
    htop_star hcard5 hcent hustar2 hwit

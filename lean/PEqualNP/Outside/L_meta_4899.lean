import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4899

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

/-! ### Part 1: Generic append-only `foldl` lemma -/

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

lemma gateAt_eq_of_getElem? (C : Circuit) (j : ℕ) (g : Gate) (h : C.gates[j]? = some g) :
    gateAt C j = g := by
  simp only [gateAt, List.getD_eq_getElem?_getD, h, Option.getD_some]

/-! ### Part 2: `wires`, `cones`, `orSets` unfolding lemmas -/

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

lemma orReaches_le (n : ℕ) (C : Circuit) : ∀ k g, OrReaches n C (n + k) g → g ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro g hg
    have hk : k < C.gates.length := by
      have := orReaches_lt_len n C (n + k) g hg; omega
    rw [orReaches_iff_gate n C k g hk] at hg
    rcases hg with rfl | ⟨_, u, _, hult, hge, hgu⟩
    · exact le_rfl
    · have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hgu
      have hle := ih (u - n) (by omega) g ⟨by omega, by simpa using hgu⟩
      omega

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

lemma orIn_mono_of_orReaches (n : ℕ) (C : Circuit) (w k : ℕ) (u : Fin n)
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or)
    (hmem : u.val ∈ (gateAt C k).inputs) (hr : OrReaches n C w k) :
    u ∈ orIn n C w := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr ⟨k, hk, hr, hop, hmem⟩

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

/-! ### Part 3: Core Structural Lemmas for `TopForm` with `junk = {x4, x5}` -/

lemma no_and_below_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (x4 x5 : ℕ)
    (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hjunk : junk G C = {x4, x5})
    (hnc45 : ¬InCone n C x4 x5) (hnc54 : ¬InCone n C x5 x4)
    (j : ℕ) (hj : j = x4 ∨ j = x5) (b : Fin 2) (g : ℕ)
    (hr : OrReaches n C (opnd C j b) g) : (gateAt C g).op ≠ GateOp.and := by
  have hjmem : j ∈ junk G C := by rw [hjunk]; rcases hj with rfl | rfl <;> simp
  unfold junk gatesWhere at hjmem
  rw [Finset.mem_filter, Finset.mem_range] at hjmem
  unfold IsDirtyAnd IsDirty at hjmem
  have hjlt : j < C.gates.length := hjmem.1
  have hjop : (gateAt C j).op = GateOp.and := hjmem.2.1
  have hcone : InCone n C g j := orReaches_imp_inCone_parent n C hAO j hjlt b g hr
  have hglt : g < j := inCone_lt n C j g hcone
  intro hgop
  by_cases hbf : BelowF G C g
  · exact hTF g (by omega) j hjlt hgop hbf hjop hcone
  · have hgdirty : g ∈ junk G C := by
      unfold junk gatesWhere
      rw [Finset.mem_filter, Finset.mem_range]
      unfold IsDirtyAnd IsDirty
      refine ⟨by omega, hgop, by omega, ?_⟩
      unfold BelowF at hbf
      push_neg at hbf
      obtain ⟨x, hx1, hx2⟩ := hbf
      exact ⟨x, hx1, Bool.eq_false_iff.mpr hx2⟩
    rw [hjunk] at hgdirty
    simp only [Finset.mem_insert, Finset.mem_singleton] at hgdirty
    rcases hj with rfl | rfl <;> rcases hgdirty with rfl | rfl
    · exact Nat.lt_irrefl _ hglt
    · exact hnc54 hcone
    · exact hnc45 hcone
    · exact Nat.lt_irrefl _ hglt

lemma junk_val_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (x4 x5 : ℕ)
    (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hjunk : junk G C = {x4, x5})
    (hnc45 : ¬InCone n C x4 x5) (hnc54 : ¬InCone n C x5 x4)
    (j : ℕ) (hj : j = x4 ∨ j = x5) (x : Fin n → Bool) :
    gateVal n C j x = true ↔
      (∃ a ∈ side (n := n) C j 0, x a = true) ∧ (∃ b ∈ side (n := n) C j 1, x b = true) := by
  have hjmem : j ∈ junk G C := by rw [hjunk]; rcases hj with rfl | rfl <;> simp
  unfold junk gatesWhere at hjmem
  rw [Finset.mem_filter, Finset.mem_range] at hjmem
  unfold IsDirtyAnd IsDirty at hjmem
  have hjlt : j < C.gates.length := hjmem.1
  have hjop : (gateAt C j).op = GateOp.and := hjmem.2.1
  obtain ⟨_, h0, h1, _⟩ := isAO2_inputs n C hAO j hjlt
  rw [gateVal_and_iff n C hAO j hjlt hjop x]
  constructor
  · rintro ⟨hv0, hv1⟩
    exact ⟨pure_or_wireVal_imp_orIn n C hAO x (opnd C j 0) (by omega)
        (no_and_below_junk G C x4 x5 hAO hTF hjunk hnc45 hnc54 j hj 0) hv0,
      pure_or_wireVal_imp_orIn n C hAO x (opnd C j 1) (by omega)
        (no_and_below_junk G C x4 x5 hAO hTF hjunk hnc45 hnc54 j hj 1) hv1⟩
  · rintro ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩
    exact ⟨orIn_wireVal_true n C hAO x (opnd C j 0) a ha hxa,
      orIn_wireVal_true n C hAO x (opnd C j 1) b hb hxb⟩

lemma top_other_side_no_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (x4 x5 : ℕ)
    (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hjunk : junk G C = {x4, x5})
    (hdisj : ∀ t ∈ tops G C, InCone n C x4 t → ¬InCone n C x5 t)
    (t : ℕ) (ht : t ∈ tops G C) (b : Fin 2) (j : ℕ) (hj : j = x4 ∨ j = x5)
    (hr : OrReaches n C (opnd C t b) j) :
    ∀ g, OrReaches n C (opnd C t (1 - b)) g → (gateAt C g).op ≠ GateOp.and := by
  have htmem := ht
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htmem
  have htlt : t < C.gates.length := htmem.1
  have htop : (gateAt C t).op = GateOp.and := htmem.2.1
  have htbf : BelowF G C t := htmem.2.2
  have hjt : InCone n C j t := orReaches_imp_inCone_parent n C hAO t htlt b j hr
  intro g hrg hgop
  have hgt : InCone n C g t := orReaches_imp_inCone_parent n C hAO t htlt (1 - b) g hrg
  have hglt : g < t := inCone_lt n C t g hgt
  by_cases hbf : BelowF G C g
  · exact hTF g (by omega) t htlt hgop hbf htop hgt
  · have hgdirty : g ∈ junk G C := by
      unfold junk gatesWhere
      rw [Finset.mem_filter, Finset.mem_range]
      unfold IsDirtyAnd IsDirty
      refine ⟨by omega, hgop, by omega, ?_⟩
      unfold BelowF at hbf; push_neg at hbf
      obtain ⟨x, hx1, hx2⟩ := hbf
      exact ⟨x, hx1, Bool.eq_false_iff.mpr hx2⟩
    rw [hjunk] at hgdirty
    simp only [Finset.mem_insert, Finset.mem_singleton] at hgdirty
    have hgj : g = j := by
      rcases hj with hj' | hj' <;> rcases hgdirty with hg' | hg'
      · omega
      · exact (hdisj t ht (hj' ▸ hjt) (hg' ▸ hgt)).elim
      · exact (hdisj t ht (hg' ▸ hgt) (hj' ▸ hjt)).elim
      · omega
    subst hgj
    -- Both operands of t OR-reach g, contradicting that g is dirty while t is BelowF!
    have hjmem : g ∈ junk G C := by rw [hjunk]; rcases hj with rfl | rfl <;> simp
    unfold junk gatesWhere at hjmem
    rw [Finset.mem_filter, Finset.mem_range] at hjmem
    unfold IsDirtyAnd IsDirty at hjmem
    obtain ⟨x, hjx, hfx⟩ := hjmem.2.2.2
    have hv1 := orReaches_wireVal_true n C hAO x (opnd C t b) g hr hjx
    have hv2 := orReaches_wireVal_true n C hAO x (opnd C t (1 - b)) g hrg hjx
    have htv : gateVal n C t x = true := by
      rw [gateVal_and_iff n C hAO t htlt htop x]
      fin_cases b
      · exact ⟨hv1, hv2⟩
      · exact ⟨hv2, hv1⟩
    have hft := htbf x htv
    rw [hfx] at hft; cases hft

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

lemma no_induced_matching_same_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (x4 x5 : ℕ)
    (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hjunk : junk G C = {x4, x5})
    (hnc45 : ¬InCone n C x4 x5) (hnc54 : ¬InCone n C x5 x4)
    (hdisj : ∀ t ∈ tops G C, InCone n C x4 t → ¬InCone n C x5 t)
    (j : ℕ) (hj : j = x4 ∨ j = x5)
    (u1 v1 u2 v2 : Fin n)
    (hcross : ¬G.Adj u1 u2 ∧ ¬G.Adj u1 v2 ∧ ¬G.Adj v1 u2 ∧ ¬G.Adj v1 v2)
    (t1 : ℕ) (ht1 : t1 ∈ tops G C) (b1 : Fin 2)
    (ht1v : gateVal n C t1 (pairInput u1 v1) = true)
    (hr1 : OrReaches n C (opnd C t1 b1) j)
    (hj1 : gateVal n C j (pairInput u1 v1) = true)
    (t2 : ℕ) (ht2 : t2 ∈ tops G C) (b2 : Fin 2)
    (ht2v : gateVal n C t2 (pairInput u2 v2) = true)
    (hr2 : OrReaches n C (opnd C t2 b2) j)
    (hj2 : gateVal n C j (pairInput u2 v2) = true) : False := by
  have hj1' := (junk_val_iff G C x4 x5 hAO hTF hjunk hnc45 hnc54 j hj (pairInput u1 v1)).mp hj1
  have hj2' := (junk_val_iff G C x4 x5 hAO hTF hjunk hnc45 hnc54 j hj (pairInput u2 v2)).mp hj2
  obtain ⟨⟨a1, ha1, hpa1⟩, ⟨c1, hc1, hpc1⟩⟩ := hj1'
  obtain ⟨⟨a2, ha2, hpa2⟩, ⟨c2, hc2, hpc2⟩⟩ := hj2'
  simp only [pairInput, decide_eq_true_eq] at hpa1 hpc1 hpa2 hpc2
  -- Extract w1 ∈ {u1, v1} ∩ side t1 (1 - b1) and w2 ∈ {u2, v2} ∩ side t2 (1 - b2)
  have get_w : ∀ (t : ℕ) (ht : t ∈ tops G C) (b : Fin 2) (u v : Fin n),
      gateVal n C t (pairInput u v) = true → OrReaches n C (opnd C t b) j →
      ∃ w ∈ side (n := n) C t (1 - b), w = u ∨ w = v := by
    intro t ht b u v htv hr
    have htmem := ht
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htmem
    obtain ⟨_, h0, h1, _⟩ := isAO2_inputs n C hAO t htmem.1
    rw [gateVal_and_iff n C hAO t htmem.1 htmem.2.1 (pairInput u v)] at htv
    have hval : wireVal n C (opnd C t (1 - b)) (pairInput u v) = true := by
      fin_cases b
      · exact htv.2
      · exact htv.1
    have hlt : opnd C t (1 - b) < n + C.gates.length := by
      fin_cases b
      · change opnd C t 1 < n + C.gates.length; omega
      · change opnd C t 0 < n + C.gates.length; omega
    obtain ⟨w, hw, hpw⟩ := pure_or_wireVal_imp_orIn n C hAO (pairInput u v) (opnd C t (1 - b)) hlt
      (top_other_side_no_and G C x4 x5 hAO hTF hjunk hdisj t ht b j hj hr) hval
    simp only [pairInput, decide_eq_true_eq] at hpw
    exact ⟨w, hw, hpw⟩
  obtain ⟨w1, hw1, hpw1⟩ := get_w t1 ht1 b1 u1 v1 ht1v hr1
  obtain ⟨w2, hw2, hpw2⟩ := get_w t2 ht2 b2 u2 v2 ht2v hr2
  -- Helper: if a ∈ side j 0, c ∈ side j 1, w ∈ side t (1-b) and OrReaches (opnd t b) j,
  -- and {a, c, w} has at most 2 distinct elements p, q (i.e. a, c, w ∈ {p, q}), then G.Adj p q!
  have fire : ∀ (t : ℕ) (ht : t ∈ tops G C) (b : Fin 2) (p q : Fin n),
      OrReaches n C (opnd C t b) j →
      (∃ a ∈ side (n := n) C j 0, a = p ∨ a = q) →
      (∃ c ∈ side (n := n) C j 1, c = p ∨ c = q) →
      (∃ w ∈ side (n := n) C t (1 - b), w = p ∨ w = q) →
      G.Adj p q := by
    intro t ht b p q hr ⟨a, ha, hapq⟩ ⟨c, hc, hcpq⟩ ⟨w, hw, hwpq⟩
    have htmem := ht
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htmem
    have hjv : gateVal n C j (pairInput p q) = true := by
      rw [junk_val_iff G C x4 x5 hAO hTF hjunk hnc45 hnc54 j hj (pairInput p q)]
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
  · -- a1 ∈ side j 0 ∩ side j 1, pair with w2 ∈ side t2 (1 - b2)!
    have hadj := fire t2 ht2 b2 a1 w2 hr2
      ⟨a1, ha1, Or.inl rfl⟩ ⟨c1, hc1, Or.inl heq.symm⟩ ⟨w2, hw2, Or.inr rfl⟩
    exact hno a1 w2 hpa1 hpw2 hadj
  · -- {a1, c1} = {u1, v1}, so w1 = a1 or w1 = c1!
    have hw_cases : w1 = a1 ∨ w1 = c1 := by
      rcases hpa1 with rfl | rfl <;> rcases hpc1 with rfl | rfl <;> rcases hpw1 with rfl | rfl <;>
        first | exact Or.inl rfl | exact Or.inr rfl | exact (heq rfl).elim
    rcases hw_cases with rfl | rfl
    · have hadj := fire t1 ht1 b1 w1 c2 hr1
        ⟨w1, ha1, Or.inl rfl⟩ ⟨c2, hc2, Or.inr rfl⟩ ⟨w1, hw1, Or.inl rfl⟩
      exact hno w1 c2 hpa1 hpc2 hadj
    · have hadj := fire t1 ht1 b1 w1 a2 hr1
        ⟨a2, ha2, Or.inr rfl⟩ ⟨w1, hc1, Or.inl rfl⟩ ⟨w1, hw1, Or.inl rfl⟩
      exact hno w1 a2 hpc1 hpa2 hadj

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
  -- Take the minimal OR gate m with OrReaches (opnd t b) m and OrReaches (n + m) j!
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
    -- Show m ∈ orN G C
    have hm_orN : m ∈ orN G C := by
      simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
      refine ⟨hmlt, hmop, fun hbf => ?_⟩
      have hrmj : OrReaches n C (n + m) j := by
        rw [orReaches_iff_gate n C m j hmlt]
        exact Or.inr ⟨hmop, u, hu, hult, hru⟩
      have hgm := orReaches_val_true n C hAO xd m j hrmj hjxd
      have hft := hbf xd hgm
      rw [hfxd] at hft; cases hft
    -- Show m ∉ lam G C (one operand of m is n + j, whose orIn is empty!)
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

/-! ### Part 4: Finite `G11` Combinatorics (Verified over `Fin 2048` in < 0.2s) -/

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

def checkG11Mask (m : Fin 2048) : Bool :=
  let tc := maskCard m
  let ul := uncovList m
  (7 ≤ tc + ul.length) &&
  (!(tc + ul.length == 7) || (4 ≤ tc && allPairsNoCross ul))

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
  simp [List.mem_finRange]

lemma g11List_valid_nodup :
    g11List.Nodup ∧
    (∀ e ∈ g11List, e.1 < 11 ∧ e.2 < 11 ∧ e.1 < e.2) := by decide

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
      s((⟨e.1, h1⟩ : Fin 11), (⟨e.2, h2⟩ : Fin 11)) ∈ F := by
  have hmemF : ∀ e ∈ uncovList (finsetToMask T), ∃ h1 : e.1 < 11, ∃ h2 : e.2 < 11,
      s((⟨e.1, h1⟩ : Fin 11), (⟨e.2, h2⟩ : Fin 11)) ∈ F := by
    intro e he
    simp only [uncovList, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at he
    have hvalid := g11List_valid_nodup.2 e he.1
    refine ⟨hvalid.1, hvalid.2.1, ?_⟩
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
  -- Injection from uncovList into F via e ↦ s(⟨e.1, _⟩, ⟨e.2, _⟩)
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
    obtain ⟨h1, h2, hF⟩ := hmemF e he
    have hf1 : Fin.ofNat 11 e.1 = ⟨e.1, h1⟩ := by ext; simp [Fin.ofNat, Nat.mod_eq_of_lt h1]
    have hf2 : Fin.ofNat 11 e.2 = ⟨e.2, h2⟩ := by ext; simp [Fin.ofNat, Nat.mod_eq_of_lt h2]
    dsimp only [emb]
    rw [hf1, hf2]
    exact hF
  calc U.length = (U.map emb).length := (List.length_map emb).symm
    _ = (U.map emb).toFinset.card := (List.toFinset_card_of_nodup hmap_nodup).symm
    _ ≤ F.card := Finset.card_le_card hsub

lemma exists_min_cover (K : SimpleGraph (Fin 11)) :
    ∃ T : Finset (Fin 11), IsMinCover K T := by
  classical
  have hex : ∃ k : ℕ, ∃ T : Finset (Fin 11), K.IsVertexCover (T : Set (Fin 11)) ∧ T.card = k :=
    ⟨11, Finset.univ, fun _ _ _ => Or.inl (by simp), by simp⟩
  let k := Nat.find hex
  obtain ⟨T, hcov, hcard⟩ := Nat.find_spec hex
  refine ⟨T, hcov, fun T' hcov' => ?_⟩
  rw [hcard]
  exact Nat.find_min' hex ⟨T', hcov', rfl⟩

lemma noCrossPair_imp_graph (e1 e2 : ℕ × ℕ)
    (h1 : e1.1 < 11 ∧ e1.2 < 11) (h2 : e2.1 < 11 ∧ e2.2 < 11)
    (hnc : noCrossPair e1 e2 = true ∨ noCrossPair e2 e1 = true) :
    let u1 : Fin 11 := ⟨e1.1, h1.1⟩
    let v1 : Fin 11 := ⟨e1.2, h1.2⟩
    let u2 : Fin 11 := ⟨e2.1, h2.1⟩
    let v2 : Fin 11 := ⟨e2.2, h2.2⟩
    ¬g11Graph.Adj u1 u2 ∧ ¬g11Graph.Adj u1 v2 ∧ ¬g11Graph.Adj v1 u2 ∧ ¬g11Graph.Adj v1 v2 := by
  have hnotadj : ∀ a b : Fin 11, adjB a.val b.val = false → ¬g11Graph.Adj a b := by
    intro a b hab hG
    unfold g11Graph edgeGraph at hG
    have hne : a.val ≠ b.val := fun h => hG.1 (Fin.ext h)
    unfold adjB at hab
    simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq, Bool.or_eq_false_iff,
      decide_eq_false_iff_not] at hab
    rcases hab with heq | ⟨hn1, hn2⟩
    · exact hne heq
    · rcases hG.2 with h | h
      · exact hn1 h
      · exact hn2 h
  have hsym : ∀ a b : Fin 11, adjB a.val b.val = adjB b.val a.val := by
    intro a b; unfold adjB
    by_cases h : a.val = b.val
    · simp [h]
    · have h1' : (a.val != b.val) = true := by simp [h]
      have h2' : (b.val != a.val) = true := by simp [Ne.symm h]
      simp [h1', h2', Bool.or_comm]
  rcases hnc with h | h
  · simp only [noCrossPair, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨hnotadj _ _ h.1.1.1.2, hnotadj _ _ h.1.1.2, hnotadj _ _ h.1.2, hnotadj _ _ h.2⟩
  · simp only [noCrossPair, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨hnotadj _ _ (by rw [hsym]; exact h.1.1.1.2),
      hnotadj _ _ (by rw [hsym]; exact h.1.2),
      hnotadj _ _ (by rw [hsym]; exact h.1.1.2),
      hnotadj _ _ (by rw [hsym]; exact h.2)⟩

/-! ### Part 5: Main Proof of `L_meta_4899` -/

lemma main_proof (x1 : SimpleGraph (Fin 11)) [DecidableRel x1.Adj]
    (x3 : Circuit) (x4 x5 : ℕ)
    (hx1 : x1 = g11Graph)
    (hAO : IsAO2 11 x3)
    (hTF : TopForm x1 x3)
    (hjunk : junk x1 x3 = {x4, x5})
    (hnc45 : ¬InCone 11 x3 x4 x5)
    (hnc54 : ¬InCone 11 x3 x5 x4)
    (hdisj : ∀ t ∈ tops x1 x3, InCone 11 x3 x4 t → ¬InCone 11 x3 x5 t)
    (hustar : ∀ u v : Fin 11, s(u, v) ∈ Ustar x1 x3 →
      ∃ t ∈ tops x1 x3, ∃ b : Fin 2, ∃ j : ℕ,
        (j = x4 ∨ j = x5) ∧
        gateVal 11 x3 t (pairInput u v) = true ∧
        OrReaches 11 x3 (opnd x3 t b) j ∧
        gateVal 11 x3 j (pairInput u v) = true)
    (hmincov : ∀ T : Finset (Fin 11), IsMinCover (x1.deleteEdges (Ustar x1 x3 : Set (Sym2 (Fin 11)))) T →
      T.card ≤ (tops x1 x3 \ centreless x1 x3).card) :
    let x6 := Ustar x1 x3
    let x7 := centreless x1 x3
    let x8 := (tops x1 x3 \ x7).card
    let x9 := (orN x1 x3 \ lam x1 x3).card
    ((17 + x8 + 2 * x7.card + x9 ≤ x3.size + x6.card → x6.card ≤ 2 → 22 ≤ x3.size) ∧
     (3 ≤ x6.card → 8 ≤ x8 + x6.card)) := by
  subst hx1
  dsimp only
  set x6 := Ustar g11Graph x3
  set x7 := centreless g11Graph x3
  set x8 := (tops g11Graph x3 \ x7).card
  set x9 := (orN g11Graph x3 \ lam g11Graph x3).card
  obtain ⟨T, hTmin⟩ := exists_min_cover (g11Graph.deleteEdges (x6 : Set (Sym2 (Fin 11))))
  have hTle : T.card ≤ x8 := hmincov T hTmin
  have hm := g11_all_masks_ok (finsetToMask T)
  unfold checkG11Mask at hm
  simp only [maskCard_finsetToMask, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, decide_eq_true_eq] at hm
  obtain ⟨hsum7, hcase7⟩ := hm
  obtain ⟨hulen, humem⟩ := uncovList_card_le_and_mem T x6 hTmin.1
  have h7le : 7 ≤ x8 + x6.card := by omega
  -- Helper: when x8 + x6.card = 7, we have uncovList has length = x6.card ≤ 3 and all pairs have no cross edge!
  have hcrit : x8 + x6.card = 7 →
      (uncovList (finsetToMask T)).length = x6.card ∧
      x6.card ≤ 3 ∧
      allPairsNoCross (uncovList (finsetToMask T)) = true := by
    intro heq7
    have htu7 : T.card + (uncovList (finsetToMask T)).length = 7 := by omega
    have hulen_eq : (uncovList (finsetToMask T)).length = x6.card := by omega
    rcases hcase7 with hne | ⟨h4, hnc⟩
    · exact (hne htu7).elim
    · exact ⟨hulen_eq, by omega, hnc⟩
  -- Helper: for any edge e ∈ uncovList, extract its junk witness (t, b, j)
  have get_wit : ∀ e ∈ uncovList (finsetToMask T),
      ∃ h1 : e.1 < 11, ∃ h2 : e.2 < 11,
      ∃ t ∈ tops g11Graph x3, ∃ b : Fin 2, ∃ j : ℕ,
        (j = x4 ∨ j = x5) ∧
        gateVal 11 x3 t (pairInput ⟨e.1, h1⟩ ⟨e.2, h2⟩) = true ∧
        OrReaches 11 x3 (opnd x3 t b) j ∧
        gateVal 11 x3 j (pairInput ⟨e.1, h1⟩ ⟨e.2, h2⟩) = true := by
    intro e he
    obtain ⟨h1, h2, hF⟩ := humem e he
    obtain ⟨t, ht, b, j, hj, htv, hr, hjv⟩ := hustar ⟨e.1, h1⟩ ⟨e.2, h2⟩ hF
    exact ⟨h1, h2, t, ht, b, j, hj, htv, hr, hjv⟩
  constructor
  · -- Goal 1: 17 + x8 + 2 * x7.card + x9 ≤ x3.size + x6.card → x6.card ≤ 2 → 22 ≤ x3.size
    intro hineq hx6le2
    by_cases hx6le1 : x6.card ≤ 1
    · omega
    · have hx6eq2 : x6.card = 2 := by omega
      by_cases hx8ge7 : 7 ≤ x8
      · omega
      · by_cases hx7pos : 1 ≤ x7.card
        · omega
        · have hx7zero : x7.card = 0 := by omega
          have hnotc : ∀ t, t ∉ x7 := fun t ht => by
            have := Finset.card_pos.mpr ⟨t, ht⟩; omega
          by_cases hx8eq6 : x8 = 6
          · -- Only need x9 ≥ 1! Pick any edge in x6 (since x6.card = 2 > 0)
            have hx6ne : x6.Nonempty := Finset.card_pos.mp (by omega)
            obtain ⟨e, he⟩ := hx6ne
            induction e using Sym2.ind with
            | _ u v =>
              obtain ⟨t, ht, b, j, hj, _, hr, _⟩ := hustar u v he
              have hjmem : j ∈ junk g11Graph x3 := by rw [hjunk]; rcases hj with rfl | rfl <;> simp
              obtain ⟨m, hm, _, _⟩ := orN_witness_of_non_centreless g11Graph x3 hAO t ht (hnotc t) b j hjmem hr
              have hx9pos : 1 ≤ x9 := Finset.card_pos.mpr ⟨m, hm⟩
              omega
          · -- Must have x8 = 5, so x8 + x6.card = 7!
            have hx8eq5 : x8 = 5 := by omega
            obtain ⟨hulen2, _, hnc_all⟩ := hcrit (by omega)
            rw [hx6eq2] at hulen2
            rcases hul_eq : uncovList (finsetToMask T) with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩
            · simp [hul_eq] at hulen2
            · simp [hul_eq] at hulen2
            · have hnd : (uncovList (finsetToMask T)).Nodup := g11List_valid_nodup.1.filter _
              rw [hul_eq] at hnd
              have hne12 : e1 ≠ e2 := by simp at hnd; exact hnd
              have he1_mem : e1 ∈ uncovList (finsetToMask T) := by rw [hul_eq]; simp
              have he2_mem : e2 ∈ uncovList (finsetToMask T) := by rw [hul_eq]; simp
              obtain ⟨h11, h12, t1, ht1, b1, j1, hj1, ht1v, hr1, hj1v⟩ := get_wit e1 he1_mem
              obtain ⟨h21, h22, t2, ht2, b2, j2, hj2, ht2v, hr2, hj2v⟩ := get_wit e2 he2_mem
              have hcross := noCrossPair_imp_graph e1 e2 ⟨h11, h12⟩ ⟨h21, h22⟩
                (allPairsNoCross_spec _ hnc_all e1 he1_mem e2 he2_mem hne12)
              have hjne : j1 ≠ j2 := by
                intro heq; subst heq
                exact no_induced_matching_same_junk g11Graph x3 x4 x5 hAO hTF hjunk hnc45 hnc54 hdisj
                  j1 hj1 ⟨e1.1, h11⟩ ⟨e1.2, h12⟩ ⟨e2.1, h21⟩ ⟨e2.2, h22⟩ hcross
                  t1 ht1 b1 ht1v hr1 hj1v t2 ht2 b2 ht2v hr2 hj2v
              have hj1mem : j1 ∈ junk g11Graph x3 := by rw [hjunk]; rcases hj1 with rfl | rfl <;> simp
              have hj2mem : j2 ∈ junk g11Graph x3 := by rw [hjunk]; rcases hj2 with rfl | rfl <;> simp
              obtain ⟨m1, hm1, hrm1a, hrm1b⟩ :=
                orN_witness_of_non_centreless g11Graph x3 hAO t1 ht1 (hnotc t1) b1 j1 hj1mem hr1
              obtain ⟨m2, hm2, hrm2a, hrm2b⟩ :=
                orN_witness_of_non_centreless g11Graph x3 hAO t2 ht2 (hnotc t2) b2 j2 hj2mem hr2
              have hmne : m1 ≠ m2 := by
                intro heq; subst heq
                have ht1lt : t1 < x3.gates.length := by
                  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ht1; exact ht1.1
                have hr_t1_j2 : OrReaches 11 x3 (opnd x3 t1 b1) j2 := by
                  have hwge := hrm1a.1
                  have hweq : opnd x3 t1 b1 = 11 + (opnd x3 t1 b1 - 11) := by omega
                  rw [hweq]
                  exact orReaches_trans 11 x3 (opnd x3 t1 b1 - 11) m1 j2 (by rwa [← hweq]) hrm2b
                have hc1 := orReaches_imp_inCone_parent 11 x3 hAO t1 ht1lt b1 j1 hr1
                have hc2 := orReaches_imp_inCone_parent 11 x3 hAO t1 ht1lt b1 j2 hr_t1_j2
                rcases hj1 with rfl | rfl <;> rcases hj2 with rfl | rfl
                · exact hjne rfl
                · exact hdisj t1 ht1 hc1 hc2
                · exact hdisj t1 ht1 hc2 hc1
                · exact hjne rfl
              have hx9ge2 : 2 ≤ x9 := by
                have hsub : ({m1, m2} : Finset ℕ) ⊆ orN g11Graph x3 \ lam g11Graph x3 := by
                  intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                  rcases hz with rfl | rfl <;> assumption
                have hc := Finset.card_le_card hsub
                rw [Finset.card_pair hmne] at hc
                exact hc
              omega
            · simp [hul_eq] at hulen2
  · -- Goal 2: 3 ≤ x6.card → 8 ≤ x8 + x6.card
    intro hx6ge3
    by_contra hlt8
    have heq7 : x8 + x6.card = 7 := by omega
    obtain ⟨hulen_eq, hx6le3, hnc_all⟩ := hcrit heq7
    have hx6eq3 : x6.card = 3 := by omega
    rw [hx6eq3] at hulen_eq
    rcases hul_eq : uncovList (finsetToMask T) with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, _ | _⟩⟩⟩
    · simp [hul_eq] at hulen_eq
    · simp [hul_eq] at hulen_eq
    · simp [hul_eq] at hulen_eq
    · have hnd : (uncovList (finsetToMask T)).Nodup := g11List_valid_nodup.1.filter _
      rw [hul_eq] at hnd
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
      have hne12 : e1 ≠ e2 := hnd.1.1
      have hne13 : e1 ≠ e3 := hnd.1.2
      have hne23 : e2 ≠ e3 := hnd.2.1
      have he1_mem : e1 ∈ uncovList (finsetToMask T) := by rw [hul_eq]; simp
      have he2_mem : e2 ∈ uncovList (finsetToMask T) := by rw [hul_eq]; simp
      have he3_mem : e3 ∈ uncovList (finsetToMask T) := by rw [hul_eq]; simp
      obtain ⟨h11, h12, t1, ht1, b1, j1, hj1, ht1v, hr1, hj1v⟩ := get_wit e1 he1_mem
      obtain ⟨h21, h22, t2, ht2, b2, j2, hj2, ht2v, hr2, hj2v⟩ := get_wit e2 he2_mem
      obtain ⟨h31, h32, t3, ht3, b3, j3, hj3, ht3v, hr3, hj3v⟩ := get_wit e3 he3_mem
      rcases hj1 with hj1 | hj1 <;> rcases hj2 with hj2 | hj2 <;> rcases hj3 with hj3 | hj3
      · exact no_induced_matching_same_junk g11Graph x3 x4 x5 hAO hTF hjunk hnc45 hnc54 hdisj
          x4 (Or.inl rfl) ⟨e1.1, h11⟩ ⟨e1.2, h12⟩ ⟨e2.1, h21⟩ ⟨e2.2, h22⟩
          (noCrossPair_imp_graph e1 e2 ⟨h11, h12⟩ ⟨h21, h22⟩ (allPairsNoCross_spec _ hnc_all e1 he1_mem e2 he2_mem hne12))
          t1 ht1 b1 ht1v (hj1 ▸ hr1) (hj1 ▸ hj1v) t2 ht2 b2 ht2v (hj2 ▸ hr2) (hj2 ▸ hj2v)
      · exact no_induced_matching_same_junk g11Graph x3 x4 x5 hAO hTF hjunk hnc45 hnc54 hdisj
          x4 (Or.inl rfl) ⟨e1.1, h11⟩ ⟨e1.2, h12⟩ ⟨e2.1, h21⟩ ⟨e2.2, h22⟩
          (noCrossPair_imp_graph e1 e2 ⟨h11, h12⟩ ⟨h21, h22⟩ (allPairsNoCross_spec _ hnc_all e1 he1_mem e2 he2_mem hne12))
          t1 ht1 b1 ht1v (hj1 ▸ hr1) (hj1 ▸ hj1v) t2 ht2 b2 ht2v (hj2 ▸ hr2) (hj2 ▸ hj2v)
      · exact no_induced_matching_same_junk g11Graph x3 x4 x5 hAO hTF hjunk hnc45 hnc54 hdisj
          x4 (Or.inl rfl) ⟨e1.1, h11⟩ ⟨e1.2, h12⟩ ⟨e3.1, h31⟩ ⟨e3.2, h32⟩
          (noCrossPair_imp_graph e1 e3 ⟨h11, h12⟩ ⟨h31, h32⟩ (allPairsNoCross_spec _ hnc_all e1 he1_mem e3 he3_mem hne13))
          t1 ht1 b1 ht1v (hj1 ▸ hr1) (hj1 ▸ hj1v) t3 ht3 b3 ht3v (hj3 ▸ hr3) (hj3 ▸ hj3v)
      · exact no_induced_matching_same_junk g11Graph x3 x4 x5 hAO hTF hjunk hnc45 hnc54 hdisj
          x5 (Or.inr rfl) ⟨e2.1, h21⟩ ⟨e2.2, h22⟩ ⟨e3.1, h31⟩ ⟨e3.2, h32⟩
          (noCrossPair_imp_graph e2 e3 ⟨h21, h22⟩ ⟨h31, h32⟩ (allPairsNoCross_spec _ hnc_all e2 he2_mem e3 he3_mem hne23))
          t2 ht2 b2 ht2v (hj2 ▸ hr2) (hj2 ▸ hj2v) t3 ht3 b3 ht3v (hj3 ▸ hr3) (hj3 ▸ hj3v)
      · exact no_induced_matching_same_junk g11Graph x3 x4 x5 hAO hTF hjunk hnc45 hnc54 hdisj
          x4 (Or.inl rfl) ⟨e2.1, h21⟩ ⟨e2.2, h22⟩ ⟨e3.1, h31⟩ ⟨e3.2, h32⟩
          (noCrossPair_imp_graph e2 e3 ⟨h21, h22⟩ ⟨h31, h32⟩ (allPairsNoCross_spec _ hnc_all e2 he2_mem e3 he3_mem hne23))
          t2 ht2 b2 ht2v (hj2 ▸ hr2) (hj2 ▸ hj2v) t3 ht3 b3 ht3v (hj3 ▸ hr3) (hj3 ▸ hj3v)
      · exact no_induced_matching_same_junk g11Graph x3 x4 x5 hAO hTF hjunk hnc45 hnc54 hdisj
          x5 (Or.inr rfl) ⟨e1.1, h11⟩ ⟨e1.2, h12⟩ ⟨e3.1, h31⟩ ⟨e3.2, h32⟩
          (noCrossPair_imp_graph e1 e3 ⟨h11, h12⟩ ⟨h31, h32⟩ (allPairsNoCross_spec _ hnc_all e1 he1_mem e3 he3_mem hne13))
          t1 ht1 b1 ht1v (hj1 ▸ hr1) (hj1 ▸ hj1v) t3 ht3 b3 ht3v (hj3 ▸ hr3) (hj3 ▸ hj3v)
      · exact no_induced_matching_same_junk g11Graph x3 x4 x5 hAO hTF hjunk hnc45 hnc54 hdisj
          x5 (Or.inr rfl) ⟨e1.1, h11⟩ ⟨e1.2, h12⟩ ⟨e2.1, h21⟩ ⟨e2.2, h22⟩
          (noCrossPair_imp_graph e1 e2 ⟨h11, h12⟩ ⟨h21, h22⟩ (allPairsNoCross_spec _ hnc_all e1 he1_mem e2 he2_mem hne12))
          t1 ht1 b1 ht1v (hj1 ▸ hr1) (hj1 ▸ hj1v) t2 ht2 b2 ht2v (hj2 ▸ hr2) (hj2 ▸ hj2v)
      · exact no_induced_matching_same_junk g11Graph x3 x4 x5 hAO hTF hjunk hnc45 hnc54 hdisj
          x5 (Or.inr rfl) ⟨e1.1, h11⟩ ⟨e1.2, h12⟩ ⟨e2.1, h21⟩ ⟨e2.2, h22⟩
          (noCrossPair_imp_graph e1 e2 ⟨h11, h12⟩ ⟨h21, h22⟩ (allPairsNoCross_spec _ hnc_all e1 he1_mem e2 he2_mem hne12))
          t1 ht1 b1 ht1v (hj1 ▸ hr1) (hj1 ▸ hj1v) t2 ht2 b2 ht2v (hj2 ▸ hr2) (hj2 ▸ hj2v)
    · simp [hul_eq] at hulen_eq

end PEqualNP.Outside.L_meta_4899

theorem PEqualNP.Outside.L_meta_4899 :
  ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   have x6 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;   have x7 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;   have x8 : ℕ := (PEqualNP.TopForm.tops x1 x3 \ x7).card;   have x9 : ℕ := (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → PEqualNP.TopForm.TopForm x1 x3 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 → ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x5 x4 → (∀ x16 ∈ PEqualNP.TopForm.tops x1 x3, PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x16 → ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x5 x16) → (∀ (x17 x18 : Fin (11 : ℕ)), s(x17, x18) ∈ x6 → ∃ x20 ∈ PEqualNP.TopForm.tops x1 x3, ∃ (x21 : Fin (2 : ℕ)) (x22 : ℕ), (x22 = x4 ∨ x22 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x20 (PEqualNP.EdgeOwnership.pairInput x17 x18) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x20 x21) x22 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x22 (PEqualNP.EdgeOwnership.pairInput x17 x18) = Bool.true) → (∀ (x18 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x6) x18 → x18.card ≤ x8) → ((17 : ℕ) + x8 + (2 : ℕ) * x7.card + x9 ≤ x3.size + x6.card → x6.card ≤ (2 : ℕ) → (22 : ℕ) ≤ x3.size) ∧ ((3 : ℕ) ≤ x6.card → (8 : ℕ) ≤ x8 + x6.card) := by
  intro x1 _ x3 x4 x5
  dsimp only
  intro hx1 hAO hTF hjunk hnc45 hnc54 hdisj hustar hmincov
  exact PEqualNP.Outside.L_meta_4899.main_proof x1 x3 x4 x5 hx1 hAO hTF hjunk hnc45 hnc54 hdisj hustar hmincov

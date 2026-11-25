import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.StructuralPrefix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount

private lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

private lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

private lemma inputs_eq_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ hmem
  unfold opnd
  rcases h : (gateAt C j).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · simp
  · simp [h] at hlen

private lemma opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [inputs_eq_pair hAO hj]
  fin_cases b <;> simp

private lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem_inputs hAO hj b)

private lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  unfold Circuit.wires
  rw [foldl_append_length, List.length_ofFn]

private lemma wireVal_input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C i.val x = x i := by
  unfold wireVal Circuit.wires
  have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
  rw [foldl_append_getD_lt _ C.gates (List.ofFn x) false i.val hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

private lemma wireVal_ge {n : ℕ} (C : Circuit) {w : ℕ} (hw : n + C.gates.length ≤ w)
    (x : Fin n → Bool) :
    wireVal n C w x = false := by
  unfold wireVal
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [wires_length]; exact hw

private lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => wireVal n C w x) := by
  unfold wireVal Circuit.wires
  have hgate := foldl_append_getD_gate
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn x) false j hj ⟨GateOp.or, []⟩
  rw [List.length_ofFn] at hgate
  rw [hgate]
  change (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false) =
    (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false)
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < (List.ofFn x).length + j := by
    rw [List.length_ofFn]
    exact hAO.2.1 j hj i hi
  exact foldl_append_take_getD _ C.gates (List.ofFn x) false j i (Nat.le_of_lt hj) hilt

private lemma wireVal_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

private lemma wireVal_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

private lemma circuitFun_eq_wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = wireVal n C C.output x := rfl


private lemma gate_op {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  apply hAO.1
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma wire_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ a, x a = true → y a = true) :
    ∀ w, wireVal n C w x = true → wireVal n C w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n
    · simpa only [wireVal_input C ⟨w, hin⟩] using hxy ⟨w, hin⟩
    by_cases hout : n + C.gates.length ≤ w
    · simp [wireVal_ge C hout]
    let j := w - n
    have hj : j < C.gates.length := by dsimp [j]; omega
    have hw : w = n + j := by dsimp [j]; omega
    have h0 := opnd_lt hAO hj (0 : Fin 2)
    have h1 := opnd_lt hAO hj (1 : Fin 2)
    have i0 := ih (opnd C j 0) (by omega)
    have i1 := ih (opnd C j 1) (by omega)
    rcases gate_op hAO hj with hand | hor
    · rw [hw, wireVal_and hAO hj hand, wireVal_and hAO hj hand]
      simp only [Bool.and_eq_true]
      exact fun h => ⟨i0 h.1, i1 h.2⟩
    · rw [hw, wireVal_or hAO hj hor, wireVal_or hAO hj hor]
      simp only [Bool.or_eq_true]
      exact fun h => h.imp i0 i1

lemma prefix_support {n k : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C)
    (hclean : ∀ j < k, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false) :
    ∀ w < n + k, ∀ x : Fin n → Bool, wireVal n C w x = true →
      graphFun G ∅ x = true ∨ ∃ a : Fin n, x a = true ∧
        wireVal n C w (unitInput a) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwk x hx
    by_cases hin : w < n
    · right
      refine ⟨⟨w, hin⟩, ?_, ?_⟩
      · simpa only [wireVal_input C ⟨w, hin⟩] using hx
      · rw [wireVal_input C ⟨w, hin⟩]
        simp [unitInput]
    by_cases hout : n + C.gates.length ≤ w
    · rw [wireVal_ge C hout] at hx
      contradiction
    let j := w - n
    have hj : j < C.gates.length := by dsimp [j]; omega
    have hjk : j < k := by dsimp [j]; omega
    have hw : w = n + j := by dsimp [j]; omega
    have h0 := opnd_lt hAO hj (0 : Fin 2)
    have h1 := opnd_lt hAO hj (1 : Fin 2)
    have i0 := ih (opnd C j 0) (by omega) (by omega) x
    have i1 := ih (opnd C j 1) (by omega) (by omega) x
    rcases gate_op hAO hj with hand | hor
    · rw [hw, wireVal_and hAO hj hand, Bool.and_eq_true] at hx
      rcases i0 hx.1 with hf | ⟨a, hxa, ha⟩
      · exact Or.inl hf
      rcases i1 hx.2 with hf | ⟨b, hxb, hb⟩
      · exact Or.inl hf
      have ha' : wireVal n C (opnd C j 0) (pairInput a b) = true := by
        apply wire_mono hAO (unitInput a) (pairInput a b) _ _ ha
        intro v hv
        simp only [unitInput, decide_eq_true_eq] at hv
        subst v
        simp [pairInput]
      have hb' : wireVal n C (opnd C j 1) (pairInput a b) = true := by
        apply wire_mono hAO (unitInput b) (pairInput a b) _ _ hb
        intro v hv
        simp only [unitInput, decide_eq_true_eq] at hv
        subst v
        simp [pairInput]
      have hg : gateVal n C j (pairInput a b) = true := by
        change wireVal n C (n + j) (pairInput a b) = true
        rw [wireVal_and hAO hj hand, ha', hb']
        rfl
      have hab : G.Adj a b := by
        by_contra hab
        have hf := hclean j hjk hj hand a b hab
        rw [hf] at hg
        contradiction
      left
      simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨a, b, hab, hxa, hxb⟩
    · rw [hw, wireVal_or hAO hj hor, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · rcases i0 hx with hf | ⟨a, hxa, ha⟩
        · exact Or.inl hf
        · right
          refine ⟨a, hxa, ?_⟩
          rw [hw, wireVal_or hAO hj hor, ha]
          rfl
      · rcases i1 hx with hf | ⟨a, hxa, ha⟩
        · exact Or.inl hf
        · right
          refine ⟨a, hxa, ?_⟩
          rw [hw, wireVal_or hAO hj hor, ha, Bool.or_true]

lemma pair_clean_prefix_below {n k : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C)
    (hclean : ∀ j < k, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false) :
    ∀ j < k, j < C.gates.length → (gateAt C j).op = GateOp.and → BelowF G C j := by
  intro j hjk hj hand x hx
  have h := prefix_support G hAO hclean (n + j) (by omega) x hx
  rcases h with hf | ⟨a, _, ha⟩
  · exact hf
  · have hf := hclean j hjk hj hand a a (G.loopless.irrefl a)
    have he : pairInput a a = unitInput a := by
      funext v
      simp [pairInput, unitInput]
    rw [he] at hf
    change wireVal n C (n + j) (unitInput a) = false at hf
    rw [hf] at ha
    contradiction

end PEqualNP.Outside.L_meta_4675.StructuralPrefix

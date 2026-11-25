import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.Redirect

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
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

lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
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

lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

lemma inputs_eq_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
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

lemma opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [inputs_eq_pair hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem_inputs hAO hj b)

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  unfold Circuit.wires
  rw [foldl_append_length, List.length_ofFn]

lemma wireVal_input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C i.val x = x i := by
  unfold wireVal Circuit.wires
  have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
  rw [foldl_append_getD_lt _ C.gates (List.ofFn x) false i.val hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

lemma wireVal_ge {n : ℕ} (C : Circuit) {w : ℕ} (hw : n + C.gates.length ≤ w)
    (x : Fin n → Bool) :
    wireVal n C w x = false := by
  unfold wireVal
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [wires_length]; exact hw

lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
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

lemma wireVal_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

lemma wireVal_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

lemma circuitFun_eq_wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = wireVal n C C.output x := rfl

lemma orSets_length (n : ℕ) (C : Circuit) :
    (orSets n C).length = C.gates.length := by
  unfold orSets orStep
  rw [foldl_append_length]
  simp

lemma orSets_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (orSets n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [orSets_length]; exact hj

lemma orSets_getD_lt_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    (orSets n C).getD j [] =
      j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = _
  rw [hprelen, ite_eq_left_of_eq_true _ _ (eq_true hop)]
  congr 1
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

lemma orSets_getD_lt_not_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op ≠ GateOp.or) :
    (orSets n C).getD j [] = [j] := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = [j]
  rw [hprelen, ite_eq_right_of_eq_false _ _ (eq_false hop)]

lemma orReaches_iff {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (w g : ℕ) :
    OrReaches n C w g ↔
      ∃ j < C.gates.length, w = n + j ∧
        (g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ b : Fin 2, OrReaches n C (opnd C j b) g)) := by
  constructor
  · rintro ⟨hnw, hmem⟩
    have hlt : w - n < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [orSets_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨w - n, hlt, by omega, ?_⟩
    by_cases hop : (gateAt C (w - n)).op = GateOp.or
    · rw [orSets_getD_lt_or n C hlt hop, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inl rfl
      · right
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨u, hu, hgu⟩
        rw [List.mem_filter, decide_eq_true_eq] at hu
        rw [inputs_eq_pair hAO hlt] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu.1 with rfl | rfl
        · exact ⟨hop, 0, hu.2.1, hgu⟩
        · exact ⟨hop, 1, hu.2.1, hgu⟩
    · rw [orSets_getD_lt_not_or n C hlt hop, List.mem_singleton] at hmem
      exact Or.inl hmem
  · rintro ⟨j, hj, rfl, hcase⟩
    refine ⟨Nat.le_add_right n j, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rcases hcase with rfl | ⟨hop, b, hnu, hgu⟩
    · by_cases hop : (gateAt C g).op = GateOp.or
      · rw [orSets_getD_lt_or n C hj hop]; exact List.mem_cons_self
      · rw [orSets_getD_lt_not_or n C hj hop]; exact List.mem_singleton_self g
    · rw [orSets_getD_lt_or n C hj hop, List.mem_cons]
      right
      rw [List.mem_flatMap]
      refine ⟨opnd C j b, ?_, hgu⟩
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨opnd_mem_inputs hAO hj b, hnu, opnd_lt hAO hj b⟩

lemma orReaches_self {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff hAO (n + j) j).mpr ⟨j, hj, rfl, Or.inl rfl⟩

lemma orReaches_le {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g → n + g ≤ w ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨_, b, hb⟩⟩
    · exact ⟨le_rfl, hj⟩
    · have hlt : opnd C j b < n + j := opnd_lt hAO hj b
      have hrec := ih _ hlt g hb
      exact ⟨by omega, hrec.2⟩

lemma orReaches_trans {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g h : ℕ, OrReaches n C w g → OrReaches n C (n + g) h → OrReaches n C w h := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g h hwg hgh
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact hgh
    · have hrec := ih _ (opnd_lt hAO hj b) g h hb hgh
      exact (orReaches_iff hAO (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, b, hrec⟩⟩

lemma orReaches_parent {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g →
      w = n + g ∨
        ∃ h < C.gates.length, (gateAt C h).op = GateOp.or ∧ OrReaches n C w h ∧
          ∃ b : Fin 2, opnd C h b = n + g := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact Or.inl rfl
    · right
      rcases ih _ (opnd_lt hAO hj b) g hb with hEq | ⟨h, hh, hhop, hreach, b', hb'⟩
      · exact ⟨j, hj, hop, orReaches_self hAO hj, b, hEq⟩
      · exact ⟨h, hh, hhop, (orReaches_iff hAO (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, b, hreach⟩⟩, b', hb'⟩

lemma wireVal_of_orReaches {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g →
      ∀ x : Fin n → Bool, wireVal n C (n + g) x = true → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg x hxg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact hxg
    · have hsub := ih _ (opnd_lt hAO hj b) g hb x hxg
      rw [wireVal_or hAO hj hop, Bool.or_eq_true]
      fin_cases b
      · exact Or.inl hsub
      · exact Or.inr hsub

lemma orIn_input {n : ℕ} {C : Circuit} (i : Fin n) :
    orIn n C i.val = {i} := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (hu | ⟨k, _, ⟨hni, _⟩, _, _⟩)
    · exact Fin.ext hu
    · omega
  · rintro rfl
    exact Or.inl rfl

lemma orIn_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {w : ℕ}
    (hw : n + C.gates.length ≤ w) :
    orIn n C w = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hwk, _, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hwk
    rcases hwk with ⟨j, hj, rfl, _⟩
    omega

lemma orIn_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hjk, hkop, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hjk
    rcases hjk with ⟨j', _, heq, hcase⟩
    have hjj' : j' = j := by omega
    subst hjj'
    rcases hcase with rfl | ⟨hor, _⟩
    · rw [hop] at hkop; cases hkop
    · rw [hop] at hor; cases hor

lemma orIn_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext u
  unfold orIn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hjk, hkop, huk⟩)
    · omega
    · rw [orReaches_iff hAO] at hjk
      rcases hjk with ⟨j', _, heq, hcase⟩
      have hjj' : j' = j := by omega
      subst hjj'
      rcases hcase with rfl | ⟨_, b, hb⟩
      · rw [inputs_eq_pair hAO hj] at huk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
        rcases huk with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl h1)
      · fin_cases b
        · exact Or.inl (Or.inr ⟨k, hk, hb, hkop, huk⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hb, hkop, huk⟩)
  · rintro ((h0 | ⟨k, hk, h0k, hkop, huk⟩) | (h1 | ⟨k, hk, h1k, hkop, huk⟩))
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h0]
      exact opnd_mem_inputs hAO hj 0
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 0, h0k⟩⟩
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h1]
      exact opnd_mem_inputs hAO hj 1
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 1, h1k⟩⟩

lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {w g : ℕ} (hwg : OrReaches n C w g) :
    orIn n C (n + g) ⊆ orIn n C w := by
  intro u hu
  unfold orIn at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with hEq | ⟨k, hk, hgk, hkop, huk⟩
  · omega
  · exact Or.inr ⟨k, hk, orReaches_trans hAO w g k hwg hgk, hkop, huk⟩

lemma wireVal_true_of_mem_orIn {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {i : Fin n} {x : Fin n → Bool} (hxi : x i = true) :
    ∀ w : ℕ, i ∈ orIn n C w → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hi
    by_cases hlt : w < n
    · have heq : orIn n C w = {⟨w, hlt⟩} := orIn_input ⟨w, hlt⟩
      rw [heq, Finset.mem_singleton] at hi
      subst hi
      exact (wireVal_input C ⟨w, hlt⟩ x).trans hxi
    · by_cases hge : n + C.gates.length ≤ w
      · rw [orIn_ge hAO hge] at hi
        simp at hi
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hi ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [orIn_and hAO hj hop] at hi
          simp at hi
        · rw [orIn_or hAO hj hop, Finset.mem_union] at hi
          rw [wireVal_or hAO hj hop, Bool.or_eq_true]
          rcases hi with h0 | h1
          · exact Or.inl (ih _ (hw ▸ opnd_lt hAO hj 0) h0)
          · exact Or.inr (ih _ (hw ▸ opnd_lt hAO hj 1) h1)

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C D : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt D k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  simp [tau, hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho
  split_ifs <;> omega

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho
  split_ifs <;> omega

lemma rho_surj (r j m : ℕ) (hr : r < m) (hj : j < m) (hne : j ≠ r) :
    ∃ k, k < m - 1 ∧ rho r k = j := by
  by_cases hlt : j < r
  · exact ⟨j, by omega, by simp [rho, hlt]⟩
  · refine ⟨j - 1, by omega, ?_⟩
    unfold rho
    split_ifs <;> omega

lemma redirect_opnd (n : ℕ) (C D : Circuit) (r b k : ℕ)
    (hb : b < n + r) (hk : k < C.gates.length - 1)
    (hrd : IsRedirect n C D r b) (e : Fin 2) :
    opnd D k e = tau n r b (opnd C (rho r k) e) := by
  unfold opnd
  rw [hrd k hk]
  have hz : tau n r b 0 = 0 := tau_low n r b 0 (by omega)
  simpa only [hz] using List.getD_map (gateAt C (rho r k)).inputs 0 (n := e.val) (tau n r b)

lemma orIn_redirect_subset (n : ℕ) (C D : Circuit) (r b : ℕ)
    (hC : IsAO2 n C) (hD : IsAO2 n D)
    (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ D.gates.length)
    (hrd : IsRedirect n C D r b)
    (hsub : orIn n C b ⊆ orIn n C (n + r)) :
    ∀ w, w < n + C.gates.length → orIn n D (tau n r b w) ⊆ orIn n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hinput : w < n
    · rw [tau_low n r b w (by omega)]
      have h1 := orIn_input (C := C) (⟨w, hinput⟩ : Fin n)
      have h2 := orIn_input (C := D) (⟨w, hinput⟩ : Fin n)
      dsimp only at h1 h2
      rw [h1, h2]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases heq : j = r
      · subst j
        have hb' := ih b hb (by omega)
        rw [tau_low n r b b hb] at hb'
        have ht : tau n r b (n + r) = b := by simp [tau]
        rw [ht]
        exact hb'.trans hsub
      · obtain ⟨k, hk, hkj⟩ := rho_surj r j C.gates.length hr hj heq
        have hkD : k < D.gates.length := lt_of_lt_of_le hk hlen
        have ht : tau n r b (n + j) = n + k := by
          rw [← hkj]
          exact tau_rho n r b k
        have hg := hrd k hk
        rw [hkj] at hg
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
            Option.getD_some]
          exact List.getElem_mem hj
        have hopnd : ∀ e : Fin 2, opnd D k e = tau n r b (opnd C j e) := by
          intro e
          rw [← hkj]
          exact redirect_opnd n C D r b k hb hk hrd e
        rcases hC.1 _ hmem with hop | hop
        · have hopD : (gateAt D k).op = GateOp.and := by rw [hg]; exact hop
          rw [ht, orIn_and hD hkD hopD, orIn_and hC hj hop]
        · have hopD : (gateAt D k).op = GateOp.or := by rw [hg]; exact hop
          rw [ht, orIn_or hD hkD hopD, orIn_or hC hj hop, hopnd 0, hopnd 1]
          apply Finset.union_subset_union
          · exact ih _ (opnd_lt hC hj 0) (by have := opnd_lt hC hj 0; omega)
          · exact ih _ (opnd_lt hC hj 1) (by have := opnd_lt hC hj 1; omega)

lemma below_singleton_free_orIn_empty (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (F : (Fin n → Bool) → Bool)
    (hF : ∀ i : Fin n, F (fun j => decide (j = i)) = false)
    (w : ℕ) (hw : ∀ x, wireVal n C w x = true → F x = true) :
    orIn n C w = ∅ := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    have hwi := wireVal_true_of_mem_orIn hC (i := i)
      (x := fun j => decide (j = i)) (by simp) w hi
    have hfi := hw _ hwi
    rw [hF i] at hfi
    cases hfi
  · simp

lemma tCount_redirect_zero (n : ℕ) (C D : Circuit) (r b : ℕ) (s : ℕ → Bool)
    (hC : IsAO2 n C) (hD : IsAO2 n D)
    (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ D.gates.length)
    (hrd : IsRedirect n C D r b)
    (hsub : orIn n C b ⊆ orIn n C (n + r))
    (hnew : ∀ g < D.gates.length, C.gates.length - 1 ≤ g → orIn n D (n + g) = ∅)
    (hz : PEqualNP.TwoColour.tCount n C s = 0) : PEqualNP.TwoColour.tCount n D s = 0 := by
  unfold PEqualNP.TwoColour.tCount PEqualNP.TwoColour.twoColour at *
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hz ⊢
  intro g _ hg
  rcases hg with ⟨hgD, hopD, ⟨a, ha, hsa⟩, ⟨b', hb', hsb⟩⟩
  by_cases hsmall : g < C.gates.length - 1
  · have hj := rho_lt r g C.gates.length hr hsmall
    have hgate := hrd g hsmall
    have hop : (gateAt C (rho r g)).op = GateOp.or := by
      rw [hgate] at hopD
      exact hopD
    have hs := orIn_redirect_subset n C D r b hC hD hr hb hlen hrd hsub
      (n + rho r g) (by omega)
    rw [tau_rho] at hs
    exact hz (Finset.mem_range.mpr hj)
      ⟨hj, hop, ⟨a, hs ha, hsa⟩, ⟨b', hs hb', hsb⟩⟩
  · rw [hnew g hgD (by omega)] at ha
    simp at ha

end PEqualNP.Outside.L_meta_4675.Redirect

namespace PEqualNP.Outside.L_meta_4675.Lift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ite_eq_left ((hC j hj).2 i hi)]

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

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [ite_eq_left (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [ite_eq_left hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [ite_eq_left (by omega)]
            · unfold rho; rw [ite_eq_left hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
            · unfold rho; rw [ite_eq_right (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [ite_eq_left hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [ite_eq_left hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [ite_eq_right (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma mem_gateAt (C : Circuit) (g : Gate) (hg : g ∈ C.gates) :
    ∃ j, j < C.gates.length ∧ gateAt C j = g := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  exact ⟨j, hj, by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]⟩


lemma ao2_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro j hj
  have hm := gateAt_mem C j hj
  exact ⟨h1 _ hm, List.length_eq_two.mp (h3 _ hm), h2 j hj⟩

lemma ao2_to (n : ℕ) (C : Circuit) (h : AO2 n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    exact (h j hj).1
  · intro j hj
    exact (h j hj).2.2
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    obtain ⟨a, b, hab⟩ := (h j hj).2.1
    rw [hab]
    rfl


lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [ite_eq_left hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [ite_eq_right (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

lemma orIn_below_empty (n : ℕ) (C : Circuit) (hC : AO2 n C)
    (hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false)
    (w : ℕ) (hw : ∀ x, wv n C x w = true → wv n C x C.output = true) :
    PEqualNP.TopForm.orIn n C w = ∅ := by
  exact PEqualNP.Outside.L_meta_4675.Redirect.below_singleton_free_orIn_empty n C
    (ao2_to n C hC) (fun x => wv n C x C.output) hsingle w hw

lemma orIn_or_input_subset (n : ℕ) (C : Circuit) (hC : AO2 n C)
    (r : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (b : ℕ) (hb : b ∈ (gateAt C r).inputs) :
    PEqualNP.TopForm.orIn n C b ⊆ PEqualNP.TopForm.orIn n C (n + r) := by
  obtain ⟨a, c, heq⟩ := (hC r hr).2.1
  rw [heq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rw [PEqualNP.Outside.L_meta_4675.Redirect.orIn_or (ao2_to n C hC) hr hop]
  simp only [PEqualNP.TopForm.opnd, heq]
  change PEqualNP.TopForm.orIn n C b ⊆ PEqualNP.TopForm.orIn n C a ∪ PEqualNP.TopForm.orIn n C c
  rcases hb with rfl | rfl
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

lemma V1_tzero (n : ℕ) (C : Circuit) (r b : ℕ) (s : ℕ → Bool)
    (hC : AO2 n C) (hr : r < C.gates.length) (hb : b < n + r)
    (hz : PEqualNP.TwoColour.tCount n C s = 0)
    (hsub : PEqualNP.TopForm.orIn n C b ⊆ PEqualNP.TopForm.orIn n C (n + r)) :
    PEqualNP.TwoColour.tCount n (V1 n C r b) s = 0 := by
  apply PEqualNP.Outside.L_meta_4675.Redirect.tCount_redirect_zero n C (V1 n C r b) r b s
    (ao2_to n C hC) (ao2_to n _ (V1_AO2 n C r b hC hr hb)) hr hb
    (by rw [V1_len]) (V1_red n C r b) hsub
  · intro g hg hge
    rw [V1_len] at hg
    omega
  · exact hz

lemma V2_tzero (n : ℕ) (C : Circuit) (r b i : ℕ) (s : ℕ → Bool)
    (hC : AO2 n C) (hr : r < C.gates.length) (hb : b < n + r)
    (hD : AO2 n (V2 n C r b i))
    (hfun : ∀ x, wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output)
    (hop : (gateAt C r).op = GateOp.or) (hbin : b ∈ (gateAt C r).inputs)
    (hz : PEqualNP.TwoColour.tCount n C s = 0)
    (hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false) :
    PEqualNP.TwoColour.tCount n (V2 n C r b i) s = 0 := by
  apply PEqualNP.Outside.L_meta_4675.Redirect.tCount_redirect_zero n C (V2 n C r b i) r b s
    (ao2_to n C hC) (ao2_to n _ hD) hr hb (by rw [V2_len]; omega)
    (V2_red n C r b i) (orIn_or_input_subset n C hC r hr hop b hbin)
  · intro g hg hge
    rw [V2_len] at hg
    have hg' : g = C.gates.length - 1 := by omega
    subst g
    have hidx : n + (C.gates.length - 1) = (V2 n C r b i).output := by
      dsimp [V2]
      omega
    rw [hidx]
    exact orIn_below_empty n _ hD (fun a => (hfun _).trans (hsingle a)) _ (fun _ h => h)
  · exact hz

variable {s : ℕ → Bool}

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = wv n C x C.output) →
    PEqualNP.TwoColour.tCount n D s = 0 → C.gates.length ≤ D.gates.length

lemma reader_or (n : ℕ) (C : Circuit) (hL : Least (s := s) n C) (hzero : PEqualNP.TwoColour.tCount n C s = 0)
    (hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hz' := V1_tzero n C r (n + i) s hL.1 hr hir hzero (by
    rw [orIn_below_empty n C hL.1 hsingle (n + i) hbel]
    exact Finset.empty_subset _)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun hz' 
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hL : Least (s := s) n C) (hzero : PEqualNP.TwoColour.tCount n C s = 0)
    (hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hL hzero hsingle hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hL hzero hsingle hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hc2mem : c2 ∈ (gateAt C r2).inputs := by
    rcases hi2 with e | e <;> rw [e] <;> simp
  have hDz := V2_tzero n C r2 c2 i s hL.1 hr2 hc2lt hD hDfun hop2 hc2mem hzero hsingle
  have hgate1 : gateAt (V2 n C r2 c2 i) r1 = gateAt C r1 := by
    rw [V2_gate n C r2 c2 i r1 (by omega)]
    have hrho : rho r2 r1 = r1 := by simp [rho, h12]
    rw [hrho]
    have hm : (gateAt C r1).inputs.map (tau n r2 c2) = (gateAt C r1).inputs.map id := by
      apply List.map_congr_left
      intro w hw
      exact tau_low n r2 c2 w (by have := (hL.1 r1 hr1).2.2 w hw; omega)
    rw [hm, List.map_id]
  have hc1mem : c1 ∈ (gateAt C r1).inputs := by
    rcases hi1 with e | e <;> rw [e] <;> simp
  have hEz := V1_tzero n (V2 n C r2 c2 i) r1 c1 s hD (by rw [hDlen]; omega)
    hc1lt hDz (orIn_or_input_subset n (V2 n C r2 c2 i) hD r1 (by rw [hDlen]; omega)
      (by rw [hgate1]; exact hop1) c1 (by rw [hgate1]; exact hc1mem))
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun hEz
  rw [V1_len, hDlen] at hle
  omega

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [ite_eq_left h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [ite_eq_left h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [ite_eq_left (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [ite_eq_right h1] at hwk
        by_cases h2 : w = n + r
        · rw [ite_eq_left h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [ite_eq_left (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [ite_eq_right h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [ite_eq_right (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [ite_eq_left h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [ite_eq_right h1] at hwk
    by_cases h2 : w = n + r
    · rw [ite_eq_left h2] at hwk
      exact hci hwk
    · rw [ite_eq_right h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [ite_eq_left h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [ite_eq_right (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma step3_core (n : ℕ) (C : Circuit) (hL : Least (s := s) n C) (hzero : PEqualNP.TwoColour.tCount n C s = 0)
    (hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hL hzero hsingle hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hL hzero hsingle hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (reader_unique n C hL hzero hsingle hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma least_of_same (n : ℕ) (C D : Circuit) (hL : Least (s := s) n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) : Least (s := s) n D :=
  ⟨hD, fun E hE hEf hEz => by rw [hlen]; exact hL.2 E hE (fun x => (hEf x).trans (hfun x)) hEz⟩

lemma V2_gateval (n : ℕ) (C : Circuit) (r c i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    wv n (V2 n C r c i) x (n + k') = wv n C x (n + rho r k') := by
  have h := V2_same n C r c i x hC hr hb hi hout h0 (n + rho r k')
    (by have := rho_lt r k' _ hr hk'; omega)
  rw [tau_rho] at h
  exact h

lemma V2_below (n : ℕ) (C : Circuit) (r c i : ℕ) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbelF : ∀ x, wv n C x (n + i) = true → F x = true)
    (h0 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    (∀ x, wv n (V2 n C r c i) x (n + k') = true → F x = true) ↔
      (∀ x, wv n C x (n + rho r k') = true → F x = true) := by
  constructor
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [← V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv


lemma card_filter_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q]
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    ((Finset.range m).filter Q).card = ((Finset.range m).filter P).card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [Finset.mem_filter, Finset.mem_range] at hk' ⊢
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩


lemma step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : Least (s := s) n C) (hzero : PEqualNP.TwoColour.tCount n C s = 0)
    (hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least (s := s) n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') ∧
      PEqualNP.TwoColour.tCount n C' s = 0 := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hL hzero hsingle hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, least_of_same n C _ hL hD hfun (V2_len n C r c i),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_,
    V2_tzero n C r c i s hL.1 hr hclt hD hfun hop hcin hzero hsingle⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [ite_eq_left hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma card_mem_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < m ∧ P k) (hS' : ∀ k, k ∈ S' ↔ k < m ∧ Q k)
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    S'.card = S.card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [hS'] at hk'
    rw [hS]
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [hS] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [hS']
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma junk_eq (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)
    (hS' : ∀ k, k ∈ S' ↔ k < C'.gates.length ∧ (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true) :
    S'.card = S.card := by
  rw [hlen] at hS'
  apply card_mem_rho C.gates.length r hr _ _ S S' hS hS'
  · intro k' hk'
    rw [hops k' hk', hbelow k' hk']
  · rintro ⟨h, _⟩
    rw [hopr] at h
    exact absurd h (by simp)
  · rintro ⟨h, _⟩
    rw [htop] at h
    exact absurd h (by simp)



end PEqualNP.Outside.L_meta_4675.Lift

namespace PEqualNP.Outside.L_meta_4675.Minimum

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.TwoColour

lemma constrained_least {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ → Bool)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = f)
    (ht : tCount n C s = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = f ∧ tCount n D s = 0 ∧
      D.size ≤ C.size ∧
      ∀ D' : Circuit, IsAO2 n D' → circuitFun n D' = f → tCount n D' s = 0 →
        D.size ≤ D'.size := by
  classical
  let P : ℕ → Prop := fun k => ∃ D : Circuit,
    IsAO2 n D ∧ circuitFun n D = f ∧ tCount n D s = 0 ∧ D.size = k
  have hex : ∃ k, P k := ⟨C.size, C, hAO, hfun, ht, rfl⟩
  obtain ⟨D, hD, hDf, hDt, hsize⟩ := Nat.find_spec hex
  refine ⟨D, hD, hDf, hDt, ?_, ?_⟩
  · rw [hsize]
    exact Nat.find_min' hex ⟨C, hAO, hfun, ht, rfl⟩
  · intro D' hD' hDf' hDt'
    rw [hsize]
    exact Nat.find_min' hex ⟨D', hD', hDf', hDt', rfl⟩

lemma constrained_least_pairs {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ → Bool)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = f)
    (ht : tCount n C s = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = f ∧ tCount n D s = 0 ∧
      D.size ≤ C.size ∧
      (∀ D' : Circuit, IsAO2 n D' → circuitFun n D' = f → tCount n D' s = 0 →
        D.size ≤ D'.size) ∧
      (∀ D' : Circuit, IsAO2 n D' → circuitFun n D' = f → tCount n D' s = 0 →
        D'.size = D.size → andPairs n D ≤ andPairs n D') := by
  classical
  obtain ⟨B, hB, hBf, hBt, hBC, hmin⟩ := constrained_least f s C hAO hfun ht
  let P : ℕ → Prop := fun k => ∃ D : Circuit,
    IsAO2 n D ∧ circuitFun n D = f ∧ tCount n D s = 0 ∧
      D.size = B.size ∧ andPairs n D = k
  have hex : ∃ k, P k := ⟨andPairs n B, B, hB, hBf, hBt, rfl, rfl⟩
  obtain ⟨D, hD, hDf, hDt, hsize, hpairs⟩ := Nat.find_spec hex
  refine ⟨D, hD, hDf, hDt, ?_, ?_, ?_⟩
  · exact hsize.trans_le hBC
  · intro D' hD' hDf' hDt'
    exact hsize.trans_le (hmin D' hD' hDf' hDt')
  · intro D' hD' hDf' hDt' hsize'
    rw [hpairs]
    exact Nat.find_min' hex ⟨D', hD', hDf', hDt', hsize'.trans hsize, rfl⟩

end PEqualNP.Outside.L_meta_4675.Minimum

namespace PEqualNP.Outside.L_meta_4675.Lift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.TwoColour

lemma exists_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  refine ⟨fun _ => true, ?_⟩
  obtain ⟨e, he⟩ := hG
  rw [SimpleGraph.mem_edgeFinset] at he
  revert he
  refine Sym2.inductionOn e ?_
  intro u v he
  have hadj : G.Adj u v := he
  unfold graphFun
  have hd : decide (∃ u v, G.Adj u v ∧ (fun _ : Fin n => true) u = true ∧
      (fun _ : Fin n => true) v = true) = true := decide_eq_true ⟨u, v, hadj, rfl, rfl⟩
  rw [hd]
  simp

lemma top_form_of_constrained_minima (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hG : G.edgeFinset.Nonempty)
    (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C s = 0)
    (hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = graphFun G ∅ → tCount n D s = 0 →
      C.size ≤ D.size)
    (hpairs : ∀ D : Circuit, IsAO2 n D → circuitFun n D = graphFun G ∅ → tCount n D s = 0 →
      D.size = C.size → andPairs n C ≤ andPairs n D) :
    PEqualNP.TopForm.TopForm G C := by
  classical
  have hL : Least (s := s) n C := by
    refine ⟨ao2_of n C hC, ?_⟩
    intro D hD hDf hDz
    exact hmin D (ao2_to n D hD) (funext fun x => (hDf x).trans (congrFun hfun x)) hDz
  have hF : ∀ x, wv n C x C.output = graphFun G ∅ x := congrFun hfun
  have hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false := by
    intro a
    rw [hF]
    simp [graphFun]
  intro i hi j hj hopi hbi hopj hcone
  obtain ⟨x, hx⟩ := exists_true n G hG
  have hout : C.output < n + C.gates.length := out_lt n C x (by rw [hF]; exact hx)
  obtain ⟨D, r, hr, hir, hLD, hFD, hlen, hops, htop, _, _, hcn, hno, hDz⟩ :=
    step3_struct n C (graphFun G ∅) hL hz hsingle hF hout i j hbi hcone
  have hlt := pairs_lt n C D r i j hr hir hlen hops htop hcn hno hopi hopj hcone
  have hcount (X : Circuit) :
      ((Finset.range X.gates.length ×ˢ Finset.range X.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt X p.1).op = GateOp.and ∧
          (gateAt X p.2).op = GateOp.and ∧ InCone n X p.1 p.2)).card = andPairs n X := by
    unfold andPairs
    congr 1
    ext p
    simp only [Finset.mem_filter]
  rw [hcount D, hcount C] at hlt
  have hge := hpairs D (ao2_to n D hLD.1) (funext hFD) hDz hlen
  omega

lemma exists_top_form_zero (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hG : G.edgeFinset.Nonempty)
    (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C s = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ tCount n D s = 0 ∧
      D.size ≤ C.size ∧ PEqualNP.TopForm.TopForm G D ∧
      (∀ D' : Circuit, IsAO2 n D' → circuitFun n D' = graphFun G ∅ → tCount n D' s = 0 →
        D.size ≤ D'.size) := by
  obtain ⟨D, hD, hDf, hDz, hsize, hmin, hpairs⟩ :=
    PEqualNP.Outside.L_meta_4675.Minimum.constrained_least_pairs (graphFun G ∅) s C hC hfun hz
  exact ⟨D, hD, hDf, hDz, hsize,
    top_form_of_constrained_minima n G D s hG hD hDf hDz hmin hpairs, hmin⟩

end PEqualNP.Outside.L_meta_4675.Lift


namespace PEqualNP.Outside.L_meta_4675.SemanticFold

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
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

lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
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

lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

lemma inputs_eq_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
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

lemma opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [inputs_eq_pair hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem_inputs hAO hj b)

lemma orSets_length (n : ℕ) (C : Circuit) :
    (orSets n C).length = C.gates.length := by
  unfold orSets orStep
  rw [foldl_append_length]
  simp

lemma orSets_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (orSets n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [orSets_length]; exact hj

lemma orSets_getD_lt_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    (orSets n C).getD j [] =
      j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = _
  rw [hprelen, ite_eq_left_of_eq_true _ _ (eq_true hop)]
  congr 1
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

lemma orSets_getD_lt_not_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op ≠ GateOp.or) :
    (orSets n C).getD j [] = [j] := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = [j]
  rw [hprelen, ite_eq_right_of_eq_false _ _ (eq_false hop)]

lemma orReaches_iff {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (w g : ℕ) :
    OrReaches n C w g ↔
      ∃ j < C.gates.length, w = n + j ∧
        (g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ b : Fin 2, OrReaches n C (opnd C j b) g)) := by
  constructor
  · rintro ⟨hnw, hmem⟩
    have hlt : w - n < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [orSets_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨w - n, hlt, by omega, ?_⟩
    by_cases hop : (gateAt C (w - n)).op = GateOp.or
    · rw [orSets_getD_lt_or n C hlt hop, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inl rfl
      · right
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨u, hu, hgu⟩
        rw [List.mem_filter, decide_eq_true_eq] at hu
        rw [inputs_eq_pair hAO hlt] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu.1 with rfl | rfl
        · exact ⟨hop, 0, hu.2.1, hgu⟩
        · exact ⟨hop, 1, hu.2.1, hgu⟩
    · rw [orSets_getD_lt_not_or n C hlt hop, List.mem_singleton] at hmem
      exact Or.inl hmem
  · rintro ⟨j, hj, rfl, hcase⟩
    refine ⟨Nat.le_add_right n j, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rcases hcase with rfl | ⟨hop, b, hnu, hgu⟩
    · by_cases hop : (gateAt C g).op = GateOp.or
      · rw [orSets_getD_lt_or n C hj hop]; exact List.mem_cons_self
      · rw [orSets_getD_lt_not_or n C hj hop]; exact List.mem_singleton_self g
    · rw [orSets_getD_lt_or n C hj hop, List.mem_cons]
      right
      rw [List.mem_flatMap]
      refine ⟨opnd C j b, ?_, hgu⟩
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨opnd_mem_inputs hAO hj b, hnu, opnd_lt hAO hj b⟩

lemma orReaches_self {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff hAO (n + j) j).mpr ⟨j, hj, rfl, Or.inl rfl⟩

lemma orReaches_le {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g → n + g ≤ w ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨_, b, hb⟩⟩
    · exact ⟨le_rfl, hj⟩
    · have hlt : opnd C j b < n + j := opnd_lt hAO hj b
      have hrec := ih _ hlt g hb
      exact ⟨by omega, hrec.2⟩

lemma orIn_input {n : ℕ} {C : Circuit} (i : Fin n) :
    orIn n C i.val = {i} := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (hu | ⟨k, _, ⟨hni, _⟩, _, _⟩)
    · exact Fin.ext hu
    · omega
  · rintro rfl
    exact Or.inl rfl

lemma orIn_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {w : ℕ}
    (hw : n + C.gates.length ≤ w) :
    orIn n C w = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hwk, _, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hwk
    rcases hwk with ⟨j, hj, rfl, _⟩
    omega

lemma orIn_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hjk, hkop, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hjk
    rcases hjk with ⟨j', _, heq, hcase⟩
    have hjj' : j' = j := by omega
    subst hjj'
    rcases hcase with rfl | ⟨hor, _⟩
    · rw [hop] at hkop; cases hkop
    · rw [hop] at hor; cases hor

lemma orIn_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext u
  unfold orIn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hjk, hkop, huk⟩)
    · omega
    · rw [orReaches_iff hAO] at hjk
      rcases hjk with ⟨j', _, heq, hcase⟩
      have hjj' : j' = j := by omega
      subst hjj'
      rcases hcase with rfl | ⟨_, b, hb⟩
      · rw [inputs_eq_pair hAO hj] at huk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
        rcases huk with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl h1)
      · fin_cases b
        · exact Or.inl (Or.inr ⟨k, hk, hb, hkop, huk⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hb, hkop, huk⟩)
  · rintro ((h0 | ⟨k, hk, h0k, hkop, huk⟩) | (h1 | ⟨k, hk, h1k, hkop, huk⟩))
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h0]
      exact opnd_mem_inputs hAO hj 0
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 0, h0k⟩⟩
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h1]
      exact opnd_mem_inputs hAO hj 1
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 1, h1k⟩⟩


lemma orIn_snoc_old {n : ℕ} (gs : List Gate) (g : Gate)
    (hAO : IsAO2 n ⟨gs, 0⟩) (w : ℕ) (hw : w < n + gs.length) :
    orIn n ⟨gs ++ [g], 0⟩ w = orIn n ⟨gs, 0⟩ w := by
  have hreach : ∀ k, OrReaches n ⟨gs ++ [g], 0⟩ w k ↔
      OrReaches n ⟨gs, 0⟩ w k := by
    intro k
    unfold OrReaches
    by_cases hn : n ≤ w
    · have hw' : w - n < (orSets n ⟨gs, 0⟩).length := by
        rw [orSets_length]
        exact Nat.sub_lt_left_of_lt_add hn hw
      unfold orSets
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      unfold orStep
      unfold orSets orStep at hw'
      rw [List.getD_append _ _ _ _ hw']
    · simp only [hn, false_and]
  ext i
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hi | ⟨k, hk, hr, hop, hm⟩)
    · exact Or.inl hi
    · have hr' := (hreach k).mp hr
      have hk' := (orReaches_le hAO w k hr').2
      have he : gateAt ⟨gs ++ [g], 0⟩ k = gateAt ⟨gs, 0⟩ k :=
        List.getD_append _ _ _ _ hk'
      exact Or.inr ⟨k, hk', hr', he ▸ hop, he ▸ hm⟩
  · rintro (hi | ⟨k, hk, hr, hop, hm⟩)
    · exact Or.inl hi
    · have he : gateAt ⟨gs ++ [g], 0⟩ k = gateAt ⟨gs, 0⟩ k :=
        List.getD_append _ _ _ _ hk
      exact Or.inr ⟨k, by simp only [List.length_append, List.length_singleton]; omega,
        (hreach k).mpr hr, he.symm ▸ hop, he.symm ▸ hm⟩


abbrev Src (n : ℕ) (ι : Type) := Option (Fin n ⊕ ι)


def srcAt {n : ℕ} {ι : Type} (x : Fin n → Bool) (t : ι → Bool) (s : Src n ι) : Bool :=
  s.elim false (Sum.elim x t)


def opv (a : Bool) (p q : Bool) : Bool := if a then p && q else p || q

lemma opv_mono (a p q p' q' : Bool) (h : p = true → p' = true) (h' : q = true → q' = true) :
    opv a p q = true → opv a p' q' = true := by
  cases a <;> cases p <;> cases q <;> cases p' <;> cases q' <;> simp_all [opv]

abbrev Prog (n : ℕ) (ι : Type) := (ι → Bool) × (ι → Fin 2 → Src n ι)

variable {n : ℕ} {ι : Type}


def Closed (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) : Prop :=
  ∀ i ∈ K, ∀ b : Fin 2, ∀ j : ι, P.2 i b = some (Sum.inr j) → j ∈ K ∧ rank j < rank i


def SolAt (P : Prog n ι) (K : Finset ι) (x : Fin n → Bool) (t : ι → Bool) : Prop :=
  ∀ i ∈ K, t i = opv (P.1 i) (srcAt x t (P.2 i 0)) (srcAt x t (P.2 i 1))


def Sol (P : Prog n ι) (K : Finset ι) (v : ι → (Fin n → Bool) → Bool) : Prop :=
  ∀ x, SolAt P K x (fun i => v i x)

lemma rank_induction (rank : ι → ℕ) (p : ι → Prop)
    (h : ∀ i, (∀ j, rank j < rank i → p j) → p i) : ∀ i, p i := by
  have key : ∀ m, ∀ i, rank i = m → p i := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih => exact fun i hi => h i fun j hj => ih (rank j) (hi ▸ hj) j rfl
  exact fun i => key _ i rfl


lemma sol_le (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) (x : Fin n → Bool)
    (t u : ι → Bool) (ht : SolAt P K x t)
    (hs : ∀ i ∈ K, opv (P.1 i) (srcAt x u (P.2 i 0)) (srcAt x u (P.2 i 1)) = true → u i = true) :
    ∀ i ∈ K, t i = true → u i = true := by
  refine fun i => rank_induction rank (fun i => i ∈ K → t i = true → u i = true) ?_ i
  intro i ih hi hti
  rw [ht i hi] at hti
  refine hs i hi (opv_mono _ _ _ _ _ ?_ ?_ hti)
  all_goals
    intro h
    revert h
    generalize hb : P.2 i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact fun h => h
    · intro h
      obtain ⟨hj, hr⟩ := hcl i hi _ j hb
      exact ih j hr hj h


lemma le_sol (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) (x : Fin n → Bool)
    (t u : ι → Bool) (ht : SolAt P K x t)
    (hs : ∀ i ∈ K, u i = true → opv (P.1 i) (srcAt x u (P.2 i 0)) (srcAt x u (P.2 i 1)) = true) :
    ∀ i ∈ K, u i = true → t i = true := by
  refine fun i => rank_induction rank (fun i => i ∈ K → u i = true → t i = true) ?_ i
  intro i ih hi hui
  rw [ht i hi]
  refine opv_mono _ _ _ _ _ ?_ ?_ (hs i hi hui)
  all_goals
    intro h
    revert h
    generalize hb : P.2 i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact fun h => h
    · intro h
      obtain ⟨hj, hr⟩ := hcl i hi _ j hb
      exact ih j hr hj h


lemma sol_mono (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K)
    (v : ι → (Fin n → Bool) → Bool) (hv : Sol P K v) (x y : Fin n → Bool)
    (hxy : ∀ a, x a = true → y a = true) : ∀ i ∈ K, v i x = true → v i y = true := by
  refine sol_le P rank K hcl x (fun i => v i x) (fun i => v i y) (hv x) ?_
  intro i hi h
  have e := hv y i hi
  simp only at e
  rw [e]
  refine opv_mono _ _ _ _ _ ?_ ?_ h
  all_goals
    generalize P.2 i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact hxy a
    · exact fun h => h


lemma sol_exists (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) :
    ∃ v : ι → (Fin n → Bool) → Bool, Sol P K v := by
  classical
  suffices h : ∀ L : Finset ι, L ⊆ K → Closed P rank L → ∃ v : ι → (Fin n → Bool) → Bool, Sol P L v from
    h K (Finset.Subset.refl K) hcl
  intro L
  induction L using Finset.induction_on_max_value rank with
  | empty => exact fun _ _ => ⟨fun _ _ => false, fun _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha hmax ih =>
    intro hsub hL
    have hs : Closed P rank s := by
      intro i hi b j hj
      obtain ⟨h1, h2⟩ := hL i (Finset.mem_insert_of_mem hi) b j hj
      refine ⟨(Finset.mem_insert.1 h1).resolve_left ?_, h2⟩
      rintro rfl
      exact absurd (hmax i hi) (by omega)
    obtain ⟨v, hv⟩ := ih ((Finset.subset_insert a s).trans hsub) hs
    let v' : ι → (Fin n → Bool) → Bool := fun i x => if i = a then
      opv (P.1 a) (srcAt x (fun j => v j x) (P.2 a 0)) (srcAt x (fun j => v j x) (P.2 a 1)) else v i x
    have hsrc : ∀ i ∈ insert a s, ∀ b x, srcAt x (fun j => v' j x) (P.2 i b)
        = srcAt x (fun j => v j x) (P.2 i b) := by
      intro i hi b x
      rcases hb : P.2 i b with _ | (c | j)
      · rfl
      · rfl
      · obtain ⟨_, hr⟩ := hL i hi b j hb
        have hja : j ≠ a := by
          rintro rfl
          rcases Finset.mem_insert.1 hi with rfl | hi'
          · exact absurd hr (lt_irrefl _)
          · exact absurd (hmax i hi') (by omega)
        simp [srcAt, v', hja]
    refine ⟨v', fun x i hi => ?_⟩
    simp only
    rw [hsrc i hi 0 x, hsrc i hi 1 x]
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · simp [v']
    · have hia : i ≠ a := by
        rintro rfl
        exact ha hi'
      have := hv x i hi'
      simpa [v', hia] using this

lemma wires_length (gs : List Gate) (w0 : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs generalizing w0 with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

lemma wires_snoc (gs : List Gate) (g : Gate) (o : ℕ) (x : List Bool) :
    (⟨gs ++ [g], o⟩ : Circuit).wires x = (⟨gs, o⟩ : Circuit).wires x
      ++ [g.op.eval (g.inputs.map fun i => ((⟨gs, o⟩ : Circuit).wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

lemma wireVal_old (gs : List Gate) (g : Gate) (w : ℕ) (hw : w < n + gs.length) (x : Fin n → Bool) :
    wireVal n ⟨gs ++ [g], 0⟩ w x = wireVal n ⟨gs, 0⟩ w x := by
  unfold wireVal
  rw [wires_snoc, List.getD_append]
  have : ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    have h := wires_length gs (List.ofFn x)
    rw [List.length_ofFn] at h
    exact h
  omega

lemma wireVal_new (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wireVal n ⟨gs ++ [g], 0⟩ (n + gs.length) x
      = g.op.eval (g.inputs.map fun i => wireVal n ⟨gs, 0⟩ i x) := by
  unfold wireVal
  have : ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    have h := wires_length gs (List.ofFn x)
    rw [List.length_ofFn] at h
    exact h
  rw [wires_snoc, List.getD_append_right _ _ _ _ (by omega), this]
  simp

lemma wires_prefix (gs : List Gate) (w0 : List Bool) (i : ℕ) (hi : i < w0.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).getD i false
      = w0.getD i false := by
  induction gs generalizing w0 with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma wireVal_input (gs : List Gate) (i : Fin n) (x : Fin n → Bool) :
    wireVal n ⟨gs, 0⟩ (i : ℕ) x = x i := by
  unfold wireVal Circuit.wires
  rw [wires_prefix _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]


lemma isAO2_snoc (gs : List Gate) (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (a b : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (h : IsAO2 n ⟨gs, 0⟩) :
    IsAO2 n ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h1 g hg
    · rw [List.mem_singleton.1 hg]
      exact ho
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < gs.length
    · have e : gateAt ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        exact List.getD_append _ _ _ _ hjl
      rw [e] at hi
      exact h2 j hjl i hi
    · have hj' : j = gs.length := by omega
      subst hj'
      have e : gateAt ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ gs.length = ⟨o, [a, b]⟩ := by
        simp [gateAt]
      rw [e] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h3 g hg
    · rw [List.mem_singleton.1 hg]
      rfl

def kept (P : Prog n ι) (v : ι → (Fin n → Bool) → Bool) (K : Finset ι) : Finset ι :=
  K.filter fun i => srcAt (fun _ => true) (fun j => v j fun _ => true) (P.2 i 0) = true ∧
    srcAt (fun _ => true) (fun j => v j fun _ => true) (P.2 i 1) = true


def srcReach {n : ℕ} {ι : Type} (R : ι → Finset (Fin n)) (s : Src n ι) : Finset (Fin n) :=
  s.elim ∅ (Sum.elim (fun i => {i}) R)

def Res (gs : List Gate) (f : (Fin n → Bool) → Bool) (R : Finset (Fin n)) : Prop :=
  (∀ x, f x = false) ∨ (f (fun _ => true) = true ∧ ∃ w < n + gs.length,
    (∀ x, wireVal n ⟨gs, 0⟩ w x = f x) ∧ orIn n ⟨gs, 0⟩ w ⊆ R)

def Good (color : Fin n → Bool) (gs : List Gate) : Prop :=
  ∀ j < gs.length, (gateAt ⟨gs, 0⟩ j).op = GateOp.or →
    ∀ u ∈ orIn n ⟨gs, 0⟩ (n + j), ∀ v ∈ orIn n ⟨gs, 0⟩ (n + j), color u = color v

lemma res_mono (gs : List Gate) (g : Gate) (hAO : IsAO2 n ⟨gs, 0⟩)
    (f : (Fin n → Bool) → Bool) (R : Finset (Fin n)) (h : Res gs f R) :
    Res (gs ++ [g]) f R := by
  rcases h with h | ⟨h1, w, hw, h2, hR⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, w, by simp; omega, ?_, ?_⟩
    · intro x
      rw [wireVal_old gs g w hw x, h2 x]
    · rwa [orIn_snoc_old gs g hAO w hw]

lemma good_snoc (color : Fin n → Bool) (gs : List Gate) (o : GateOp)
    (ho : o = GateOp.and ∨ o = GateOp.or) (a b : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hAO : IsAO2 n ⟨gs, 0⟩) (hgood : Good color gs)
    (hcolor : o = GateOp.or →
      ∀ u ∈ orIn n ⟨gs, 0⟩ a ∪ orIn n ⟨gs, 0⟩ b,
      ∀ v ∈ orIn n ⟨gs, 0⟩ a ∪ orIn n ⟨gs, 0⟩ b, color u = color v) :
    Good color (gs ++ [⟨o, [a, b]⟩]) := by
  intro j hj hjop u hu v hv
  by_cases hjold : j < gs.length
  · have he : gateAt ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ j = gateAt ⟨gs, 0⟩ j :=
      List.getD_append _ _ _ _ hjold
    rw [orIn_snoc_old gs _ hAO (n + j) (by omega)] at hu hv
    exact hgood j hjold (he ▸ hjop) u hu v hv
  · have hj' : j = gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    have he : gateAt ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ gs.length = ⟨o, [a, b]⟩ := by simp [gateAt]
    have hop : o = GateOp.or := by simpa only [he] using hjop
    have hAO' := isAO2_snoc gs o ho a b ha hb hAO
    have hr := orIn_or hAO' (by simp) hjop
    have h0 : opnd ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ gs.length 0 = a := by simp [opnd, he]
    have h1 : opnd ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ gs.length 1 = b := by simp [opnd, he]
    rw [hr, h0, h1, orIn_snoc_old gs _ hAO a ha, orIn_snoc_old gs _ hAO b hb] at hu hv
    exact hcolor hop u hu v hv

lemma build (P : Prog n ι) (rank : ι → ℕ) (v : ι → (Fin n → Bool) → Bool)
    (K : Finset ι) (R : ι → Finset (Fin n)) (color : Fin n → Bool)
    (hcl : Closed P rank K) (hv : Sol P K v)
    (hR : ∀ i ∈ K, P.1 i = false → srcReach R (P.2 i 0) ∪ srcReach R (P.2 i 1) ⊆ R i)
    (hcolor : ∀ i ∈ K, P.1 i = false → ∀ u ∈ R i, ∀ w ∈ R i, color u = color w) :
    ∃ gs : List Gate, IsAO2 n ⟨gs, 0⟩ ∧ Good color gs ∧
      gs.length ≤ (kept P v K).card ∧ ∀ i ∈ K, Res gs (v i) (R i) := by
  classical
  induction K using Finset.induction_on_max_value rank with
  | empty =>
    refine ⟨[], ⟨?_, ?_, ?_⟩, ?_, by simp, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · intro g hg; simp at hg
    · intro j hj; simp at hj
    · intro g hg; simp at hg
    · intro j hj; simp at hj
  | insert a s ha hmax ih =>
    have hs : Closed P rank s := by
      intro i hi b j hj
      obtain ⟨h1, h2⟩ := hcl i (Finset.mem_insert_of_mem hi) b j hj
      refine ⟨(Finset.mem_insert.1 h1).resolve_left ?_, h2⟩
      rintro rfl
      exact absurd (hmax i hi) (by omega)
    obtain ⟨gs, hAO, hgood, hlen, hres⟩ := ih hs
      (fun x i hi => hv x i (Finset.mem_insert_of_mem hi))
      (fun i hi => hR i (Finset.mem_insert_of_mem hi))
      (fun i hi => hcolor i (Finset.mem_insert_of_mem hi))
    have hsrc : ∀ b : Fin 2,
        Res gs (fun x => srcAt x (fun j => v j x) (P.2 a b)) (srcReach R (P.2 a b)) := by
      intro b
      rcases hb : P.2 a b with _ | (c | j)
      · exact Or.inl fun x => rfl
      · refine Or.inr ⟨rfl, c, by have := c.2; omega, fun x => wireVal_input gs c x, ?_⟩
        rw [orIn_input]
        exact Finset.Subset.refl _
      · obtain ⟨h1, h2⟩ := hcl a (Finset.mem_insert_self a s) b j hb
        refine hres j ((Finset.mem_insert.1 h1).resolve_left ?_)
        rintro rfl
        exact absurd h2 (lt_irrefl _)
    have hva : ∀ x, v a x = opv (P.1 a) (srcAt x (fun j => v j x) (P.2 a 0))
        (srcAt x (fun j => v j x) (P.2 a 1)) := fun x => hv x a (Finset.mem_insert_self a s)
    have hsub : kept P v s ⊆ kept P v (insert a s) :=
      Finset.filter_subset_filter _ (Finset.subset_insert a s)
    have hlen' : gs.length ≤ (kept P v (insert a s)).card := hlen.trans (Finset.card_le_card hsub)
    have same : Res gs (v a) (R a) → ∃ gs : List Gate,
        IsAO2 n ⟨gs, 0⟩ ∧ Good color gs ∧ gs.length ≤ (kept P v (insert a s)).card ∧
        ∀ i ∈ insert a s, Res gs (v i) (R i) := by
      intro h
      refine ⟨gs, hAO, hgood, hlen', fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · exact h
      · exact hres i hi'
    simp only [Res] at hsrc
    rcases hsrc 0 with h0 | ⟨h0, w0, hw0, hv0, hr0⟩
    · refine same ?_
      cases hop : P.1 a
      · rcases hsrc 1 with h1 | ⟨h1, w1, hw1, hv1, hr1⟩
        · exact Or.inl fun x => by rw [hva x, h0 x, h1 x, hop]; rfl
        · refine Or.inr ⟨by rw [hva, h0, h1, hop]; rfl, w1, hw1, ?_, ?_⟩
          · intro x
            rw [hv1 x, hva x, h0 x, hop]; simp [opv]
          · intro u hu
            exact hR a (Finset.mem_insert_self a s) hop (Finset.mem_union_right _ (hr1 hu))
      · exact Or.inl fun x => by rw [hva x, h0 x, hop]; rfl
    · rcases hsrc 1 with h1 | ⟨h1, w1, hw1, hv1, hr1⟩
      · refine same ?_
        cases hop : P.1 a
        · refine Or.inr ⟨by rw [hva, h0, h1, hop]; rfl, w0, hw0, ?_, ?_⟩
          · intro x
            rw [hv0 x, hva x, h1 x, hop]; simp [opv]
          · intro u hu
            exact hR a (Finset.mem_insert_self a s) hop (Finset.mem_union_left _ (hr0 hu))
        · exact Or.inl fun x => by rw [hva x, h1 x, hop]; simp [opv]
      · have hak : a ∈ kept P v (insert a s) :=
          Finset.mem_filter.2 ⟨Finset.mem_insert_self a s, h0, h1⟩
        have hcard : (kept P v s).card + 1 ≤ (kept P v (insert a s)).card := by
          have hnot : a ∉ kept P v s := fun h => ha (Finset.mem_filter.1 h).1
          rw [← Finset.card_insert_of_notMem hnot]
          exact Finset.card_le_card (Finset.insert_subset hak hsub)
        let o : GateOp := if P.1 a then GateOp.and else GateOp.or
        have ho : o = GateOp.and ∨ o = GateOp.or := by
          by_cases h : P.1 a = true <;> simp [o, h]
        have hor : o = GateOp.or → P.1 a = false := by
          intro h
          cases he : P.1 a <;> simp [o, he] at h ⊢
        have hreach : P.1 a = false →
            orIn n ⟨gs, 0⟩ w0 ∪ orIn n ⟨gs, 0⟩ w1 ⊆ R a := by
          intro ha' u hu
          apply hR a (Finset.mem_insert_self a s) ha'
          rcases Finset.mem_union.mp hu with hu | hu
          · exact Finset.mem_union_left _ (hr0 hu)
          · exact Finset.mem_union_right _ (hr1 hu)
        have hAO' := isAO2_snoc gs o ho w0 w1 hw0 hw1 hAO
        have hgood' : Good color (gs ++ [⟨o, [w0, w1]⟩]) := by
          apply good_snoc color gs o ho w0 w1 hw0 hw1 hAO hgood
          intro hop u hu w hw
          exact hcolor a (Finset.mem_insert_self a s) (hor hop)
            u (hreach (hor hop) hu) w (hreach (hor hop) hw)
        refine ⟨gs ++ [⟨o, [w0, w1]⟩], hAO', hgood', ?_, fun i hi => ?_⟩
        · simp only [List.length_append, List.length_singleton]; omega
        · rcases Finset.mem_insert.1 hi with rfl | hi'
          · refine Or.inr ⟨?_, n + gs.length, by simp, ?_, ?_⟩
            · rw [hva]
              rw [h0, h1]
              cases P.1 i <;> rfl
            · intro x
              rw [wireVal_new, hva x]
              simp only [List.map_cons, List.map_nil, hv0 x, hv1 x]
              by_cases h : P.1 i = true
              · simp [o, h, opv, GateOp.eval]
              · simp [o, h, opv, GateOp.eval]
            · have hi' : gs.length < (gs ++ [({ op := o, inputs := [w0, w1] } : Gate)]).length := by simp
              have he : gateAt ⟨gs ++ [⟨o, [w0, w1]⟩], 0⟩ gs.length = ⟨o, [w0, w1]⟩ := by simp [gateAt]
              cases hp : P.1 i
              · have hop : (gateAt ⟨gs ++ [⟨o, [w0, w1]⟩], 0⟩ gs.length).op = GateOp.or := by rw [he]; simp [o, hp]
                rw [orIn_or hAO' hi' hop]
                have he0 : opnd ⟨gs ++ [⟨o, [w0, w1]⟩], 0⟩ gs.length 0 = w0 := by simp [opnd, he]
                have he1 : opnd ⟨gs ++ [⟨o, [w0, w1]⟩], 0⟩ gs.length 1 = w1 := by simp [opnd, he]
                rw [he0, he1, orIn_snoc_old gs _ hAO w0 hw0, orIn_snoc_old gs _ hAO w1 hw1]
                exact hreach hp
              · have hop : (gateAt ⟨gs ++ [⟨o, [w0, w1]⟩], 0⟩ gs.length).op = GateOp.and := by rw [he]; simp [o, hp]
                rw [orIn_and hAO' hi' hop]
                exact Finset.empty_subset _
          · exact res_mono gs _ hAO _ _ (hres i hi')

lemma good_tCount_zero (gs : List Gate) (color : ℕ → Bool)
    (hgood : Good (fun i : Fin n => color i) gs) :
    PEqualNP.TwoColour.tCount n ⟨gs, 0⟩ color = 0 := by
  apply Finset.card_eq_zero.mpr
  ext j
  simp only [Finset.notMem_empty, iff_false]
  intro hj
  obtain ⟨_, hj, hop, ⟨u, hu, hcu⟩, ⟨v, hv, hcv⟩⟩ := Finset.mem_filter.mp hj
  have he := hgood j hj hop u hu v hv
  change color u = color v at he
  rw [hcu, hcv] at he
  cases he

lemma fold_prog (P : Prog n ι) (rank : ι → ℕ) (v : ι → (Fin n → Bool) → Bool)
    (K : Finset ι) (R : ι → Finset (Fin n)) (color : ℕ → Bool)
    (hcl : Closed P rank K) (hv : Sol P K v)
    (hR : ∀ i ∈ K, P.1 i = false → srcReach R (P.2 i 0) ∪ srcReach R (P.2 i 1) ⊆ R i)
    (hcolor : ∀ i ∈ K, P.1 i = false → ∀ u ∈ R i, ∀ w ∈ R i, color u = color w)
    (o : Src n ι) (ho : ∀ j, o = some (Sum.inr j) → j ∈ K)
    (h1 : srcAt (fun _ => true) (fun j => v j fun _ => true) o = true) :
    ∃ D : Circuit, IsAO2 n D ∧ PEqualNP.TwoColour.tCount n D color = 0 ∧
      D.size ≤ (kept P v K).card ∧
      (∀ x : Fin n → Bool, circuitFun n D x = srcAt x (fun j => v j x) o) ∧
      orIn n D D.output ⊆ srcReach R o := by
  obtain ⟨gs, hAO, hgood, hlen, hres⟩ := build P rank v K R (fun i => color i) hcl hv hR hcolor
  have hR' : Res gs (fun x => srcAt x (fun j => v j x) o) (srcReach R o) := by
    rcases o with _ | (c | j)
    · exact Or.inl fun x => rfl
    · refine Or.inr ⟨rfl, c, by have := c.2; omega, fun x => wireVal_input gs c x, ?_⟩
      rw [orIn_input]
      exact Finset.Subset.refl _
    · exact hres j (ho j rfl)
  rcases hR' with h | ⟨_, w, _, hw, hr⟩
  · exact absurd (h1.symm.trans (h fun _ => true)) (by decide)
  · exact ⟨⟨gs, w⟩, hAO, good_tCount_zero gs color hgood, hlen, hw, hr⟩

open PEqualNP.EdgeOwnership (gateVal pairInput)

def srcOf (n w : ℕ) : Src n ℕ := if h : w < n then some (Sum.inl ⟨w, h⟩) else some (Sum.inr (w - n))

lemma srcOf_inr (w j : ℕ) (h : srcOf n w = some (Sum.inr j)) : w = n + j := by
  unfold srcOf at h
  split_ifs at h with hw
  · simp at h
  · simp only [Option.some.injEq, Sum.inr.injEq] at h
    omega


def isA : GateOp → Bool
  | GateOp.and => true
  | _ => false


def progOf (C : Circuit) (ρ : ℕ → Fin 2 → Src n ℕ) : Prog n ℕ :=
  ⟨fun i => isA (gateAt C i).op, ρ⟩

lemma wireVal_lt (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  rw [wires_prefix _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma srcAt_srcOf (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    srcAt x (fun j => gateVal n C j x) (srcOf n w) = wireVal n C w x := by
  unfold srcOf
  split_ifs with hw
  · exact (wireVal_lt C w hw x).symm
  · show gateVal n C (w - n) x = _
    have : n + (w - n) = w := by omega
    unfold gateVal wireVal
    rw [this]


lemma gate_eq (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) (x : Fin n → Bool) :
    gateVal n C k x = opv (isA (gateAt C k).op) (wireVal n C (opnd C k 0) x)
      (wireVal n C (opnd C k 1) x) := by
  have hg : C.gates[k]? = some (gateAt C k) := by
    simp [gateAt, List.getD_eq_getElem?_getD, hk]
  have hmem : gateAt C k ∈ C.gates := List.mem_of_getElem? hg
  have hlen := hC.2.2 _ hmem
  have hop := hC.1 _ hmem
  have hback := hC.2.1 k hk
  have hsplit : C.gates = C.gates.take k ++ gateAt C k :: C.gates.drop (k + 1) := by
    have h := List.take_append_drop k C.gates
    rw [List.drop_eq_getElem_cons hk] at h
    have e : C.gates[k] = gateAt C k := by simp [gateAt, List.getD_eq_getElem?_getD, hk]
    rw [e] at h
    exact h.symm
  have htake : (C.gates.take k).length = k := by simp; omega
  have hold : ∀ w < n + k, wireVal n C w x = wireVal n ⟨C.gates.take k, 0⟩ w x := by
    intro w hw
    unfold wireVal Circuit.wires
    conv_lhs => rw [hsplit, List.foldl_append]
    rw [wires_prefix]
    rw [wires_length, htake]
    simpa using hw
  have hnew : gateVal n C k x = (gateAt C k).op.eval
      ((gateAt C k).inputs.map fun i => wireVal n ⟨C.gates.take k, 0⟩ i x) := by
    rw [← wireVal_new, htake]
    unfold gateVal wireVal Circuit.wires
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [wires_prefix]
    · simp [List.foldl_append]
    · rw [List.length_append, wires_length, htake, List.length_ofFn]; simp
  obtain ⟨p, q, hpq⟩ : ∃ p q, (gateAt C k).inputs = [p, q] := List.length_eq_two.1 hlen
  have hp : p < n + k := hback p (by rw [hpq]; simp)
  have hq : q < n + k := hback q (by rw [hpq]; simp)
  rw [hnew]
  simp only [opnd, hpq, List.map_cons, List.map_nil, ← hold p hp, ← hold q hq]
  rcases hop with h | h <;> simp [h, GateOp.eval, opv, isA]

lemma super_of_le (C : Circuit) (hC : IsAO2 n C) (K : Finset ℕ) (hK : ∀ k ∈ K, k < C.gates.length)
    (ρ : ℕ → Fin 2 → Src n ℕ) (x : Fin n → Bool)
    (h : ∀ k ∈ K, ∀ b, srcAt x (fun j => gateVal n C j x) (ρ k b) = true → wireVal n C (opnd C k b) x = true) :
    ∀ k ∈ K, opv ((progOf C ρ).1 k) (srcAt x (fun j => gateVal n C j x) (ρ k 0))
      (srcAt x (fun j => gateVal n C j x) (ρ k 1)) = true → gateVal n C k x = true := by
  intro k hk hv
  rw [gate_eq C hC k (hK k hk) x]
  exact opv_mono _ _ _ _ _ (h k hk 0) (h k hk 1) hv


def killSrc (n j w : ℕ) : Src n ℕ := if w = n + j then none else srcOf n w

lemma killSrc_inr (j w k : ℕ) (h : killSrc n j w = some (Sum.inr k)) :
    w = n + k ∧ k ≠ j := by
  by_cases hw : w = n + j
  · simp [killSrc, hw] at h
  · have hsrc : srcOf n w = some (Sum.inr k) := by simpa [killSrc, hw] using h
    have hk := srcOf_inr w k hsrc
    exact ⟨hk, by intro he; subst k; exact hw hk⟩

lemma killSrc_le (C : Circuit) (j w : ℕ) (x : Fin n → Bool) :
    srcAt x (fun k => gateVal n C k x) (killSrc n j w) = true → wireVal n C w x = true := by
  unfold killSrc
  split_ifs with hw
  · intro h
    exact False.elim (Bool.false_ne_true h)
  · rw [srcAt_srcOf]
    exact id

lemma killSrc_eq (C : Circuit) (j w : ℕ) (x : Fin n → Bool)
    (hz : gateVal n C j x = false) :
    srcAt x (fun k => gateVal n C k x) (killSrc n j w) = wireVal n C w x := by
  unfold killSrc
  split_ifs with hw
  · subst w
    exact hz.symm
  · exact srcAt_srcOf C w x

lemma srcReach_srcOf (C : Circuit) (w : ℕ) :
    srcReach (fun k => orIn n C (n + k)) (srcOf n w) = orIn n C w := by
  unfold srcOf
  split_ifs with hw
  · exact (orIn_input (C := C) ⟨w, hw⟩).symm
  · change orIn n C (n + (w - n)) = orIn n C w
    rw [Nat.add_sub_of_le (by omega)]

lemma srcReach_kill (C : Circuit) (j w : ℕ) :
    srcReach (fun k => orIn n C (n + k)) (killSrc n j w) ⊆ orIn n C w := by
  unfold killSrc
  split_ifs
  · exact Finset.empty_subset _
  · rw [srcReach_srcOf]

lemma tCount_zero_good (C : Circuit) (color : ℕ → Bool)
    (hzero : PEqualNP.TwoColour.tCount n C color = 0) :
    Good (fun i : Fin n => color i) C.gates := by
  intro j hj hop u hu v hv
  have he : PEqualNP.TwoColour.twoColour n C color = ∅ := Finset.card_eq_zero.mp hzero
  have hn : ¬ PEqualNP.TwoColour.IsTwoColour n C color j := by
    intro h
    have hm : j ∈ PEqualNP.TwoColour.twoColour n C color :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, h⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  change color u = color v
  cases hcu : color u <;> cases hcv : color v
  · rfl
  · exact False.elim (hn ⟨hj, hop, ⟨u, hu, hcu⟩, ⟨v, hv, hcv⟩⟩)
  · exact False.elim (hn ⟨hj, hop, ⟨v, hv, hcv⟩, ⟨u, hu, hcu⟩⟩)
  · rfl

lemma srcAt_eq_of_eq {ι : Type} (K : Finset ι) (x : Fin n → Bool) (t u : ι → Bool)
    (o : Src n ι) (ho : ∀ j, o = some (Sum.inr j) → j ∈ K)
    (h : ∀ j ∈ K, t j = u j) : srcAt x t o = srcAt x u o := by
  rcases o with _ | (c | j)
  · rfl
  · rfl
  · exact h j (ho j rfl)

lemma srcAt_le_of_le {ι : Type} (K : Finset ι) (x : Fin n → Bool) (t u : ι → Bool)
    (o : Src n ι) (ho : ∀ j, o = some (Sum.inr j) → j ∈ K)
    (h : ∀ j ∈ K, t j = true → u j = true) : srcAt x t o = true → srcAt x u o = true := by
  rcases o with _ | (c | j)
  · exact id
  · exact id
  · exact h j (ho j rfl)

lemma isA_false_or (C : Circuit) (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (h : isA (gateAt C j).op = false) :
    (gateAt C j).op = GateOp.or := by
  have hjg : C.gates[j]? = some (gateAt C j) := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have hjm : gateAt C j ∈ C.gates := List.mem_of_getElem? hjg
  rcases hAO.1 _ hjm with ha | ho
  · simp [ha, isA] at h
  · exact ho

lemma delete_gate (C : Circuit) (color : ℕ → Bool) (j : ℕ)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hj : j < C.gates.length)
    (hpos : ∃ x : Fin n → Bool, gateVal n C j x = false ∧ circuitFun n C x = true) :
    ∃ D : Circuit, IsAO2 n D ∧ PEqualNP.TwoColour.tCount n D color = 0 ∧ D.size < C.size ∧
      (∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true) ∧
      (∀ x : Fin n → Bool, gateVal n C j x = false → circuitFun n D x = circuitFun n C x) := by
  classical
  let K : Finset ℕ := (Finset.range C.gates.length).erase j
  let ρ : ℕ → Fin 2 → Src n ℕ := fun k b => killSrc n j (opnd C k b)
  let P : Prog n ℕ := progOf C ρ
  let o : Src n ℕ := killSrc n j C.output
  let R : ℕ → Finset (Fin n) := fun k => orIn n C (n + k)
  have hK : ∀ k ∈ K, k < C.gates.length := by
    intro k hk
    exact Finset.mem_range.mp (Finset.mem_erase.mp hk).2
  have hcl : Closed P id K := by
    intro k hk b i hi
    have hii : opnd C k b = n + i ∧ i ≠ j := killSrc_inr j (opnd C k b) i hi
    have hback := opnd_lt hAO (hK k hk) b
    have hik : i < k := by omega
    exact ⟨Finset.mem_erase.mpr ⟨hii.2, Finset.mem_range.mpr (lt_trans hik (hK k hk))⟩, hik⟩
  have hout : C.output < n + C.gates.length := by
    obtain ⟨x, _, hx⟩ := hpos
    by_contra h
    have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
      exact (wires_length C.gates (List.ofFn x)).trans (by simp)
    change (C.wires (List.ofFn x)).getD C.output false = true at hx
    rw [List.getD_eq_default _ _ (by omega)] at hx
    cases hx
  have ho : ∀ k, o = some (Sum.inr k) → k ∈ K := by
    intro k hk
    obtain ⟨he, hne⟩ := killSrc_inr j C.output k hk
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨v, hv⟩ := sol_exists P id K hcl
  have hsubsol (x : Fin n → Bool) : ∀ k ∈ K,
      opv (P.1 k) (srcAt x (fun i => gateVal n C i x) (P.2 k 0))
        (srcAt x (fun i => gateVal n C i x) (P.2 k 1)) = true → gateVal n C k x = true := by
    exact super_of_le C hAO K hK ρ x (fun k _ b => killSrc_le C j (opnd C k b) x)
  have hle (x : Fin n → Bool) :
      srcAt x (fun k => v k x) o = true → circuitFun n C x = true := by
    intro hx
    have hvals := sol_le P id K hcl x (fun k => v k x) (fun k => gateVal n C k x) (hv x) (hsubsol x)
    exact killSrc_le C j C.output x (srcAt_le_of_le K x _ _ o ho hvals hx)
  have heq (x : Fin n → Bool) (hz : gateVal n C j x = false) :
      srcAt x (fun k => v k x) o = circuitFun n C x := by
    have hold : SolAt P K x (fun k => gateVal n C k x) := by
      intro k hk
      change gateVal n C k x = opv (isA (gateAt C k).op)
        (srcAt x (fun i => gateVal n C i x) (killSrc n j (opnd C k 0)))
        (srcAt x (fun i => gateVal n C i x) (killSrc n j (opnd C k 1)))
      rw [killSrc_eq C j _ x hz, killSrc_eq C j _ x hz]
      exact gate_eq C hAO k (hK k hk) x
    have hvals : ∀ k ∈ K, v k x = gateVal n C k x := by
      intro k hk
      have h1 := sol_le P id K hcl x (fun k => v k x) (fun k => gateVal n C k x) (hv x)
        (fun i hi h => (hold i hi).trans h) k hk
      have h2 := le_sol P id K hcl x (fun k => v k x) (fun k => gateVal n C k x) (hv x)
        (fun i hi h => (hold i hi).symm.trans h) k hk
      apply Bool.eq_iff_iff.mpr
      exact ⟨h1, h2⟩
    rw [srcAt_eq_of_eq K x _ _ o ho hvals]
    exact killSrc_eq C j C.output x hz
  have h1 : srcAt (fun _ => true) (fun k => v k fun _ => true) o = true := by
    obtain ⟨x, hz, hx⟩ := hpos
    have hvx : srcAt x (fun k => v k x) o = true := (heq x hz).trans hx
    rcases ho' : o with _ | (c | k)
    · rw [ho'] at hvx
      exact False.elim (Bool.false_ne_true hvx)
    · rfl
    · rw [ho'] at hvx
      exact sol_mono P id K hcl v hv x (fun _ => true) (fun _ _ => rfl) k (ho k ho') hvx
  have hR : ∀ i ∈ K, P.1 i = false → srcReach R (P.2 i 0) ∪ srcReach R (P.2 i 1) ⊆ R i := by
    intro i hi hio
    have hop := isA_false_or C hAO (hK i hi) hio
    change srcReach R (killSrc n j (opnd C i 0)) ∪ srcReach R (killSrc n j (opnd C i 1)) ⊆ orIn n C (n + i)
    rw [orIn_or hAO (hK i hi) hop]
    exact Finset.union_subset_union (srcReach_kill C j _) (srcReach_kill C j _)
  have hcolor : ∀ i ∈ K, P.1 i = false → ∀ u ∈ R i, ∀ w ∈ R i, color u = color w := by
    intro i hi hio u hu w hw
    exact tCount_zero_good C color hzero i (hK i hi) (isA_false_or C hAO (hK i hi) hio) u hu w hw
  obtain ⟨D, hD, hDz, hDs, hDf, _⟩ := fold_prog P id v K R color hcl hv hR hcolor o ho h1
  refine ⟨D, hD, hDz, ?_, ?_, ?_⟩
  · have hcard : (kept P v K).card ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hKcard : K.card < C.size := by
      dsimp [K, Circuit.size]
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hj), Finset.card_range]
      omega
    exact lt_of_le_of_lt hDs (lt_of_le_of_lt hcard hKcard)
  · intro x hx
    rw [hDf x] at hx
    exact hle x hx
  · intro x hz
    rw [hDf x]
    exact heq x hz

lemma wireVal_mono (C : Circuit) (hAO : IsAO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, wireVal n C w x = true → wireVal n C w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases hw : w < n
    · rw [wireVal_lt C w hw x] at hx
      rw [wireVal_lt C w hw y]
      exact hxy _ hx
    · by_cases hvalid : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have hidx : n + (w - n) = w := by omega
        have ex : wireVal n C w x = gateVal n C (w - n) x := by
          unfold wireVal gateVal
          rw [hidx]
        have ey : wireVal n C w y = gateVal n C (w - n) y := by
          unfold wireVal gateVal
          rw [hidx]
        rw [ex, gate_eq C hAO (w - n) hj x] at hx
        rw [ey, gate_eq C hAO (w - n) hj y]
        apply opv_mono _ _ _ _ _ ?_ ?_ hx
        · exact ih _ (by have := opnd_lt hAO hj 0; omega)
        · exact ih _ (by have := opnd_lt hAO hj 1; omega)
      · have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length :=
          (wires_length C.gates (List.ofFn x)).trans (by simp)
        unfold wireVal at hx
        rw [List.getD_eq_default _ _ (by omega)] at hx
        cases hx

lemma graphFun_empty (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true := by
  simp [graphFun]

lemma graphFun_pair (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  apply (graphFun_empty G _).mpr
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma delete_pair_inactive (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool) (j : ℕ)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u v, G.Adj u v)
    (hj : j < C.gates.length)
    (hinactive : ∀ u v, G.Adj u v → gateVal n C j (pairInput u v) = false) :
    ∃ D : Circuit, IsAO2 n D ∧ PEqualNP.TwoColour.tCount n D color = 0 ∧
      D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  have hpos : ∃ x, gateVal n C j x = false ∧ circuitFun n C x = true := by
    obtain ⟨u, v, huv⟩ := hne
    refine ⟨pairInput u v, hinactive u v huv, ?_⟩
    rw [hfun]
    exact graphFun_pair G u v huv
  obtain ⟨D, hD, hDz, hDs, hle, heq⟩ := delete_gate C color j hAO hzero hj hpos
  refine ⟨D, hD, hDz, hDs, funext fun x => ?_⟩
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rw [← hfun]
    exact hle x hx
  · intro hx
    obtain ⟨u, v, huv, hxu, hxv⟩ := (graphFun_empty G x).mp hx
    have hp : circuitFun n D (pairInput u v) = true := by
      rw [heq _ (hinactive u v huv), hfun]
      exact graphFun_pair G u v huv
    apply wireVal_mono D hD (pairInput u v) x ?_ D.output hp
    intro i hi
    simp only [pairInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hxu
    · exact hxv

lemma normalise_pair_active (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u v, G.Adj u v) :
    ∃ D : Circuit, IsAO2 n D ∧ PEqualNP.TwoColour.tCount n D color = 0 ∧
      D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ j < D.gates.length, ∃ u v, G.Adj u v ∧ gateVal n D j (pairInput u v) = true := by
  classical
  let Q : ℕ → Prop := fun m => ∃ D : Circuit, IsAO2 n D ∧
    PEqualNP.TwoColour.tCount n D color = 0 ∧ circuitFun n D = graphFun G ∅ ∧ D.size = m
  have hex : ∃ m, Q m := ⟨C.size, C, hAO, hzero, hfun, rfl⟩
  obtain ⟨D, hD, hDz, hDf, hDs⟩ := Nat.find_spec hex
  have hmin : ∀ D' : Circuit, IsAO2 n D' → PEqualNP.TwoColour.tCount n D' color = 0 →
      circuitFun n D' = graphFun G ∅ → D.size ≤ D'.size := by
    intro D' hD' hz' hf'
    rw [hDs]
    exact Nat.find_min' hex ⟨D', hD', hz', hf', rfl⟩
  refine ⟨D, hD, hDz, hmin C hAO hzero hfun, hDf, ?_⟩
  intro j hj
  by_contra hn
  have hinactive : ∀ u v, G.Adj u v → gateVal n D j (pairInput u v) = false := by
    intro u v huv
    cases hval : gateVal n D j (pairInput u v)
    · rfl
    · exact False.elim (hn ⟨u, v, huv, hval⟩)
  obtain ⟨D', hD', hz', hs', hf'⟩ := delete_pair_inactive G D color j hD hDz hDf hne hj hinactive
  exact Nat.not_lt_of_ge (hmin D' hD' hz' hf') hs'

lemma least_pair_active (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u v, G.Adj u v)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D color = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size) :
    ∀ j < C.gates.length, ∃ u v, G.Adj u v ∧ gateVal n C j (pairInput u v) = true := by
  classical
  intro j hj
  by_contra hn
  have hinactive : ∀ u v, G.Adj u v → gateVal n C j (pairInput u v) = false := by
    intro u v huv
    cases hval : gateVal n C j (pairInput u v)
    · rfl
    · exact False.elim (hn ⟨u, v, huv, hval⟩)
  obtain ⟨D, hD, hz, hs, hf⟩ := delete_pair_inactive G C color j hAO hzero hfun hne hj hinactive
  exact Nat.not_lt_of_ge (hmin D hD hz hf) hs

def cutKeep (C : Circuit) (j : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).erase j

def cutProg (C : Circuit) (j : ℕ) : Prog n ℕ :=
  progOf C (fun k b => killSrc n j (opnd C k b))

def cutFun (C : Circuit) (j : ℕ) (v : ℕ → (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : Bool :=
  srcAt x (fun k => v k x) (killSrc n j C.output)

lemma cutKeep_lt (C : Circuit) (j k : ℕ) (hk : k ∈ cutKeep C j) :
    k < C.gates.length :=
  Finset.mem_range.mp (Finset.mem_erase.mp hk).2

lemma cut_closed (C : Circuit) (j : ℕ) (hAO : IsAO2 n C) :
    Closed (cutProg (n := n) C j) id (cutKeep C j) := by
  intro k hk b i hi
  have hii : opnd C k b = n + i ∧ i ≠ j := killSrc_inr j (opnd C k b) i hi
  have hback := opnd_lt hAO (cutKeep_lt C j k hk) b
  have hik : i < k := by omega
  exact ⟨Finset.mem_erase.mpr ⟨hii.2,
    Finset.mem_range.mpr (lt_trans hik (cutKeep_lt C j k hk))⟩, hik⟩

lemma cut_solution_exists (C : Circuit) (j : ℕ) (hAO : IsAO2 n C) :
    ∃ v : ℕ → (Fin n → Bool) → Bool, Sol (cutProg C j) (cutKeep C j) v :=
  sol_exists (cutProg C j) id (cutKeep C j) (cut_closed C j hAO)

lemma cut_output_closed (C : Circuit) (j : ℕ) (hout : C.output < n + C.gates.length) :
    ∀ k, killSrc n j C.output = some (Sum.inr k) → k ∈ cutKeep C j := by
  intro k hk
  obtain ⟨he, hne⟩ := killSrc_inr j C.output k hk
  exact Finset.mem_erase.mpr ⟨hne, Finset.mem_range.mpr (by omega)⟩

lemma cut_le (C : Circuit) (j : ℕ) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length)
    (v : ℕ → (Fin n → Bool) → Bool) (hv : Sol (cutProg C j) (cutKeep C j) v)
    (x : Fin n → Bool) : cutFun C j v x = true → circuitFun n C x = true := by
  intro hx
  have hsuper := super_of_le C hAO (cutKeep C j) (fun k hk => cutKeep_lt C j k hk)
    (fun k b => killSrc n j (opnd C k b)) x
    (fun k _ b => killSrc_le C j (opnd C k b) x)
  have hvals := sol_le (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
    (fun k => v k x) (fun k => gateVal n C k x) (hv x) hsuper
  exact killSrc_le C j C.output x
    (srcAt_le_of_le (cutKeep C j) x _ _ _ (cut_output_closed C j hout) hvals hx)

lemma cut_same (C : Circuit) (j : ℕ) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length)
    (v : ℕ → (Fin n → Bool) → Bool) (hv : Sol (cutProg C j) (cutKeep C j) v)
    (x : Fin n → Bool) (hz : gateVal n C j x = false) :
    cutFun C j v x = circuitFun n C x := by
  have hold : SolAt (cutProg C j) (cutKeep C j) x (fun k => gateVal n C k x) := by
    intro k hk
    change gateVal n C k x = opv (isA (gateAt C k).op)
      (srcAt x (fun i => gateVal n C i x) (killSrc n j (opnd C k 0)))
      (srcAt x (fun i => gateVal n C i x) (killSrc n j (opnd C k 1)))
    rw [killSrc_eq C j _ x hz, killSrc_eq C j _ x hz]
    exact gate_eq C hAO k (cutKeep_lt C j k hk) x
  have hvals : ∀ k ∈ cutKeep C j, v k x = gateVal n C k x := by
    intro k hk
    have h1 := sol_le (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
      (fun k => v k x) (fun k => gateVal n C k x) (hv x)
      (fun i hi h => (hold i hi).trans h) k hk
    have h2 := le_sol (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
      (fun k => v k x) (fun k => gateVal n C k x) (hv x)
      (fun i hi h => (hold i hi).symm.trans h) k hk
    exact Bool.eq_iff_iff.mpr ⟨h1, h2⟩
  unfold cutFun
  rw [srcAt_eq_of_eq (cutKeep C j) x _ _ _ (cut_output_closed C j hout) hvals]
  exact killSrc_eq C j C.output x hz

lemma cut_unique (C : Circuit) (j : ℕ) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length)
    (v w : ℕ → (Fin n → Bool) → Bool)
    (hv : Sol (cutProg C j) (cutKeep C j) v)
    (hw : Sol (cutProg C j) (cutKeep C j) w) : cutFun C j v = cutFun C j w := by
  funext x
  apply srcAt_eq_of_eq (cutKeep C j) x _ _ _ (cut_output_closed C j hout)
  intro k hk
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact sol_le (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
      (fun k => v k x) (fun k => w k x) (hv x)
      (fun i hi h => (hw x i hi).trans h) k hk
  · exact sol_le (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
      (fun k => w k x) (fun k => v k x) (hw x)
      (fun i hi h => (hv x i hi).trans h) k hk

lemma fold_cut (C : Circuit) (color : ℕ → Bool) (j : ℕ)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hj : j < C.gates.length) (hout : C.output < n + C.gates.length)
    (v : ℕ → (Fin n → Bool) → Bool) (hv : Sol (cutProg C j) (cutKeep C j) v)
    (hpos : ∃ x, cutFun C j v x = true) :
    ∃ D : Circuit, IsAO2 n D ∧ PEqualNP.TwoColour.tCount n D color = 0 ∧
      D.size < C.size ∧ circuitFun n D = cutFun C j v := by
  let P := cutProg (n := n) C j
  let K := cutKeep C j
  let R : ℕ → Finset (Fin n) := fun k => orIn n C (n + k)
  let o := killSrc n j C.output
  have hcl : Closed P id K := cut_closed C j hAO
  have ho : ∀ k, o = some (Sum.inr k) → k ∈ K := cut_output_closed C j hout
  have h1 : srcAt (fun _ => true) (fun k => v k fun _ => true) o = true := by
    obtain ⟨x, hx⟩ := hpos
    rcases ho' : o with _ | (c | k)
    · change srcAt x (fun k => v k x) o = true at hx
      rw [ho'] at hx
      exact False.elim (Bool.false_ne_true hx)
    · rfl
    · change srcAt x (fun k => v k x) o = true at hx
      rw [ho'] at hx
      exact sol_mono P id K hcl v hv x (fun _ => true) (fun _ _ => rfl) k (ho k ho') hx
  have hR : ∀ i ∈ K, P.1 i = false → srcReach R (P.2 i 0) ∪ srcReach R (P.2 i 1) ⊆ R i := by
    intro i hi hio
    have hop := isA_false_or C hAO (cutKeep_lt C j i hi) hio
    change srcReach R (killSrc n j (opnd C i 0)) ∪ srcReach R (killSrc n j (opnd C i 1)) ⊆ orIn n C (n + i)
    rw [orIn_or hAO (cutKeep_lt C j i hi) hop]
    exact Finset.union_subset_union (srcReach_kill C j _) (srcReach_kill C j _)
  have hcolor : ∀ i ∈ K, P.1 i = false → ∀ u ∈ R i, ∀ w ∈ R i, color u = color w := by
    intro i hi hio u hu w hw
    exact tCount_zero_good C color hzero i (cutKeep_lt C j i hi)
      (isA_false_or C hAO (cutKeep_lt C j i hi) hio) u hu w hw
  obtain ⟨D, hD, hDz, hDs, hDf, _⟩ := fold_prog P id v K R color hcl hv hR hcolor o ho h1
  refine ⟨D, hD, hDz, ?_, funext hDf⟩
  have hcard : (kept P v K).card ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hKcard : K.card < C.size := by
    dsimp [K, cutKeep, Circuit.size]
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hj), Finset.card_range]
    omega
  exact lt_of_le_of_lt hDs (lt_of_le_of_lt hcard hKcard)

lemma output_lt_of_true (C : Circuit) (x : Fin n → Bool) (hx : circuitFun n C x = true) :
    C.output < n + C.gates.length := by
  by_contra h
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length :=
    (wires_length C.gates (List.ofFn x)).trans (by simp)
  change (C.wires (List.ofFn x)).getD C.output false = true at hx
  rw [List.getD_eq_default _ _ (by omega)] at hx
  cases hx

lemma least_gate_pivotal (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u w, G.Adj u w)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D color = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length)
    (v : ℕ → (Fin n → Bool) → Bool) (hv : Sol (cutProg C j) (cutKeep C j) v) :
    ∃ u w, G.Adj u w ∧ cutFun C j v (pairInput u w) = false ∧
      gateVal n C j (pairInput u w) = true := by
  classical
  have hout : C.output < n + C.gates.length := by
    obtain ⟨u, w, huw⟩ := hne
    apply output_lt_of_true C (pairInput u w)
    rw [hfun]
    exact graphFun_pair G u w huw
  suffices h : ∃ u w, G.Adj u w ∧ cutFun C j v (pairInput u w) = false by
    obtain ⟨u, w, huw, hc⟩ := h
    refine ⟨u, w, huw, hc, ?_⟩
    cases hg : gateVal n C j (pairInput u w)
    · have he := cut_same C j hAO hout v hv (pairInput u w) hg
      rw [hc, hfun, graphFun_pair G u w huw] at he
      cases he
    · rfl
  by_contra hn
  have hkeep : ∀ u w, G.Adj u w → cutFun C j v (pairInput u w) = true := by
    intro u w huw
    cases hc : cutFun C j v (pairInput u w)
    · exact False.elim (hn ⟨u, w, huw, hc⟩)
    · rfl
  have hpos : ∃ x, cutFun C j v x = true := by
    obtain ⟨u, w, huw⟩ := hne
    exact ⟨pairInput u w, hkeep u w huw⟩
  obtain ⟨D, hD, hDz, hDs, hDf⟩ := fold_cut C color j hAO hzero hj hout v hv hpos
  have heq : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      rw [hDf] at hx
      rw [← hfun]
      exact cut_le C j hAO hout v hv x hx
    · intro hx
      obtain ⟨u, w, huw, hxu, hxw⟩ := (graphFun_empty G x).mp hx
      have hp : circuitFun n D (pairInput u w) = true := by
        rw [hDf]
        exact hkeep u w huw
      apply wireVal_mono D hD (pairInput u w) x ?_ D.output hp
      intro i hi
      simp only [pairInput, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hxu
      · exact hxw
  exact Nat.not_lt_of_ge (hmin D hD hDz heq) hDs

lemma cut_same_of_no_reader (C : Circuit) (j : ℕ) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length) (hjo : n + j ≠ C.output)
    (hread : ∀ k < C.gates.length, n + j ∉ (gateAt C k).inputs)
    (v : ℕ → (Fin n → Bool) → Bool) (hv : Sol (cutProg C j) (cutKeep C j) v) :
    cutFun C j v = circuitFun n C := by
  funext x
  have hold : SolAt (cutProg C j) (cutKeep C j) x (fun k => gateVal n C k x) := by
    intro k hk
    have hopnd (b : Fin 2) : opnd C k b ≠ n + j := by
      intro he
      exact hread k (cutKeep_lt C j k hk) (he ▸ opnd_mem_inputs hAO (cutKeep_lt C j k hk) b)
    change gateVal n C k x = opv (isA (gateAt C k).op)
      (srcAt x (fun i => gateVal n C i x) (killSrc n j (opnd C k 0)))
      (srcAt x (fun i => gateVal n C i x) (killSrc n j (opnd C k 1)))
    simp only [killSrc, ite_eq_right (hopnd 0), ite_eq_right (hopnd 1), srcAt_srcOf]
    exact gate_eq C hAO k (cutKeep_lt C j k hk) x
  have hvals : ∀ k ∈ cutKeep C j, v k x = gateVal n C k x := by
    intro k hk
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact sol_le (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
        (fun k => v k x) (fun k => gateVal n C k x) (hv x)
        (fun i hi h => (hold i hi).trans h) k hk
    · exact le_sol (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
        (fun k => v k x) (fun k => gateVal n C k x) (hv x)
        (fun i hi h => (hold i hi).symm.trans h) k hk
  unfold cutFun
  rw [srcAt_eq_of_eq (cutKeep C j) x _ _ _ (cut_output_closed C j hout) hvals]
  simp only [killSrc, ite_eq_right (Ne.symm hjo), srcAt_srcOf]
  rfl

lemma least_no_unused (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u w, G.Adj u w)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D color = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size) :
    ∀ j < C.gates.length, n + j ≠ C.output →
      ∃ r, j < r ∧ r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs := by
  classical
  intro j hj hjo
  by_contra hn
  have hread : ∀ k < C.gates.length, n + j ∉ (gateAt C k).inputs := by
    intro k hk hm
    have hback := hAO.2.1 k hk (n + j) hm
    exact hn ⟨k, by omega, hk, hm⟩
  have hout : C.output < n + C.gates.length := by
    obtain ⟨u, w, huw⟩ := hne
    apply output_lt_of_true C (pairInput u w)
    rw [hfun]
    exact graphFun_pair G u w huw
  obtain ⟨v, hv⟩ := cut_solution_exists C j hAO
  obtain ⟨u, w, huw, hc, _⟩ := least_gate_pivotal G C color hAO hzero hfun hne hmin j hj v hv
  rw [cut_same_of_no_reader C j hAO hout hjo hread v hv, hfun,
    graphFun_pair G u w huw] at hc
  cases hc

lemma graphFun_singleton_false (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n) :
    graphFun G ∅ (fun i => decide (i = a)) = false := by
  cases he : graphFun G ∅ (fun i => decide (i = a))
  · rfl
  · obtain ⟨u, w, huw, hu, hw⟩ := (graphFun_empty G _).mp he
    simp only [decide_eq_true_eq] at hu hw
    subst u
    subst w
    exact False.elim (G.ne_of_adj huw rfl)

lemma graph_output_ge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hfun : circuitFun n C = graphFun G ∅) : n ≤ C.output := by
  by_contra hn
  have ho : C.output < n := by omega
  let a : Fin n := ⟨C.output, ho⟩
  have hx : circuitFun n C (fun i => decide (i = a)) = true := by
    change wireVal n C C.output _ = true
    rw [wireVal_lt C C.output ho]
    simp [a]
  rw [hfun, graphFun_singleton_false G a] at hx
  cases hx

lemma least_output_last (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u w, G.Adj u w)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D color = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size) :
    n ≤ C.output ∧ C.output + 1 = n + C.gates.length := by
  have hlo := graph_output_ge G C hfun
  have hhi : C.output < n + C.gates.length := by
    obtain ⟨u, w, huw⟩ := hne
    apply output_lt_of_true C (pairInput u w)
    rw [hfun]
    exact graphFun_pair G u w huw
  have hnz : 0 < C.gates.length := by omega
  by_cases he : n + (C.gates.length - 1) = C.output
  · exact ⟨hlo, by omega⟩
  · obtain ⟨r, hr, hr', _⟩ := least_no_unused G C color hAO hzero hfun hne hmin
      (C.gates.length - 1) (by omega) he
    omega

end PEqualNP.Outside.L_meta_4675.SemanticFold

namespace PEqualNP.Outside.L_meta_4675.MaskMerge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4675.Lift

def merged (n : ℕ) (C : Circuit) (j k a b : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (fun r =>
    if r = j then ⟨GateOp.or, [a,b]⟩
    else if r = k then ⟨GateOp.and, [n+j,n+j]⟩ else gateAt C r), C.output⟩

lemma merged_len (n : ℕ) (C : Circuit) (j k a b : ℕ) :
    (merged n C j k a b).gates.length = C.gates.length := by simp [merged]

lemma merged_gate (n : ℕ) (C : Circuit) (j k a b r : ℕ) (hr : r < C.gates.length) :
    gateAt (merged n C j k a b) r =
      if r = j then ⟨GateOp.or, [a,b]⟩
      else if r = k then ⟨GateOp.and, [n+j,n+j]⟩ else gateAt C r := by
  exact gateAt_range _ _ _ _ hr

lemma merged_AO (n : ℕ) (C : Circuit) (j k a b : ℕ) (hC : AO2 n C)
    (hjk : j < k) (ha : a < n+j) (hb : b < n+j) :
    AO2 n (merged n C j k a b) := by
  intro r hr
  rw [merged_len] at hr
  rw [merged_gate n C j k a b r hr]
  split_ifs with hj hk
  · subst r
    refine ⟨Or.inr rfl, ⟨a,b,rfl⟩, ?_⟩
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl <;> assumption
  · subst r
    refine ⟨Or.inl rfl, ⟨n+j,n+j,rfl⟩, ?_⟩
    intro w hw
    have hw' : w = n+j := by simpa using hw
    omega
  · exact hC r hr

lemma merged_values (n : ℕ) (C : Circuit) (i j k a b : ℕ)
    (hC : AO2 n C) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (hkGate : gateAt C k = ⟨GateOp.or,[n+i,n+j]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k → n+j ∉ (gateAt C r).inputs)
    (x : Fin n → Bool) :
    ∀ w < n+C.gates.length,
      wv n (merged n C j k a b) x w =
        if w = n+j then (wv n C x a || wv n C x b) else wv n C x w := by
  have hi : i < C.gates.length := by omega
  have hj : j < C.gates.length := by omega
  have ha := (hC i hi).2.2 a (by simp [hiGate])
  have hb := (hC j hj).2.2 b (by simp [hjGate])
  have hD := merged_AO n C j k a b hC hjk (by omega) hb
  have va : wv n C x (n+i) = wv n C x a := by
    rw [wv_rec n C x (aob hC) i hi, hiGate]
    simp [GateOp.eval]
  have vb : wv n C x (n+j) = wv n C x b := by
    rw [wv_rec n C x (aob hC) j hj, hjGate]
    simp [GateOp.eval]
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · rw [wv_input n _ x w hin, wv_input n C x w hin, ite_eq_right (by omega)]
    obtain ⟨r,rfl⟩ : ∃r,w=n+r := ⟨w-n,by omega⟩
    have hr : r < C.gates.length := by omega
    rw [wv_rec n _ x (aob hD) r (by rw [merged_len]; exact hr), merged_gate n C j k a b r hr]
    by_cases hrj : r = j
    · subst r
      rw [ite_eq_left rfl, ite_eq_left rfl]
      rw [eval_or_pair, ih a (by omega) (by omega), ih b (by omega) (by omega)]
      simp [show a ≠ n+j by omega,show b ≠ n+j by omega]
    · by_cases hrk : r = k
      · subst r
        rw [ite_eq_right hrj, ite_eq_left rfl, ite_eq_right (by omega)]
        rw [eval_and_pair, ih (n+j) (by omega) (by omega), ite_eq_left rfl]
        rw [wv_rec n C x (aob hC) k hk, hkGate, eval_or_pair, va, vb]
        simp
      · rw [ite_eq_right hrj, ite_eq_right hrk, ite_eq_right (by omega), wv_rec n C x (aob hC) r hr]
        congr 1
        apply List.map_congr_left
        intro v hv
        have hvlt := (hC r hr).2.2 v hv
        have hvne : v ≠ n+j := fun he => huses r hr hrk (he ▸ hv)
        rw [ih v hvlt (by omega), ite_eq_right hvne]

lemma merged_reach (n : ℕ) (C : Circuit) (i j k a b : ℕ)
    (hC : AO2 n C) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (hkGate : gateAt C k = ⟨GateOp.or,[n+i,n+j]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k → n+j ∉ (gateAt C r).inputs) :
    ∀ w < n+C.gates.length,
      orIn n (merged n C j k a b) w =
        if w = n+j then orIn n C a ∪ orIn n C b else orIn n C w := by
  have hi : i < C.gates.length := by omega
  have hj : j < C.gates.length := by omega
  have ha := (hC i hi).2.2 a (by simp [hiGate])
  have hb := (hC j hj).2.2 b (by simp [hjGate])
  have hD := merged_AO n C j k a b hC hjk (by omega) hb
  have hAO := ao2_to n C hC
  have hDO := ao2_to n _ hD
  have reachK : orIn n C (n+k) = ∅ := by
    rw [Redirect.orIn_or hAO hk (by rw [hkGate])]
    simp only [opnd,hkGate]
    change orIn n C (n+i) ∪ orIn n C (n+j) = ∅
    rw [Redirect.orIn_and hAO hi (by rw [hiGate]), Redirect.orIn_and hAO hj (by rw [hjGate])]
    simp
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · rw [Redirect.orIn_input (C := merged n C j k a b) ⟨w,hin⟩,
        Redirect.orIn_input (C := C) ⟨w,hin⟩, ite_eq_right (by omega)]
    obtain ⟨r,rfl⟩ : ∃r,w=n+r := ⟨w-n,by omega⟩
    have hr : r < C.gates.length := by omega
    have hrD : r < (merged n C j k a b).gates.length := by rw [merged_len]; exact hr
    have hg := merged_gate n C j k a b r hr
    by_cases hrj : r = j
    · subst r
      have hg' : gateAt (merged n C j k a b) j = ⟨GateOp.or,[a,b]⟩ := by simpa using hg
      rw [Redirect.orIn_or hDO hrD (by rw [hg']), ite_eq_left rfl]
      simp only [opnd,hg']
      change orIn n (merged n C j k a b) a ∪ orIn n (merged n C j k a b) b = _
      rw [ih a (by omega) (by omega), ih b (by omega) (by omega)]
      simp [show a ≠ n+j by omega,show b ≠ n+j by omega]
    · by_cases hrk : r = k
      · subst r
        have hg' : gateAt (merged n C j k a b) k = ⟨GateOp.and,[n+j,n+j]⟩ := by simpa [hrj] using hg
        rw [Redirect.orIn_and hDO hrD (by rw [hg']), ite_eq_right (by omega), reachK]
      · have hgs : gateAt (merged n C j k a b) r = gateAt C r := by simpa [hrj,hrk] using hg
        rw [ite_eq_right (by omega)]
        rcases (hC r hr).1 with hand | hor
        · rw [Redirect.orIn_and hDO hrD (by rw [hgs]; exact hand), Redirect.orIn_and hAO hr hand]
        · obtain ⟨u,v,huv⟩ := (hC r hr).2.1
          have huin : u ∈ (gateAt C r).inputs := by simp [huv]
          have hvin : v ∈ (gateAt C r).inputs := by simp [huv]
          have hult := (hC r hr).2.2 u huin
          have hvlt := (hC r hr).2.2 v hvin
          have hune : u ≠ n+j := fun he => huses r hr hrk (he ▸ huin)
          have hvne : v ≠ n+j := fun he => huses r hr hrk (he ▸ hvin)
          rw [Redirect.orIn_or hDO hrD (by rw [hgs]; exact hor), Redirect.orIn_or hAO hr hor]
          simp only [opnd,hgs,huv]
          change orIn n (merged n C j k a b) u ∪ orIn n (merged n C j k a b) v = orIn n C u ∪ orIn n C v
          rw [ih u hult (by omega), ih v hvlt (by omega), ite_eq_right hune, ite_eq_right hvne]


lemma merged_tzero (n : ℕ) (C : Circuit) (i j k a b : ℕ) (s : ℕ → Bool)
    (hC : AO2 n C) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (hkGate : gateAt C k = ⟨GateOp.or,[n+i,n+j]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k → n+j ∉ (gateAt C r).inputs)
    (hz : tCount n C s = 0)
    (hmono : ∀ u ∈ orIn n C a ∪ orIn n C b, ∀ v ∈ orIn n C a ∪ orIn n C b,
      s u = s v) :
    tCount n (merged n C j k a b) s = 0 := by
  classical
  have hzC := Finset.card_eq_zero.mp hz
  change (Finset.range C.gates.length).filter (IsTwoColour n C s) = ∅ at hzC
  have hnone := Finset.filter_eq_empty_iff.mp hzC
  unfold tCount twoColour
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro r hr hbad
  rw [Finset.mem_range, merged_len] at hr
  obtain ⟨_, hop, ⟨u,hu,hsu⟩, ⟨v,hv,hsv⟩⟩ := hbad
  have hreach := merged_reach n C i j k a b hC hij hjk hk hiGate hjGate hkGate huses
    (n+r) (by omega)
  have hg := merged_gate n C j k a b r hr
  by_cases hrj : r = j
  · subst r
    rw [ite_eq_left rfl] at hreach
    rw [hreach] at hu hv
    have he := hmono u hu v hv
    rw [hsu,hsv] at he
    contradiction
  · by_cases hrk : r = k
    · subst r
      rw [hg,ite_eq_right hrj,ite_eq_left rfl] at hop
      cases hop
    · have hgs : gateAt (merged n C j k a b) r = gateAt C r := by simpa [hrj,hrk] using hg
      rw [hgs] at hop
      rw [ite_eq_right (by omega)] at hreach
      rw [hreach] at hu hv
      exact hnone (Finset.mem_range.mpr hr) ⟨hr,hop,⟨u,hu,hsu⟩,⟨v,hv,hsv⟩⟩

lemma merged_fun (n : ℕ) (C : Circuit) (i j k a b : ℕ)
    (hC : AO2 n C) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (hkGate : gateAt C k = ⟨GateOp.or,[n+i,n+j]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k → n+j ∉ (gateAt C r).inputs)
    (hout : C.output < n+C.gates.length) (houtj : C.output ≠ n+j) :
    circuitFun n (merged n C j k a b) = circuitFun n C := by
  funext x
  change wv n (merged n C j k a b) x C.output = wv n C x C.output
  rw [merged_values n C i j k a b hC hij hjk hk hiGate hjGate hkGate huses x C.output hout,
    ite_eq_right houtj]

lemma merged_unused (n : ℕ) (C : Circuit) (i j k a b : ℕ)
    (hC : AO2 n C) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k → n+i ∉ (gateAt C r).inputs) :
    ∀ r < (merged n C j k a b).gates.length,
      n+i ∉ (gateAt (merged n C j k a b) r).inputs := by
  have hi : i < C.gates.length := by omega
  have hj : j < C.gates.length := by omega
  have ha := (hC i hi).2.2 a (by simp [hiGate])
  have hb : b ≠ n+i := by
    intro he
    exact huses j hj (by omega) (by simp [hjGate,he])
  intro r hr
  rw [merged_len] at hr
  rw [merged_gate n C j k a b r hr]
  split_ifs with hrj hrk
  · simp [show n+i ≠ a by omega, Ne.symm hb]
  · simp [show i ≠ j by omega]
  · exact huses r hr hrk

lemma minimum_no_private_buffer_merge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hC : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C s = 0)
    (hne : ∃ u v, G.Adj u v)
    (hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = graphFun G ∅ → tCount n D s = 0 →
      C.size ≤ D.size)
    (i j k a b : ℕ) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (hkGate : gateAt C k = ⟨GateOp.or,[n+i,n+j]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k →
      n+i ∉ (gateAt C r).inputs ∧ n+j ∉ (gateAt C r).inputs)
    (houti : C.output ≠ n+i) (houtj : C.output ≠ n+j)
    (hmono : ∀ u ∈ orIn n C a ∪ orIn n C b, ∀ v ∈ orIn n C a ∪ orIn n C b,
      s u = s v) : False := by
  have hAO := ao2_of n C hC
  have hi : i < C.gates.length := by omega
  have hj : j < C.gates.length := by omega
  have ha := (hAO i hi).2.2 a (by simp [hiGate])
  have hb := (hAO j hj).2.2 b (by simp [hjGate])
  have hD := ao2_to n _ (merged_AO n C j k a b hAO hjk (by omega) hb)
  have hout : C.output < n+C.gates.length := by
    obtain ⟨u,v,huv⟩ := hne
    apply out_lt n C (pairInput u v)
    change circuitFun n C (pairInput u v) = true
    rw [hfun]
    exact SemanticFold.graphFun_pair G u v huv
  have hDf := (merged_fun n C i j k a b hAO hij hjk hk hiGate hjGate hkGate
    (fun r hr hrk => (huses r hr hrk).2) hout houtj).trans hfun
  have hDz := merged_tzero n C i j k a b s hAO hij hjk hk hiGate hjGate hkGate
    (fun r hr hrk => (huses r hr hrk).2) hz hmono
  have hDmin : ∀ D : Circuit, IsAO2 n D → tCount n D s = 0 → circuitFun n D = graphFun G ∅ →
      (merged n C j k a b).size ≤ D.size := by
    intro D hD' hDz' hDf'
    have h := hmin D hD' hDf' hDz'
    simpa only [Circuit.size,merged_len] using h
  obtain ⟨r,_,hr,hm⟩ := SemanticFold.least_no_unused G (merged n C j k a b) s
    hD hDz hDf hne hDmin i (by rw [merged_len]; exact hi) (Ne.symm houti)
  exact merged_unused n C i j k a b hAO hij hjk hk hiGate hjGate
    (fun r hr hrk => (huses r hr hrk).1) r hr hm

end PEqualNP.Outside.L_meta_4675.MaskMerge

namespace PEqualNP.Outside.L_meta_4675.MaskMerge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.TwoColour

lemma private_buffer_merge_smaller (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hC : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C s = 0)
    (hne : ∃ u v, G.Adj u v)
    (i j k a b : ℕ) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (hkGate : gateAt C k = ⟨GateOp.or,[n+i,n+j]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k →
      n+i ∉ (gateAt C r).inputs ∧ n+j ∉ (gateAt C r).inputs)
    (houti : C.output ≠ n+i) (houtj : C.output ≠ n+j)
    (hmono : ∀ u ∈ orIn n C a ∪ orIn n C b, ∀ v ∈ orIn n C a ∪ orIn n C b,
      s u = s v) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ tCount n D s = 0 ∧
      D.size < C.size := by
  classical
  by_contra hn
  have hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = graphFun G ∅ → tCount n D s = 0 →
      C.size ≤ D.size := by
    intro D hD hDf hDz
    by_contra hs
    exact hn ⟨D,hD,hDf,hDz,by omega⟩
  exact minimum_no_private_buffer_merge n G C s hC hfun hz hne hmin
    i j k a b hij hjk hk hiGate hjGate hkGate huses houti houtj hmono

end PEqualNP.Outside.L_meta_4675.MaskMerge

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

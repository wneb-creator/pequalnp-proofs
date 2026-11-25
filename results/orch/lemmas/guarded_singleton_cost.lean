import PEqualNP.Defs

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

lemma junkInputHits (hAO : IsAO2 n C) (hT : TopForm G C) {j k : ℕ}
    (hs : junk G C = {j,k}) (joint : Joint G C j k) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C \ coveredByJunk G C)
    (hjval : gateVal n C j (pairInput u v) = true)
    (hkval : gateVal n C k (pairInput u v) = true) (b : Fin 2) :
    ∃ t ∈ side (n := n) C j b, t = u ∨ t = v := by
  have hj : j ∈ junk G C := by simp [hs]
  have hk : k ∈ junk G C := by simp [hs]
  obtain ⟨hl,ho,_⟩ := junkData hj
  have trace (i : Fin 2) := operandSupport hAO hT hl ho
    ((andValOperands hAO hl ho (pairInput u v)).mp hjval i)
  have other {i g} (hg : g ∈ junk G C) (hr : OrReaches n C (opnd C j i) g) : g = k :=
    (memJunkPair hs hg).resolve_left (fun eq => (Nat.ne_of_lt (operandReachLt hAO hl hr)) eq)
  have makeJ {x : Fin n → Bool}
      (l : val C (List.ofFn x) (opnd C j b) = true)
      (r : val C (List.ofFn x) (opnd C j (1-b)) = true) : gateVal n C j x = true :=
    (andValOperands hAO hl ho x).mpr (fun i => by
      rcases eitherOperand b i with rfl | rfl
      · exact l
      · exact r)
  rcases trace b with h | ⟨g,hg,hr,_⟩
  · exact h
  · have eg := other hg hr
    subst g
    exfalso
    rcases trace (1-b) with ⟨t,ht,et⟩ | ⟨g,hg,hr',_⟩
    · apply freeOfWmax he hk hkval et
      simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
      intro x hx xt
      exact joint x (makeJ (reachVal hr hx) (sideVal ht xt)) hx
    · have eg := other hg hr'
      subst g
      obtain ⟨_,_,x,hx,hfx⟩ := junkData hk
      exact Bool.false_ne_true (hfx.symm.trans
        (joint x (makeJ (reachVal hr hx) (reachVal hr' hx)) hx))

def exclusive (C : Circuit) (j : ℕ) (b : Fin 2) : Finset (Fin n) :=
  side C j b \ side C j (1-b)

lemma exclusiveDisjoint {j : ℕ} {t : Fin n} {b : Fin 2}
    (ht : t ∈ exclusive (n := n) C j b) (ht' : t ∈ side (n := n) C j (1-b)) : False :=
  (Finset.mem_sdiff.mp ht).2 ht'

lemma junkOrientation (hAO : IsAO2 n C) (hT : TopForm G C) {j k : ℕ}
    (hs : junk G C = {j,k}) (joint : Joint G C j k) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C \ coveredByJunk G C)
    (hjval : gateVal n C j (pairInput u v) = true)
    (hkval : gateVal n C k (pairInput u v) = true) :
    (u ∈ exclusive (n := n) C j 0 ∧ v ∈ exclusive (n := n) C j 1) ∨
    (v ∈ exclusive (n := n) C j 0 ∧ u ∈ exclusive (n := n) C j 1) := by
  have hj : j ∈ junk G C := by simp [hs]
  have hk : k ∈ junk G C := by simp [hs]
  obtain ⟨hl,ho,_⟩ := junkData hj
  have disj {t : Fin n} (ht : t = u ∨ t = v)
      (h0 : t ∈ side (n := n) C j 0) (h1 : t ∈ side (n := n) C j 1) : False := by
    apply freeOfWmax he hk hkval ht
    simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx xt
    exact joint x (andFromInputs hAO hl ho h0 h1 xt xt) hx
  obtain ⟨l,hl',el⟩ := junkInputHits hAO hT hs joint he hjval hkval 0
  obtain ⟨r,hr',er⟩ := junkInputHits hAO hT hs joint he hjval hkval 1
  have le : l ∈ exclusive (n := n) C j 0 :=
    Finset.mem_sdiff.mpr ⟨hl', fun h => disj el hl' h⟩
  have re : r ∈ exclusive (n := n) C j 1 :=
    Finset.mem_sdiff.mpr ⟨hr', fun h => disj er h hr'⟩
  rcases el with rfl | rfl <;> rcases er with rfl | rfl
  · exact (disj (.inl rfl) hl' hr').elim
  · exact .inl ⟨le,re⟩
  · exact .inr ⟨le,re⟩
  · exact (disj (.inr rfl) hl' hr').elim


lemma uniqueCenter (h4 : NoFourCycle G) {X : Finset (Fin n)} {a b : Fin n}
    (hX : 1 < X.card) (ha : ∀ x ∈ X, G.Adj a x) (hb : ∀ x ∈ X, G.Adj b x) :
    a = b := by
  by_contra ne
  have hsub : X ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    intro x hx
    simp [ha x hx, hb x hx]
  exact (Nat.not_le_of_lt hX) ((Finset.card_le_card hsub).trans (h4 a b ne))

lemma orInRaw {w : ℕ} (h : w < n) :
    orIn n C w = {⟨w,h⟩} := by
  ext x
  constructor
  · intro hx
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach x hx) with he | ⟨z,hz,_⟩
    · exact Finset.mem_singleton.mpr (Fin.ext he.symm)
    · obtain ⟨k,_,eq,_,_,_⟩ := hz
      omega
  · intro hx
    obtain rfl := Finset.mem_singleton.mp hx
    exact reach_mem_orIn _ Relation.ReflTransGen.refl

lemma orInAnd {j : ℕ} (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach x hx) with he | ⟨z, hs, _⟩
  · have := x.isLt
    omega
  · obtain ⟨k, _, he, hk, _, _⟩ := hs
    have e : k = j := by omega
    subst k
    rw [hop] at hk
    contradiction

-- Stop following an OR path as soon as its support contains at most one leaf.
def RelevantStep (n : ℕ) (C : Circuit) (X : Finset (Fin n)) (p q : ℕ) : Prop :=
  OrStep n C p q ∧ 1 < (orIn n C p ∩ X).card

def RelevantReach (n : ℕ) (C : Circuit) (X : Finset (Fin n)) :=
  Relation.ReflTransGen (RelevantStep n C X)

lemma relevantImpliesOr {X : Finset (Fin n)} {w z : ℕ}
    (h : RelevantReach n C X w z) : Relation.ReflTransGen (OrStep n C) w z := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.tail step.1

noncomputable def relevantCone (n : ℕ) (C : Circuit) (X : Finset (Fin n)) (w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (w+1)).filter (RelevantReach n C X w)

lemma relevantMem {X : Finset (Fin n)} {w z : ℕ} :
    z ∈ relevantCone n C X w ↔ RelevantReach n C X w z := by
  classical
  simp only [relevantCone,Finset.mem_filter,Finset.mem_range]
  exact ⟨And.right,fun h => ⟨Nat.lt_succ_of_le (orStep_le (relevantImpliesOr h)),h⟩⟩

lemma relevantBoundary {X : Finset (Fin n)} {w : ℕ} {x : Fin n}
    (path : Relation.ReflTransGen (OrStep n C) w x.val) :
    ∃ z, RelevantReach n C X w z ∧ (orIn n C z ∩ X).card ≤ 1 ∧ x ∈ orIn n C z := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨x.val,Relation.ReflTransGen.refl, ?_,reach_mem_orIn x Relation.ReflTransGen.refl⟩
    rw [orInRaw x.isLt]
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton _)
  | @head a b step path ih =>
    by_cases many : 1 < (orIn n C a ∩ X).card
    · obtain ⟨z,hz,few,mem⟩ := ih
      exact ⟨z,hz.head ⟨step,many⟩,few,mem⟩
    · exact ⟨a,Relation.ReflTransGen.refl,by omega,reach_mem_orIn x (path.head step)⟩

lemma starLeafBudget (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {c : Fin n} {X : Finset (Fin n)} {w : ℕ} (hw : w < n + C.gates.length)
    (hX : X ⊆ orIn n C w) (hedge : ∀ x ∈ X, s(c,x) ∈ Ustar G C) :
    ∃ P ⊆ orN G C \ lam G C, X.card ≤ P.card + 1 ∧
      ∀ i ∈ P, Relation.ReflTransGen (OrStep n C) w (n+i) ∧
        (orIn n C (n+i) ∩ X).Nonempty := by
  classical
  let cone := relevantCone n C X w
  let big (z : ℕ) := 1 < (orIn n C z ∩ X).card
  let internal := cone.filter big
  let frontier := cone \ internal
  have rootIncluded : ({w} : Finset ℕ) ⊆ cone := by
    intro z hz
    obtain rfl := Finset.mem_singleton.mp hz
    exact relevantMem.mpr .refl
  have internalIncluded : internal ⊆ cone := Finset.filter_subset _ _
  have childCoverage :
      cone \ {w} ⊆ internal.biUnion (fun z => {opnd C (z-n) 0, opnd C (z-n) 1}) := by
    intro y hy
    obtain ⟨cy, notRoot⟩ := Finset.mem_sdiff.mp hy
    rcases Relation.ReflTransGen.cases_tail (relevantMem.mp cy) with same | ⟨z,reach,last⟩
    · exact (notRoot (by simp [same])).elim
    · obtain ⟨i,hi,eq,_,input,_⟩ := last.1
      have zm : z ∈ internal := Finset.mem_filter.mpr ⟨relevantMem.mpr reach,last.2⟩
      refine Finset.mem_biUnion.mpr ⟨z,zm,?_⟩
      obtain ⟨b,hb⟩ := inputsAsOpnd hAO hi input
      have ezi : z - n = i := by omega
      rw [ezi,hb]
      fin_cases b <;> simp
  have branchCount : (internal.biUnion (fun z => {opnd C (z-n) 0, opnd C (z-n) 1})).card ≤
      2 * internal.card := by
    refine Finset.card_biUnion_le.trans ?_
    have sum := Finset.sum_le_sum (s := internal) (fun v (_ : v ∈ internal) =>
      (Finset.card_insert_le (opnd C (v-n) 0) {opnd C (v-n) 1}).trans_eq
        (by simp : ({opnd C (v-n) 1} : Finset ℕ).card + 1 = 2))
    simpa [Nat.mul_comm] using sum
  have frontierCard : frontier.card ≤ internal.card + 1 := by
    have h0 := (Finset.card_le_card childCoverage).trans branchCount
    have h1 := Finset.card_sdiff_add_card_eq_card rootIncluded
    have h2 := Finset.card_sdiff_add_card_eq_card internalIncluded
    rw [Finset.card_singleton] at h1
    change (cone \ internal).card ≤ internal.card + 1
    omega
  have traceWire (z : ℕ) (hz : z ∈ internal) :
      Relation.ReflTransGen (OrStep n C) w z :=
    relevantImpliesOr (relevantMem.mp (Finset.mem_filter.mp hz).1)
  have nle (z : ℕ) (hz : z ∈ internal) : n ≤ z := by
    by_contra! small
    have h := (Finset.mem_filter.mp hz).2
    change 1 < (orIn n C z ∩ X).card at h
    rw [orInRaw small] at h
    have le := Finset.card_le_card (Finset.inter_subset_left :
      ({⟨z,small⟩} : Finset (Fin n)) ∩ X ⊆ {⟨z,small⟩})
    rw [Finset.card_singleton] at le
    omega
  let P := internal.image (fun z => z-n)
  have iCount : P.card = internal.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy e
    have xN := nle x hx
    have yN := nle y hy
    change x-n = y-n at e
    omega
  have subP : P ⊆ orN G C \ lam G C := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    have nz := nle z hz
    have eq : n+(z-n)=z := by omega
    have below := orStep_le (traceWire z hz)
    have hkl : z-n < C.gates.length := by omega
    have bigZ : 1 < (orIn n C (n+(z-n)) ∩ X).card := by
      rw [eq]
      exact (Finset.mem_filter.mp hz).2
    have hop : (gateAt C (z-n)).op = GateOp.or := by
      rcases hAO.1 _ (gateAt_mem hkl) with hand | hor
      · rw [orInAnd hand, Finset.empty_inter, Finset.card_empty] at bigZ
        omega
      · exact hor
    have existsLeaf := Finset.card_pos.mp (by omega : 0 < (orIn n C (n+(z-n)) ∩ X).card)
    obtain ⟨x,hx⟩ := existsLeaf
    refine Finset.mem_sdiff.mpr ⟨orNOfRaw hkl hop ⟨x,(Finset.mem_inter.mp hx).1⟩, ?_⟩
    intro hlam
    obtain ⟨t,ht⟩ := lamAvoidsUstar hlam (fun a ha u hu v hv => topAdj hAO ha hu hv)
    have et : t = c := uniqueCenter h4 bigZ (fun y hy => (ht y (Finset.mem_inter.mp hy).1).1)
      (fun y hy => SimpleGraph.mem_edgeFinset.mp
        (Finset.mem_sdiff.mp (hedge y (Finset.mem_inter.mp hy).2)).1)
    subst t
    exact (ht x (Finset.mem_inter.mp hx).1).2 (hedge x (Finset.mem_inter.mp hx).2)
  have trace (k : ℕ) (hk : k ∈ P) :
      Relation.ReflTransGen (OrStep n C) w (n+k) ∧ (orIn n C (n+k) ∩ X).Nonempty := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    have hn := nle z hz
    have eq : n+(z-n)=z := by omega
    rw [eq]
    have hz' : 1 < (orIn n C z ∩ X).card := (Finset.mem_filter.mp hz).2
    exact ⟨traceWire z hz, Finset.card_pos.mp (by omega)⟩
  let leaves (z : ℕ) := orIn n C z ∩ X
  have coverage : X ⊆ frontier.biUnion leaves := by
    intro x hx
    obtain ⟨z,zr,small,xz⟩ := relevantBoundary (X := X) (mem_orIn_reach x (hX hx))
    refine Finset.mem_biUnion.mpr ⟨z, ?_, Finset.mem_inter.mpr ⟨xz,hx⟩⟩
    have mz : z ∈ cone := relevantMem.mpr zr
    exact Finset.mem_sdiff.mpr ⟨mz,
      fun bad => (Nat.not_le_of_lt (Finset.mem_filter.mp bad).2) small⟩
  have leafOne : ∀ z ∈ frontier, (leaves z).card ≤ 1 := by
    intro z hz
    obtain ⟨atCone,notInt⟩ := Finset.mem_sdiff.mp hz
    exact Nat.le_of_not_gt (fun h => notInt (Finset.mem_filter.mpr ⟨atCone,h⟩))
  refine ⟨P,subP,?_,trace⟩
  calc
    X.card ≤ (frontier.biUnion leaves).card := Finset.card_le_card coverage
    _ ≤ ∑ v ∈ frontier, (leaves v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ frontier, (1 : ℕ) := Finset.sum_le_sum leafOne
    _ = frontier.card := by simp
    _ ≤ internal.card + 1 := frontierCard
    _ = P.card + 1 := by rw [iCount]


def crossBlock (A B : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (A ×ˢ B).image fun p => s(p.1,p.2)

lemma crossBlock_comm (A B : Finset (Fin n)) : crossBlock A B = crossBlock B A := by
  ext e
  constructor <;> intro he
  all_goals
    obtain ⟨⟨u,v⟩,h,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp h
    exact Finset.mem_image.mpr ⟨(v,u), Finset.mem_product.mpr ⟨hv,hu⟩, Sym2.eq_swap⟩

lemma starFromSingleton {A B : Finset (Fin n)} {E : Finset (Sym2 (Fin n))}
    (hE : E ⊆ crossBlock A B) (hne : E.Nonempty) (hB : B.card ≤ 1) :
    ∃ c : Fin n, ∃ X ⊆ A, E.card ≤ X.card ∧ ∀ x ∈ X, s(c,x) ∈ E := by
  classical
  obtain ⟨e,he⟩ := hne
  obtain ⟨⟨u,c⟩,huv,_⟩ := Finset.mem_image.mp (hE he)
  have hc := (Finset.mem_product.mp huv).2
  let X := A.filter fun x => s(c,x) ∈ E
  have hSub : E ⊆ X.image (fun x => s(c,x)) := by
    intro f hf
    obtain ⟨⟨x,d⟩,hxd,rfl⟩ := Finset.mem_image.mp (hE hf)
    obtain ⟨hx,hd⟩ := Finset.mem_product.mp hxd
    have eq := Finset.card_le_one.mp hB d hd c hc
    change d = c at eq
    subst d
    rw [Sym2.eq_swap] at hf
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx,hf⟩, Sym2.eq_swap⟩
  exact ⟨c, X, Finset.filter_subset _ _, (Finset.card_le_card hSub).trans
    Finset.card_image_le, fun x hx => (Finset.mem_filter.mp hx).2⟩

lemma blockStar (h4 : NoFourCycle G) {A B : Finset (Fin n)} {E : Finset (Sym2 (Fin n))}
    (hE : E ⊆ crossBlock A B) (hne : E.Nonempty)
    (adj : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v) :
    (∃ c : Fin n, ∃ X ⊆ A, E.card ≤ X.card ∧ ∀ x ∈ X, s(c,x) ∈ E) ∨
    (∃ c : Fin n, ∃ X ⊆ B, E.card ≤ X.card ∧ ∀ x ∈ X, s(c,x) ∈ E) := by
  by_cases hB : B.card ≤ 1
  · exact .inl (starFromSingleton hE hne hB)
  · have hA : A.card ≤ 1 := by
      by_contra! h
      obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp h
      exact ne (uniqueCenter h4 (Nat.lt_of_not_ge hB) (adj a ha) (adj b hb))
    exact .inr (starFromSingleton (crossBlock_comm A B ▸ hE) hne hA)

lemma twoStarsOnOppositeSides (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {a : ℕ} (ha : a < C.gates.length)
    {b d : Fin 2} (hne : b ≠ d)
    {c f : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ exclusive (n := n) C a b)
    (hY : Y ⊆ exclusive (n := n) C a d)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C)
    (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C) :
    X.card + Y.card ≤ 2 + (orN G C \ lam G C).card := by
  have hx : X ⊆ side (n := n) C a b := fun _ h => (Finset.mem_sdiff.mp (hX h)).1
  have hy : Y ⊆ side (n := n) C a d := fun _ h => (Finset.mem_sdiff.mp (hY h)).1
  have bound (i : Fin 2) : opnd C a i < n + C.gates.length :=
    (opndBound hAO ha i).trans (by omega)
  obtain ⟨P,hP,pn,pt⟩ := starLeafBudget hAO h4 (bound b) hx ex
  obtain ⟨Q,hQ,qn,qt⟩ := starLeafBudget hAO h4 (bound d) hy ey
  have ed : d = 1-b := (eitherOperand b d).resolve_left (Ne.symm hne)
  have hpq : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro i hiP hiQ
    obtain ⟨x,hx⟩ := (pt i hiP).2
    obtain ⟨hin,hx⟩ := Finset.mem_inter.mp hx
    have hm : x ∈ side (n := n) C a d := orInTrans (qt i hiQ).1 hin
    exact exclusiveDisjoint (hX hx) (ed ▸ hm)
  have cards := Finset.card_le_card (Finset.union_subset hP hQ)
  rw [Finset.card_union_of_disjoint hpq] at cards
  omega

lemma oppositeAddOne (b : Fin 2) : b + 1 = 1 - b := by
  fin_cases b <;> decide

lemma residualBound (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hTwo : (junk G C).card = 2) :
    (Ustar G C \ coveredByJunk G C).card ≤ 2 + (orN G C \ lam G C).card := by
  classical
  let R := Ustar G C \ coveredByJunk G C
  change R.card ≤ _
  by_cases hR : R.Nonempty
  · obtain ⟨j,k,_,hs⟩ := Finset.card_eq_two.mp hTwo
    have hj : j ∈ junk G C := by simp [hs]
    have hk : k ∈ junk G C := by simp [hs]
    have sk : junk G C = {k,j} := hs.trans (Finset.pair_comm _ _)
    obtain ⟨edge,he⟩ := hR
    induction edge using Sym2.ind with
    | h u v =>
      have joint := (residualJoint hL hT hs he).1
      let A (r : Fin 2) := exclusive (n := n) C j 0 ∩ exclusive (n := n) C k r
      let B (r : Fin 2) := exclusive (n := n) C j 1 ∩ exclusive (n := n) C k (1-r)
      let E (r : Fin 2) := R ∩ crossBlock (A r) (B r)
      have adj (r : Fin 2) (x : Fin n) (hx : x ∈ A r) (y : Fin n) (hy : y ∈ B r) :
          G.Adj x y := by
        have jx := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).1).1
        have jy := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).1).1
        have kx := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
        have ky := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).2).1
        obtain ⟨jl,jo,_⟩ := junkData hj
        obtain ⟨kl,ko,_⟩ := junkData hk
        apply (graphFun_pair G x y).mp
        apply joint
        · exact andFromInputs hL.1 jl jo jx jy (pairInput_left x y) (pairInput_right x y)
        · fin_cases r
          · exact andFromInputs hL.1 kl ko kx ky (pairInput_left x y) (pairInput_right x y)
          · exact andFromInputs hL.1 kl ko ky kx (pairInput_right x y) (pairInput_left x y)
      have star (r : Fin 2) : ∃ (b : Fin 2) (c : Fin n) (X : Finset (Fin n)),
          X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k (r+b) ∧
          (E r).card ≤ X.card ∧ ∀ x ∈ X, s(c,x) ∈ Ustar G C := by
        by_cases hn : (E r).Nonempty
        · rcases blockStar h4 (E := E r) Finset.inter_subset_right hn (adj r) with
            ⟨c,X,hX,hc,h⟩ | ⟨c,X,hX,hc,h⟩
          · exact ⟨0,c,X,by simpa [A] using hX,hc,
              fun x hx => (Finset.mem_sdiff.mp (Finset.mem_inter.mp (h x hx)).1).1⟩
          · exact ⟨1,c,X,by simpa [B, oppositeAddOne] using hX,hc,
              fun x hx => (Finset.mem_sdiff.mp (Finset.mem_inter.mp (h x hx)).1).1⟩
        · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
          exact ⟨0,u,∅,by simp,by simp,by simp⟩
      have cover : R ⊆ E 0 ∪ E 1 := by
        intro e h
        induction e using Sym2.ind with
        | h x y =>
          obtain ⟨joint,hjv,hkv⟩ := residualJoint hL hT hs h
          have hL' := junkOrientation hL.1 hT hs joint h hjv hkv
          have hR' := junkOrientation hL.1 hT sk (joint_comm joint) h hkv hjv
          have put (p q : Fin n) (r : Fin 2) (hp : p ∈ A r) (hq : q ∈ B r)
              (eq : s(p,q) = s(x,y)) : s(x,y) ∈ E r :=
            Finset.mem_inter.mpr ⟨h, Finset.mem_image.mpr
              ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,eq⟩⟩
          apply Finset.mem_union.mpr
          rcases hL' with ⟨l,r⟩ | ⟨l,r⟩ <;> rcases hR' with ⟨l',r'⟩ | ⟨l',r'⟩
          · exact .inl (put x y 0 (Finset.mem_inter.mpr ⟨l,l'⟩)
              (Finset.mem_inter.mpr ⟨r,r'⟩) rfl)
          · exact .inr (put x y 1 (Finset.mem_inter.mpr ⟨l,r'⟩)
              (Finset.mem_inter.mpr ⟨r,l'⟩) rfl)
          · exact .inr (put y x 1 (Finset.mem_inter.mpr ⟨l,r'⟩)
              (Finset.mem_inter.mpr ⟨r,l'⟩) Sym2.eq_swap)
          · exact .inl (put y x 0 (Finset.mem_inter.mpr ⟨l,l'⟩)
              (Finset.mem_inter.mpr ⟨r,r'⟩) Sym2.eq_swap)
      obtain ⟨b,c,X,hX,xn,hxe⟩ := star 0
      obtain ⟨d,f,Y,hY,yn,hye⟩ := star 1
      have budget : X.card + Y.card ≤ 2 + (orN G C \ lam G C).card := by
        by_cases e : b = d
        · subst d
          have hn : (0 : Fin 2) + b ≠ 1 + b := by fin_cases b <;> decide
          exact twoStarsOnOppositeSides hL.1 h4 (junkData hk).1 hn
            (fun _ hx => (Finset.mem_inter.mp (hX hx)).2)
            (fun _ hy => (Finset.mem_inter.mp (hY hy)).2) hxe hye
        · exact twoStarsOnOppositeSides hL.1 h4 (junkData hj).1 e
            (fun _ hx => (Finset.mem_inter.mp (hX hx)).1)
            (fun _ hy => (Finset.mem_inter.mp (hY hy)).1) hxe hye
      have hcard := (Finset.card_le_card cover).trans (Finset.card_union_le (E 0) (E 1))
      omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hR, Finset.card_empty]
    exact Nat.zero_le _


lemma coveredByJunk_empty (hw : ∀ j ∈ junk G C, wmax G C j = ∅) :
    coveredByJunk G C = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
  have hd := (Finset.mem_filter.mp he).2
  rw [hw j hj] at hd
  exact hd (Finset.disjoint_empty_right _)

lemma wmax_empty_residual_bound (h4 : NoFourCycle G) (hL : IsLeastAO G C)
    (hT : TopForm G C) (hTwo : (junk G C).card = 2)
    (hw : ∀ j ∈ junk G C, wmax G C j = ∅) :
    (Ustar G C).card ≤ 2 + (orN G C \ lam G C).card := by
  have h := residualBound h4 hL hT hTwo
  rw [coveredByJunk_empty hw, Finset.sdiff_empty] at h
  exact h

lemma leafBudget (hAO : IsAO2 n C)
    {X : Finset (Fin n)} {w : ℕ} (hw : w < n + C.gates.length)
    (hX : X ⊆ orIn n C w)
    (hfree : ∀ k, k < C.gates.length → 1 < (orIn n C (n+k) ∩ X).card → k ∉ lam G C) :
    ∃ P ⊆ orN G C \ lam G C, X.card ≤ P.card + 1 ∧
      ∀ i ∈ P, Relation.ReflTransGen (OrStep n C) w (n+i) ∧
        1 < (orIn n C (n+i) ∩ X).card := by
  classical
  let cone := relevantCone n C X w
  let big (z : ℕ) := 1 < (orIn n C z ∩ X).card
  let internal := cone.filter big
  let frontier := cone \ internal
  have rootIncluded : ({w} : Finset ℕ) ⊆ cone := by
    intro z hz
    obtain rfl := Finset.mem_singleton.mp hz
    exact relevantMem.mpr .refl
  have internalIncluded : internal ⊆ cone := Finset.filter_subset _ _
  have childCoverage :
      cone \ {w} ⊆ internal.biUnion (fun z => {opnd C (z-n) 0, opnd C (z-n) 1}) := by
    intro y hy
    obtain ⟨cy, notRoot⟩ := Finset.mem_sdiff.mp hy
    rcases Relation.ReflTransGen.cases_tail (relevantMem.mp cy) with same | ⟨z,reach,last⟩
    · exact (notRoot (by simp [same])).elim
    · obtain ⟨i,hi,eq,_,input,_⟩ := last.1
      have zm : z ∈ internal := Finset.mem_filter.mpr ⟨relevantMem.mpr reach,last.2⟩
      refine Finset.mem_biUnion.mpr ⟨z,zm,?_⟩
      obtain ⟨b,hb⟩ := inputsAsOpnd hAO hi input
      have ezi : z - n = i := by omega
      rw [ezi,hb]
      fin_cases b <;> simp
  have branchCount : (internal.biUnion (fun z => {opnd C (z-n) 0, opnd C (z-n) 1})).card ≤
      2 * internal.card := by
    refine Finset.card_biUnion_le.trans ?_
    have sum := Finset.sum_le_sum (s := internal) (fun v (_ : v ∈ internal) =>
      (Finset.card_insert_le (opnd C (v-n) 0) {opnd C (v-n) 1}).trans_eq
        (by simp : ({opnd C (v-n) 1} : Finset ℕ).card + 1 = 2))
    simpa [Nat.mul_comm] using sum
  have frontierCard : frontier.card ≤ internal.card + 1 := by
    have h0 := (Finset.card_le_card childCoverage).trans branchCount
    have h1 := Finset.card_sdiff_add_card_eq_card rootIncluded
    have h2 := Finset.card_sdiff_add_card_eq_card internalIncluded
    rw [Finset.card_singleton] at h1
    change (cone \ internal).card ≤ internal.card + 1
    omega
  have traceWire (z : ℕ) (hz : z ∈ internal) :
      Relation.ReflTransGen (OrStep n C) w z :=
    relevantImpliesOr (relevantMem.mp (Finset.mem_filter.mp hz).1)
  have nle (z : ℕ) (hz : z ∈ internal) : n ≤ z := by
    by_contra! small
    have h := (Finset.mem_filter.mp hz).2
    change 1 < (orIn n C z ∩ X).card at h
    rw [orInRaw small] at h
    have le := Finset.card_le_card (Finset.inter_subset_left :
      ({⟨z,small⟩} : Finset (Fin n)) ∩ X ⊆ {⟨z,small⟩})
    rw [Finset.card_singleton] at le
    omega
  let P := internal.image (fun z => z-n)
  have iCount : P.card = internal.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy e
    have xN := nle x hx
    have yN := nle y hy
    change x-n = y-n at e
    omega
  have subP : P ⊆ orN G C \ lam G C := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    have nz := nle z hz
    have eq : n+(z-n)=z := by omega
    have below := orStep_le (traceWire z hz)
    have hkl : z-n < C.gates.length := by omega
    have bigZ : 1 < (orIn n C (n+(z-n)) ∩ X).card := by
      rw [eq]
      exact (Finset.mem_filter.mp hz).2
    have hop : (gateAt C (z-n)).op = GateOp.or := by
      rcases hAO.1 _ (gateAt_mem hkl) with hand | hor
      · rw [orInAnd hand, Finset.empty_inter, Finset.card_empty] at bigZ
        omega
      · exact hor
    have existsLeaf := Finset.card_pos.mp (by omega : 0 < (orIn n C (n+(z-n)) ∩ X).card)
    obtain ⟨x,hx⟩ := existsLeaf
    refine Finset.mem_sdiff.mpr ⟨orNOfRaw hkl hop ⟨x,(Finset.mem_inter.mp hx).1⟩, ?_⟩
    exact hfree (z-n) hkl bigZ
  have trace (k : ℕ) (hk : k ∈ P) :
      Relation.ReflTransGen (OrStep n C) w (n+k) ∧ 1 < (orIn n C (n+k) ∩ X).card := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    have hn := nle z hz
    have eq : n+(z-n)=z := by omega
    rw [eq]
    have hz' : 1 < (orIn n C z ∩ X).card := (Finset.mem_filter.mp hz).2
    exact ⟨traceWire z hz, hz'⟩
  let leaves (z : ℕ) := orIn n C z ∩ X
  have coverage : X ⊆ frontier.biUnion leaves := by
    intro x hx
    obtain ⟨z,zr,small,xz⟩ := relevantBoundary (X := X) (mem_orIn_reach x (hX hx))
    refine Finset.mem_biUnion.mpr ⟨z, ?_, Finset.mem_inter.mpr ⟨xz,hx⟩⟩
    have mz : z ∈ cone := relevantMem.mpr zr
    exact Finset.mem_sdiff.mpr ⟨mz,
      fun bad => (Nat.not_le_of_lt (Finset.mem_filter.mp bad).2) small⟩
  have leafOne : ∀ z ∈ frontier, (leaves z).card ≤ 1 := by
    intro z hz
    obtain ⟨atCone,notInt⟩ := Finset.mem_sdiff.mp hz
    exact Nat.le_of_not_gt (fun h => notInt (Finset.mem_filter.mpr ⟨atCone,h⟩))
  refine ⟨P,subP,?_,trace⟩
  calc
    X.card ≤ (frontier.biUnion leaves).card := Finset.card_le_card coverage
    _ ≤ ∑ v ∈ frontier, (leaves v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ frontier, (1 : ℕ) := Finset.sum_le_sum leafOne
    _ = frontier.card := by simp
    _ ≤ internal.card + 1 := frontierCard
    _ = P.card + 1 := by rw [iCount]


lemma lam_same_color (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) {k : ℕ} (hk : k ∈ lam G C)
    {a b : Fin n} (ha : a ∈ orIn n C (n+k)) (hb : b ∈ orIn n C (n+k)) : s a = s b := by
  obtain ⟨t, ht⟩ := lamAvoidsUstar hk (fun j hj u hu v hv => topAdj hAO hj hu hv)
  have hta := hs t a (ht a ha).1
  have htb := hs t b (ht b hb).1
  cases hs0 : s t <;> cases hs1 : s a <;> cases hs2 : s b <;> simp_all

lemma star_pair_not_lam (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {c a b : Fin n} (hab : a ≠ b)
    (hae : s(c,a) ∈ Ustar G C) (hbe : s(c,b) ∈ Ustar G C)
    {k : ℕ} (ha : a ∈ orIn n C (n+k)) (hb : b ∈ orIn n C (n+k)) : k ∉ lam G C := by
  intro hk
  obtain ⟨t, ht⟩ := lamAvoidsUstar hk (fun j hj u hu v hv => topAdj hAO hj hu hv)
  have hp : 1 < ({a,b} : Finset (Fin n)).card := by simp [hab]
  have etc : t = c := uniqueCenter h4 hp
    (by
      intro x hx
      have hx' : x = a ∨ x = b := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
      rcases hx' with hx' | hx'
      · exact hx' ▸ (ht a ha).1
      · exact hx' ▸ (ht b hb).1)
    (by intro x hx; rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx : x = a ∨ x = b) with rfl | rfl
        exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hae).1
        exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hbe).1)
  subst t
  exact (ht a ha).2 hae

lemma anchored_star_free (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {c z : Fin n} {X : Finset (Fin n)}
    (hedge : ∀ x ∈ X, s(c,x) ∈ Ustar G C)
    (hcolor : ∀ x ∈ X, s x ≠ s z)
    (k : ℕ) (hbig : 1 < (orIn n C (n+k) ∩ insert z X).card) : k ∉ lam G C := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hbig
  obtain ⟨hIa, hXa⟩ := Finset.mem_inter.mp ha
  obtain ⟨hIb, hXb⟩ := Finset.mem_inter.mp hb
  rcases Finset.mem_insert.mp hXa with haz | hXa
  · rcases Finset.mem_insert.mp hXb with hbz | hXb
    · exact (hab (haz.trans hbz.symm)).elim
    · intro hk
      have he := lam_same_color hAO s hs hk hIb hIa
      exact hcolor b hXb (he.trans (congrArg s haz))
  · rcases Finset.mem_insert.mp hXb with hbz | hXb
    · intro hk
      have he := lam_same_color hAO s hs hk hIa hIb
      exact hcolor a hXa (he.trans (congrArg s hbz))
    · exact star_pair_not_lam hAO h4 hab (hedge a hXa) (hedge b hXb) hIa hIb

lemma insert_big_has_leaf {X : Finset (Fin n)} {z : Fin n} {S : Finset (Fin n)}
    (hbig : 1 < (S ∩ insert z X).card) : (S ∩ X).Nonempty := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hbig
  obtain ⟨hIa, hXa⟩ := Finset.mem_inter.mp ha
  obtain ⟨hIb, hXb⟩ := Finset.mem_inter.mp hb
  rcases Finset.mem_insert.mp hXa with haz | hXa
  · rcases Finset.mem_insert.mp hXb with hbz | hXb
    · exact (hab (haz.trans hbz.symm)).elim
    · exact ⟨b, Finset.mem_inter.mpr ⟨hIb,hXb⟩⟩
  · exact ⟨a, Finset.mem_inter.mpr ⟨hIa,hXa⟩⟩

lemma anchored_star_budget (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {c z : Fin n} {X : Finset (Fin n)} {w : ℕ} (hw : w < n + C.gates.length)
    (hX : X ⊆ orIn n C w) (hz : z ∈ orIn n C w)
    (hedge : ∀ x ∈ X, s(c,x) ∈ Ustar G C)
    (hcolor : ∀ x ∈ X, s x ≠ s z) :
    ∃ P ⊆ orN G C \ lam G C, X.card ≤ P.card ∧
      ∀ i ∈ P, Relation.ReflTransGen (OrStep n C) w (n+i) ∧
        (orIn n C (n+i) ∩ X).Nonempty := by
  have hzX : z ∉ X := fun h => hcolor z h rfl
  obtain ⟨P,hP,hcount,htrace⟩ := leafBudget hAO hw
    (Finset.insert_subset hz hX)
    (fun k _ hbig => anchored_star_free hAO h4 s hs hedge hcolor k hbig)
  refine ⟨P,hP,?_,?_⟩
  · rw [Finset.card_insert_of_notMem hzX] at hcount
    omega
  · intro k hk
    exact ⟨(htrace k hk).1, insert_big_has_leaf (htrace k hk).2⟩

lemma anchored_opposite_sides_budget (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {a : ℕ} (ha : a < C.gates.length) {b d : Fin 2} (hbd : b ≠ d)
    {c f : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ exclusive (n := n) C a b) (hY : Y ⊆ exclusive (n := n) C a d)
    (hf : f ∈ side (n := n) C a b) (hc : c ∈ side (n := n) C a d)
    (hcf : s c = s f)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C) :
    X.card + Y.card ≤ (orN G C \ lam G C).card := by
  have hx : X ⊆ side (n := n) C a b := fun _ h => (Finset.mem_sdiff.mp (hX h)).1
  have hy : Y ⊆ side (n := n) C a d := fun _ h => (Finset.mem_sdiff.mp (hY h)).1
  have bound (i : Fin 2) : opnd C a i < n + C.gates.length :=
    (opndBound hAO ha i).trans (by omega)
  have hcolorX : ∀ x ∈ X, s x ≠ s f := by
    intro x hx
    have hc := hs c x (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ex x hx)).1)
    exact fun he => hc (hcf.trans he.symm)
  have hcolorY : ∀ y ∈ Y, s y ≠ s c := by
    intro y hy
    have hf := hs f y (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ey y hy)).1)
    exact fun he => hf (hcf.symm.trans he.symm)
  obtain ⟨P,hP,pn,pt⟩ := anchored_star_budget hAO h4 s hs (bound b) hx hf ex hcolorX
  obtain ⟨Q,hQ,qn,qt⟩ := anchored_star_budget hAO h4 s hs (bound d) hy hc ey hcolorY
  have ed : d = 1-b := (eitherOperand b d).resolve_left (Ne.symm hbd)
  have hpq : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro i hiP hiQ
    obtain ⟨x,hx⟩ := (pt i hiP).2
    obtain ⟨hin,hx⟩ := Finset.mem_inter.mp hx
    have hm : x ∈ side (n := n) C a d := orInTrans (qt i hiQ).1 hin
    exact exclusiveDisjoint (hX hx) (ed ▸ hm)
  have cards := Finset.card_le_card (Finset.union_subset hP hQ)
  rw [Finset.card_union_of_disjoint hpq] at cards
  omega

lemma two_stars_union_free (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {c f : Fin n} {X Y : Finset (Fin n)} (hcf : s c ≠ s f)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C)
    (k : ℕ) (hbig : 1 < (orIn n C (n+k) ∩ (X ∪ Y)).card) : k ∉ lam G C := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hbig
  obtain ⟨ha,ha'⟩ := Finset.mem_inter.mp ha
  obtain ⟨hb,hb'⟩ := Finset.mem_inter.mp hb
  have mixed {x y : Fin n} (hx : x ∈ X) (hy : y ∈ Y)
      (hix : x ∈ orIn n C (n+k)) (hiy : y ∈ orIn n C (n+k)) : k ∉ lam G C := by
    intro hk
    have hcx := hs c x (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ex x hx)).1)
    have hfy := hs f y (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ey y hy)).1)
    have hxy := lam_same_color hAO s hs hk hix hiy
    cases hc : s c <;> cases hf : s f <;> cases hx' : s x <;> cases hy' : s y <;> simp_all
  rcases Finset.mem_union.mp ha' with ha' | ha' <;> rcases Finset.mem_union.mp hb' with hb' | hb'
  · exact star_pair_not_lam hAO h4 hab (ex a ha') (ex b hb') ha hb
  · exact mixed ha' hb' ha hb
  · exact mixed hb' ha' hb ha
  · exact star_pair_not_lam hAO h4 hab (ey a ha') (ey b hb') ha hb

lemma mixed_wire_gate (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) {w : ℕ} (hw : w < n+C.gates.length)
    {c f : Fin n} (hc : c ∈ orIn n C w) (hf : f ∈ orIn n C w) (hcf : s c ≠ s f) :
    ∃ k ∈ orN G C \ lam G C, w = n+k := by
  have hn : n ≤ w := by
    by_contra! hlt
    rw [orInRaw hlt] at hc hf
    have ec := Finset.mem_singleton.mp hc
    have ef := Finset.mem_singleton.mp hf
    exact hcf (congrArg s (ec.trans ef.symm))
  let k := w-n
  have he : w=n+k := by dsimp [k]; omega
  have hk : k<C.gates.length := by omega
  have hop : (gateAt C k).op = GateOp.or := by
    rcases hAO.1 _ (gateAt_mem hk) with hand | hor
    · rw [he, orInAnd hand] at hc
      exact (Finset.notMem_empty c hc).elim
    · exact hor
  refine ⟨k, Finset.mem_sdiff.mpr ⟨orNOfRaw hk hop ?_, ?_⟩, he⟩
  · exact ⟨c, he ▸ hc⟩
  · intro hlam
    exact hcf (lam_same_color hAO s hs hlam (he ▸ hc) (he ▸ hf))

lemma opposite_color_same_side_budget (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {a : ℕ} (ha : a < C.gates.length) {b : Fin 2}
    {c f : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ exclusive (n := n) C a b) (hY : Y ⊆ exclusive (n := n) C a b)
    (hc : c ∈ side (n := n) C a (1-b)) (hf : f ∈ side (n := n) C a (1-b))
    (hcf : s c ≠ s f)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C) :
    X.card + Y.card ≤ (orN G C \ lam G C).card := by
  have hXY : X ∪ Y ⊆ exclusive (n := n) C a b := Finset.union_subset hX hY
  have hleaves : X ∪ Y ⊆ side (n := n) C a b := fun _ h => (Finset.mem_sdiff.mp (hXY h)).1
  have bound (i : Fin 2) : opnd C a i < n + C.gates.length :=
    (opndBound hAO ha i).trans (by omega)
  have hdisj : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hcx := hs c x (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ex x hx)).1)
    have hfx := hs f x (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ey x hy)).1)
    cases hc : s c <;> cases hf : s f <;> cases hx' : s x <;> simp_all
  obtain ⟨P,hP,pn,pt⟩ := leafBudget hAO (bound b) hleaves
    (fun k _ hbig => two_stars_union_free hAO h4 s hs hcf ex ey k hbig)
  obtain ⟨k,hk,hkw⟩ := mixed_wire_gate hAO s hs (bound (1-b)) hc hf hcf
  have hkP : k ∉ P := by
    intro hkp
    have hbig := (pt k hkp).2
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < (orIn n C (n+k) ∩ (X ∪ Y)).card)
    obtain ⟨hin,hx⟩ := Finset.mem_inter.mp hx
    have hother : x ∈ side (n := n) C a (1-b) := by
      change x ∈ orIn n C (opnd C a (1-b))
      rw [hkw]
      exact hin
    exact exclusiveDisjoint (hXY hx) hother
  have hsubset : insert k P ⊆ orN G C \ lam G C := Finset.insert_subset hk hP
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_insert_of_notMem hkP] at hcard
  rw [Finset.card_union_of_disjoint hdisj] at pn
  omega

lemma crossed_stars_budget (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {j k : ℕ} (hj : j < C.gates.length) (hk : k < C.gates.length)
    {b d : Fin 2} {c f : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k b)
    (hY : Y ⊆ exclusive (n := n) C j d ∩ exclusive (n := n) C k (1+d))
    (hc : c ∈ exclusive (n := n) C j (1-b) ∩ exclusive (n := n) C k (1-b))
    (hf : f ∈ exclusive (n := n) C j (1-d) ∩ exclusive (n := n) C k d)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C) :
    X.card + Y.card ≤ (orN G C \ lam G C).card := by
  have jx : X ⊆ exclusive (n := n) C j b := fun x hx => (Finset.mem_inter.mp (hX hx)).1
  have jy : Y ⊆ exclusive (n := n) C j d := fun y hy => (Finset.mem_inter.mp (hY hy)).1
  have kx : X ⊆ exclusive (n := n) C k b := fun x hx => (Finset.mem_inter.mp (hX hx)).2
  have ky : Y ⊆ exclusive (n := n) C k (1+d) := fun y hy => (Finset.mem_inter.mp (hY hy)).2
  have jc : c ∈ side (n := n) C j (1-b) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hc).1).1
  have kc : c ∈ side (n := n) C k (1-b) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hc).2).1
  have jf : f ∈ side (n := n) C j (1-d) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hf).1).1
  have kf : f ∈ side (n := n) C k d := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hf).2).1
  fin_cases b <;> fin_cases d
  all_goals norm_num at jx jy kx ky jc kc jf kf
  all_goals
    by_cases hcol : s c = s f
    · first
      | exact anchored_opposite_sides_budget hAO h4 s hs hj (by decide) jx jy jf jc hcol ex ey
      | exact anchored_opposite_sides_budget hAO h4 s hs hk (by decide) kx ky kf kc hcol ex ey
    · first
      | exact opposite_color_same_side_budget hAO h4 s hs hj jx jy jc jf hcol ex ey
      | exact opposite_color_same_side_budget hAO h4 s hs hk kx ky kc kf hcol ex ey

lemma starExtract {A B : Finset (Fin n)} {E : Finset (Sym2 (Fin n))}
    (hE : E ⊆ crossBlock A B) (hne : E.Nonempty) (hB : B.card ≤ 1) :
    ∃ c ∈ B, ∃ X ⊆ A, X.Nonempty ∧ E ⊆ X.image (fun x => s(c,x)) ∧
      ∀ x ∈ X, s(c,x) ∈ E := by
  classical
  obtain ⟨e,he⟩ := hne
  obtain ⟨⟨u,c⟩,huv,_⟩ := Finset.mem_image.mp (hE he)
  have hc := (Finset.mem_product.mp huv).2
  let X := A.filter fun x => s(c,x) ∈ E
  have hSub : E ⊆ X.image (fun x => s(c,x)) := by
    intro f hf
    obtain ⟨⟨x,d⟩,hxd,rfl⟩ := Finset.mem_image.mp (hE hf)
    obtain ⟨hx,hd⟩ := Finset.mem_product.mp hxd
    have eq := Finset.card_le_one.mp hB d hd c hc
    change d = c at eq
    subst d
    rw [Sym2.eq_swap] at hf
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx,hf⟩, Sym2.eq_swap⟩
  have hXne : X.Nonempty := by
    obtain ⟨x,hx,_⟩ := Finset.mem_image.mp (hSub he)
    exact ⟨x,hx⟩
  exact ⟨c,hc,X,Finset.filter_subset _ _,hXne,hSub,fun x hx => (Finset.mem_filter.mp hx).2⟩

lemma blockStarExtract (h4 : NoFourCycle G) {A B : Finset (Fin n)} {E : Finset (Sym2 (Fin n))}
    (hE : E ⊆ crossBlock A B) (hne : E.Nonempty)
    (adj : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v) :
    (∃ c ∈ B, ∃ X ⊆ A, X.Nonempty ∧ E ⊆ X.image (fun x => s(c,x)) ∧ ∀ x ∈ X, s(c,x) ∈ E) ∨
    (∃ c ∈ A, ∃ X ⊆ B, X.Nonempty ∧ E ⊆ X.image (fun x => s(c,x)) ∧ ∀ x ∈ X, s(c,x) ∈ E) := by
  by_cases hB : B.card ≤ 1
  · exact .inl (starExtract hE hne hB)
  · have hA : A.card ≤ 1 := by
      by_contra! h
      obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp h
      exact ne (uniqueCenter h4 (Nat.lt_of_not_ge hB) (adj a ha) (adj b hb))
    exact .inr (starExtract (crossBlock_comm A B ▸ hE) hne hA)

lemma one_star_package {R : Finset (Sym2 (Fin n))} {c : Fin n} {X : Finset (Fin n)}
    {B : ℕ} (hX : X.Nonempty) (hcov : R ⊆ X.image (fun x => s(c,x)))
    (hedge : ∀ x ∈ X, G.Adj c x) (hcost : X.card+1 ≤ B) :
    ∃ (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n)),
      (∀ v ∈ Z, (L v).Nonempty) ∧ (∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u) ∧
      (∀ e ∈ R, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) ∧
      (∑ v ∈ Z, (L v).card) + Z.card ≤ B := by
  refine ⟨{c},fun _ => X,?_,?_,?_,?_⟩
  · intro v hv; exact hX
  · intro v hv u hu
    obtain rfl := Finset.mem_singleton.mp hv
    exact hedge u hu
  · intro e he
    obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp (hcov he)
    exact ⟨c,by simp,x,hx,hxe.symm⟩
  · simpa using hcost

lemma two_star_package {R : Finset (Sym2 (Fin n))} {c f : Fin n} {X Y : Finset (Fin n)}
    {B : ℕ} (hX : X.Nonempty) (hY : Y.Nonempty)
    (hcov : R ⊆ X.image (fun x => s(c,x)) ∪ Y.image (fun y => s(f,y)))
    (ex : ∀ x ∈ X, G.Adj c x) (ey : ∀ y ∈ Y, G.Adj f y)
    (hcost : X.card+Y.card+2 ≤ B) :
    ∃ (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n)),
      (∀ v ∈ Z, (L v).Nonempty) ∧ (∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u) ∧
      (∀ e ∈ R, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) ∧
      (∑ v ∈ Z, (L v).card) + Z.card ≤ B := by
  classical
  by_cases hcf : c = f
  · subst f
    apply one_star_package (X := X ∪ Y) (c := c) (hX.mono Finset.subset_union_left)
    · intro e he
      rcases Finset.mem_union.mp (hcov he) with he | he
      · obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp he
        exact Finset.mem_image.mpr ⟨x,Finset.mem_union_left Y hx,hxe⟩
      · obtain ⟨y,hy,hye⟩ := Finset.mem_image.mp he
        exact Finset.mem_image.mpr ⟨y,Finset.mem_union_right X hy,hye⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact ex x hx
      · exact ey x hx
    · have h := Finset.card_union_le X Y
      omega
  · refine ⟨{c,f},fun v => if v=c then X else Y,?_,?_,?_,?_⟩
    · intro v hv
      by_cases hvc : v=c
      · simpa [hvc] using hX
      · simpa [hvc] using hY
    · intro v hv u hu
      have hv' : v=c ∨ v=f := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hv
      rcases hv' with rfl | rfl
      · exact ex u (by simpa using hu)
      · exact ey u (by simpa [Ne.symm hcf] using hu)
    · intro e he
      rcases Finset.mem_union.mp (hcov he) with he | he
      · obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp he
        exact ⟨c,by simp,x,by simpa using hx,hxe.symm⟩
      · obtain ⟨y,hy,hye⟩ := Finset.mem_image.mp he
        exact ⟨f,by simp,y,by simpa [Ne.symm hcf] using hy,hye.symm⟩
    · simpa [hcf,Ne.symm hcf] using hcost

lemma residual_star_cover (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hTwo : (junk G C).card = 2) :
    ∃ (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n)),
      (∀ v ∈ Z, (L v).Nonempty) ∧ (∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u) ∧
      (∀ e ∈ Ustar G C \ coveredByJunk G C, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) ∧
      (∑ v ∈ Z, (L v).card) + Z.card ≤ (orN G C \ lam G C).card + 2 := by
  classical
  let R := Ustar G C \ coveredByJunk G C
  by_cases hR : R.Nonempty
  · obtain ⟨j,k,_,hs⟩ := Finset.card_eq_two.mp hTwo
    have hj : j ∈ junk G C := by simp [hs]
    have hk : k ∈ junk G C := by simp [hs]
    have sk : junk G C = {k,j} := hs.trans (Finset.pair_comm _ _)
    obtain ⟨edge,he⟩ := hR
    induction edge using Sym2.ind with
    | h u v =>
      have joint := (residualJoint hL hT hs he).1
      let A (r : Fin 2) := exclusive (n := n) C j 0 ∩ exclusive (n := n) C k r
      let B (r : Fin 2) := exclusive (n := n) C j 1 ∩ exclusive (n := n) C k (1-r)
      let E (r : Fin 2) := R ∩ crossBlock (A r) (B r)
      have adj (r : Fin 2) (x : Fin n) (hx : x ∈ A r) (y : Fin n) (hy : y ∈ B r) :
          G.Adj x y := by
        have jx := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).1).1
        have jy := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).1).1
        have kx := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
        have ky := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).2).1
        obtain ⟨jl,jo,_⟩ := junkData hj
        obtain ⟨kl,ko,_⟩ := junkData hk
        apply (graphFun_pair G x y).mp
        apply joint
        · exact andFromInputs hL.1 jl jo jx jy (pairInput_left x y) (pairInput_right x y)
        · fin_cases r
          · exact andFromInputs hL.1 kl ko kx ky (pairInput_left x y) (pairInput_right x y)
          · exact andFromInputs hL.1 kl ko ky kx (pairInput_right x y) (pairInput_left x y)
      have star (r : Fin 2) (hn : (E r).Nonempty) :
          ∃ (b : Fin 2) (c : Fin n) (X : Finset (Fin n)),
          c ∈ exclusive (n := n) C j (1-b) ∩ exclusive (n := n) C k (1-(r+b)) ∧
          X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k (r+b) ∧
          X.Nonempty ∧ (E r) ⊆ X.image (fun x => s(c,x)) ∧ ∀ x ∈ X, s(c,x) ∈ Ustar G C := by
        rcases blockStarExtract h4 (E := E r) Finset.inter_subset_right hn (adj r) with
          ⟨c,hc,X,hX,hne,hcov,h⟩ | ⟨c,hc,X,hX,hne,hcov,h⟩
        · refine ⟨0,c,X,?_,?_,hne,hcov,fun x hx => (Finset.mem_sdiff.mp (Finset.mem_inter.mp (h x hx)).1).1⟩
          · simpa [B] using hc
          · simpa [A] using hX
        · refine ⟨1,c,X,?_,?_,hne,hcov,fun x hx => (Finset.mem_sdiff.mp (Finset.mem_inter.mp (h x hx)).1).1⟩
          · fin_cases r <;> simpa [A] using hc
          · simpa [B,oppositeAddOne] using hX
      have cover : R ⊆ E 0 ∪ E 1 := by
        intro e h
        induction e using Sym2.ind with
        | h x y =>
          obtain ⟨joint,hjv,hkv⟩ := residualJoint hL hT hs h
          have hL' := junkOrientation hL.1 hT hs joint h hjv hkv
          have hR' := junkOrientation hL.1 hT sk (joint_comm joint) h hkv hjv
          have put (p q : Fin n) (r : Fin 2) (hp : p ∈ A r) (hq : q ∈ B r)
              (eq : s(p,q) = s(x,y)) : s(x,y) ∈ E r :=
            Finset.mem_inter.mpr ⟨h, Finset.mem_image.mpr
              ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,eq⟩⟩
          apply Finset.mem_union.mpr
          rcases hL' with ⟨l,r⟩ | ⟨l,r⟩ <;> rcases hR' with ⟨l',r'⟩ | ⟨l',r'⟩
          · exact .inl (put x y 0 (Finset.mem_inter.mpr ⟨l,l'⟩)
              (Finset.mem_inter.mpr ⟨r,r'⟩) rfl)
          · exact .inr (put x y 1 (Finset.mem_inter.mpr ⟨l,r'⟩)
              (Finset.mem_inter.mpr ⟨r,l'⟩) rfl)
          · exact .inr (put y x 1 (Finset.mem_inter.mpr ⟨l,r'⟩)
              (Finset.mem_inter.mpr ⟨r,l'⟩) Sym2.eq_swap)
          · exact .inl (put y x 0 (Finset.mem_inter.mpr ⟨l,l'⟩)
              (Finset.mem_inter.mpr ⟨r,r'⟩) Sym2.eq_swap)
      have single_budget {r : Fin 2} {b : Fin 2} {c : Fin n} {X : Finset (Fin n)}
          (hX : X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k (r+b))
          (hex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) : X.card+1 ≤ (orN G C \ lam G C).card+2 := by
        have hroot := (opndBound hL.1 (junkData hj).1 b).trans (Nat.add_lt_add_left (junkData hj).1 n)
        have hside : X ⊆ side (n := n) C j b := fun x hx =>
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp (hX hx)).1).1
        obtain ⟨P,hP,hcount,_⟩ := starLeafBudget hL.1 h4 hroot hside hex
        have hp := Finset.card_le_card hP
        omega
      by_cases h0 : (E 0).Nonempty
      · obtain ⟨b,c,X,hc,hX,hXne,hcovX,hex⟩ := star 0 h0
        by_cases h1 : (E 1).Nonempty
        · obtain ⟨d,f,Y,hf,hY,hYne,hcovY,hey⟩ := star 1 h1
          have hx' : X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k b := by simpa using hX
          have hc' : c ∈ exclusive (n := n) C j (1-b) ∩ exclusive (n := n) C k (1-b) := by simpa using hc
          have hf' : f ∈ exclusive (n := n) C j (1-d) ∩ exclusive (n := n) C k d := by
            fin_cases d <;> simpa using hf
          have hcost := crossed_stars_budget hL.1 h4 s hbip (junkData hj).1 (junkData hk).1 hx' hY hc' hf' hex hey
          apply two_star_package hXne hYne
          · exact cover.trans (Finset.union_subset_union hcovX hcovY)
          · exact fun x hx => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hex x hx)).1
          · exact fun y hy => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hey y hy)).1
          · omega
        · have he1 := Finset.not_nonempty_iff_eq_empty.mp h1
          have cov : R ⊆ X.image (fun x => s(c,x)) := by
            have he : R ⊆ E 0 := by simpa [he1] using cover
            exact he.trans hcovX
          exact one_star_package hXne cov
            (fun x hx => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hex x hx)).1)
            (single_budget hX hex)
      · have he0 := Finset.not_nonempty_iff_eq_empty.mp h0
        have he1 : (E 1).Nonempty := by
          have hsub : R ⊆ E 1 := by simpa [he0] using cover
          exact ⟨s(u,v),hsub he⟩
        obtain ⟨d,f,Y,hf,hY,hYne,hcovY,hey⟩ := star 1 he1
        have cov : R ⊆ Y.image (fun y => s(f,y)) := by
          have he : R ⊆ E 1 := by simpa [he0] using cover
          exact he.trans hcovY
        exact one_star_package hYne cov
          (fun y hy => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hey y hy)).1)
          (single_budget hY hey)
  · refine ⟨∅,fun _ => ∅,by simp,by simp,?_,by simp⟩
    intro e he
    exact (hR ⟨e,he⟩).elim

lemma empty_wmax_centerless (hL : IsLeastAO G C) (hT : TopForm G C)
    (hw : ∀ j ∈ junk G C, wmax G C j = ∅) (hU : (Ustar G C).Nonempty) :
    (centreless G C).Nonempty := by
  obtain ⟨e,he⟩ := hU
  induction e using Sym2.ind with
  | h u v =>
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
    obtain ⟨a,ha,hv⟩ := acceptedTop hL hadj
    obtain ⟨hl,ho,hb⟩ := topData ha
    have traces (b : Fin 2) := operandSupport hL.1 hT hl ho
      ((andValOperands hL.1 hl ho (pairInput u v)).mp hv b)
    have empty_side {g : ℕ} {b : Fin 2} (hg : g ∈ junk G C)
        (hr : OrReaches n C (opnd C a b) g) : side (n := n) C a (1-b) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hm := oppositeSideWmax hL.1 ha hr hx
      rw [hw g hg] at hm
      exact Finset.notMem_empty x hm
    rcases traces 0 with ⟨x,hx,hxe⟩ | ⟨g,hg,hrg,hvg⟩
    · rcases traces 1 with ⟨y,hy,hye⟩ | ⟨g,hg,hrg,hvg⟩
      · have hxy := G.ne_of_adj (topAdj hL.1 ha hx hy)
        have eq : s(u,v) = s(x,y) := by
          rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
          · exact (hxy rfl).elim
          · rfl
          · exact Sym2.eq_swap
          · exact (hxy rfl).elim
        exact ((Finset.mem_sdiff.mp he).2 (eq ▸ Finset.mem_biUnion.mpr ⟨a,ha,
          Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,rfl⟩⟩)).elim
      · refine ⟨a,Finset.mem_filter.mpr ⟨ha,Or.inl ?_⟩⟩
        simpa using empty_side hg hrg
    · refine ⟨a,Finset.mem_filter.mpr ⟨ha,Or.inr ?_⟩⟩
      simpa using empty_side hg hrg

lemma empty_wmax_star_cover (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hTwo : (junk G C).card = 2)
    (hw : ∀ j ∈ junk G C, wmax G C j = ∅) :
    ∃ (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n)),
      (∀ v ∈ Z, (L v).Nonempty) ∧ (∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u) ∧
      (∀ e ∈ Ustar G C, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) ∧
      (∑ v ∈ Z, (L v).card) + Z.card ≤ (orN G C \ lam G C).card + 2 := by
  have h := residual_star_cover s hbip h4 hL hT hTwo
  rw [coveredByJunk_empty hw, Finset.sdiff_empty] at h
  exact h

lemma branchLeafBudget (hAO : IsAO2 n C) {X : Finset (Fin n)} {w : ℕ}
    (hw : w < n+C.gates.length) (hX : X ⊆ orIn n C w) (F : Finset ℕ)
    (hcharge : ∀ k, k < C.gates.length → 1 < (orIn n C (n+k) ∩ X).card →
      (orIn n C (opnd C k 0) ∩ X).Nonempty →
      (orIn n C (opnd C k 1) ∩ X).Nonempty → k ∈ F) :
    ∃ P ⊆ F, X.card ≤ P.card+1 ∧ ∀ k ∈ P,
      Relation.ReflTransGen (OrStep n C) w (n+k) ∧
      1 < (orIn n C (n+k) ∩ X).card ∧
      (orIn n C (opnd C k 0) ∩ X).Nonempty ∧
      (orIn n C (opnd C k 1) ∩ X).Nonempty := by
  classical
  by_cases hxne : X.Nonempty
  swap
  · refine ⟨∅,by simp,?_,by simp⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hxne]
    simp
  let cone := relevantCone n C X w
  let nz (z : ℕ) := (orIn n C z ∩ X).Nonempty
  let active := cone.filter nz
  let big (z : ℕ) := 1 < (orIn n C z ∩ X).card
  let internal := cone.filter big
  let branching := internal.filter (fun z => nz (opnd C (z-n) 0) ∧ nz (opnd C (z-n) 1))
  let frontier := active \ internal
  let children (z : ℕ) := ({opnd C (z-n) 0,opnd C (z-n) 1} : Finset ℕ).filter nz
  have rootIncluded : ({w} : Finset ℕ) ⊆ active := by
    intro z hz
    obtain rfl := Finset.mem_singleton.mp hz
    refine Finset.mem_filter.mpr ⟨relevantMem.mpr .refl,?_⟩
    obtain ⟨x,hx⟩ := hxne
    exact ⟨x,Finset.mem_inter.mpr ⟨hX hx,hx⟩⟩
  have internalIncluded : internal ⊆ active := by
    intro z hz
    obtain ⟨hz,hbig⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨hz,?_⟩
    exact Finset.card_pos.mp (by change 1 < (orIn n C z ∩ X).card at hbig; omega)
  have branchingIncluded : branching ⊆ internal := Finset.filter_subset _ _
  have childCoverage : active \ {w} ⊆ internal.biUnion children := by
    intro y hy
    obtain ⟨hy,notRoot⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨cy,ny⟩ := Finset.mem_filter.mp hy
    rcases Relation.ReflTransGen.cases_tail (relevantMem.mp cy) with same | ⟨z,reach,last⟩
    · exact (notRoot (by simp [same])).elim
    · obtain ⟨i,hi,eq,_,input,_⟩ := last.1
      have zm : z ∈ internal := Finset.mem_filter.mpr ⟨relevantMem.mpr reach,last.2⟩
      refine Finset.mem_biUnion.mpr ⟨z,zm,Finset.mem_filter.mpr ⟨?_,ny⟩⟩
      obtain ⟨b,hb⟩ := inputsAsOpnd hAO hi input
      have ezi : z-n=i := by omega
      rw [ezi,hb]
      fin_cases b <;> simp
  have childCount (z : ℕ) (hz : z ∈ internal) :
      (children z).card ≤ 1 + if z ∈ branching then 1 else 0 := by
    by_cases hb : z ∈ branching
    · rw [ite_eq_left hb]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
        ((Finset.card_insert_le _ _).trans (by simp))
    · rw [ite_eq_right hb]
      have hnot : ¬ (nz (opnd C (z-n) 0) ∧ nz (opnd C (z-n) 1)) :=
        fun hh => hb (Finset.mem_filter.mpr ⟨hz,hh⟩)
      by_cases h0 : nz (opnd C (z-n) 0)
      · have h1 : ¬ nz (opnd C (z-n) 1) := fun h => hnot ⟨h0,h⟩
        have hsub : children z ⊆ {opnd C (z-n) 0} := by
          intro u hu
          obtain ⟨hu,hnz⟩ := Finset.mem_filter.mp hu
          have hu' : u=opnd C (z-n) 0 ∨ u=opnd C (z-n) 1 := by simpa using hu
          rcases hu' with rfl | rfl
          · simp
          · exact (h1 hnz).elim
        exact (Finset.card_le_card hsub).trans_eq (by simp)
      · have hsub : children z ⊆ {opnd C (z-n) 1} := by
          intro u hu
          obtain ⟨hu,hnz⟩ := Finset.mem_filter.mp hu
          have hu' : u=opnd C (z-n) 0 ∨ u=opnd C (z-n) 1 := by simpa using hu
          rcases hu' with rfl | rfl
          · exact (h0 hnz).elim
          · simp
        exact (Finset.card_le_card hsub).trans_eq (by simp)
  have branchCount : (internal.biUnion children).card ≤ internal.card+branching.card := by
    have hf : internal.filter (fun z => z ∈ branching) = branching := by
      ext z
      simp only [Finset.mem_filter]
      exact ⟨And.right,fun hz => ⟨branchingIncluded hz,hz⟩⟩
    calc
      (internal.biUnion children).card ≤ ∑ z ∈ internal, (children z).card := Finset.card_biUnion_le
      _ ≤ ∑ z ∈ internal, (1 + if z ∈ branching then 1 else 0 : ℕ) := Finset.sum_le_sum childCount
      _ = internal.card+branching.card := by simp [Finset.sum_add_distrib, Finset.inter_eq_right.mpr branchingIncluded]
  have frontierCard : frontier.card ≤ branching.card+1 := by
    have h0 := (Finset.card_le_card childCoverage).trans branchCount
    have h1 := Finset.card_sdiff_add_card_eq_card rootIncluded
    have h2 := Finset.card_sdiff_add_card_eq_card internalIncluded
    rw [Finset.card_singleton] at h1
    change (active \ internal).card ≤ branching.card+1
    omega
  have traceWire (z : ℕ) (hz : z ∈ internal) : Relation.ReflTransGen (OrStep n C) w z :=
    relevantImpliesOr (relevantMem.mp (Finset.mem_filter.mp hz).1)
  have nle (z : ℕ) (hz : z ∈ internal) : n ≤ z := by
    by_contra! small
    have h := (Finset.mem_filter.mp hz).2
    change 1 < (orIn n C z ∩ X).card at h
    rw [orInRaw small] at h
    have le := Finset.card_le_card (Finset.inter_subset_left :
      ({⟨z,small⟩} : Finset (Fin n)) ∩ X ⊆ {⟨z,small⟩})
    rw [Finset.card_singleton] at le
    omega
  let P := branching.image (fun z => z-n)
  have pCount : P.card = branching.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy e
    have xN := nle x (branchingIncluded hx)
    have yN := nle y (branchingIncluded hy)
    change x-n=y-n at e
    omega
  have subP : P ⊆ F := by
    intro k hk
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    have hi := branchingIncluded hz
    have nz := nle z hi
    have eq : n+(z-n)=z := by omega
    have below := orStep_le (traceWire z hi)
    have hkl : z-n<C.gates.length := by omega
    have hbig : 1 < (orIn n C (n+(z-n)) ∩ X).card := by
      rw [eq]
      exact (Finset.mem_filter.mp hi).2
    exact hcharge (z-n) hkl hbig (Finset.mem_filter.mp hz).2.1 (Finset.mem_filter.mp hz).2.2
  have trace (k : ℕ) (hk : k ∈ P) :
      Relation.ReflTransGen (OrStep n C) w (n+k) ∧
      1 < (orIn n C (n+k) ∩ X).card ∧
      (orIn n C (opnd C k 0) ∩ X).Nonempty ∧
      (orIn n C (opnd C k 1) ∩ X).Nonempty := by
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hk
    have hi := branchingIncluded hz
    have hn := nle z hi
    have eq : n+(z-n)=z := by omega
    rw [eq]
    exact ⟨traceWire z hi,(Finset.mem_filter.mp hi).2,(Finset.mem_filter.mp hz).2⟩
  let leaves (z : ℕ) := orIn n C z ∩ X
  have coverage : X ⊆ frontier.biUnion leaves := by
    intro x hx
    obtain ⟨z,zr,small,xz⟩ := relevantBoundary (X := X) (mem_orIn_reach x (hX hx))
    refine Finset.mem_biUnion.mpr ⟨z,?_,Finset.mem_inter.mpr ⟨xz,hx⟩⟩
    have mz : z ∈ active := Finset.mem_filter.mpr ⟨relevantMem.mpr zr,⟨x,Finset.mem_inter.mpr ⟨xz,hx⟩⟩⟩
    exact Finset.mem_sdiff.mpr ⟨mz,fun bad => (Nat.not_le_of_lt (Finset.mem_filter.mp bad).2) small⟩
  have leafOne : ∀ z ∈ frontier, (leaves z).card ≤ 1 := by
    intro z hz
    obtain ⟨atActive,notInt⟩ := Finset.mem_sdiff.mp hz
    have atCone := (Finset.mem_filter.mp atActive).1
    exact Nat.le_of_not_gt (fun h => notInt (Finset.mem_filter.mpr ⟨atCone,h⟩))
  refine ⟨P,subP,?_,trace⟩
  calc
    X.card ≤ (frontier.biUnion leaves).card := Finset.card_le_card coverage
    _ ≤ ∑ v ∈ frontier, (leaves v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ frontier, (1 : ℕ) := Finset.sum_le_sum leafOne
    _ = frontier.card := by simp
    _ ≤ branching.card+1 := frontierCard
    _ = P.card+1 := by rw [pCount]

noncomputable def splitExtra (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Finset ℕ := by
  classical
  exact (orN G C \ lam G C).filter (fun k =>
    (orIn n C (opnd C k 0)).Nonempty ∧ (orIn n C (opnd C k 1)).Nonempty)

lemma leafBudgetSplit (hAO : IsAO2 n C) {X : Finset (Fin n)} {w : ℕ}
    (hw : w < n+C.gates.length) (hX : X ⊆ orIn n C w)
    (hfree : ∀ k, k < C.gates.length → 1 < (orIn n C (n+k) ∩ X).card → k ∉ lam G C) :
    ∃ P ⊆ splitExtra G C, X.card ≤ P.card+1 ∧
      ∀ k ∈ P, Relation.ReflTransGen (OrStep n C) w (n+k) ∧
        1 < (orIn n C (n+k) ∩ X).card := by
  obtain ⟨P,hP,hcount,htrace⟩ := branchLeafBudget hAO hw hX (splitExtra G C) (by
    intro k hk hbig h0 h1
    have hop : (gateAt C k).op = GateOp.or := by
      rcases hAO.1 _ (gateAt_mem hk) with hand | hor
      · rw [orInAnd hand,Finset.empty_inter,Finset.card_empty] at hbig
        omega
      · exact hor
    have raw : (orIn n C (n+k)).Nonempty :=
      (Finset.card_pos.mp (by omega : 0 < (orIn n C (n+k) ∩ X).card)).mono Finset.inter_subset_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨orNOfRaw hk hop raw,hfree k hk hbig⟩,
      h0.mono Finset.inter_subset_left,h1.mono Finset.inter_subset_left⟩)
  exact ⟨P,hP,hcount,fun k hk => ⟨(htrace k hk).1,(htrace k hk).2.1⟩⟩

lemma starLeafBudgetSplit (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {c : Fin n} {X : Finset (Fin n)} {w : ℕ} (hw : w < n+C.gates.length)
    (hX : X ⊆ orIn n C w) (hedge : ∀ x ∈ X, s(c,x) ∈ Ustar G C) :
    ∃ P ⊆ splitExtra G C, X.card ≤ P.card+1 ∧
      ∀ k ∈ P, Relation.ReflTransGen (OrStep n C) w (n+k) ∧
        (orIn n C (n+k) ∩ X).Nonempty := by
  obtain ⟨P,hP,hcount,htrace⟩ := leafBudgetSplit hAO hw hX (by
    intro k hk hbig
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hbig
    obtain ⟨ha,hXa⟩ := Finset.mem_inter.mp ha
    obtain ⟨hb,hXb⟩ := Finset.mem_inter.mp hb
    exact star_pair_not_lam hAO h4 hab (hedge a hXa) (hedge b hXb) ha hb)
  exact ⟨P,hP,hcount,fun k hk => ⟨(htrace k hk).1,Finset.card_pos.mp (by have := (htrace k hk).2; omega)⟩⟩

lemma mixed_wire_branch (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) {w : ℕ} (hw : w < n+C.gates.length)
    {c f : Fin n} (hc : c ∈ orIn n C w) (hf : f ∈ orIn n C w) (hcf : s c ≠ s f) :
    ∃ k ∈ splitExtra G C, Relation.ReflTransGen (OrStep n C) w (n+k) := by
  have hne : c ≠ f := fun h => hcf (congrArg s h)
  have hsub : ({c,f} : Finset (Fin n)) ⊆ orIn n C w := by
    intro x hx
    have hx' : x=c ∨ x=f := by simpa using hx
    rcases hx' with rfl | rfl
    · exact hc
    · exact hf
  obtain ⟨P,hP,hcount,htrace⟩ := leafBudgetSplit hAO hw hsub (by
    intro k hk hbig hlam
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hbig
    obtain ⟨hIa,hXa⟩ := Finset.mem_inter.mp ha
    obtain ⟨hIb,hXb⟩ := Finset.mem_inter.mp hb
    have he := lam_same_color hAO s hs hlam hIa hIb
    have ha' : a=c ∨ a=f := by simpa using hXa
    have hb' : b=c ∨ b=f := by simpa using hXb
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact hab (ha'.trans hb'.symm)
    · exact hcf ((congrArg s ha').symm.trans (he.trans (congrArg s hb')))
    · exact hcf ((congrArg s hb').symm.trans (he.symm.trans (congrArg s ha')))
    · exact hab (ha'.trans hb'.symm))
  have hp : P.Nonempty := by
    simp only [Finset.card_pair hne] at hcount
    exact Finset.card_pos.mp (by omega)
  obtain ⟨k,hk⟩ := hp
  exact ⟨k,hP hk,(htrace k hk).1⟩

lemma mixing_not_splitExtra {k : ℕ}
    (hk : orIn n C (opnd C k 0) = ∅ ∨ orIn n C (opnd C k 1) = ∅) :
    k ∉ splitExtra G C := by
  intro hm
  have hh := (Finset.mem_filter.mp hm).2
  rcases hk with h0 | h1
  · exact hh.1.ne_empty h0
  · exact hh.2.ne_empty h1

lemma anchored_star_budgetSplit (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {c z : Fin n} {X : Finset (Fin n)} {w : ℕ} (hw : w < n + C.gates.length)
    (hX : X ⊆ orIn n C w) (hz : z ∈ orIn n C w)
    (hedge : ∀ x ∈ X, s(c,x) ∈ Ustar G C)
    (hcolor : ∀ x ∈ X, s x ≠ s z) :
    ∃ P ⊆ splitExtra G C, X.card ≤ P.card ∧
      ∀ i ∈ P, Relation.ReflTransGen (OrStep n C) w (n+i) ∧
        (orIn n C (n+i) ∩ X).Nonempty := by
  have hzX : z ∉ X := fun h => hcolor z h rfl
  obtain ⟨P,hP,hcount,htrace⟩ := leafBudgetSplit hAO hw
    (Finset.insert_subset hz hX)
    (fun k _ hbig => anchored_star_free hAO h4 s hs hedge hcolor k hbig)
  refine ⟨P,hP,?_,?_⟩
  · rw [Finset.card_insert_of_notMem hzX] at hcount
    omega
  · intro k hk
    exact ⟨(htrace k hk).1, insert_big_has_leaf (htrace k hk).2⟩


lemma anchored_opposite_sides_budgetSplit (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {a : ℕ} (ha : a < C.gates.length) {b d : Fin 2} (hbd : b ≠ d)
    {c f : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ exclusive (n := n) C a b) (hY : Y ⊆ exclusive (n := n) C a d)
    (hf : f ∈ side (n := n) C a b) (hc : c ∈ side (n := n) C a d)
    (hcf : s c = s f)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C) :
    X.card + Y.card ≤ (splitExtra G C).card := by
  have hx : X ⊆ side (n := n) C a b := fun _ h => (Finset.mem_sdiff.mp (hX h)).1
  have hy : Y ⊆ side (n := n) C a d := fun _ h => (Finset.mem_sdiff.mp (hY h)).1
  have bound (i : Fin 2) : opnd C a i < n + C.gates.length :=
    (opndBound hAO ha i).trans (by omega)
  have hcolorX : ∀ x ∈ X, s x ≠ s f := by
    intro x hx
    have hc := hs c x (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ex x hx)).1)
    exact fun he => hc (hcf.trans he.symm)
  have hcolorY : ∀ y ∈ Y, s y ≠ s c := by
    intro y hy
    have hf := hs f y (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ey y hy)).1)
    exact fun he => hf (hcf.symm.trans he.symm)
  obtain ⟨P,hP,pn,pt⟩ := anchored_star_budgetSplit hAO h4 s hs (bound b) hx hf ex hcolorX
  obtain ⟨Q,hQ,qn,qt⟩ := anchored_star_budgetSplit hAO h4 s hs (bound d) hy hc ey hcolorY
  have ed : d = 1-b := (eitherOperand b d).resolve_left (Ne.symm hbd)
  have hpq : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro i hiP hiQ
    obtain ⟨x,hx⟩ := (pt i hiP).2
    obtain ⟨hin,hx⟩ := Finset.mem_inter.mp hx
    have hm : x ∈ side (n := n) C a d := orInTrans (qt i hiQ).1 hin
    exact exclusiveDisjoint (hX hx) (ed ▸ hm)
  have cards := Finset.card_le_card (Finset.union_subset hP hQ)
  rw [Finset.card_union_of_disjoint hpq] at cards
  omega


lemma opposite_color_same_side_budgetSplit (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {a : ℕ} (ha : a < C.gates.length) {b : Fin 2}
    {c f : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ exclusive (n := n) C a b) (hY : Y ⊆ exclusive (n := n) C a b)
    (hc : c ∈ side (n := n) C a (1-b)) (hf : f ∈ side (n := n) C a (1-b))
    (hcf : s c ≠ s f)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C) :
    X.card + Y.card ≤ (splitExtra G C).card := by
  have hXY : X ∪ Y ⊆ exclusive (n := n) C a b := Finset.union_subset hX hY
  have hleaves : X ∪ Y ⊆ side (n := n) C a b := fun _ h => (Finset.mem_sdiff.mp (hXY h)).1
  have bound (i : Fin 2) : opnd C a i < n + C.gates.length :=
    (opndBound hAO ha i).trans (by omega)
  have hdisj : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hcx := hs c x (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ex x hx)).1)
    have hfx := hs f x (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (ey x hy)).1)
    cases hc : s c <;> cases hf : s f <;> cases hx' : s x <;> simp_all
  obtain ⟨P,hP,pn,pt⟩ := leafBudgetSplit hAO (bound b) hleaves
    (fun k _ hbig => two_stars_union_free hAO h4 s hs hcf ex ey k hbig)
  obtain ⟨k,hk,hkw⟩ := mixed_wire_branch hAO s hs (bound (1-b)) hc hf hcf
  have hkP : k ∉ P := by
    intro hkp
    have hbig := (pt k hkp).2
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < (orIn n C (n+k) ∩ (X ∪ Y)).card)
    obtain ⟨hin,hx⟩ := Finset.mem_inter.mp hx
    have hother : x ∈ side (n := n) C a (1-b) := orInTrans hkw hin
    exact exclusiveDisjoint (hXY hx) hother
  have hsubset : insert k P ⊆ splitExtra G C := Finset.insert_subset hk hP
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_insert_of_notMem hkP] at hcard
  rw [Finset.card_union_of_disjoint hdisj] at pn
  omega


lemma crossed_stars_budgetSplit (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {j k : ℕ} (hj : j < C.gates.length) (hk : k < C.gates.length)
    {b d : Fin 2} {c f : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k b)
    (hY : Y ⊆ exclusive (n := n) C j d ∩ exclusive (n := n) C k (1+d))
    (hc : c ∈ exclusive (n := n) C j (1-b) ∩ exclusive (n := n) C k (1-b))
    (hf : f ∈ exclusive (n := n) C j (1-d) ∩ exclusive (n := n) C k d)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C) :
    X.card + Y.card ≤ (splitExtra G C).card := by
  have jx : X ⊆ exclusive (n := n) C j b := fun x hx => (Finset.mem_inter.mp (hX hx)).1
  have jy : Y ⊆ exclusive (n := n) C j d := fun y hy => (Finset.mem_inter.mp (hY hy)).1
  have kx : X ⊆ exclusive (n := n) C k b := fun x hx => (Finset.mem_inter.mp (hX hx)).2
  have ky : Y ⊆ exclusive (n := n) C k (1+d) := fun y hy => (Finset.mem_inter.mp (hY hy)).2
  have jc : c ∈ side (n := n) C j (1-b) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hc).1).1
  have kc : c ∈ side (n := n) C k (1-b) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hc).2).1
  have jf : f ∈ side (n := n) C j (1-d) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hf).1).1
  have kf : f ∈ side (n := n) C k d := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hf).2).1
  fin_cases b <;> fin_cases d
  all_goals norm_num at jx jy kx ky jc kc jf kf
  all_goals
    by_cases hcol : s c = s f
    · first
      | exact anchored_opposite_sides_budgetSplit hAO h4 s hs hj (by decide) jx jy jf jc hcol ex ey
      | exact anchored_opposite_sides_budgetSplit hAO h4 s hs hk (by decide) kx ky kf kc hcol ex ey
    · first
      | exact opposite_color_same_side_budgetSplit hAO h4 s hs hj jx jy jc jf hcol ex ey
      | exact opposite_color_same_side_budgetSplit hAO h4 s hs hk kx ky kc kf hcol ex ey


lemma residual_star_coverSplit (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hTwo : (junk G C).card = 2) :
    ∃ (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n)),
      (∀ v ∈ Z, (L v).Nonempty) ∧ (∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u) ∧
      (∀ e ∈ Ustar G C \ coveredByJunk G C, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) ∧
      (∑ v ∈ Z, (L v).card) + Z.card ≤ (splitExtra G C).card + 2 := by
  classical
  let R := Ustar G C \ coveredByJunk G C
  by_cases hR : R.Nonempty
  · obtain ⟨j,k,_,hs⟩ := Finset.card_eq_two.mp hTwo
    have hj : j ∈ junk G C := by simp [hs]
    have hk : k ∈ junk G C := by simp [hs]
    have sk : junk G C = {k,j} := hs.trans (Finset.pair_comm _ _)
    obtain ⟨edge,he⟩ := hR
    induction edge using Sym2.ind with
    | h u v =>
      have joint := (residualJoint hL hT hs he).1
      let A (r : Fin 2) := exclusive (n := n) C j 0 ∩ exclusive (n := n) C k r
      let B (r : Fin 2) := exclusive (n := n) C j 1 ∩ exclusive (n := n) C k (1-r)
      let E (r : Fin 2) := R ∩ crossBlock (A r) (B r)
      have adj (r : Fin 2) (x : Fin n) (hx : x ∈ A r) (y : Fin n) (hy : y ∈ B r) :
          G.Adj x y := by
        have jx := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).1).1
        have jy := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).1).1
        have kx := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).2).1
        have ky := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).2).1
        obtain ⟨jl,jo,_⟩ := junkData hj
        obtain ⟨kl,ko,_⟩ := junkData hk
        apply (graphFun_pair G x y).mp
        apply joint
        · exact andFromInputs hL.1 jl jo jx jy (pairInput_left x y) (pairInput_right x y)
        · fin_cases r
          · exact andFromInputs hL.1 kl ko kx ky (pairInput_left x y) (pairInput_right x y)
          · exact andFromInputs hL.1 kl ko ky kx (pairInput_right x y) (pairInput_left x y)
      have star (r : Fin 2) (hn : (E r).Nonempty) :
          ∃ (b : Fin 2) (c : Fin n) (X : Finset (Fin n)),
          c ∈ exclusive (n := n) C j (1-b) ∩ exclusive (n := n) C k (1-(r+b)) ∧
          X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k (r+b) ∧
          X.Nonempty ∧ (E r) ⊆ X.image (fun x => s(c,x)) ∧ ∀ x ∈ X, s(c,x) ∈ Ustar G C := by
        rcases blockStarExtract h4 (E := E r) Finset.inter_subset_right hn (adj r) with
          ⟨c,hc,X,hX,hne,hcov,h⟩ | ⟨c,hc,X,hX,hne,hcov,h⟩
        · refine ⟨0,c,X,?_,?_,hne,hcov,fun x hx => (Finset.mem_sdiff.mp (Finset.mem_inter.mp (h x hx)).1).1⟩
          · simpa [B] using hc
          · simpa [A] using hX
        · refine ⟨1,c,X,?_,?_,hne,hcov,fun x hx => (Finset.mem_sdiff.mp (Finset.mem_inter.mp (h x hx)).1).1⟩
          · fin_cases r <;> simpa [A] using hc
          · simpa [B,oppositeAddOne] using hX
      have cover : R ⊆ E 0 ∪ E 1 := by
        intro e h
        induction e using Sym2.ind with
        | h x y =>
          obtain ⟨joint,hjv,hkv⟩ := residualJoint hL hT hs h
          have hL' := junkOrientation hL.1 hT hs joint h hjv hkv
          have hR' := junkOrientation hL.1 hT sk (joint_comm joint) h hkv hjv
          have put (p q : Fin n) (r : Fin 2) (hp : p ∈ A r) (hq : q ∈ B r)
              (eq : s(p,q) = s(x,y)) : s(x,y) ∈ E r :=
            Finset.mem_inter.mpr ⟨h, Finset.mem_image.mpr
              ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,eq⟩⟩
          apply Finset.mem_union.mpr
          rcases hL' with ⟨l,r⟩ | ⟨l,r⟩ <;> rcases hR' with ⟨l',r'⟩ | ⟨l',r'⟩
          · exact .inl (put x y 0 (Finset.mem_inter.mpr ⟨l,l'⟩)
              (Finset.mem_inter.mpr ⟨r,r'⟩) rfl)
          · exact .inr (put x y 1 (Finset.mem_inter.mpr ⟨l,r'⟩)
              (Finset.mem_inter.mpr ⟨r,l'⟩) rfl)
          · exact .inr (put y x 1 (Finset.mem_inter.mpr ⟨l,r'⟩)
              (Finset.mem_inter.mpr ⟨r,l'⟩) Sym2.eq_swap)
          · exact .inl (put y x 0 (Finset.mem_inter.mpr ⟨l,l'⟩)
              (Finset.mem_inter.mpr ⟨r,r'⟩) Sym2.eq_swap)
      have single_budget {r : Fin 2} {b : Fin 2} {c : Fin n} {X : Finset (Fin n)}
          (hX : X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k (r+b))
          (hex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) : X.card+1 ≤ (splitExtra G C).card+2 := by
        have hroot := (opndBound hL.1 (junkData hj).1 b).trans (Nat.add_lt_add_left (junkData hj).1 n)
        have hside : X ⊆ side (n := n) C j b := fun x hx =>
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp (hX hx)).1).1
        obtain ⟨P,hP,hcount,_⟩ := starLeafBudgetSplit hL.1 h4 hroot hside hex
        have hp := Finset.card_le_card hP
        omega
      by_cases h0 : (E 0).Nonempty
      · obtain ⟨b,c,X,hc,hX,hXne,hcovX,hex⟩ := star 0 h0
        by_cases h1 : (E 1).Nonempty
        · obtain ⟨d,f,Y,hf,hY,hYne,hcovY,hey⟩ := star 1 h1
          have hx' : X ⊆ exclusive (n := n) C j b ∩ exclusive (n := n) C k b := by simpa using hX
          have hc' : c ∈ exclusive (n := n) C j (1-b) ∩ exclusive (n := n) C k (1-b) := by simpa using hc
          have hf' : f ∈ exclusive (n := n) C j (1-d) ∩ exclusive (n := n) C k d := by
            fin_cases d <;> simpa using hf
          have hcost := crossed_stars_budgetSplit hL.1 h4 s hbip (junkData hj).1 (junkData hk).1 hx' hY hc' hf' hex hey
          apply two_star_package hXne hYne
          · exact cover.trans (Finset.union_subset_union hcovX hcovY)
          · exact fun x hx => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hex x hx)).1
          · exact fun y hy => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hey y hy)).1
          · omega
        · have he1 := Finset.not_nonempty_iff_eq_empty.mp h1
          have cov : R ⊆ X.image (fun x => s(c,x)) := by
            have he : R ⊆ E 0 := by simpa [he1] using cover
            exact he.trans hcovX
          exact one_star_package hXne cov
            (fun x hx => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hex x hx)).1)
            (single_budget hX hex)
      · have he0 := Finset.not_nonempty_iff_eq_empty.mp h0
        have he1 : (E 1).Nonempty := by
          have hsub : R ⊆ E 1 := by simpa [he0] using cover
          exact ⟨s(u,v),hsub he⟩
        obtain ⟨d,f,Y,hf,hY,hYne,hcovY,hey⟩ := star 1 he1
        have cov : R ⊆ Y.image (fun y => s(f,y)) := by
          have he : R ⊆ E 1 := by simpa [he0] using cover
          exact he.trans hcovY
        exact one_star_package hYne cov
          (fun y hy => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hey y hy)).1)
          (single_budget hY hey)
  · refine ⟨∅,fun _ => ∅,by simp,by simp,?_,by simp⟩
    intro e he
    exact (hR ⟨e,he⟩).elim


lemma mixed_wire_branch_support (hAO : IsAO2 n C) (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) {w : ℕ} (hw : w < n+C.gates.length)
    {c f : Fin n} (hc : c ∈ orIn n C w) (hf : f ∈ orIn n C w) (hcf : s c ≠ s f) :
    ∃ k ∈ splitExtra G C, Relation.ReflTransGen (OrStep n C) w (n+k) ∧
      c ∈ orIn n C (n+k) ∧ f ∈ orIn n C (n+k) := by
  have hne : c ≠ f := fun h => hcf (congrArg s h)
  have hsub : ({c,f} : Finset (Fin n)) ⊆ orIn n C w := by
    intro x hx
    have hx' : x=c ∨ x=f := by simpa using hx
    rcases hx' with rfl | rfl
    · exact hc
    · exact hf
  obtain ⟨P,hP,hcount,htrace⟩ := leafBudgetSplit hAO hw hsub (by
    intro k hk hbig hlam
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hbig
    obtain ⟨hIa,hXa⟩ := Finset.mem_inter.mp ha
    obtain ⟨hIb,hXb⟩ := Finset.mem_inter.mp hb
    have he := lam_same_color hAO s hs hlam hIa hIb
    have ha' : a=c ∨ a=f := by simpa using hXa
    have hb' : b=c ∨ b=f := by simpa using hXb
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact hab (ha'.trans hb'.symm)
    · exact hcf ((congrArg s ha').symm.trans (he.trans (congrArg s hb')))
    · exact hcf ((congrArg s hb').symm.trans (he.symm.trans (congrArg s ha')))
    · exact hab (ha'.trans hb'.symm))
  have hp : P.Nonempty := by
    simp only [Finset.card_pair hne] at hcount
    exact Finset.card_pos.mp (by omega)
  obtain ⟨k,hk⟩ := hp
  have hbig := (htrace k hk).2
  have heq : orIn n C (n+k) ∩ {c,f} = {c,f} := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    simp only [Finset.card_pair hne]
    omega
  have hck : c ∈ orIn n C (n+k) :=
    (Finset.mem_inter.mp (by rw [heq]; simp : c ∈ orIn n C (n+k) ∩ {c,f})).1
  have hfk : f ∈ orIn n C (n+k) :=
    (Finset.mem_inter.mp (by rw [heq]; simp : f ∈ orIn n C (n+k) ∩ {c,f})).1
  exact ⟨k,hP hk,(htrace k hk).1,hck,hfk⟩

lemma monochrome_stars_mixed_overhead (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {u v w : ℕ} (hu : u < n+C.gates.length) (hv : v < n+C.gates.length)
    (hw : w < n+C.gates.length) {c f a b : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ orIn n C u) (hY : Y ⊆ orIn n C v)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C)
    (ha : a ∈ orIn n C w) (hb : b ∈ orIn n C w) (hab : s a ≠ s b)
    (hmonoU : ∀ x ∈ orIn n C u, s x = s a)
    (hmonoV : ∀ y ∈ orIn n C v, s y = s b) :
    X.card+Y.card ≤ (splitExtra G C).card+1 := by
  obtain ⟨P,hP,hpc,hpt⟩ := starLeafBudgetSplit hAO h4 hu hX ex
  obtain ⟨Q,hQ,hqc,hqt⟩ := starLeafBudgetSplit hAO h4 hv hY ey
  obtain ⟨m,hm,_,ham,hbm⟩ := mixed_wire_branch_support hAO s hs hw ha hb hab
  have hpq : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro k hkp hkq
    obtain ⟨x,hx⟩ := (hpt k hkp).2
    have hxraw := (Finset.mem_inter.mp hx).1
    have hxu := orInTrans (hpt k hkp).1 hxraw
    have hxv := orInTrans (hqt k hkq).1 hxraw
    exact hab ((hmonoU x hxu).symm.trans (hmonoV x hxv))
  have hmP : m ∉ P := by
    intro hmp
    have hbU := orInTrans (hpt m hmp).1 hbm
    exact hab (hmonoU b hbU).symm
  have hmQ : m ∉ Q := by
    intro hmq
    have haV := orInTrans (hqt m hmq).1 ham
    exact hab (hmonoV a haV)
  have hmPQ : m ∉ P ∪ Q := by simpa only [Finset.mem_union,not_or] using And.intro hmP hmQ
  have hsub : insert m (P ∪ Q) ⊆ splitExtra G C :=
    Finset.insert_subset hm (Finset.union_subset hP hQ)
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hmPQ,Finset.card_union_of_disjoint hpq] at hcount
  omega


lemma forestLeafBudgetSplit (hAO : IsAO2 n C) (R : Finset ℕ)
    (hR : ∀ w ∈ R, w < n+C.gates.length) {X : Finset (Fin n)}
    (hX : X ⊆ R.biUnion (orIn n C))
    (hfree : ∀ k, k < C.gates.length → 1 < (orIn n C (n+k) ∩ X).card → k ∉ lam G C) :
    ∃ P ⊆ splitExtra G C, X.card ≤ P.card+R.card ∧
      ∀ k ∈ P, ∃ w ∈ R, Relation.ReflTransGen (OrStep n C) w (n+k) ∧
        (orIn n C (n+k) ∩ X).Nonempty := by
  classical
  induction R using Finset.induction_on generalizing X with
  | empty =>
      have hXe : X = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro x hx
        simpa using hX hx)
      refine ⟨∅, by simp, ?_, by simp⟩
      simp [hXe]
  | @insert w R hw ih =>
      let A := X ∩ orIn n C w
      let B := X \ orIn n C w
      have hA : A ⊆ X := Finset.inter_subset_left
      have hB : B ⊆ X := Finset.sdiff_subset
      have free_sub {S : Finset (Fin n)} (hS : S ⊆ X) :
          ∀ k, k < C.gates.length → 1 < (orIn n C (n+k) ∩ S).card → k ∉ lam G C := by
        intro k hk hbig
        apply hfree k hk
        apply Nat.lt_of_lt_of_le hbig
        apply Finset.card_le_card
        intro x hx
        obtain ⟨hi, hx⟩ := Finset.mem_inter.mp hx
        exact Finset.mem_inter.mpr ⟨hi, hS hx⟩
      have hBR : B ⊆ R.biUnion (orIn n C) := by
        intro x hx
        obtain ⟨hxX, hxw⟩ := Finset.mem_sdiff.mp hx
        obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp (hX hxX)
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact (hxw hxv).elim
        · exact Finset.mem_biUnion.mpr ⟨v, hv, hxv⟩
      obtain ⟨P, hP, hPc, hPt⟩ := leafBudgetSplit hAO (hR w (by simp))
        (show A ⊆ orIn n C w from Finset.inter_subset_right) (free_sub hA)
      obtain ⟨Q, hQ, hQc, hQt⟩ := ih (fun v hv => hR v (Finset.mem_insert_of_mem hv))
        hBR (free_sub hB)
      have hpq : Disjoint P Q := by
        apply Finset.disjoint_left.mpr
        intro k hkP hkQ
        obtain ⟨v, hv, htrace, x, hx⟩ := hQt k hkQ
        obtain ⟨hxin, hxB⟩ := Finset.mem_inter.mp hx
        exact (Finset.mem_sdiff.mp hxB).2 (orInTrans (hPt k hkP).1 hxin)
      have hcount : B.card+A.card=X.card := by
        exact Finset.card_sdiff_add_card_inter X (orIn n C w)
      refine ⟨P ∪ Q, Finset.union_subset hP hQ, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hpq, Finset.card_insert_of_notMem hw]
        omega
      · intro k hk
        rcases Finset.mem_union.mp hk with hk | hk
        · refine ⟨w, by simp, (hPt k hk).1, ?_⟩
          have hpos : 0 < (orIn n C (n+k) ∩ A).card := by
            have := (hPt k hk).2
            omega
          obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
          obtain ⟨hxin, hxA⟩ := Finset.mem_inter.mp hx
          exact ⟨x, Finset.mem_inter.mpr ⟨hxin, hA hxA⟩⟩
        · obtain ⟨v, hv, htrace, x, hx⟩ := hQt k hk
          obtain ⟨hxin, hxB⟩ := Finset.mem_inter.mp hx
          exact ⟨v, Finset.mem_insert_of_mem hv, htrace, x,
            Finset.mem_inter.mpr ⟨hxin, hB hxB⟩⟩

lemma starForestBudgetSplit (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (R : Finset ℕ) (hR : ∀ w ∈ R, w < n+C.gates.length) {c : Fin n}
    {X : Finset (Fin n)} (hX : X ⊆ R.biUnion (orIn n C))
    (hedge : ∀ x ∈ X, s(c,x) ∈ Ustar G C) :
    ∃ P ⊆ splitExtra G C, X.card ≤ P.card+R.card ∧
      ∀ k ∈ P, ∃ w ∈ R, Relation.ReflTransGen (OrStep n C) w (n+k) ∧
        (orIn n C (n+k) ∩ X).Nonempty := by
  apply forestLeafBudgetSplit hAO R hR hX
  intro k hk hbig
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hbig
  obtain ⟨ha, hXa⟩ := Finset.mem_inter.mp ha
  obtain ⟨hb, hXb⟩ := Finset.mem_inter.mp hb
  exact star_pair_not_lam hAO h4 hab (hedge a hXa) (hedge b hXb) ha hb


lemma monochrome_forest_star_mixed_overhead (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (R : Finset ℕ) (hR : ∀ w ∈ R, w < n+C.gates.length)
    {v w : ℕ} (hv : v < n+C.gates.length) (hw : w < n+C.gates.length)
    {c f a b : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ R.biUnion (orIn n C)) (hY : Y ⊆ orIn n C v)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C)
    (ha : a ∈ orIn n C w) (hb : b ∈ orIn n C w) (hab : s a ≠ s b)
    (hmonoR : ∀ u ∈ R, ∀ x ∈ orIn n C u, s x = s a)
    (hmonoV : ∀ y ∈ orIn n C v, s y = s b) :
    X.card+Y.card ≤ (splitExtra G C).card+R.card := by
  obtain ⟨P,hP,hpc,hpt⟩ := starForestBudgetSplit hAO h4 R hR hX ex
  obtain ⟨Q,hQ,hqc,hqt⟩ := starLeafBudgetSplit hAO h4 hv hY ey
  obtain ⟨m,hm,_,ham,hbm⟩ := mixed_wire_branch_support hAO s hs hw ha hb hab
  have hpq : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro k hkp hkq
    obtain ⟨u,hu,hku,x,hx⟩ := hpt k hkp
    have hxraw := (Finset.mem_inter.mp hx).1
    have hxu := orInTrans hku hxraw
    have hxv := orInTrans (hqt k hkq).1 hxraw
    exact hab ((hmonoR u hu x hxu).symm.trans (hmonoV x hxv))
  have hmP : m ∉ P := by
    intro hmp
    obtain ⟨u,hu,hmu,_⟩ := hpt m hmp
    have hbU := orInTrans hmu hbm
    exact hab (hmonoR u hu b hbU).symm
  have hmQ : m ∉ Q := by
    intro hmq
    have haV := orInTrans (hqt m hmq).1 ham
    exact hab (hmonoV a haV)
  have hmPQ : m ∉ P ∪ Q := by simpa only [Finset.mem_union,not_or] using And.intro hmP hmQ
  have hsub : insert m (P ∪ Q) ⊆ splitExtra G C :=
    Finset.insert_subset hm (Finset.union_subset hP hQ)
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hmPQ,Finset.card_union_of_disjoint hpq] at hcount
  omega


lemma overlap_guarded_forest_budget (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (P Q W : Finset (Fin n))
    (hclean : ∀ w ∈ W, ∀ p ∈ P, ∀ q ∈ Q,
      G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {r t : Fin n} (hrP : r ∈ P) (hrQ : r ∈ Q) (htP : t ∈ P) (htW : t ∈ W)
    (R : Finset ℕ) (hR : ∀ w ∈ R, w < n+C.gates.length)
    {p q : ℕ} (hp : p < n+C.gates.length) (hq : q < n+C.gates.length)
    (hP : P ⊆ orIn n C p) (hQ : orIn n C q ⊆ Q)
    (hW : ∀ w ∈ R, orIn n C w ⊆ W) {X Y : Finset (Fin n)}
    (hX : X ⊆ R.biUnion (orIn n C)) (hY : Y ⊆ orIn n C q)
    (ex : ∀ x ∈ X, s(r,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(t,y) ∈ Ustar G C) :
    X.card+Y.card ≤ (splitExtra G C).card+R.card := by
  have hrW : ∀ w ∈ W, G.Adj r w := by
    intro w hw
    rcases hclean w hw r hrP r hrQ with h | h | h
    · exact (G.irrefl h).elim
    · exact h
    · exact h
  have htQ : ∀ q ∈ Q, G.Adj t q := by
    intro q hq
    rcases hclean t htW t htP q hq with h | h | h
    · exact h
    · exact (G.irrefl h).elim
    · exact h.symm
  have hrt := hrW t htW
  have hmonoR : ∀ u ∈ R, ∀ x ∈ orIn n C u, s x = s t := by
    intro u hu x hx
    have h1 := hs r x (hrW x (hW u hu hx))
    have h2 := hs r t hrt
    cases hrval : s r <;> cases hxval : s x <;> cases htval : s t <;> simp_all
  have hmonoQ : ∀ y ∈ orIn n C q, s y = s r := by
    intro y hy
    have h1 := hs t y (htQ y (hQ hy))
    have h2 := hs t r hrt.symm
    cases htval : s t <;> cases hyval : s y <;> cases hrval : s r <;> simp_all
  exact monochrome_forest_star_mixed_overhead hAO h4 s hs R hR hq hp hX hY ex ey
    (hP htP) (hP hrP) (hs t r hrt.symm) hmonoR hmonoQ


lemma forest_star_separated_mixed_overhead (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (R : Finset ℕ) (hR : ∀ w ∈ R, w < n+C.gates.length)
    {v w : ℕ} (hv : v < n+C.gates.length) (hw : w < n+C.gates.length)
    {c f a b : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ R.biUnion (orIn n C)) (hY : Y ⊆ orIn n C v)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C)
    (ha : a ∈ orIn n C w) (hb : b ∈ orIn n C w) (hab : s a ≠ s b)
    (hcolorX : ∀ x ∈ X, s x = s a)
    (havoid : ∀ u ∈ R, b ∉ orIn n C u)
    (hmonoV : ∀ y ∈ orIn n C v, s y = s b) :
    X.card+Y.card ≤ (splitExtra G C).card+R.card := by
  obtain ⟨P,hP,hpc,hpt⟩ := starForestBudgetSplit hAO h4 R hR hX ex
  obtain ⟨Q,hQ,hqc,hqt⟩ := starLeafBudgetSplit hAO h4 hv hY ey
  obtain ⟨m,hm,_,ham,hbm⟩ := mixed_wire_branch_support hAO s hs hw ha hb hab
  have hpq : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro k hkp hkq
    obtain ⟨u,hu,hku,x,hx⟩ := hpt k hkp
    obtain ⟨hxraw,hxX⟩ := Finset.mem_inter.mp hx
    have hxv := orInTrans (hqt k hkq).1 hxraw
    exact hab ((hcolorX x hxX).symm.trans (hmonoV x hxv))
  have hmP : m ∉ P := by
    intro hmp
    obtain ⟨u,hu,hmu,_⟩ := hpt m hmp
    exact havoid u hu (orInTrans hmu hbm)
  have hmQ : m ∉ Q := by
    intro hmq
    exact hab (hmonoV a (orInTrans (hqt m hmq).1 ham))
  have hmPQ : m ∉ P ∪ Q := by simpa only [Finset.mem_union,not_or] using And.intro hmP hmQ
  have hsub : insert m (P ∪ Q) ⊆ splitExtra G C :=
    Finset.insert_subset hm (Finset.union_subset hP hQ)
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hmPQ,Finset.card_union_of_disjoint hpq] at hcount
  omega


lemma star_neighbor_pair_not_lam (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {c a b : Fin n} (hab : a ≠ b) (hae : s(c,a) ∈ Ustar G C) (hcb : G.Adj c b)
    {k : ℕ} (ha : a ∈ orIn n C (n+k)) (hb : b ∈ orIn n C (n+k)) : k ∉ lam G C := by
  intro hk
  obtain ⟨t, ht⟩ := lamAvoidsUstar hk (fun j hj u hu v hv => topAdj hAO hj hu hv)
  have hp : 1 < ({a,b} : Finset (Fin n)).card := by simp [hab]
  have het : t = c := uniqueCenter h4 hp
    (by
      intro x hx
      have hx' : x=a ∨ x=b := by simpa using hx
      rcases hx' with hx' | hx'
      · exact hx' ▸ (ht a ha).1
      · exact hx' ▸ (ht b hb).1)
    (by
      intro x hx
      have hx' : x=a ∨ x=b := by simpa using hx
      rcases hx' with rfl | rfl
      · exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hae).1
      · exact hcb)
  subst t
  exact (ht a ha).2 hae

lemma neighbor_anchor_star_free (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {c z : Fin n} {X : Finset (Fin n)} (hz : G.Adj c z)
    (hedge : ∀ x ∈ X, s(c,x) ∈ Ustar G C)
    (k : ℕ) (hbig : 1 < (orIn n C (n+k) ∩ insert z X).card) : k ∉ lam G C := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hbig
  obtain ⟨hIa, hXa⟩ := Finset.mem_inter.mp ha
  obtain ⟨hIb, hXb⟩ := Finset.mem_inter.mp hb
  rcases Finset.mem_insert.mp hXa with haz | hXa
  · rcases Finset.mem_insert.mp hXb with hbz | hXb
    · exact (hab (haz.trans hbz.symm)).elim
    · subst a
      exact star_neighbor_pair_not_lam hAO h4 (Ne.symm hab) (hedge b hXb) hz hIb hIa
  · rcases Finset.mem_insert.mp hXb with hbz | hXb
    · subst b
      exact star_neighbor_pair_not_lam hAO h4 hab (hedge a hXa) hz hIa hIb
    · exact star_pair_not_lam hAO h4 hab (hedge a hXa) (hedge b hXb) hIa hIb

lemma neighbor_anchored_star_budgetSplit (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {c z : Fin n} {X : Finset (Fin n)} {w : ℕ} (hw : w < n+C.gates.length)
    (hX : X ⊆ orIn n C w) (hz : z ∈ orIn n C w) (hzX : z ∉ X)
    (hcz : G.Adj c z) (hedge : ∀ x ∈ X, s(c,x) ∈ Ustar G C) :
    ∃ P ⊆ splitExtra G C, X.card ≤ P.card ∧
      ∀ k ∈ P, Relation.ReflTransGen (OrStep n C) w (n+k) ∧
        (orIn n C (n+k) ∩ X).Nonempty := by
  obtain ⟨P,hP,hcount,htrace⟩ := leafBudgetSplit hAO hw (Finset.insert_subset hz hX)
    (fun k _ hbig => neighbor_anchor_star_free hAO h4 hcz hedge k hbig)
  refine ⟨P,hP,?_,?_⟩
  · rw [Finset.card_insert_of_notMem hzX] at hcount
    omega
  · intro k hk
    exact ⟨(htrace k hk).1, insert_big_has_leaf (htrace k hk).2⟩

lemma forest_neighbor_star_mixed_overhead (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    (R : Finset ℕ) (hR : ∀ w ∈ R, w < n+C.gates.length)
    {v w : ℕ} (hv : v < n+C.gates.length) (hw : w < n+C.gates.length)
    {c f a b : Fin n} {X Y : Finset (Fin n)}
    (hX : X ⊆ R.biUnion (orIn n C)) (hY : Y ⊆ orIn n C v)
    (ex : ∀ x ∈ X, s(c,x) ∈ Ustar G C) (ey : ∀ y ∈ Y, s(f,y) ∈ Ustar G C)
    (ha : a ∈ orIn n C w) (hb : b ∈ orIn n C w) (hab : s a ≠ s b)
    (hcolorX : ∀ x ∈ X, s x = s a) (havoid : ∀ u ∈ R, b ∉ orIn n C u)
    (hmonoV : ∀ y ∈ orIn n C v, s y = s b)
    (hbV : b ∈ orIn n C v) (hbY : b ∉ Y) (hfb : G.Adj f b) :
    X.card+Y.card+1 ≤ (splitExtra G C).card+R.card := by
  obtain ⟨P,hP,hpc,hpt⟩ := starForestBudgetSplit hAO h4 R hR hX ex
  obtain ⟨Q,hQ,hqc,hqt⟩ := neighbor_anchored_star_budgetSplit hAO h4 hv hY hbV hbY hfb ey
  obtain ⟨m,hm,_,ham,hbm⟩ := mixed_wire_branch_support hAO s hs hw ha hb hab
  have hpq : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro k hkp hkq
    obtain ⟨u,hu,hku,x,hx⟩ := hpt k hkp
    obtain ⟨hxraw,hxX⟩ := Finset.mem_inter.mp hx
    have hxv := orInTrans (hqt k hkq).1 hxraw
    exact hab ((hcolorX x hxX).symm.trans (hmonoV x hxv))
  have hmP : m ∉ P := by
    intro hmp
    obtain ⟨u,hu,hmu,_⟩ := hpt m hmp
    exact havoid u hu (orInTrans hmu hbm)
  have hmQ : m ∉ Q := by
    intro hmq
    exact hab (hmonoV a (orInTrans (hqt m hmq).1 ham))
  have hmPQ : m ∉ P ∪ Q := by simpa only [Finset.mem_union,not_or] using And.intro hmP hmQ
  have hsub : insert m (P ∪ Q) ⊆ splitExtra G C :=
    Finset.insert_subset hm (Finset.union_subset hP hQ)
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hmPQ,Finset.card_union_of_disjoint hpq] at hcount
  omega

end PEqualNP.Outside.L_meta_5012.MutualBudget

namespace PEqualNP.Outside.L_meta_5012.MutualBudget
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.Core PEqualNP.ReadTwo
  PEqualNP.MetaComplexity
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma singleton_cleaner_adj {r w : Fin n} {g : ℕ}
    (hsing : ∀ x : Fin n → Bool, x r = true → gateVal n C g x = true)
    (hw : w ∈ wmax G C g) : G.Adj r w := by
  have hc := (Finset.mem_filter.mp hw).2 (pairInput r w)
    (hsing (pairInput r w) (pairInput_left r w)) (pairInput_right r w)
  exact (graphFun_pair G r w).mp hc

lemma opposite_raw_pair_star {a : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    {u v : Fin n} (hu : u ∈ side (n := n) C a b)
    (hv : v ∈ side (n := n) C a (1 - b)) : s(u, v) ∈ starEdges G C := by
  apply Finset.mem_biUnion.mpr
  refine ⟨a, ha, ?_⟩
  fin_cases b
  · exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩
  · exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_product.mpr ⟨hv, hu⟩, Sym2.eq_swap⟩

lemma singleton_guarded_raw_ne {a : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    {r v w : Fin n} (hU : s(r, w) ∈ Ustar G C)
    (hv : v ∈ side (n := n) C a b)
    (hw : w ∈ side (n := n) C a (1 - b)) : v ≠ r := by
  intro heq
  subst v
  exact (Finset.mem_sdiff.mp hU).2 (opposite_raw_pair_star ha hv hw)

lemma singleton_guarded_opposite_small (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {g a : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hread : OrReaches n C (opnd C a b) g) {r v w : Fin n}
    (hsing : ∀ x : Fin n → Bool, x r = true → gateVal n C g x = true)
    (hU : s(r, w) ∈ Ustar G C)
    (hv : v ∈ side (n := n) C a b)
    (hw : w ∈ side (n := n) C a (1 - b)) :
    (side (n := n) C a (1 - b)).card ≤ 1 := by
  have hvr : v ≠ r := singleton_guarded_raw_ne ha hU hv hw
  have hsub : side (n := n) C a (1 - b) ⊆
      Finset.univ.filter (fun t => G.Adj r t ∧ G.Adj v t) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨singleton_cleaner_adj hsing (oppositeSideWmax hAO ha hread ht), ?_⟩
    fin_cases b
    · exact topAdj hAO ha hv ht
    · exact (topAdj hAO ha ht hv).symm
  exact (Finset.card_le_card hsub).trans (h4 r v (Ne.symm hvr))

lemma singleton_guarded_anchor_unique (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {g a a' : ℕ} (ha : a ∈ tops G C) (ha' : a' ∈ tops G C) {b b' : Fin 2}
    (hread : OrReaches n C (opnd C a b) g)
    (hread' : OrReaches n C (opnd C a' b') g) {r v w w' : Fin n}
    (hsing : ∀ x : Fin n → Bool, x r = true → gateVal n C g x = true)
    (hU : s(r, w) ∈ Ustar G C)
    (hv : v ∈ side (n := n) C a b)
    (hv' : v ∈ side (n := n) C a' b')
    (hw : w ∈ side (n := n) C a (1 - b))
    (hw' : w' ∈ side (n := n) C a' (1 - b')) : w = w' := by
  have hvr : v ≠ r := singleton_guarded_raw_ne ha hU hv hw
  have hrvw : G.Adj r w ∧ G.Adj v w := by
    refine ⟨singleton_cleaner_adj hsing (oppositeSideWmax hAO ha hread hw), ?_⟩
    fin_cases b
    · exact topAdj hAO ha hv hw
    · exact (topAdj hAO ha hw hv).symm
  have hrvw' : G.Adj r w' ∧ G.Adj v w' := by
    refine ⟨singleton_cleaner_adj hsing (oppositeSideWmax hAO ha' hread' hw'), ?_⟩
    fin_cases b'
    · exact topAdj hAO ha' hv' hw'
    · exact (topAdj hAO ha' hw' hv').symm
  apply Finset.card_le_one.mp (h4 r v (Ne.symm hvr))
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hrvw
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hrvw'
lemma singleton_star_trace (hL : IsLeastAO G C) (hT : TopForm G C)
    {g h : ℕ} (hjs : junk G C = {g, h}) {r w : Fin n}
    (hsing : ∀ x : Fin n → Bool, x r = true → gateVal n C g x = true)
    (hU : s(r, w) ∈ Ustar G C) :
    gateVal n C h (pairInput r w) = true ∨
      ∃ a ∈ tops G C, ∃ b : Fin 2,
        OrReaches n C (opnd C a b) g ∧ w ∈ side (n := n) C a (1 - b) := by
  have hadj : G.Adj r w := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1
  obtain ⟨a, ha, hval⟩ := acceptedTop hL hadj
  obtain ⟨hal, haand, haclean⟩ := topData ha
  have trace (b : Fin 2) := operandSupport hL.1 hT hal haand
    ((andValOperands hL.1 hal haand (pairInput r w)).mp hval b)
  have hgr : gateVal n C g (pairInput r r) = true :=
    hsing (pairInput r r) (pairInput_left r r)
  have no_singleton (h0 : val C (List.ofFn (pairInput r r)) (opnd C a 0) = true)
      (h1 : val C (List.ofFn (pairInput r r)) (opnd C a 1) = true) : False :=
    G.irrefl ((graphFun_pair G r r).mp
      (haclean _ ((andValBoth hL.1 hal haand (pairInput r r)).mpr ⟨h0, h1⟩)))
  have finish {b : Fin 2} {t : Fin n} {k : ℕ}
      (ht : t ∈ side (n := n) C a (1 - b)) (htrow : t = r ∨ t = w)
      (hk : k ∈ junk G C) (hread : OrReaches n C (opnd C a b) k)
      (hkv : gateVal n C k (pairInput r w) = true) :
      gateVal n C h (pairInput r w) = true ∨
        ∃ a ∈ tops G C, ∃ b : Fin 2,
          OrReaches n C (opnd C a b) g ∧ w ∈ side (n := n) C a (1 - b) := by
    rw [hjs] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · rcases htrow with rfl | rfl
      · exfalso
        fin_cases b
        · exact no_singleton (reachVal hread hgr) (sideVal ht (by simp [pairInput]))
        · exact no_singleton (sideVal ht (by simp [pairInput])) (reachVal hread hgr)
      · exact Or.inr ⟨a, ha, b, hread, ht⟩
    · exact Or.inl hkv
  rcases trace 0 with ⟨u, hu, hurow⟩ | ⟨k, hk, hkr, hkv⟩ <;>
    rcases trace 1 with ⟨v, hv, hvrow⟩ | ⟨k', hk', hk'r, hk'v⟩
  · exfalso
    have hne : u ≠ v := G.ne_of_adj (topAdj hL.1 ha hu hv)
    have heq : s(r, w) = s(u, v) := by
      rcases hurow with rfl | rfl <;> rcases hvrow with rfl | rfl
      · exact (hne rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hne rfl).elim
    exact (Finset.mem_sdiff.mp hU).2 (heq ▸ Finset.mem_biUnion.mpr
      ⟨a, ha, Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩⟩)
  · exact finish (b := 1) hu hurow hk' hk'r hk'v
  · exact finish (b := 0) hv hvrow hk hkr hkv
  · rw [hjs] at hk hk'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk hk'
    rcases hk with rfl | rfl
    · rcases hk' with rfl | rfl
      · exact False.elim (no_singleton (reachVal hkr hgr) (reachVal hk'r hgr))
      · exact Or.inl hk'v
    · exact Or.inl hkv

lemma singleton_star_mixed_trace (hL : IsLeastAO G C) (hT : TopForm G C)
    (hcent : centreless G C = ∅) {g h : ℕ} (hjs : junk G C = {g, h}) {r w : Fin n}
    (hsing : ∀ x : Fin n → Bool, x r = true → gateVal n C g x = true)
    (hU : s(r, w) ∈ Ustar G C)
    (hhfalse : gateVal n C h (pairInput r w) ≠ true) :
    ∃ a ∈ tops G C, ∃ b : Fin 2,
      OrReaches n C (opnd C a b) g ∧ (side (n := n) C a b).Nonempty ∧
      w ∈ side (n := n) C a (1 - b) := by
  obtain ⟨a, ha, b, hread, hw⟩ :=
    (singleton_star_trace hL hT hjs hsing hU).resolve_left hhfalse
  refine ⟨a, ha, b, hread, ?_, hw⟩
  by_contra hside
  have he := Finset.not_nonempty_iff_eq_empty.mp hside
  have hac : a ∈ centreless G C := by
    apply Finset.mem_filter.mpr
    refine ⟨ha, ?_⟩
    fin_cases b
    · exact Or.inl he
    · exact Or.inr he
  simpa only [hcent, Finset.notMem_empty] using hac
end PEqualNP.Outside.L_meta_5012.MutualBudget
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
namespace PEqualNP.Outside.L_meta_5012.MutualBudget
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.Core PEqualNP.ReadTwo
  PEqualNP.MetaComplexity
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma guarded_star_mixing_antichain {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) (hne : ∃ u v : Fin n, G.Adj u v)
    {g1 g2 g : ℕ} (hjs : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2)
    (hg : g = g1 ∨ g = g2) (r : Fin n) (X : Finset (Fin n))
    (hX : ∀ w ∈ X, s(r, w) ∈ Ustar G C)
    (hWitness : ∀ w ∈ X, ∃ a ∈ tops G C, ∃ b : Fin 2,
      OrReaches n C (opnd C a b) g ∧ (side (n := n) C a b).Nonempty ∧
      w ∈ side (n := n) C a (1 - b)) :
    ∃ P ⊆ (orN G C \ lam G C).filter (fun m =>
        orIn n C (opnd C m 0) = ∅ ∨ orIn n C (opnd C m 1) = ∅),
      X.card = P.card ∧
      (∀ m ∈ P, (orIn n C (n + m)).Nonempty ∧ OrReaches n C (n + m) g) ∧
      (∀ m ∈ P, ∀ m' ∈ P, OrReaches n C (n + m) m' → m = m') := by
  classical
  let F := (orN G C \ lam G C).filter (fun m =>
    orIn n C (opnd C m 0) = ∅ ∨ orIn n C (opnd C m 1) = ∅)
  have witness : ∀ w ∈ X, ∃ m ∈ F, (orIn n C (n + m)).Nonempty ∧
      (∀ v ∈ orIn n C (n + m), v ≠ r ∧ G.Adj v w) ∧ OrReaches n C (n + m) g := by
    intro w hw
    obtain ⟨a, ha, b, hread, hraw, hother⟩ := hWitness w hw
    have haData := topData ha
    obtain ⟨m, hm, hreach, hmg, hnon, hsub, hempty⟩ :=
      Surgery.mixing_of_reaches_and_nonempty hL hLift hne hjs hg
        (opnd C a b) (by have := opndBound hL.1 haData.1 b; omega)
        (Surgery.top_opnd_not_belowF hL hne ha b) hraw hread
    refine ⟨m, Finset.mem_filter.mpr ⟨hm, hempty⟩, hnon, ?_, hmg⟩
    intro v hv
    have hvside := hsub hv
    refine ⟨singleton_guarded_raw_ne ha (hX w hw) hvside hother, ?_⟩
    fin_cases b
    · exact topAdj hL.1 ha hvside hother
    · exact (topAdj hL.1 ha hother hvside).symm
  let f : {w // w ∈ X} → {m // m ∈ F} := fun w =>
    ⟨Classical.choose (witness w.val w.property),
      (Classical.choose_spec (witness w.val w.property)).1⟩
  have data (w : {w // w ∈ X}) : (orIn n C (n + (f w).val)).Nonempty ∧
      (∀ v ∈ orIn n C (n + (f w).val), v ≠ r ∧ G.Adj v w.val) ∧
      OrReaches n C (n + (f w).val) g :=
    (Classical.choose_spec (witness w.val w.property)).2
  have same_of_support {w w' : {w // w ∈ X}}
      (hsub : orIn n C (n + (f w').val) ⊆ orIn n C (n + (f w).val)) : w = w' := by
    obtain ⟨v, hv'⟩ := (data w').1
    have hv := hsub hv'
    have hvr := ((data w).2.1 v hv).1
    have hrw : G.Adj r w.val :=
      SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hX w.val w.property)).1
    have hrw' : G.Adj r w'.val :=
      SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hX w'.val w'.property)).1
    apply Subtype.ext
    apply Finset.card_le_one.mp (h4 r v (Ne.symm hvr))
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        And.intro hrw ((data w).2.1 v hv).2
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        And.intro hrw' ((data w').2.1 v hv').2
  have hfinj : Function.Injective (fun w => (f w).val) := by
    intro w w' hm
    change (f w).val = (f w').val at hm
    apply same_of_support
    rw [hm]
  let P := Finset.univ.image (fun w : {w // w ∈ X} => (f w).val)
  have hsubP : P ⊆ F := by
    intro m hm
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hm
    exact (f w).property
  refine ⟨P, hsubP, ?_, ?_, ?_⟩
  · have hcard := Finset.card_image_of_injective (s := Finset.univ) hfinj
    simpa only [P, Finset.card_univ, Fintype.card_coe] using hcard.symm
  · intro m hm
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨(data w).1, (data w).2.2⟩
  · intro m hm m' hm' hreach
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨w', _, rfl⟩ := Finset.mem_image.mp hm'
    have hww' : w = w' := same_of_support (by
      intro v hv
      exact orInTrans (orReaches_reach _ _ hreach).1 hv)
    rw [hww']

lemma guarded_star_mixing_strict {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
    (h4 : NoFourCycle G) (hne : ∃ u v : Fin n, G.Adj u v)
    {g h : ℕ} (hgh : g < h) (hjs : ∀ k, k ∈ junk G C ↔ k = g ∨ k = h)
    (hcent : centreless G C = ∅) (r : Fin n) (X : Finset (Fin n))
    (hX : ∀ w ∈ X, s(r, w) ∈ Ustar G C)
    (hWitness : ∀ w ∈ X, ∃ a ∈ tops G C, ∃ b : Fin 2,
      OrReaches n C (opnd C a b) g ∧ (side (n := n) C a b).Nonempty ∧
      w ∈ side (n := n) C a (1 - b)) :
    X.card + 1 ≤ ((orN G C \ lam G C).filter (fun m =>
      orIn n C (opnd C m 0) = ∅ ∨ orIn n C (opnd C m 1) = ∅)).card := by
  obtain ⟨P, hP, hcard, htrace, hanti⟩ :=
    guarded_star_mixing_antichain G C hL hLift h4 hne hjs (Or.inl rfl) r X hX hWitness
  obtain ⟨m, hm, hmP, hempty⟩ :=
    Surgery.antichain_unused_nonsplit hL hne hgh hjs hcent P htrace hanti
  have hsub : insert m P ⊆ (orN G C \ lam G C).filter (fun m =>
      orIn n C (opnd C m 0) = ∅ ∨ orIn n C (opnd C m 1) = ∅) :=
    Finset.insert_subset (Finset.mem_filter.mpr ⟨hm, hempty⟩) hP
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hmP, ← hcard] at hc
  exact hc


end PEqualNP.Outside.L_meta_5012.MutualBudget


namespace PEqualNP.Outside.L_meta_5012.GuardedReuseOverlap

lemma package_reused_stars_overlap {n : ℕ} (G : SimpleGraph (Fin n))
    (r t : Fin n) (hrt : r ≠ t) (X Y S : Finset (Fin n))
    (hrS : r ∉ S)
    (hX : ∀ x ∈ X, G.Adj r x) (hY : ∀ y ∈ Y, G.Adj t y)
    (hS : ∀ v ∈ S, G.Adj r v) {E : Finset (Sym2 (Fin n))}
    (hcov : E ⊆ X.image (fun x => s(r,x)) ∪ Y.image (fun y => s(t,y)) ∪
      S.image (fun v => s(r,v))) :
    ∃ (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n)), S ⊆ Z ∧
      (∀ v ∈ Z, (L v).Nonempty) ∧ (∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u) ∧
      (∀ e ∈ E, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) ∧
      (∑ v ∈ Z, (L v).card) + (Z \ S).card ≤ X.card+Y.card+S.card+2 ∧
      (∀ v ∈ S, L v = if v=t then insert r Y else {r}) ∧
      (t ∈ S → (Z \ S).card ≤ 1) := by
  classical
  let core : Fin n → Finset (Fin n) := fun v => if v=r then X else if v=t then Y else ∅
  let K := ({r,t} : Finset (Fin n)).filter (fun v => v ∉ S ∧ (core v).Nonempty)
  let Z := K ∪ S
  let L : Fin n → Finset (Fin n) :=
    fun v => if v ∈ S then if v=t then insert r Y else {r} else core v
  have hKsub : K ⊆ ({r,t} : Finset (Fin n)) := Finset.filter_subset _ _
  have hKS : Disjoint K S := by
    apply Finset.disjoint_left.mpr
    intro v hv hvS
    exact (Finset.mem_filter.mp hv).2.1 hvS
  have hLcore : ∀ v ∈ K, L v = core v := by
    intro v hv
    exact if_neg (Finset.mem_filter.mp hv).2.1
  have hKsmall (htS : t ∈ S) : K ⊆ {r} := by
    intro v hv
    have hv' : v=r ∨ v=t := by simpa using hKsub hv
    rcases hv' with rfl | rfl
    · simp
    · exact ((Finset.mem_filter.mp hv).2.1 htS).elim
  have hsumK : (∑ v ∈ K, (L v).card) ≤ X.card + if t ∈ S then 0 else Y.card := by
    rw [show (∑ v ∈ K, (L v).card) = ∑ v ∈ K, (core v).card by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hLcore v hv]]
    by_cases htS : t ∈ S
    · have hh := Finset.sum_le_sum_of_subset_of_nonneg (hKsmall htS)
        (f := fun v => (core v).card) (by intros; exact Nat.zero_le _)
      simpa [core, htS] using hh
    · have hh := Finset.sum_le_sum_of_subset_of_nonneg hKsub
        (f := fun v => (core v).card) (by intros; exact Nat.zero_le _)
      simpa [core, htS, hrt, Ne.symm hrt] using hh
  have hsumS : (∑ v ∈ S, (L v).card) ≤ S.card + if t ∈ S then Y.card else 0 := by
    calc
      (∑ v ∈ S, (L v).card) ≤ ∑ v ∈ S, (1 + if v=t then Y.card else 0) := by
        apply Finset.sum_le_sum
        intro v hv
        by_cases hvt : v=t
        · subst v
          have hh := Finset.card_insert_le r Y
          simpa [L,hv,Nat.add_comm] using hh
        · simp [L,hv,hvt]
      _ = S.card + if t ∈ S then Y.card else 0 := by
        simp [Finset.sum_add_distrib]
  have hdiff : Z \ S = K := Finset.union_sdiff_cancel_right hKS
  have hcard : (Z \ S).card ≤ 2 := by
    rw [hdiff]
    simpa [hrt] using Finset.card_le_card hKsub
  refine ⟨Z,L,Finset.subset_union_right,?_,?_,?_,?_,?_,?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hvK | hvS
    · rw [hLcore v hvK]
      exact (Finset.mem_filter.mp hvK).2.2
    · by_cases hvt : v=t
      · subst v
        simp [L,hvS]
      · simp [L,hvS,hvt]
  · intro v hv u hu
    rcases Finset.mem_union.mp hv with hvK | hvS
    · rw [hLcore v hvK] at hu
      have hv' : v=r ∨ v=t := by simpa using hKsub hvK
      rcases hv' with rfl | rfl
      · exact hX u (by simpa [core] using hu)
      · exact hY u (by simpa [core,Ne.symm hrt] using hu)
    · by_cases hvt : v=t
      · subst v
        have hu' : u=r ∨ u∈Y := by simpa [L,hvS] using hu
        rcases hu' with rfl | huY
        · exact (hS t hvS).symm
        · exact hY u huY
      · have hur : u=r := by simpa [L,hvS,hvt] using hu
        subst u
        exact (hS v hvS).symm
  · intro e he
    rcases Finset.mem_union.mp (hcov he) with he | he
    · rcases Finset.mem_union.mp he with he | he
      · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
        have hrK : r ∈ K := by
          simp only [K,Finset.mem_filter]
          exact ⟨by simp,hrS,by simpa [core] using (show X.Nonempty from ⟨x,hx⟩)⟩
        exact ⟨r,Finset.mem_union_left _ hrK,x,by simpa [L,hrS,core] using hx,rfl⟩
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
        by_cases htS : t ∈ S
        · exact ⟨t,Finset.mem_union_right _ htS,y,by simp [L,htS,hy],rfl⟩
        · have htK : t ∈ K := by
            simp only [K,Finset.mem_filter]
            exact ⟨by simp,htS,by simpa [core,Ne.symm hrt] using (show Y.Nonempty from ⟨y,hy⟩)⟩
          exact ⟨t,Finset.mem_union_left _ htK,y,by simpa [L,htS,core,Ne.symm hrt] using hy,rfl⟩
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
      refine ⟨v,Finset.mem_union_right _ hv,r,?_,Sym2.eq_swap⟩
      by_cases hvt : v=t
      · subst v
        simp [L,hv]
      · simp [L,hv,hvt]
  · have hsum : (∑ v ∈ Z, (L v).card) =
        (∑ v ∈ K, (L v).card) + (∑ v ∈ S, (L v).card) := Finset.sum_union hKS
    by_cases htS : t ∈ S <;> simp [htS] at hsumK hsumS <;> omega
  · intro v hv
    simp [L,hv]
  · intro htS
    rw [hdiff]
    simpa using Finset.card_le_card (hKsmall htS)

end PEqualNP.Outside.L_meta_5012.GuardedReuseOverlap

namespace PEqualNP.Outside.L_meta_5012.MutualBudget
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.Core
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma singleton_reused_tops (hL : IsLeastAO G C) (hT : TopForm G C)
    (h4 : NoFourCycle G) (hcent : centreless G C = ∅)
    {g h : ℕ} (hjs : junk G C = {g,h}) (r : Fin n) (S : Finset (Fin n))
    (hsing : ∀ x : Fin n → Bool, x r = true → gateVal n C g x = true)
    (hS : ∀ w ∈ S, s(r,w) ∈ Ustar G C)
    (hno : ∀ w ∈ S, gateVal n C h (pairInput r w) ≠ true) :
    ∃ topOf : Fin n → ℕ,
      (∀ w ∈ S, topOf w ∈ tops G C \ centreless G C) ∧
      (∀ w ∈ S, side (n := n) C (topOf w) 0 = {w} ∨ side (n := n) C (topOf w) 1 = {w}) ∧
      (∀ w ∈ S, ∀ w' ∈ S, topOf w=topOf w' → w=w') := by
  classical
  have witness : ∀ w ∈ S, ∃ a ∈ tops G C, ∃ b : Fin 2,
      OrReaches n C (opnd C a b) g ∧ side (n := n) C a (1-b) = {w} := by
    intro w hw
    obtain ⟨a,ha,b,hread,hraw,hother⟩ := singleton_star_mixed_trace hL hT hcent hjs hsing (hS w hw) (hno w hw)
    obtain ⟨v,hv⟩ := hraw
    have hsmall := singleton_guarded_opposite_small hL.1 h4 ha hread hsing (hS w hw) hv hother
    refine ⟨a,ha,b,hread,?_⟩
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hother, ?_⟩
    intro x hx
    apply Finset.card_le_one.mp hsmall
    · exact hx
    · exact hother
  let topOf : Fin n → ℕ := fun w => if hw : w∈S then Classical.choose (witness w hw) else 0
  have data : ∀ w ∈ S, topOf w ∈ tops G C ∧ ∃ b : Fin 2,
      OrReaches n C (opnd C (topOf w) b) g ∧ side (n := n) C (topOf w) (1-b) = {w} := by
    intro w hw
    simpa only [topOf, dif_pos hw] using Classical.choose_spec (witness w hw)
  refine ⟨topOf,?_,?_,?_⟩
  · intro w hw
    exact Finset.mem_sdiff.mpr ⟨(data w hw).1,by simp [hcent]⟩
  · intro w hw
    obtain ⟨_,b,hread,hside⟩ := data w hw
    fin_cases b
    · exact Or.inr hside
    · exact Or.inl hside
  · intro w hw w' hw' heq
    obtain ⟨ha,b,hread,hside⟩ := data w hw
    obtain ⟨_,b',hread',hside'⟩ := data w' hw'
    rw [← heq] at hread' hside'
    have same (he : b=b') : w=w' := by
      rw [← he] at hside'
      exact Finset.singleton_injective (hside.symm.trans hside')
    have no_both (h0 : OrReaches n C (opnd C (topOf w) 0) g)
        (h1 : OrReaches n C (opnd C (topOf w) 1) g) : False := by
      obtain ⟨hal,haand,hclean⟩ := topData ha
      have hgr := hsing (pairInput r r) (pairInput_left r r)
      have hval := (andValBoth hL.1 hal haand (pairInput r r)).mpr
        ⟨reachVal h0 hgr, reachVal h1 hgr⟩
      exact G.irrefl ((graphFun_pair G r r).mp (hclean _ hval))
    fin_cases b <;> fin_cases b'
    · exact same rfl
    · exact (no_both hread hread').elim
    · exact (no_both hread' hread).elim
    · exact same rfl

end PEqualNP.Outside.L_meta_5012.MutualBudget

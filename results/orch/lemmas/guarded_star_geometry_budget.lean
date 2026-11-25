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

end PEqualNP.Outside.L_meta_5012.MutualBudget

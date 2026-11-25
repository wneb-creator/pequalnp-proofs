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


end PEqualNP.Outside.L_meta_5012.MutualBudget


namespace PEqualNP.Outside.L_meta_5012.Reconvergence

lemma ancestors_comparable_of_unique_parents {α : Type*} (R : α → α → Prop) (r : α)
    (hunique : ∀ p q y, Relation.ReflTransGen R r p → Relation.ReflTransGen R r q →
      R p y → R q y → p = q)
    {a b x : α} (hra : Relation.ReflTransGen R r a)
    (hrb : Relation.ReflTransGen R r b)
    (hax : Relation.ReflTransGen R a x) (hbx : Relation.ReflTransGen R b x) :
    Relation.ReflTransGen R a b ∨ Relation.ReflTransGen R b a := by
  induction hax generalizing b with
  | refl => exact Or.inr hbx
  | @tail x y hax hxy ih =>
    rcases Relation.ReflTransGen.cases_tail hbx with hby | ⟨z, hbz, hzy⟩
    · subst b
      exact Or.inl (hax.tail hxy)
    · have hxz : x = z := hunique x z y (hra.trans hax) (hrb.trans hbz) hxy hzy
      subst z
      exact ih hrb hbz

lemma incomparable_paths_reconverge {α : Type*} (R : α → α → Prop) (r : α)
    {a b x : α} (hra : Relation.ReflTransGen R r a)
    (hrb : Relation.ReflTransGen R r b)
    (hax : Relation.ReflTransGen R a x) (hbx : Relation.ReflTransGen R b x)
    (hab : ¬ Relation.ReflTransGen R a b) (hba : ¬ Relation.ReflTransGen R b a) :
    ∃ p q y, Relation.ReflTransGen R r p ∧ Relation.ReflTransGen R r q ∧
      R p y ∧ R q y ∧ p ≠ q := by
  classical
  by_contra hno
  have hu : ∀ p q y, Relation.ReflTransGen R r p → Relation.ReflTransGen R r q →
      R p y → R q y → p = q := by
    intro p q y hp hq hpy hqy
    by_contra hpq
    exact hno ⟨p, q, y, hp, hq, hpy, hqy, hpq⟩
  rcases ancestors_comparable_of_unique_parents R r hu hra hrb hax hbx with h | h
  · exact hab h
  · exact hba h

end PEqualNP.Outside.L_meta_5012.Reconvergence

namespace PEqualNP.Outside.L_meta_5012.ORReconvergence

open PEqualNP.TopForm PEqualNP.Outside.L_meta_5012.MutualBudget
  PEqualNP.Outside.L_meta_5012.Reconvergence

lemma support_mono {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit} {w z : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w z) : orIn n C z ⊆ orIn n C w := by
  intro x hx
  exact reach_mem_orIn x (h.trans (mem_orIn_reach x hx))

lemma reach_relevant_of_many {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit}
    {X : Finset (Fin n)} {w z : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w z)
    (hz : 1 < (orIn n C z ∩ X).card) : RelevantReach n C X w z := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head a b step rest ih =>
    have hsub : orIn n C z ∩ X ⊆ orIn n C a ∩ X :=
      Finset.inter_subset_inter_right (support_mono (rest.head step))
    have ha : 1 < (orIn n C a ∩ X).card :=
      lt_of_lt_of_le hz (Finset.card_le_card hsub)
    exact ih.head ⟨step, ha⟩

lemma support_diamond {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit}
    {X : Finset (Fin n)} {r a b : ℕ} {x : Fin n}
    (hra : Relation.ReflTransGen (OrStep n C) r a)
    (hrb : Relation.ReflTransGen (OrStep n C) r b)
    (ha : 1 < (orIn n C a ∩ X).card) (hb : 1 < (orIn n C b ∩ X).card)
    (hax : x ∈ orIn n C a) (hbx : x ∈ orIn n C b)
    (hab : ¬ orIn n C a ⊆ orIn n C b) (hba : ¬ orIn n C b ⊆ orIn n C a) :
    (∃ p q y, RelevantReach n C X r p ∧ RelevantReach n C X r q ∧
      RelevantStep n C X p y ∧ RelevantStep n C X q y ∧ p ≠ q) ∨
    (∃ za zb, za ≠ zb ∧ RelevantReach n C X r za ∧ RelevantReach n C X r zb ∧
      (orIn n C za ∩ X).card ≤ 1 ∧ (orIn n C zb ∩ X).card ≤ 1 ∧
      x ∈ orIn n C za ∧ x ∈ orIn n C zb) := by
  classical
  have hra' := reach_relevant_of_many hra ha
  have hrb' := reach_relevant_of_many hrb hb
  obtain ⟨za, haza, hza, hzax⟩ := relevantBoundary (X := X) (mem_orIn_reach x hax)
  obtain ⟨zb, hbzb, hzb, hzbx⟩ := relevantBoundary (X := X) (mem_orIn_reach x hbx)
  by_cases hzab : za = zb
  · subst zb
    apply Or.inl
    apply incomparable_paths_reconverge (RelevantStep n C X) r hra' hrb' haza hbzb
    · intro h
      exact hba (support_mono (relevantImpliesOr h))
    · intro h
      exact hab (support_mono (relevantImpliesOr h))
  · exact Or.inr ⟨za, zb, hzab, hra'.trans haza, hrb'.trans hbzb, hza, hzb, hzax, hzbx⟩

end PEqualNP.Outside.L_meta_5012.ORReconvergence

import PEqualNP.Defs

-- The first part is the checked proof of L-meta-7897 from this repository (namespace renamed);
-- the mask helpers are from the checked proof of L-meta-17665.

namespace PEqualNP.Outside.L_meta_17749

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
theorem inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
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


lemma andRawEmpty {j : ℕ} (hj : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with he | ⟨k, _, hr, ho, _⟩
  · have := v.isLt
    omega
  · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
    · subst k
      rw [hj] at ho
      cases ho
    · rw [hj] at hof
      cases hof

lemma lastOrBefore {j w : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w (n + j)) :
    w = n + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
      n + j ∈ (gateAt C m).inputs ∧ n + j < n + m ∧
      Relation.ReflTransGen (OrStep n C) w (n + m) := by
  rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
  · exact .inl eq.symm
  · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hstep
    exact .inr ⟨m, hm, ho, hi, hb, hz⟩

lemma lastOrOutside {j m : ℕ} (hAO : IsAO2 n C) (hj : j ∈ junk G C)
    (hm : m < C.gates.length) (ho : (gateAt C m).op = GateOp.or)
    (hi : n + j ∈ (gateAt C m).inputs) (hb : n + j < n + m) :
    m ∈ orN G C \ lam G C := by
  obtain ⟨_, hjop, x, hjx, hx⟩ := junkData hj
  have hNotBelow : ¬ BelowF G C m := by
    intro h
    have hvm : gateVal n C m x = true := (val_or (n := n) (by simp) hm ho).mpr
      ⟨n + j, hi, hb, hjx⟩
    exact Bool.noConfusion (hx.symm.trans (h x hvm))
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro ho hNotBelow)
  · intro hl
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, be⟩ := inputsAsOpnd hAO hm hi
    have hnonempty : (orIn n C (opnd C m b)).Nonempty := by
      fin_cases b
      · exact h0
      · exact h1
    rw [← be, andRawEmpty (n := n) hjop] at hnonempty
    exact Finset.not_nonempty_empty hnonempty

lemma residualTrace (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
      gateVal n C a (pairInput u v) = true ∧ OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
  obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
  have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
  obtain ⟨a, ha, hv⟩ := acceptedTop hL adj'
  obtain ⟨hl, ho, _⟩ := topData ha
  have h := (andValOperands hL.1 hl ho _).mp hv
  rcases operandSupport hL.1 hT hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
  · rcases operandSupport hL.1 hT hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
    · have hxy : x ≠ y := (topAdj hL.1 ha hx hy).ne
      apply (miss ?_).elim
      unfold starEdges
      refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, ?_⟩⟩
      rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    · exact ⟨a, ha, 1, j, hj, hv, hr, hjv⟩
  · exact ⟨a, ha, 0, j, hj, hv, hr, hjv⟩


lemma opposite (b c : Fin 2) : c = b ∨ c = 1 - b := by
  revert b c
  decide

lemma topSides (empty : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) : (side (n := n) C a b).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have hc : a ∈ centreless G C := by
    apply Finset.mem_filter.mpr
    refine ⟨ha, ?_⟩
    fin_cases b
    · exact Or.inl he
    · exact Or.inr he
  rw [empty] at hc
  exact Finset.notMem_empty _ hc

lemma orData {m : ℕ} (hm : m ∈ orN G C \ lam G C) :
    m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
  simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    (Finset.mem_sdiff.mp hm).1

lemma emptyInputOutside (ao : IsAO2 n C) {j m : ℕ}
    (dirty : ¬ BelowF G C j) (empty : orIn n C (n + j) = ∅)
    (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hin : n + j ∈ (gateAt C m).inputs) :
    m ∈ orN G C \ lam G C := by
  have hbad : ¬ BelowF G C m := by
    intro hb
    apply dirty
    intro x hx
    exact hb x ((val_or (n := n) (by simp) hm hop).mpr
      ⟨_, hin, ao.2.1 _ hm _ hin, hx⟩)
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro hop hbad)
  · intro hl
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, hb⟩ := inputsAsOpnd ao hm hin
    have hne : (orIn n C (opnd C m b)).Nonempty := by
      fin_cases b
      · exact h0
      · exact h1
    rw [← hb, empty] at hne
    exact Finset.not_nonempty_empty hne

lemma residualPath (ao : IsAO2 n C) (empty : centreless G C = ∅)
    {a j : ℕ} {b : Fin 2} (ha : a ∈ tops G C) (hj : j ∈ junk G C)
    (path : OrReaches n C (opnd C a b) j) :
    ∃ m ∈ orN G C \ lam G C, n + j ∈ (gateAt C m).inputs ∧
      Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m) := by
  rcases lastOrBefore (orReaches_reach j _ path).1 with he | ⟨m, hm, hop, hin, hlt, hp⟩
  · have hne := topSides empty ha b
    change (orIn n C (opnd C a b)).Nonempty at hne
    rw [he, andRawEmpty (junkData hj).2.1] at hne
    exact (Finset.not_nonempty_empty hne).elim
  · exact ⟨m, lastOrOutside ao hj hm hop hin hlt, hin, hp⟩

lemma mixingRaw (ao : IsAO2 n C) (empty : centreless G C = ∅) {m a : ℕ} {b : Fin 2}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (ha : a ∈ tops G C) (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m)) :
    (orIn n C (n + m)).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hz
  rcases lastOrBefore path with he | ⟨k, hk, hop, hin, hlt, _⟩
  · have hne := topSides empty ha b
    change (orIn n C (opnd C a b)).Nonempty at hne
    rw [he, hz] at hne
    exact Finset.not_nonempty_empty hne
  · have hk' := emptyInputOutside ao (orData hm).2.2 hz hk hop hin
    rw [only, Finset.mem_singleton] at hk'
    omega

lemma singleJunkInput (ao : IsAO2 n C) {m j k : ℕ}
    (hm : m ∈ orN G C \ lam G C) (hne : (orIn n C (n + m)).Nonempty)
    (hj : j ∈ junk G C) (hk : k ∈ junk G C)
    (hjin : n + j ∈ (gateAt C m).inputs) (hkin : n + k ∈ (gateAt C m).inputs) :
    j = k := by
  by_contra hjk
  obtain ⟨p, q, hpq⟩ := binaryInputs ao (orData hm).1
  have hinputs : ∀ w ∈ (gateAt C m).inputs, w = n + j ∨ w = n + k := by
    intro w hw
    simp only [hpq, List.mem_cons, List.not_mem_nil, or_false] at hjin hkin hw
    omega
  obtain ⟨t, ht⟩ := hne
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach t ht) with he | ⟨w, hs, hrest⟩
  · have := t.isLt
    omega
  · obtain ⟨l, _, he, _, hin, _⟩ := hs
    have hl : l = m := by omega
    subst l
    have ht' := reach_mem_orIn t hrest
    rcases hinputs w hin with rfl | rfl
    · rw [andRawEmpty (junkData hj).2.1] at ht'
      exact Finset.notMem_empty _ ht'
    · rw [andRawEmpty (junkData hk).2.1] at ht'
      exact Finset.notMem_empty _ ht'

lemma cleanAdj (ao : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    {t w : Fin n} (ht : t ∈ side C a b) (hw : w ∈ side C a (1 - b)) :
    (G.deleteEdges ↑(Ustar G C)).Adj t w := by
  have cross {u v : Fin n} (hu : u ∈ side C a 0) (hv : v ∈ side C a 1) :
      (G.deleteEdges ↑(Ustar G C)).Adj u v := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨topAdj ao ha hu hv, ?_⟩
    intro he
    apply (Finset.mem_sdiff.mp (show s(u, v) ∈ Ustar G C from he)).2
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
      ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩⟩
  fin_cases b
  · exact cross ht hw
  · exact (cross hw ht).symm

lemma firingTop (ao : IsAO2 n C) {a m : ℕ} {b : Fin 2} {w : Fin n}
    (ha : a ∈ tops G C)
    (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m))
    (hw : w ∈ side C a (1 - b)) (x : Fin n → Bool)
    (hmx : gateVal n C m x = true) (hwx : x w = true) :
    graphFun G ∅ x = true := by
  obtain ⟨haLen, haOp, haBelow⟩ := topData ha
  apply haBelow x ((andValOperands ao haLen haOp x).mpr ?_)
  intro c
  rcases opposite b c with rfl | rfl
  · exact orStep_up (n := n) (by simp) path hmx
  · exact sideVal hw hwx

lemma oppositeEndpoint (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C = ∅) {m a : ℕ} {b : Fin 2} {u v : Fin n}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (ha : a ∈ tops G C) (hv : gateVal n C a (pairInput u v) = true)
    (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m)) :
    ∃ w ∈ side C a (1 - b), w = u ∨ w = v := by
  obtain ⟨al, aop, ab⟩ := topData ha
  have hv' := (andValOperands least.1 al aop _).mp hv (1 - b)
  rcases operandSupport least.1 top al aop hv' with h | ⟨j, hj, hr, _⟩
  · exact h
  · obtain ⟨k, hk, _, hp⟩ := residualPath least.1 empty ha hj hr
    rw [only, Finset.mem_singleton] at hk
    subst k
    exfalso
    apply (orData hm).2.2
    intro x hx
    apply ab x ((andValOperands least.1 al aop x).mpr ?_)
    intro c
    rcases opposite b c with rfl | rfl
    · exact orStep_up (n := n) (by simp) path hx
    · exact orStep_up (n := n) (by simp) hp hx

lemma rawCoverShape (ao : IsAO2 n C) {m w : ℕ}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (hw : w < n + m) :
    (orIn n C w).card ≤ 1 ∨
      ∃ z : Fin n, ∀ t ∈ orIn n C w, (G.deleteEdges ↑(Ustar G C)).Adj t z := by
  by_cases hcard : (orIn n C w).card ≤ 1
  · exact Or.inl hcard
  have hne : (orIn n C w).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, hu⟩ := hne
  by_cases hi : w < n
  · exfalso
    apply hcard
    apply Finset.card_le_one.mpr
    intro t ht v hv
    have eq (z : Fin n) (hz : z ∈ orIn n C w) : (z : ℕ) = w := by
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach z hz) with he | ⟨_, hs, _⟩
      · exact he.symm
      · obtain ⟨k, _, he, _, _, _⟩ := hs
        omega
    exact Fin.ext ((eq t ht).trans (eq v hv).symm)
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  have hkm : k < m := by omega
  have hkl := hkm.trans (orData hm).1
  have hko : (gateAt C k).op = GateOp.or := by
    rcases ao.1 _ (gateAt_mem hkl) with h | h
    · rw [andRawEmpty h] at hu
      exact (Finset.notMem_empty _ hu).elim
    · exact h
  have hbelow : ¬ BelowF G C k := by
    intro hb
    have hv := reach_var_val (pairInput u u) _ u (mem_orIn_reach u hu) (pairInput_left u u)
    exact G.irrefl ((graphFun_pair G u u).mp (hb _ hv))
  have hkN : k ∈ orN G C := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hkl (And.intro hko hbelow)
  have hkL : k ∈ lam G C := by
    by_contra hn
    have hk := Finset.mem_sdiff.mpr ⟨hkN, hn⟩
    rw [only, Finset.mem_singleton] at hk
    omega
  obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hkL
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1 - b)).card)
  exact Or.inr ⟨z, fun t ht => cleanAdj ao ha b
    (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz⟩

lemma falseJunkCover (ao : IsAO2 n C) (top : TopForm G C) {m : ℕ}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (x : Fin n → Bool) :
    ∀ j < m, j ∈ junk G C →
      (∀ u v : Fin n, s(u, v) ∈ Ustar G C → gateVal n C j (pairInput u v) = true) →
      gateVal n C j x = false →
      ∃ S : Finset (Fin n), (S.card ≤ 1 ∨
        ∃ z : Fin n, ∀ t ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj t z) ∧
        (∀ u v : Fin n, s(u, v) ∈ Ustar G C → u ∈ S ∨ v ∈ S) ∧
        ∀ t ∈ S, x t = false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjm hj fires hx
    obtain ⟨jl, jo, _⟩ := junkData hj
    have hfalse : ∃ b : Fin 2, val C (List.ofFn x) (opnd C j b) = false := by
      by_contra hn
      have hv := (andValOperands ao jl jo x).mpr
        (fun b => by
          cases hval : val C (List.ofFn x) (opnd C j b) with
          | true => rfl
          | false => exact (hn ⟨b, hval⟩).elim)
      exact Bool.false_ne_true (hx.symm.trans hv)
    obtain ⟨b, hb⟩ := hfalse
    have firesOp (u v : Fin n) (he : s(u, v) ∈ Ustar G C) :
        val C (List.ofFn (pairInput u v)) (opnd C j b) = true :=
      (andValOperands ao jl jo _).mp (fires u v he) b
    have direct (k : ℕ) (hk : k ∈ junk G C) (hr : OrReaches n C (opnd C j b) k) :
        opnd C j b = n + k := by
      rcases lastOrBefore (orReaches_reach k _ hr).1 with h | ⟨r, rl, ro, ri, rb, rp⟩
      · exact h
      · have hr' := lastOrOutside ao hk rl ro ri rb
        rw [only, Finset.mem_singleton] at hr'
        have hle := orStep_le rp
        have hlt := opndBound ao jl b
        omega
    by_cases hd : ∃ k, k ∈ junk G C ∧ opnd C j b = n + k
    · obtain ⟨k, hk, he⟩ := hd
      have hbnd := opndBound ao jl b
      have hkj : k < j := by omega
      apply ih k hkj (hkj.trans hjm) hk
      · intro u v hu
        have hv := firesOp u v hu
        rw [he] at hv
        exact hv
      · rw [he] at hb
        exact hb
    · refine ⟨orIn n C (opnd C j b), rawCoverShape ao only hm (by
        have := opndBound ao jl b
        omega), ?_, ?_⟩
      · intro u v he
        rcases operandSupport ao top jl jo (firesOp u v he) with ⟨t, ht, rfl | rfl⟩ | ⟨k, hk, hr, _⟩
        · exact Or.inl ht
        · exact Or.inr ht
        · exact (hd ⟨k, hk, direct k hk hr⟩).elim
      · intro t ht
        apply Bool.eq_false_iff.mpr
        intro ht'
        exact Bool.false_ne_true (hb.symm.trans (reach_var_val x _ t (mem_orIn_reach t ht) ht'))

lemma finish (least : IsLeastAO G C) (top : TopForm G C)
    (hjunk : 2 ≤ (junk G C).card)
    (budget : 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ 3)
    (nonempty : ∃ u v : Fin n, s(u, v) ∈ Ustar G C) :
    3 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ∧
    ∃ t : Fin n, ∀ u v : Fin n, s(u, v) ∈ Ustar G C →
      ∃ w : Fin n, (w = u ∨ w = v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj t w ∧
        ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false →
          ∃ S : Finset (Fin n), (S.card ≤ 1 ∨
            ∃ z : Fin n, ∀ y ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj y z) ∧
            (∀ p q : Fin n, s(p, q) ∈ Ustar G C → p ∈ S ∨ q ∈ S) ∧
            ∀ y ∈ S, x y = false := by
  have empty : centreless G C = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨u, v, he⟩ := nonempty
  obtain ⟨a, ha, b, j, hj, _, hr, _⟩ := residualTrace least top he
  obtain ⟨m, hm, hin, path⟩ := residualPath least.1 empty ha hj hr
  have hpos := Finset.card_pos.mpr ⟨m, hm⟩
  have only : orN G C \ lam G C = {m} := by
    ext k
    rw [Finset.mem_singleton]
    exact ⟨fun hk => Finset.card_le_one.mp (by omega) k hk m hm, fun h => h.symm ▸ hm⟩
  obtain ⟨t, ht⟩ := mixingRaw least.1 empty only hm ha path
  refine ⟨by omega, t, ?_⟩
  have hml := (orData hm).1
  have hmo := (orData hm).2.1
  have hlt := least.1.2.1 m hml _ hin
  have uniform (p q : Fin n) (hpq : s(p, q) ∈ Ustar G C) :
      gateVal n C j (pairInput p q) = true := by
    obtain ⟨a', ha', b', k, hk, _, hr', hv⟩ := residualTrace least top hpq
    obtain ⟨l, hl, hkin, _⟩ := residualPath least.1 empty ha' hk hr'
    rw [only, Finset.mem_singleton] at hl
    subst l
    have heq := singleJunkInput least.1 hm ⟨t, ht⟩ hj hk hin hkin
    rwa [heq]
  intro p q hpq
  obtain ⟨a', ha', b', k, hk, hav, hr', _⟩ := residualTrace least top hpq
  obtain ⟨l, hl, _, hp⟩ := residualPath least.1 empty ha' hk hr'
  rw [only, Finset.mem_singleton] at hl
  subst l
  obtain ⟨w, hw, hend⟩ := oppositeEndpoint least top empty only hm ha' hav hp
  have ht' : t ∈ side C a' b' :=
    reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
  refine ⟨w, hend, cleanAdj least.1 ha' b' ht' hw, ?_⟩
  intro x hx hf
  have hjx : gateVal n C j x = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hmx : gateVal n C m x = true :=
      (val_or (n := n) (by simp) hml hmo).mpr ⟨_, hin, hlt, htrue⟩
    exact Bool.false_ne_true (hf.symm.trans (firingTop least.1 ha' hp hw x hmx hx))
  exact falseJunkCover least.1 top only hm x j (by omega) hj uniform hjx

-- The finite check only needs the singleton inputs 1_w.
abbrev graph : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]

def edgeList : List (Sym2 (Fin 11)) :=
  [s(0, 9), s(0, 10), s(1, 4), s(1, 8), s(2, 5), s(2, 10), s(3, 6), s(3, 7),
   s(4, 8), s(4, 10), s(5, 8), s(5, 9), s(6, 7), s(6, 10), s(7, 9), s(8, 9)]

lemma edgeList_pair : ∀ u v : Fin 11, s(u, v) ∈ edgeList ↔ graph.Adj u v := by decide

lemma edgeList_edges : edgeList.toFinset = graph.edgeFinset := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
    simpa only [List.mem_toFinset, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
      edgeList_pair u v

lemma edgeList_nodup : edgeList.Nodup := by decide

def adjacency (a b : Fin 11) : Bool :=
  ((#[1536, 272, 1056, 192, 1282, 772, 1160, 584, 562, 417, 85] : Array ℕ)[a.val]!).testBit b.val

lemma adjacency_spec : ∀ a b : Fin 11, adjacency a b = true ↔ graph.Adj a b := by decide

def hits (ok : Fin 11 → Bool) : Sym2 (Fin 11) → Bool :=
  Sym2.lift ⟨fun u v => ok u || ok v, fun u v => Bool.or_comm (ok u) (ok v)⟩

def covers (es : List (Sym2 (Fin 11))) (ok : Fin 11 → Bool) : Bool :=
  es.all (hits ok)

lemma covers_of_pairs {es : List (Sym2 (Fin 11))} {ok : Fin 11 → Bool}
    (h : ∀ u v : Fin 11, s(u, v) ∈ es → ok u = true ∨ ok v = true) :
    covers es ok = true := by
  apply List.all_eq_true.mpr
  intro e he
  induction e using Sym2.ind with
  | h u v => simpa only [hits, Sym2.lift_mk, Bool.or_eq_true] using h u v he

def cleanNeighbor (es : List (Sym2 (Fin 11))) (a b : Fin 11) : Bool :=
  adjacency a b && !(decide (s(a, b) ∈ es))

lemma cleanNeighbor_spec (es : List (Sym2 (Fin 11))) (a b : Fin 11) :
    cleanNeighbor es a b = true ↔ (graph.deleteEdges ↑es.toFinset).Adj a b := by
  simp [cleanNeighbor, adjacency_spec]

def coverAvoiding (es : List (Sym2 (Fin 11))) (w : Fin 11) : Bool :=
  (List.finRange 11).any (fun z => covers es (fun v => decide (v = z ∧ v ≠ w))) ||
  (List.finRange 11).any (fun z => covers es (fun v => cleanNeighbor es v z && decide (v ≠ w)))

def rejectedAt (t : Fin 11) (es : List (Sym2 (Fin 11))) : Bool :=
  !(covers es (cleanNeighbor es t) &&
    covers es (fun w => cleanNeighbor es t w && coverAvoiding es w))

def candidateEdge (t : Fin 11) (e : Sym2 (Fin 11)) : Bool :=
  hits (adjacency t) e && !hits (fun w => decide (w = t)) e

def incidentToNeighbors (t : Fin 11) : List (Sym2 (Fin 11)) :=
  edgeList.filter (candidateEdge t)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
lemma fourEdgeCheck (t : Fin 11) :
    ((incidentToNeighbors t).sublistsLen 4).all (rejectedAt t) = true := by
  fin_cases t <;> decide

lemma graphBound (U : Finset (Sym2 (Fin 11))) (hU : U ⊆ graph.edgeFinset)
    (t : Fin 11)
    (h : ∀ u v : Fin 11, s(u, v) ∈ U →
      ∃ w : Fin 11, (w = u ∨ w = v) ∧ (graph.deleteEdges ↑U).Adj t w ∧
        ∃ S : Finset (Fin 11), (S.card ≤ 1 ∨
          ∃ z : Fin 11, ∀ y ∈ S, (graph.deleteEdges ↑U).Adj y z) ∧
          (∀ p q : Fin 11, s(p, q) ∈ U → p ∈ S ∨ q ∈ S) ∧ w ∉ S) :
    U.card ≤ 3 := by
  by_contra hn
  obtain ⟨T, hTU, hT⟩ := Finset.exists_subset_card_eq (s := U) (n := 4) (by omega)
  have hTadj (e : Sym2 (Fin 11)) (he : e ∈ T) : candidateEdge t e = true := by
    induction e using Sym2.ind with
    | h u v =>
      have hEdge := hTU he
      obtain ⟨w, hw, hadj, _⟩ := h u v hEdge
      have hw' := (adjacency_spec t w).mpr (SimpleGraph.deleteEdges_adj.mp hadj).1
      have hno : s(t, w) ∉ U := (SimpleGraph.deleteEdges_adj.mp hadj).2
      have hu : u ≠ t := by
        intro hut
        subst u
        rcases hw with rfl | rfl
        · exact (graph.deleteEdges ↑U).irrefl hadj
        · exact hno hEdge
      have hv : v ≠ t := by
        intro hvt
        subst v
        rcases hw with rfl | rfl
        · exact hno (Sym2.eq_swap ▸ hEdge)
        · exact (graph.deleteEdges ↑U).irrefl hadj
      have hit : (adjacency t u || adjacency t v) = true := by
        rw [Bool.or_eq_true]
        rcases hw with rfl | rfl
        · exact Or.inl hw'
        · exact Or.inr hw'
      simp [candidateEdge, hits, hit, hu, hv]
  let es := (incidentToNeighbors t).filter fun e => decide (e ∈ T)
  have heT : es.toFinset = T := by
    ext e
    simp only [es, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    refine ⟨And.right, fun he => ⟨?_, he⟩⟩
    exact List.mem_filter.mpr
      ⟨List.mem_toFinset.mp (edgeList_edges.symm ▸ hU (hTU he)), hTadj e he⟩
  have hsub : List.Sublist es (incidentToNeighbors t) := List.filter_sublist
  have hnbr : List.Sublist (incidentToNeighbors t) edgeList := List.filter_sublist
  have helen : es.length = 4 := by
    rw [← List.toFinset_card_of_nodup (edgeList_nodup.sublist (hsub.trans hnbr)), heT, hT]
  have hrejected := List.all_eq_true.mp (fourEdgeCheck t) es (List.mem_sublistsLen.mpr ⟨hsub, helen⟩)
  have toU {e : Sym2 (Fin 11)} (he : e ∈ es) : e ∈ U :=
    hTU (heT ▸ List.mem_toFinset.mpr he)
  have toClean {a b : Fin 11} (hab : (graph.deleteEdges ↑U).Adj a b) :
      cleanNeighbor es a b = true := by
    apply (cleanNeighbor_spec es a b).mpr
    obtain ⟨hG, hnU⟩ := SimpleGraph.deleteEdges_adj.mp hab
    exact SimpleGraph.deleteEdges_adj.mpr ⟨hG, fun he => hnU (hTU (heT ▸ he))⟩
  have avoid (w : Fin 11) (S : Finset (Fin 11))
      (hs : S.card ≤ 1 ∨ ∃ z : Fin 11, ∀ y ∈ S, (graph.deleteEdges ↑U).Adj y z)
      (hc : ∀ p q : Fin 11, s(p, q) ∈ U → p ∈ S ∨ q ∈ S)
      (hw : w ∉ S) : coverAvoiding es w = true := by
    have coverWith {ok : Fin 11 → Bool} (hok : ∀ y ∈ S, ok y = true) :
        covers es ok = true :=
      covers_of_pairs fun p q he => (hc p q (toU he)).imp (hok p) (hok q)
    unfold coverAvoiding
    rw [Bool.or_eq_true]
    rcases hs with hcard | ⟨z, hz⟩
    · have hSne : S.Nonempty := by
        have hes : es ≠ [] := by intro he; simp [he] at helen
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hes
        induction e using Sym2.ind with
        | h p q =>
          rcases hc p q (toU he) with hp | hq
          · exact ⟨p, hp⟩
          · exact ⟨q, hq⟩
      obtain ⟨z, hz⟩ := hSne
      left
      exact List.any_eq_true.mpr ⟨z, List.mem_finRange z, coverWith fun y hy =>
        decide_eq_true ⟨Finset.card_le_one.mp hcard y hy z hz, fun h => hw (h ▸ hy)⟩⟩
    · right
      exact List.any_eq_true.mpr ⟨z, List.mem_finRange z, coverWith fun y hy =>
        by simp [toClean (hz y hy), show y ≠ w from fun h => hw (h ▸ hy)]⟩
  have hall : covers es (fun w => cleanNeighbor es t w && coverAvoiding es w) = true := by
    apply covers_of_pairs
    intro u v he
    obtain ⟨w, hend, hadj, S, hshape, hcover, havoid⟩ := h u v (toU he)
    have hw : (cleanNeighbor es t w && coverAvoiding es w) = true := by
      simp [toClean hadj, avoid w S hshape hcover havoid]
    rcases hend with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw
  have hbase : covers es (cleanNeighbor es t) = true := by
    apply covers_of_pairs
    intro u v he
    obtain ⟨w, hend, hadj, _⟩ := h u v (toU he)
    rcases hend with rfl | rfl
    · exact Or.inl (toClean hadj)
    · exact Or.inr (toClean hadj)
  simp [rejectedAt, hbase, hall] at hrejected

lemma boundForCircuit (C : Circuit) (j k m : ℕ)
    (least : IsLeastAO graph C) (top : TopForm graph C)
    (hjk : junk graph C = {j, k}) (hempty : centreless graph C = ∅)
    (hread : readers 11 C j = {k}) (hm : orN graph C \ lam graph C = {m}) :
    (Ustar graph C).card ≤ 3 := by
  have hr : k ∈ readers 11 C j := by simp [hread]
  obtain ⟨hkr, hinput⟩ := Finset.mem_filter.mp hr
  have hjkLt : j < k := by
    have := least.1.2.1 k (Finset.mem_range.mp hkr) _ hinput
    omega
  have hJ : (junk graph C).card = 2 := by simp [hjk, hjkLt.ne]
  have budget : 2 * (centreless graph C).card + (junk graph C).card +
      (orN graph C \ lam graph C).card ≤ 3 := by simp [hempty, hJ, hm]
  by_cases hU : (Ustar graph C).Nonempty
  · obtain ⟨e, he⟩ := hU
    have hpair : ∃ u v : Fin 11, s(u, v) ∈ Ustar graph C := by
      induction e using Sym2.ind with | h u v => exact ⟨u, v, he⟩
    obtain ⟨_, t, ht⟩ := finish least top (by omega) budget hpair
    apply graphBound (Ustar graph C) Finset.sdiff_subset t
    intro u v huv
    obtain ⟨w, hw, hclean, hcover⟩ := ht u v huv
    have hf : graphFun graph ∅ (pairInput w w) = false := by
      apply Bool.eq_false_iff.mpr
      exact fun hh => graph.irrefl ((graphFun_pair graph w w).mp hh)
    obtain ⟨S, hs, hS, hfalse⟩ := hcover (pairInput w w) (pairInput_left w w) hf
    exact ⟨w, hw, hclean, S, hs, hS, fun h => Bool.false_ne_true ((hfalse w h).symm.trans (pairInput_left w w))⟩
  · rw [Finset.not_nonempty_iff_eq_empty.mp hU]
    decide


def pop11 (m : ℕ) : ℕ :=
  (List.finRange 11).countP fun i => m.testBit i.val

def allPow2 : ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, base, f => f base
  | k + 1, base, f => allPow2 k base f && allPow2 k (base + 2 ^ k) f


lemma allPow2_true : ∀ k base (f : ℕ → Bool),
    allPow2 k base f = true → ∀ m, base ≤ m → m < base + 2 ^ k → f m = true := by
  intro k
  induction k with
  | zero =>
    intro base f hf m h1 h2
    have heq : m = base := by omega
    subst heq; exact hf
  | succ k ih =>
    intro base f hf m h1 h2
    simp only [allPow2, Bool.and_eq_true] at hf
    by_cases hlt : m < base + 2 ^ k
    · exact ih base f hf.1 m h1 hlt
    · exact ih (base + 2 ^ k) f hf.2 m (by omega) (by rw [Nat.pow_succ] at h2; omega)

def maskOf (S : Finset (Fin 11)) : ℕ :=
  ∑ i ∈ S, 2 ^ i.val


lemma sum_pow2_lt (n : ℕ) : ∀ (T : Finset ℕ), (∀ x ∈ T, x < n) → ∑ x ∈ T, 2 ^ x < 2 ^ n := by
  induction n with
  | zero =>
    intro T hT
    have hE : T = ∅ := Finset.eq_empty_of_forall_notMem fun x hx => Nat.not_lt_zero x (hT x hx)
    simp [hE]
  | succ n ih =>
    intro T hT
    by_cases hn : n ∈ T
    · have hsub : ∀ x ∈ T.erase n, x < n := by
        intro x hx
        have h1 := (Finset.mem_erase.mp hx).1
        have h2 := hT x (Finset.mem_erase.mp hx).2
        omega
      have h1 := ih (T.erase n) hsub
      have h2 := Finset.add_sum_erase T (fun x => 2 ^ x) hn
      rw [Nat.pow_succ]
      omega
    · have hsub : ∀ x ∈ T, x < n := by
        intro x hx
        have h2 := hT x hx
        have hne : x ≠ n := fun heq => hn (heq ▸ hx)
        omega
      have h1 := ih T hsub
      rw [Nat.pow_succ]
      omega

lemma maskOf_lt (S : Finset (Fin 11)) : maskOf S < 2048 := by
  unfold maskOf
  have h1 : ∑ i ∈ S, 2 ^ i.val = ∑ x ∈ S.image Fin.val, 2 ^ x := by
    rw [Finset.sum_image (fun a _ b _ h => Fin.ext h)]
  rw [h1]
  have h2 := sum_pow2_lt 11 (S.image Fin.val) (fun x hx => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact i.isLt)
  simpa using h2

lemma testBit_add_of_disj : ∀ (k x y : ℕ),
    (∀ j, x.testBit j = true → y.testBit j = false) →
    (x + y).testBit k = (x.testBit k || y.testBit k) := by
  intro k
  induction k with
  | zero =>
    intro x y h
    have h0 := h 0
    simp only [Nat.testBit_zero, decide_eq_true_eq, decide_eq_false_iff_not] at h0 ⊢
    by_cases hx : x % 2 = 1
    · have hy : y % 2 ≠ 1 := h0 hx
      have hxy : (x + y) % 2 = 1 := by omega
      simp [hx, hxy]
    · by_cases hy : y % 2 = 1
      · have hxy : (x + y) % 2 = 1 := by omega
        simp [hx, hy, hxy]
      · have hxy : (x + y) % 2 ≠ 1 := by omega
        simp [hx, hy, hxy]
  | succ k ih =>
    intro x y h
    have h0 := h 0
    simp only [Nat.testBit_zero, decide_eq_true_eq, decide_eq_false_iff_not] at h0
    have hdiv : (x + y) / 2 = x / 2 + y / 2 := by omega
    rw [Nat.testBit_succ, hdiv, Nat.testBit_succ, Nat.testBit_succ]
    exact ih (x / 2) (y / 2) fun j hj => by
      have h1 := h (j + 1)
      rw [Nat.testBit_succ, Nat.testBit_succ] at h1
      exact h1 hj

lemma testBit_sum_pow2 (T : Finset ℕ) : ∀ j : ℕ,
    (∑ x ∈ T, 2 ^ x).testBit j = decide (j ∈ T) := by
  induction T using Finset.induction_on with
  | empty => intro j; simp
  | insert a s ha ih =>
    intro j
    rw [Finset.sum_insert ha]
    have hdisj : ∀ k, (2 ^ a).testBit k = true → (∑ x ∈ s, 2 ^ x).testBit k = false := by
      intro k hk
      rw [Nat.testBit_two_pow] at hk
      simp only [decide_eq_true_eq] at hk
      subst hk
      rw [ih a]
      simp [ha]
    rw [testBit_add_of_disj j _ _ hdisj, Nat.testBit_two_pow, ih j]
    by_cases hja : a = j
    · subst hja; simp
    · simp [hja, Ne.symm hja]

lemma maskOf_testBit (S : Finset (Fin 11)) (i : Fin 11) :
    (maskOf S).testBit i.val = decide (i ∈ S) := by
  unfold maskOf
  have h1 : ∑ j ∈ S, 2 ^ j.val = ∑ x ∈ S.image Fin.val, 2 ^ x := by
    rw [Finset.sum_image (fun a _ b _ h => Fin.ext h)]
  rw [h1, testBit_sum_pow2]
  simp only [Finset.mem_image]
  by_cases hi : i ∈ S
  · have hex : ∃ x ∈ S, x.val = i.val := ⟨i, hi, rfl⟩
    simp [hi, hex]
  · have hne : ¬ ∃ x ∈ S, x.val = i.val := by
      rintro ⟨x, hx, hxv⟩
      exact hi (Fin.ext hxv ▸ hx)
    simp [hi, hne]

lemma pop11_maskOf (S : Finset (Fin 11)) : pop11 (maskOf S) = S.card := by
  unfold pop11
  have h1 : ((List.finRange 11).countP fun i => (maskOf S).testBit i.val) =
      ((List.finRange 11).filter fun i => decide (i ∈ S)).length := by
    rw [List.countP_eq_length_filter]
    congr 1
    exact List.filter_congr fun i _ => maskOf_testBit S i
  rw [h1]
  have hnd : ((List.finRange 11).filter fun i => decide (i ∈ S)).Nodup :=
    (List.nodup_finRange 11).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext i
  simp

-- Final step for L-meta-17749: the cover bound of the statement against the common-vertex shape.

def indepMasks : List ℕ :=
  [1288, 1408, 15, 71, 135, 43, 99, 163, 29, 269, 85, 149, 325, 389, 57, 113, 177, 526, 582,
   1066, 1546, 1186, 540, 596]

def indepOK (m : ℕ) : Bool :=
  (List.finRange 11).all fun u => (List.finRange 11).all fun v =>
    !(adjacency u v && m.testBit u.val && m.testBit v.val)

lemma indepMasks_ok : indepMasks.all indepOK = true := by decide

lemma indep_false (m : ℕ) (hm : m ∈ indepMasks) :
    graphFun graph ∅ (fun v : Fin 11 => m.testBit v.val) = false := by
  have h1 := List.all_eq_true.mp indepMasks_ok m hm
  apply Bool.eq_false_iff.mpr
  intro hh
  unfold graphFun at hh
  rw [Bool.or_eq_true] at hh
  rcases hh with hh | hh
  · have := of_decide_eq_true hh
    obtain ⟨a, ha, _⟩ := this
    exact absurd ha (Finset.notMem_empty a)
  · obtain ⟨u, v, huv, hu, hv⟩ := of_decide_eq_true hh
    have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1 u (List.mem_finRange u)) v
      (List.mem_finRange v)
    have h3 := (adjacency_spec u v).mpr huv
    simp only at hu hv
    rw [h3, hu, hv] at h2
    exact absurd h2 (by decide)

def coverAvoidingX (es : List (Sym2 (Fin 11))) (x : Fin 11 → Bool) : Bool :=
  (List.finRange 11).any (fun z => covers es (fun v => decide (v = z) && !x v)) ||
  (List.finRange 11).any (fun z => covers es (fun v => cleanNeighbor es v z && !x v))

def goodW (es : List (Sym2 (Fin 11))) (t w : Fin 11) : Bool :=
  cleanNeighbor es t w &&
    indepMasks.all (fun m => !m.testBit w.val || coverAvoidingX es (fun v => m.testBit v.val))

def uncovered (es : List (Sym2 (Fin 11))) (m : ℕ) : Bool :=
  edgeList.any (fun e => !decide (e ∈ es) && !hits (fun v => m.testBit v.val) e)

def bigCover (es : List (Sym2 (Fin 11))) : Bool :=
  allPow2 11 0 (fun m => uncovered es m || decide (es.length + 4 ≤ pop11 m))

def passes (t : Fin 11) (es : List (Sym2 (Fin 11))) : Bool :=
  !(covers es (goodW es t)) || bigCover es

set_option maxRecDepth 6000 in
set_option maxHeartbeats 4000000 in
lemma finalCheck (t : Fin 11) :
    ((incidentToNeighbors t).sublistsLen 2 ++ (incidentToNeighbors t).sublistsLen 3).all
      (passes t) = true := by
  fin_cases t <;> decide +kernel

lemma graphFinal (U : Finset (Sym2 (Fin 11))) (hU : U ⊆ graph.edgeFinset) (t : Fin 11)
    (h : ∀ u v : Fin 11, s(u, v) ∈ U →
      ∃ w : Fin 11, (w = u ∨ w = v) ∧ (graph.deleteEdges ↑U).Adj t w ∧
        ∀ x : Fin 11 → Bool, x w = true → graphFun graph ∅ x = false →
          ∃ S : Finset (Fin 11), (S.card ≤ 1 ∨
            ∃ z : Fin 11, ∀ y ∈ S, (graph.deleteEdges ↑U).Adj y z) ∧
            (∀ p q : Fin 11, s(p, q) ∈ U → p ∈ S ∨ q ∈ S) ∧ ∀ y ∈ S, x y = false)
    (h2 : 2 ≤ U.card)
    (K : Finset (Fin 11))
    (hKc : ∀ a b : Fin 11, (graph.deleteEdges ↑U).Adj a b → a ∈ K ∨ b ∈ K)
    (hKn : K.card ≤ U.card + 3) : False := by
  have h3 : U.card ≤ 3 := by
    apply graphBound U hU t
    intro u v huv
    obtain ⟨w, hw, hclean, hcover⟩ := h u v huv
    have hf : graphFun graph ∅ (pairInput w w) = false := by
      apply Bool.eq_false_iff.mpr
      exact fun hh => graph.irrefl ((graphFun_pair graph w w).mp hh)
    obtain ⟨S, hs, hS, hfalse⟩ := hcover (pairInput w w) (pairInput_left w w) hf
    exact ⟨w, hw, hclean, S, hs, hS, fun h =>
      Bool.false_ne_true ((hfalse w h).symm.trans (pairInput_left w w))⟩
  have hTadj (e : Sym2 (Fin 11)) (he : e ∈ U) : candidateEdge t e = true := by
    induction e using Sym2.ind with
    | h u v =>
      have hEdge := he
      obtain ⟨w, hw, hadj, _⟩ := h u v hEdge
      have hw' := (adjacency_spec t w).mpr (SimpleGraph.deleteEdges_adj.mp hadj).1
      have hno : s(t, w) ∉ U := (SimpleGraph.deleteEdges_adj.mp hadj).2
      have hu : u ≠ t := by
        intro hut
        subst u
        rcases hw with rfl | rfl
        · exact (graph.deleteEdges ↑U).irrefl hadj
        · exact hno hEdge
      have hv : v ≠ t := by
        intro hvt
        subst v
        rcases hw with rfl | rfl
        · exact hno (Sym2.eq_swap ▸ hEdge)
        · exact (graph.deleteEdges ↑U).irrefl hadj
      have hit : (adjacency t u || adjacency t v) = true := by
        rw [Bool.or_eq_true]
        rcases hw with rfl | rfl
        · exact Or.inl hw'
        · exact Or.inr hw'
      simp [candidateEdge, hits, hit, hu, hv]
  let es := (incidentToNeighbors t).filter fun e => decide (e ∈ U)
  have heT : es.toFinset = U := by
    ext e
    simp only [es, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    refine ⟨And.right, fun he => ⟨?_, he⟩⟩
    exact List.mem_filter.mpr
      ⟨List.mem_toFinset.mp (edgeList_edges.symm ▸ hU he), hTadj e he⟩
  have hsub : List.Sublist es (incidentToNeighbors t) := List.filter_sublist
  have hnbr : List.Sublist (incidentToNeighbors t) edgeList := List.filter_sublist
  have helen : es.length = U.card := by
    rw [← List.toFinset_card_of_nodup (edgeList_nodup.sublist (hsub.trans hnbr)), heT]
  have hmem : es ∈ (incidentToNeighbors t).sublistsLen 2 ++
      (incidentToNeighbors t).sublistsLen 3 := by
    rw [List.mem_append, List.mem_sublistsLen, List.mem_sublistsLen]
    have h4 : U.card = 2 ∨ U.card = 3 := by omega
    rcases h4 with h4 | h4
    · exact Or.inl ⟨hsub, by omega⟩
    · exact Or.inr ⟨hsub, by omega⟩
  have hpass := List.all_eq_true.mp (finalCheck t) es hmem
  have toU {e : Sym2 (Fin 11)} (he : e ∈ es) : e ∈ U := by
    rw [← heT]
    exact List.mem_toFinset.mpr he
  have ofU {e : Sym2 (Fin 11)} (he : e ∈ U) : e ∈ es := by
    rw [← heT] at he
    exact List.mem_toFinset.mp he
  have toClean {a b : Fin 11} (hab : (graph.deleteEdges ↑U).Adj a b) :
      cleanNeighbor es a b = true := by
    apply (cleanNeighbor_spec es a b).mpr
    obtain ⟨hG, hnU⟩ := SimpleGraph.deleteEdges_adj.mp hab
    exact SimpleGraph.deleteEdges_adj.mpr ⟨hG, fun he => hnU (heT ▸ he)⟩
  have avoid (x : Fin 11 → Bool) (S : Finset (Fin 11))
      (hs : S.card ≤ 1 ∨ ∃ z : Fin 11, ∀ y ∈ S, (graph.deleteEdges ↑U).Adj y z)
      (hc : ∀ p q : Fin 11, s(p, q) ∈ U → p ∈ S ∨ q ∈ S)
      (hx : ∀ y ∈ S, x y = false) : coverAvoidingX es x = true := by
    have coverWith {ok : Fin 11 → Bool} (hok : ∀ y ∈ S, ok y = true) :
        covers es ok = true :=
      covers_of_pairs fun p q he => (hc p q (toU he)).imp (hok p) (hok q)
    unfold coverAvoidingX
    rw [Bool.or_eq_true]
    rcases hs with hcard | ⟨z, hz⟩
    · have hSne : S.Nonempty := by
        have hes : es ≠ [] := by
          intro he
          rw [he] at helen
          simp at helen
          omega
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hes
        induction e using Sym2.ind with
        | h p q =>
          rcases hc p q (toU he) with hp | hq
          · exact ⟨p, hp⟩
          · exact ⟨q, hq⟩
      obtain ⟨z, hz⟩ := hSne
      left
      exact List.any_eq_true.mpr ⟨z, List.mem_finRange z, coverWith fun y hy => by
        simp [Finset.card_le_one.mp hcard y hy z hz, hx z hz]⟩
    · right
      exact List.any_eq_true.mpr ⟨z, List.mem_finRange z, coverWith fun y hy => by
        simp [toClean (hz y hy), hx y hy]⟩
  have hphi : covers es (goodW es t) = true := by
    apply covers_of_pairs
    intro u v he
    obtain ⟨w, hend, hadj, hcover⟩ := h u v (toU he)
    have hw : goodW es t w = true := by
      unfold goodW
      rw [Bool.and_eq_true]
      refine ⟨toClean hadj, List.all_eq_true.mpr fun m hm => ?_⟩
      rw [Bool.or_eq_true]
      by_cases hb : m.testBit w.val = true
      · right
        obtain ⟨S, hs, hS, hfalse⟩ := hcover (fun v => m.testBit v.val) hb (indep_false m hm)
        exact avoid _ S hs hS hfalse
      · left
        simp [hb]
    rcases hend with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw
  have hbig : bigCover es = true := by
    unfold passes at hpass
    rw [hphi] at hpass
    simpa using hpass
  have hm := allPow2_true 11 0 _ hbig (maskOf K) (Nat.zero_le _) (by simpa using maskOf_lt K)
  rw [Bool.or_eq_true] at hm
  rcases hm with hm | hm
  · unfold uncovered at hm
    obtain ⟨e, he, hprop⟩ := List.any_eq_true.mp hm
    induction e using Sym2.ind with
    | h a b =>
      rw [Bool.and_eq_true] at hprop
      obtain ⟨hne, hnh⟩ := hprop
      have hnotU : s(a, b) ∉ U := by
        intro hin
        have hin2 := ofU hin
        simp [hin2] at hne
      have hadj : (graph.deleteEdges ↑U).Adj a b :=
        SimpleGraph.deleteEdges_adj.mpr
          ⟨(edgeList_pair a b).mp he, fun hc => hnotU (Finset.mem_coe.mp hc)⟩
      have hab := hKc a b hadj
      simp only [hits, Sym2.lift_mk, maskOf_testBit, Bool.not_eq_true', Bool.or_eq_false_iff,
        decide_eq_false_iff_not] at hnh
      rcases hab with ha | hb
      · exact hnh.1 ha
      · exact hnh.2 hb
  · have hle := of_decide_eq_true hm
    rw [pop11_maskOf, helen] at hle
    omega

lemma exists_minCover (H : SimpleGraph (Fin 11)) : ∃ K : Finset (Fin 11), IsMinCover H K := by
  classical
  have hne : (Finset.filter (fun T : Finset (Fin 11) => H.IsVertexCover (↑T : Set (Fin 11)))
      (Finset.univ : Finset (Finset (Fin 11)))).Nonempty :=
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v w _ => Or.inl (by simp)⟩⟩
  obtain ⟨K, hK, hmin⟩ := Finset.exists_min_image _ Finset.card hne
  exact ⟨K, (Finset.mem_filter.mp hK).2, fun T' hT' =>
    hmin T' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)⟩

lemma core (C : Circuit) (least : IsLeastAO graph C) (top : TopForm graph C)
    (hj : (junk graph C).card = 2) (hsize : C.size ≤ 21)
    (hco : 2 * (centreless graph C).card + (orN graph C \ lam graph C).card = 1)
    (hU2 : 2 ≤ (Ustar graph C).card)
    (hled : 16 + (tops graph C \ centreless graph C).card + 2 * (centreless graph C).card +
      (junk graph C).card + (orN graph C \ lam graph C).card ≤
        C.size + (Ustar graph C).card + 1)
    (hcov : ∀ K : Finset (Fin 11), IsMinCover (graph.deleteEdges ↑(Ustar graph C)) K →
      K.card ≤ (tops graph C \ centreless graph C).card) : False := by
  have budget : 2 * (centreless graph C).card + (junk graph C).card +
      (orN graph C \ lam graph C).card ≤ 3 := by omega
  have hUne : (Ustar graph C).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e, he⟩ := hUne
  have hpair : ∃ u v : Fin 11, s(u, v) ∈ Ustar graph C := by
    induction e using Sym2.ind with | h u v => exact ⟨u, v, he⟩
  obtain ⟨_, t, ht⟩ := finish least top (by omega) budget hpair
  obtain ⟨K, hK⟩ := exists_minCover (graph.deleteEdges ↑(Ustar graph C))
  have hKn := hcov K hK
  exact graphFinal (Ustar graph C) Finset.sdiff_subset t ht hU2 K
    (fun a b hab => hK.1 hab) (by omega)

end PEqualNP.Outside.L_meta_17749

theorem PEqualNP.Outside.L_meta_17749 : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) → x2.size ≤ (21 : ℕ) → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card = (1 : ℕ) → (2 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (16 : ℕ) + (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card ≤ x2.size + (PEqualNP.TopForm.Ustar x1 x2).card + (1 : ℕ) → (∀ (x10 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑(PEqualNP.TopForm.Ustar x1 x2)) x10 → x10.card ≤ (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card) → (∀ (x11 : Fin (11 : ℕ)), ↑x11 < (4 : ℕ) → (∀ x13 < x2.size, ↑x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x13).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x13 x14 x15 : ℕ), x13 < x14 → x14 < x15 → x15 < x2.size → ↑x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x13).inputs → ↑x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x14).inputs → ↑x11 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x15).inputs) → False := by
  intro x1 C hL hT hj hs hco hU hled hcov _
  exact PEqualNP.Outside.L_meta_17749.core C hL hT hj hs hco hU hled hcov

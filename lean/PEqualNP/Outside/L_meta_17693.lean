import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17693

namespace CircuitRoute

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
  unfold junk gatesWhere at ha
  rw [Finset.mem_filter, Finset.mem_range] at ha
  rcases ha with ⟨_, hop, hal, hd⟩
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
    (empty : centreless G C = ∅)
    (budget : (orN G C \ lam G C).card ≤ 1)
    (nonempty : ∃ u v : Fin n, s(u, v) ∈ Ustar G C) :
    1 ≤ (orN G C \ lam G C).card ∧
    ∃ t : Fin n, ∀ u v : Fin n, s(u, v) ∈ Ustar G C →
      ∃ w : Fin n, (w = u ∨ w = v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj t w ∧
        ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false →
          ∃ S : Finset (Fin n), (S.card ≤ 1 ∨
            ∃ z : Fin n, ∀ y ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj y z) ∧
            (∀ p q : Fin n, s(p, q) ∈ Ustar G C → p ∈ S ∨ q ∈ S) ∧
            ∀ y ∈ S, x y = false := by
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

end CircuitRoute

namespace CoverCertificate

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

abbrev V := Fin 11
abbrev I := Fin 16

abbrev G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

abbrev graphDecidable : DecidableRel G.Adj := inferInstance

def ends : I → V × V := ![(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

def edge (i : I) : Sym2 V := s((ends i).1, (ends i).2)

def pair (i j : I) : Finset (Sym2 V) := {edge i, edge j}

def drop (D : Finset (Sym2 V)) := G.deleteEdges ↑D

def Premise (D : Finset (Sym2 V)) : Prop :=
  ∃ c : V, ∀ u v : V, s(u, v) ∈ D →
    ∃ w : V, (w = u ∨ w = v) ∧ (drop D).Adj c w ∧
      ∀ x : V → Bool, x w = true → graphFun G ∅ x = false →
        ∃ S : Finset V, (S.card ≤ 1 ∨ ∃ z : V, ∀ t ∈ S, (drop D).Adj t z) ∧
          (∀ a b : V, s(a, b) ∈ D → a ∈ S ∨ b ∈ S) ∧ ∀ t ∈ S, x t = false

lemma premise_mono {D F : Finset (Sym2 V)} (hsub : D ⊆ F) (h : Premise F) :
    Premise D := by
  have adj {u v : V} (h : (drop F).Adj u v) : (drop D).Adj u v := by
    obtain ⟨ha, hm⟩ := SimpleGraph.deleteEdges_adj.mp h
    exact SimpleGraph.deleteEdges_adj.mpr ⟨ha, fun hd => hm (hsub hd)⟩
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun u v hmem => ?_⟩
  obtain ⟨w, hw, ha, hx⟩ := hc u v (hsub hmem)
  refine ⟨w, hw, adj ha, fun x hwx hG => ?_⟩
  obtain ⟨S, hs, hcover, hfalse⟩ := hx x hwx hG
  refine ⟨S, ?_, fun a b hab => hcover a b (hsub hab), hfalse⟩
  rcases hs with hs | ⟨z, hz⟩
  · exact Or.inl hs
  · exact Or.inr ⟨z, fun t ht => adj (hz t ht)⟩

def neighborMask : V → ℕ := ![1536, 272, 1056, 192, 1282, 772, 1160, 584, 562, 417, 85]

def adjacent (u v : V) : Bool := (neighborMask u).testBit v.val

lemma adj_iff (u v : V) : G.Adj u v ↔ adjacent u v = true := by
  revert u v
  decide

def between (i : I) (u v : V) : Bool :=
  let (a, b) := ends i
  (u == a && v == b) || (u == b && v == a)

lemma between_iff (i : I) (u v : V) : between i u v = true ↔ s(u, v) = edge i := by
  rw [edge, Sym2.eq_iff]
  simp [between]

lemma index_exists : ∀ u v : V, adjacent u v = true → ∃ i : I, between i u v = true := by
  decide

lemma edge_index {a : Sym2 V} (h : a ∈ G.edgeFinset) : ∃ i : I, a = edge i := by
  revert h
  induction a using Sym2.ind with
  | _ u v =>
    intro h
    obtain ⟨i, hi⟩ := index_exists u v ((adj_iff u v).mp (show G.Adj u v from SimpleGraph.mem_edgeFinset.mp h))
    exact ⟨i, (between_iff i u v).mp hi⟩

def near (i j : I) (u v : V) : Bool :=
  adjacent u v && !between i u v && !between j u v

lemma near_iff (i j : I) (u v : V) : near i j u v = true ↔ (drop (pair i j)).Adj u v := by
  simp [near, drop, pair, SimpleGraph.deleteEdges_adj, adj_iff, ← between_iff, and_assoc]

def hit (k : I) (f : V → Bool) : Bool := f (ends k).1 || f (ends k).2

def hits (i j : I) (f : V → Bool) : Bool := hit i f && hit j f

lemma hits_of_cover {i j : I} {S : Finset V} {f : V → Bool}
    (hcover : ∀ a b : V, s(a, b) ∈ pair i j → a ∈ S ∨ b ∈ S)
    (hf : ∀ t ∈ S, f t = true) : hits i j f = true := by
  have one (k : I) (hk : edge k ∈ pair i j) : hit k f = true := by
    rcases hcover (ends k).1 (ends k).2 hk with h | h
    · simp [hit, hf _ h]
    · simp [hit, hf _ h]
  simp [hits, one i (by simp [pair]), one j (by simp [pair])]

-- Each probe selects one vertex, or the two vertices in an exceptional entry.
def extra (i j : I) (w : V) : V :=
  match i, j, w with
  | 0, 2, 9 => 4
  | 0, 2, 4 => 9
  | 0, 4, 9 => 2
  | 0, 4, 0 => 5
  | 0, 6, 9 => 6
  | 0, 6, 6 => 9
  | 0, 8, 9 => 4
  | 0, 8, 0 => 8
  | 1, 3, 10 => 8
  | 1, 3, 8 => 10
  | 1, 7, 10 => 7
  | 1, 7, 7 => 10
  | 2, 4, 5 => 4
  | 2, 4, 4 => 5
  | 3, 5, 10 => 8
  | 3, 5, 8 => 10
  | 4, 8, 5 => 4
  | 4, 8, 2 => 8
  | 4, 12, 5 => 6
  | 4, 12, 2 => 7
  | 5, 14, 10 => 9
  | 5, 14, 9 => 10
  | 8, 12, 8 => 6
  | 8, 12, 4 => 7
  | 9, 10, 4 => 5
  | 9, 10, 10 => 8
  | 9, 14, 10 => 9
  | 9, 14, 9 => 10
  | 9, 15, 10 => 8
  | 9, 15, 4 => 9
  | 11, 13, 9 => 10
  | 11, 13, 10 => 9
  | 13, 14, 10 => 7
  | 13, 14, 6 => 9
  | 13, 15, 10 => 9
  | 13, 15, 9 => 10
  | _, _, w => w

def probe (i j : I) (w t : V) : Bool := t == w || t == extra i j w

-- A mask records which vertices can hit both edges, either directly or as a center.
def vertexMask (u : V) : ℕ := 2 ^ u.val

lemma vertex_bit (u v : V) : (vertexMask u).testBit v.val = (u == v) := by
  apply Bool.eq_iff_iff.mpr
  simp [vertexMask, Nat.testBit_two_pow, Fin.ext_iff]

lemma conditional_bit (b : Bool) (m k : ℕ) :
    (if b then m else 0).testBit k = (b && m.testBit k) := by
  cases b <;> simp

def removedAt (k : I) (u : V) : ℕ :=
  (if u == (ends k).1 then vertexMask (ends k).2 else 0) |||
  (if u == (ends k).2 then vertexMask (ends k).1 else 0)

lemma removed_bit (k : I) (u v : V) : (removedAt k u).testBit v.val = between k u v := by
  simp only [removedAt, Nat.testBit_or, conditional_bit, vertex_bit, between]
  have swap (a b : V) : (a == b) = (b == a) := by
    apply Bool.eq_iff_iff.mpr
    simpa using (eq_comm : a = b ↔ b = a)
  rw [swap (ends k).2 v, swap (ends k).1 v]

def neighbors (i j : I) (u : V) : ℕ :=
  neighborMask u &&& (2047 ^^^ (removedAt i u ||| removedAt j u))

lemma neighbor_bit (i j : I) (u v : V) : (neighbors i j u).testBit v.val = near i j u v := by
  have hall : (2047 : ℕ).testBit v.val = true := by
    change (2^11 - 1 : ℕ).testBit v.val = true
    exact (Nat.testBit_two_pow_sub_one 11 v.val).trans (decide_eq_true v.isLt)
  unfold neighbors near adjacent
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_or, removed_bit, removed_bit, hall]
  cases between i u v <;> cases between j u v <;> simp

def reachMask (k : I) (f : V → Bool) (m : V → ℕ) : ℕ :=
  (if f (ends k).1 then m (ends k).1 else 0) |||
  (if f (ends k).2 then m (ends k).2 else 0)

def meetMask (i j : I) (f : V → Bool) (m : V → ℕ) : ℕ :=
  reachMask i f m &&& reachMask j f m

lemma meet_bit (i j : I) (f : V → Bool) (m : V → ℕ) (c : V) :
    (meetMask i j f m).testBit c.val = hits i j (fun t => f t && (m t).testBit c.val) := by
  simp [meetMask, reachMask, conditional_bit, hits, hit]

def failed (i j : I) (w : V) : Bool :=
  let available := fun t => !probe i j w t
  !adjacent w (extra i j w) &&
    (meetMask i j available vertexMask == 0) &&
    (meetMask i j available (neighbors i j) == 0)

lemma probe_false {i j : I} {w : V} (h : adjacent w (extra i j w) = false) :
    graphFun G ∅ (probe i j w) = false := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_false_iff_not]
  rintro ⟨u, v, ha, hu, hv⟩
  have hu' : u = w ∨ u = extra i j w := by simpa [probe] using hu
  have hv' : v = w ∨ v = extra i j w := by simpa [probe] using hv
  have nh : ¬ G.Adj w (extra i j w) := by simp [adj_iff, h]
  rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv' <;> rw [hu', hv'] at ha
  · exact G.irrefl ha
  · exact nh ha
  · exact nh ha.symm
  · exact G.irrefl ha

lemma failed_blocks {i j : I} {w : V} (h : failed i j w = true)
    (hw : ∀ x : V → Bool, x w = true → graphFun G ∅ x = false →
        ∃ S : Finset V, (S.card ≤ 1 ∨ ∃ z : V, ∀ t ∈ S, (drop (pair i j)).Adj t z) ∧
          (∀ a b : V, s(a, b) ∈ pair i j → a ∈ S ∨ b ∈ S) ∧ ∀ t ∈ S, x t = false) :
    False := by
  simp only [failed, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨hind, hsingle⟩, hstandard⟩ := h
  let x := probe i j w
  obtain ⟨S, hs, hcover, hfalse⟩ := hw x (by simp [x, probe]) (probe_false hind)
  have blocked (c : V) (m : V → ℕ) (hm : meetMask i j (fun t => !x t) m = 0)
      (hf : ∀ t ∈ S, (!x t && (m t).testBit c.val) = true) : False := by
    have hb := meet_bit i j (fun t => !x t) m c
    rw [hm, hits_of_cover hcover hf] at hb
    exact Bool.false_ne_true (by simpa only [Nat.zero_testBit] using hb)
  rcases hs with hs | ⟨c, hc⟩
  · have hmem := hcover (ends i).1 (ends i).2 (by change edge i ∈ pair i j; simp [pair])
    have hne : S.Nonempty := hmem.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
    obtain ⟨c, hc⟩ := hne
    refine blocked c vertexMask hsingle fun t ht => ?_
    simp [vertex_bit, Finset.card_le_one.mp hs t ht c hc, hfalse c hc]
  · refine blocked c (neighbors i j) hstandard fun t ht => ?_
    simp [neighbor_bit, (near_iff i j t c).mpr (hc t ht), hfalse t ht]

def allowed (i j : I) : Bool :=
  (i == 1 && j == 10) || (i == 2 && j == 11) ||
  (i == 5 && j == 15) || (i == 9 && j == 11)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
lemma pair_certificate : ∀ i j : I, i < j →
    allowed i j = true ∨ meetMask i j (fun w => !failed i j w) (neighbors i j) = 0 := by
  decide

lemma pair_allowed {i j : I} (hlt : i < j) (h : Premise (pair i j)) : allowed i j = true := by
  obtain ⟨c, hc⟩ := h
  have one (k : I) (hk : edge k ∈ pair i j) :
      hit k (fun w => !failed i j w && (neighbors i j w).testBit c.val) = true := by
    obtain ⟨w, hw, hcw, hx⟩ := hc (ends k).1 (ends k).2 hk
    have hfail : failed i j w = false := Bool.eq_false_iff.mpr fun hf => failed_blocks hf hx
    have hadj := (near_iff i j w c).mpr hcw.symm
    rcases hw with rfl | rfl <;> simp [hit, neighbor_bit, hadj, hfail]
  rcases pair_certificate i j hlt with ha | hbad
  · exact ha
  · have hb := meet_bit i j (fun w => !failed i j w) (neighbors i j) c
    rw [hbad] at hb
    simp [hits, one i (by simp [pair]), one j (by simp [pair])] at hb

def allowedEither (i j : I) : Bool := allowed i j || allowed j i

lemma subpair_allowed {D : Finset (Sym2 V)} (h : Premise D) {i j : I}
    (hi : edge i ∈ D) (hj : edge j ∈ D) (hij : i ≠ j) : allowedEither i j = true := by
  have hs (p q : I) (hp : edge p ∈ D) (hq : edge q ∈ D) : pair p q ⊆ D := by
    intro z hz
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simp [allowedEither, pair_allowed hlt (premise_mono (hs i j hi hj) h)]
  · simp [allowedEither, pair_allowed hgt (premise_mono (hs j i hj hi) h)]

lemma allowed_cases {i j : I} (h : allowed i j = true) :
    (i = 1 ∧ j = 10) ∨ (i = 2 ∧ j = 11) ∨ (i = 5 ∧ j = 15) ∨ (i = 9 ∧ j = 11) := by
  simpa [allowed, or_assoc] using h


-- A cover pays at least one vertex for an edge and two for a triangle.
lemma edge_lower {K : SimpleGraph V} {T : Finset V} (hT : K.IsVertexCover ↑T)
    {a b : V} (hab : K.Adj a b) : 1 ≤ (T ∩ {a, b}).card := by
  apply Finset.card_pos.mpr
  rcases hT hab with ha | hb
  · exact ⟨a, Finset.mem_inter.mpr ⟨ha, by simp⟩⟩
  · exact ⟨b, Finset.mem_inter.mpr ⟨hb, by simp⟩⟩

lemma triangle_lower {K : SimpleGraph V} {T : Finset V} (hT : K.IsVertexCover ↑T)
    {a b c : V} (hab : K.Adj a b) (hac : K.Adj a c) (hbc : K.Adj b c) :
    2 ≤ (T ∩ {a, b, c}).card := by
  have two (u v : V) (huv : u ≠ v) (hu : u ∈ T) (hv : v ∈ T)
      (hu' : u ∈ ({a, b, c} : Finset V)) (hv' : v ∈ ({a, b, c} : Finset V)) :
      2 ≤ (T ∩ {a, b, c}).card := by
    rw [← Finset.card_pair huv]
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hu, hu'⟩
    · exact Finset.mem_inter.mpr ⟨hv, hv'⟩
  rcases hT hab with ha | hb
  · rcases hT hbc with hb | hc
    · exact two a b hab.ne ha hb (by simp) (by simp)
    · exact two a c hac.ne ha hc (by simp) (by simp)
  · rcases hT hac with ha | hc
    · exact two a b hab.ne ha hb (by simp) (by simp)
    · exact two b c hbc.ne hb hc (by simp) (by simp)

lemma add_lower {T A B : Finset V} {a b : ℕ} (hd : Disjoint A B)
    (ha : a ≤ (T ∩ A).card) (hb : b ≤ (T ∩ B).card) :
    a + b ≤ (T ∩ (A ∪ B)).card := by
  rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint
    (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hd))]
  exact Nat.add_le_add ha hb

def packingA : List (V × V) := [(0, 9), (1, 8), (2, 5), (3, 6), (3, 7), (6, 7), (4, 10)]

def packingB : List (V × V) := [(0, 9), (1, 4), (1, 8), (4, 8), (2, 10), (3, 6), (3, 7), (6, 7)]

lemma lowerA {i j : I}
    (hp : packingA.all (fun p => near i j p.1 p.2) = true)
    {T : Finset V} (hT : (drop (pair i j)).IsVertexCover ↑T) : 6 ≤ T.card := by
  have adj (u v : V) (hm : (u, v) ∈ packingA) : (drop (pair i j)).Adj u v :=
    (near_iff i j u v).mp (List.all_eq_true.mp hp (u, v) hm)
  have h1 := edge_lower hT (adj 0 9 (by decide))
  have h2 := edge_lower hT (adj 1 8 (by decide))
  have h3 := edge_lower hT (adj 2 5 (by decide))
  have h4 := triangle_lower hT (adj 3 6 (by decide)) (adj 3 7 (by decide)) (adj 6 7 (by decide))
  have h5 := edge_lower hT (adj 4 10 (by decide))
  have h12 := add_lower (by decide) h1 h2
  have h123 := add_lower (by decide) h12 h3
  have h1234 := add_lower (by decide) h123 h4
  have h12345 := add_lower (by decide) h1234 h5
  exact h12345.trans (Finset.card_le_card Finset.inter_subset_left)

lemma lowerB {i j : I}
    (hp : packingB.all (fun p => near i j p.1 p.2) = true)
    {T : Finset V} (hT : (drop (pair i j)).IsVertexCover ↑T) : 6 ≤ T.card := by
  have adj (u v : V) (hm : (u, v) ∈ packingB) : (drop (pair i j)).Adj u v :=
    (near_iff i j u v).mp (List.all_eq_true.mp hp (u, v) hm)
  have h1 := edge_lower hT (adj 0 9 (by decide))
  have h2 := triangle_lower hT (adj 1 4 (by decide)) (adj 1 8 (by decide)) (adj 4 8 (by decide))
  have h3 := edge_lower hT (adj 2 10 (by decide))
  have h4 := triangle_lower hT (adj 3 6 (by decide)) (adj 3 7 (by decide)) (adj 6 7 (by decide))
  have h12 := add_lower (by decide) h1 h2
  have h123 := add_lower (by decide) h12 h3
  have h1234 := add_lower (by decide) h123 h4
  exact h1234.trans (Finset.card_le_card Finset.inter_subset_left)


lemma residualCoverLower (D : Finset (Sym2 V)) (sub : D ⊆ G.edgeFinset)
    (two : D.card = 2) (shape : Premise D) {K : Finset V}
    (cover : (drop D).IsVertexCover ↑K) : 6 ≤ K.card := by
  have pairBound (i j : I) (ordered : i < j) (eq : D = pair i j) : 6 ≤ K.card := by
    rw [eq] at shape cover
    have a := pair_allowed ordered shape
    rcases allowed_cases a with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact lowerA (by decide) cover
    · exact lowerA (by decide) cover
    · exact lowerA (by decide) cover
    · exact lowerB (by decide) cover
  obtain ⟨a, b, hab, hd⟩ := Finset.card_eq_two.mp two
  obtain ⟨i, rfl⟩ := edge_index (sub (by simp [hd] : a ∈ D))
  obtain ⟨j, rfl⟩ := edge_index (sub (by simp [hd] : b ∈ D))
  have hij : i ≠ j := fun e => hab (congrArg edge e)
  rcases lt_or_gt_of_ne hij with h | h
  · exact pairBound i j h hd
  · exact pairBound j i h (hd.trans (Finset.pair_comm _ _))

lemma conclude (C : PEqualNP.CircuitLowerBounds.Circuit)
    (least : PEqualNP.TopForm.IsLeastAO G C)
    (top : PEqualNP.TopForm.TopForm G C)
    (two : (PEqualNP.TopForm.Ustar G C).card = 2) (K : Finset V)
    (minCover : IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K)
    (five : 5 ≤ K.card) (empty : PEqualNP.TopForm.centreless G C = ∅)
    (budget : K.card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ 6) :
    False := by
  have ne : ∃ u v : V, s(u, v) ∈ PEqualNP.TopForm.Ustar G C := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega :
      0 < (PEqualNP.TopForm.Ustar G C).card)
    induction e using Sym2.ind with
    | h u v => exact ⟨u, v, he⟩
  obtain ⟨positive, witness⟩ := CircuitRoute.finish least top empty (by omega) ne
  have six := residualCoverLower _ Finset.sdiff_subset two witness minCover.1
  omega

end CoverCertificate

end PEqualNP.Outside.L_meta_17693

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_17693 :
∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) (x6 : Finset (Fin (11 : ℕ))), x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → x3.size < (22 : ℕ) → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → (PEqualNP.TopForm.Ustar x1 x3).card = (2 : ℕ) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑(PEqualNP.TopForm.Ustar x1 x3)) x6 → (5 : ℕ) ≤ x6.card → PEqualNP.TopForm.centreless x1 x3 = ∅ → x6.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ (6 : ℕ) → False := by
  intro G inst C j k K graph
  subst G
  have instEq : inst = PEqualNP.Outside.L_meta_17693.CoverCertificate.graphDecidable :=
    Subsingleton.elim _ _
  subst inst
  intro least top size junk two minCover five empty budget
  exact PEqualNP.Outside.L_meta_17693.CoverCertificate.conclude C
    least top two K minCover five empty budget

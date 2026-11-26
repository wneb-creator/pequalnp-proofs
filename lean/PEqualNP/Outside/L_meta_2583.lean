import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2583_aux
namespace Budget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
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
lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
lemma junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
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
lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
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
lemma operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
lemma operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
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
lemma inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
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
end Budget
def LocalCoverProperty {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (U : Finset (Sym2 V)) (w : V) : Prop :=
  ∀ x : V → Bool, x w = true →
    (∀ a b, G.Adj a b → x a = true → x b = false) →
    ∃ S : Finset V,
      (S.card ≤ 1 ∨ ∃ z, ∀ y ∈ S, G.Adj y z ∧ s(y, z) ∉ U) ∧
      (∀ p q, s(p, q) ∈ U → p ∈ S ∨ q ∈ S) ∧
      ∀ y ∈ S, x y = false
lemma bool_eq_of_ne_common (a b c : Bool) (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all
lemma clean_pencil_edges_equal {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (U : Finset (Sym2 V)) (color : V → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m)
    (t p0 w0 p1 w1 : V)
    (he0 : s(p0, w0) ∈ U) (he1 : s(p1, w1) ∈ U)
    (hp0w0 : G.Adj p0 w0) (hp1w1 : G.Adj p1 w1)
    (htw0 : G.Adj t w0) (htw1 : G.Adj t w1)
    (hclean0 : s(t, w0) ∉ U)
    (hproperty : LocalCoverProperty G U w0) :
    s(p0, w0) = s(p1, w1) := by
  classical
  by_contra hne
  have hp0t : p0 ≠ t := by
    intro h
    exact hclean0 (h ▸ he0)
  have hp01 : p0 ≠ p1 := by
    intro hp
    have hw : w0 = w1 := hfour p0 t hp0t w0 w1 hp0w0 htw0 (hp.symm ▸ hp1w1) htw1
    exact hne (by rw [hp, hw])
  have hcol0 : color p0 = color t :=
    bool_eq_of_ne_common _ _ _ (hbip p0 w0 hp0w0) (hbip t w0 htw0)
  have hcol01 : color p0 ≠ color w1 := by
    rw [hcol0]
    exact hbip t w1 htw1
  have hp0w1 : p0 ≠ w1 := fun h => hcol01 (congrArg color h)
  let x0 : V → Bool := fun a => decide (a = w0)
  have hx0 : x0 w0 = true := by simp [x0]
  have hx0ind : ∀ a b, G.Adj a b → x0 a = true → x0 b = false := by
    intro a b hab ha
    have ha' : a = w0 := by simpa [x0] using ha
    have hb' : b ≠ w0 := by
      intro hb
      subst a
      subst b
      exact G.irrefl hab
    simpa [x0] using hb'
  obtain ⟨S, hshape, hcover, hfalse⟩ := hproperty x0 hx0 hx0ind
  have hnw0 : w0 ∉ S := by
    intro hw
    have hf := hfalse w0 hw
    rw [hx0] at hf
    contradiction
  have hp0S : p0 ∈ S := (hcover p0 w0 he0).resolve_right hnw0
  have hlarge : ¬ S.card ≤ 1 := by
    intro hsmall
    rcases hcover p1 w1 he1 with hp1S | hw1S
    · exact hp01 (Finset.card_le_one.mp hsmall p0 hp0S p1 hp1S)
    · exact hp0w1 (Finset.card_le_one.mp hsmall p0 hp0S w1 hw1S)
  obtain ⟨z, hz⟩ := hshape.resolve_left hlarge
  have hp0z : G.Adj p0 z := (hz p0 hp0S).1
  have hp1S : p1 ∈ S := by
    rcases hcover p1 w1 he1 with hp | hw
    · exact hp
    · have hc : color p0 = color w1 := bool_eq_of_ne_common _ _ _
        (hbip p0 z hp0z) (hbip w1 z (hz w1 hw).1)
      exact (hcol01 hc).elim
  have hp1z : G.Adj p1 z := (hz p1 hp1S).1
  have hzw : z ≠ w0 := by
    intro h
    have hc := (hz p0 hp0S).2
    exact hc (h.symm ▸ he0)
  have hcross : ¬ G.Adj p1 w0 := by
    intro h
    exact hzw (hfour p0 p1 hp01 w0 z hp0w0 h hp0z hp1z).symm
  let x1 : V → Bool := fun a => decide (a = w0 ∨ a = p1)
  have hx1w : x1 w0 = true := by simp [x1]
  have hx1p : x1 p1 = true := by simp [x1]
  have hx1ind : ∀ a b, G.Adj a b → x1 a = true → x1 b = false := by
    intro a b hab ha
    have ha' : a = w0 ∨ a = p1 := by simpa [x1] using ha
    have hb' : ¬ (b = w0 ∨ b = p1) := by
      intro hb
      rcases ha' with rfl | rfl <;> rcases hb with rfl | rfl
      · exact G.irrefl hab
      · exact hcross hab.symm
      · exact hcross hab
      · exact G.irrefl hab
    simpa [x1] using hb'
  obtain ⟨T, hshapeT, hcoverT, hfalseT⟩ := hproperty x1 hx1w hx1ind
  have hnw0T : w0 ∉ T := by
    intro hw
    have hf := hfalseT w0 hw
    rw [hx1w] at hf
    contradiction
  have hnp1T : p1 ∉ T := by
    intro hp
    have hf := hfalseT p1 hp
    rw [hx1p] at hf
    contradiction
  have hp0T : p0 ∈ T := (hcoverT p0 w0 he0).resolve_right hnw0T
  have hw1T : w1 ∈ T := (hcoverT p1 w1 he1).resolve_left hnp1T
  rcases hshapeT with hsmall | ⟨z', hz'⟩
  · exact hp0w1 (Finset.card_le_one.mp hsmall p0 hp0T w1 hw1T)
  · exact hcol01 (bool_eq_of_ne_common _ _ _
      (hbip p0 z' (hz' p0 hp0T).1) (hbip w1 z' (hz' w1 hw1T).1))
lemma cover_property_card_le_one {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (U : Finset (Sym2 V)) (color : V → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m)
    (hUadj : ∀ u v, s(u, v) ∈ U → G.Adj u v)
    (t : V)
    (hproperty : ∀ u v, s(u, v) ∈ U → ∃ w,
      (w = u ∨ w = v) ∧ G.Adj t w ∧ s(t, w) ∉ U ∧
        LocalCoverProperty G U w) :
    U.card ≤ 1 := by
  have orient : ∀ e ∈ U, ∃ p w,
      e = s(p, w) ∧ G.Adj p w ∧ G.Adj t w ∧ s(t, w) ∉ U ∧
        LocalCoverProperty G U w := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨w, hw, htw, hclean, hlocal⟩ := hproperty a b he
      rcases hw with ha | hb
      · subst w
        exact ⟨b, a, Sym2.eq_swap, (hUadj a b he).symm, htw, hclean, hlocal⟩
      · subst w
        exact ⟨a, b, rfl, hUadj a b he, htw, hclean, hlocal⟩
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨p0, w0, rfl, ha0, ht0, hc0, hp0⟩ := orient e he
  obtain ⟨p1, w1, rfl, ha1, ht1, _, _⟩ := orient f hf
  exact clean_pencil_edges_equal G U color hbip hfour t p0 w0 p1 w1
    he hf ha0 ha1 ht0 ht1 hc0 hp0
lemma common_neighbors_unique_of_card_le_one {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfour : ∀ a b, a ≠ b →
      (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card ≤ 1) :
    ∀ a b, a ≠ b → ∀ l m,
      G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m := by
  intro a b hab l m hal hbl ham hbm
  apply Finset.card_le_one.mp (hfour a b hab) l _ m _
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hal, hbl⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ham, hbm⟩
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
lemma budget_three_ustar_card_le_one
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hfour : NoFourCycle G)
    (hleast : IsLeastAO G C) (htop : TopForm G C)
    (hjunk : 2 ≤ (junk G C).card)
    (hbudget : 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card ≤ 3) :
    (Ustar G C).card ≤ 1 := by
  classical
  by_cases hU : (Ustar G C).Nonempty
  · have hpair : ∃ u v : Fin n, s(u, v) ∈ Ustar G C := by
      obtain ⟨e, he⟩ := hU
      induction e using Sym2.ind with
      | h u v => exact ⟨u, v, he⟩
    obtain ⟨_, t, ht⟩ := Budget.finish hleast htop hjunk hbudget hpair
    have hUadj : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → G.Adj u v := by
      intro u v huv
      exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp huv).1
    apply cover_property_card_le_one G (Ustar G C) color hbip
      (common_neighbors_unique_of_card_le_one G hfour) hUadj t
    intro u v huv
    obtain ⟨w, hw, hclean, hcover⟩ := ht u v huv
    refine ⟨w, hw, (SimpleGraph.deleteEdges_adj.mp hclean).1,
      (SimpleGraph.deleteEdges_adj.mp hclean).2, ?_⟩
    intro x hx hind
    have hnone : ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
      rintro ⟨a, b, hab, ha, hb⟩
      have hf := hind a b hab ha
      rw [hb] at hf
      contradiction
    have hF : graphFun G ∅ x = false := by
      simp [graphFun, hnone]
    obtain ⟨S, hshape, hcov, hfalse⟩ := hcover x hx hF
    refine ⟨S, ?_, hcov, hfalse⟩
    rcases hshape with hsmall | ⟨z, hz⟩
    · exact Or.inl hsmall
    · exact Or.inr ⟨z, fun y hy => SimpleGraph.deleteEdges_adj.mp (hz y hy)⟩
  · simp [Finset.not_nonempty_iff_eq_empty.mp hU]
namespace Ledger
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
namespace S90
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
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
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
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
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩
lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2
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
open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]
open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]
open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]
open PEqualNP.EdgeOwnership in
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
open PEqualNP.EdgeOwnership in
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
open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩
open PEqualNP.EdgeOwnership
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
open PEqualNP.CleanedNonEdge
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
open PEqualNP.TopForm in
lemma top_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (a : ℕ) (ha : a ∈ tops G C) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) ∧
    (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
    ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
    intro u hu v hv
    simp only [side, e0] at hu
    simp only [side, e1] at hv
    exact side_adj G (graphFun G ∅) (fun u v h => (graphFun_pair G u v).mp h) a halen hop hbel
      p q hin hp hq u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)
  refine ⟨?_, hadj, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu hv
    exact G.irrefl (hadj u hu u hv)
  · by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
    have hsub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj x hx w hw, hadj y hy w hw⟩
    have h5 := Finset.card_le_card hsub
    have h6 := h4 x y hxy
    omega
end S90
namespace S98
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]
def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u
def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)
lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]
lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]
lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · simp only [hgt, ↓reduceIte]; exact hm.2.2.2.2.2 u hgt
  · simp only [hgt, ↓reduceIte]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]
lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'
lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]
def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u
def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩
def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false
def eraseC (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩
def appOr (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], n + C.gates.length⟩
def truncC (C : Circuit) (m : ℕ) : Circuit :=
  ⟨C.gates.take m, C.output⟩
lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]
lemma erase_wires (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (x : Fin n → Bool)
    (h : W n C x i = W n C x (n + j) ∨
      ∀ k, j < k → k < C.gates.length → n + j ∉ (gateAt C k).inputs) :
    ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
      W n (eraseC n C j i) x (aliasWire (n + j) i u) = W n C x u := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  have htake : C.gates.take j = pre := by rw [hgs, ← hpre_len]; simp
  have hdrop : C.gates.drop (j + 1) = post := by rw [hgs, ← hpre_len]; simp
  intro u hu
  simp only [W, eraseC, wires_eq_foldl, htake, hdrop]
  conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
  rw [List.foldl_append]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre_len]
  let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hCi : W n C x i = w0.getD i false := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
  have hCj : W n C x (n + j) = bOld := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
  have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
      ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
        vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
    intro vC vD hmv u hu'
    unfold aliasWire
    by_cases hu : u = n + j
    · have hval_eq : w0.getD i false = bOld := by rw [← hCi, ← hCj]; exact hu' hu
      subst hu
      simp only [↓reduceIte]
      rw [hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
    · simp only [hu, ↓reduceIte]
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
      ((post.map (aliasGate (n + j) i)).foldl stepWire w0) := by
    refine foldl_wiresMatch w0 bOld post (post.map (aliasGate (n + j) i)) (stepWire w0 gj) w0 hm0
      (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map, aliasGate, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    refine halias_get vC vD hmv u ?_
    intro hun
    rcases h with h | h
    · exact h
    · exfalso
      have hget : gateAt C (j + 1 + t) = post[t] := by
        rw [gateAt_eq C (j + 1 + t) (by omega)]
        have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; omega) = post[t]'htC := by
          rw [List.getElem_append_right (by omega)]
          have hsub : j + 1 + t - pre.length = t + 1 := by omega
          simp [hsub]
        simpa [hgs] using h1
      exact h (j + 1 + t) (by omega) (by omega) (by rw [hget, ← hun]; exact hu)
  exact halias_get _ _ hmEnd u hu
lemma erase_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (eraseC n C j i).gates.length + 1 = C.gates.length := by
  simp [eraseC]; omega
lemma erase_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : k < j) :
    gateAt (eraseC n C j i) k = gateAt C k := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hk]
lemma erase_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : j ≤ k)
    (hk2 : k + 1 < C.gates.length) :
    gateAt (eraseC n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  have h1 : (List.take j C.gates).length = j := by simp; omega
  have h2 : j + 1 + (k - j) = k + 1 := by omega
  rw [h1, List.getElem?_map, List.getElem?_drop, h2, List.getElem?_eq_getElem hk2]
  rfl
lemma prefix_W (n : ℕ) (pre rest1 rest2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + pre.length) :
    W n ⟨pre ++ rest1, o1⟩ x u = W n ⟨pre ++ rest2, o2⟩ x u := by
  simp only [W, wires_eq_foldl, List.foldl_append]
  have h : u < (pre.foldl stepWire (List.ofFn x)).length := by
    rw [foldl_stepWire_length]; simpa using hu
  rw [foldl_stepWire_getD_lt rest1 (pre.foldl stepWire (List.ofFn x)) u h,
    foldl_stepWire_getD_lt rest2 (pre.foldl stepWire (List.ofFn x)) u h]
lemma erase_W_lt (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool)
    (u : ℕ) (hu : u < n + j) : W n (eraseC n C j i) x u = W n C x u := by
  have h := prefix_W n (C.gates.take j) ((C.gates.drop (j + 1)).map (aliasGate (n + j) i))
    (C.gates.drop j) (aliasWire (n + j) i C.output) C.output x u
    (by rw [List.length_take]; omega)
  have e2 : (⟨C.gates.take j ++ C.gates.drop j, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h
lemma appOr_W_lt (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + C.gates.length) : W n (appOr n C a b) x u = W n C x u := by
  have h := prefix_W n C.gates [⟨GateOp.or, [a, b]⟩] [] (n + C.gates.length) C.output x u hu
  have e2 : (⟨C.gates ++ [], C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h
lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)
lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]
lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]
lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]
lemma appOr_gateAt_lt (n : ℕ) (C : Circuit) (a b k : ℕ) (hk : k < C.gates.length) :
    gateAt (appOr n C a b) k = gateAt C k := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
lemma appOr_gateAt_last (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appOr n C a b) C.gates.length = ⟨GateOp.or, [a, b]⟩ := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD]
lemma appOr_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    (appOr n C a b).eval (List.ofFn x) = (W n C x a || W n C x b) := by
  have h := W_or n (appOr n C a b) x C.gates.length (by simp [appOr]) (by rw [appOr_gateAt_last])
    a b (by rw [appOr_gateAt_last]) ha hb
  rw [appOr_W_lt n C a b x a ha, appOr_W_lt n C a b x b hb] at h
  exact h
def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k
def Least (n : ℕ) (C : Circuit) : Prop :=
  AO n C ∧ ∀ D : Circuit, AO n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    C.gates.length ≤ D.gates.length
def Bel (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∀ x : Fin n → Bool, W n C x (n + j) = true → C.eval (List.ofFn x) = true
lemma alias_lt (w i u N : ℕ) (hu : u < N + 1) (hi : i < w) (hw : w ≤ N) :
    aliasWire w i u < N := by
  unfold aliasWire shiftDown
  split_ifs <;> omega
lemma erase_AO (n : ℕ) (C : Circuit) (j i : ℕ) (hA : AO n C) (hj : j < C.gates.length)
    (hi : i < n + j) : AO n (eraseC n C j i) := by
  intro k hk
  have hlen := erase_length n C j i hj
  by_cases hkj : k < j
  · rw [erase_gateAt_lt n C j i k hj hkj]; exact hA k (by omega)
  · rw [erase_gateAt_ge n C j i k hj (by omega) (by omega)]
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hA (k + 1) (by omega)
    refine ⟨hop, aliasWire (n + j) i a, aliasWire (n + j) i b, by simp [aliasGate, hin], ?_, ?_⟩
    · exact alias_lt (n + j) i a (n + k) (by omega) hi (by omega)
    · exact alias_lt (n + j) i b (n + k) (by omega) hi (by omega)
lemma appOr_AO (n : ℕ) (C : Circuit) (a b : ℕ) (hA : AO n C) (ha : a < n + C.gates.length)
    (hb : b < n + C.gates.length) : AO n (appOr n C a b) := by
  intro k hk
  have hlen : (appOr n C a b).gates.length = C.gates.length + 1 := by simp [appOr]
  by_cases hkl : k < C.gates.length
  · rw [appOr_gateAt_lt n C a b k hkl]; exact hA k hkl
  · have hke : k = C.gates.length := by omega
    subst hke
    rw [appOr_gateAt_last]
    exact ⟨Or.inr rfl, a, b, rfl, ha, hb⟩
lemma trunc_AO (n : ℕ) (C : Circuit) (m : ℕ) (hA : AO n C) (hm : m ≤ C.gates.length) :
    AO n (truncC C m) := by
  intro k hk
  have hk' : k < m := by simp [truncC] at hk; omega
  have h : gateAt (truncC C m) k = gateAt C k := by
    simp [gateAt, truncC, List.getD_eq_getElem?_getD, hk']
  rw [h]; exact hA k (by omega)
lemma trunc_W (n : ℕ) (C : Circuit) (m : ℕ) (x : Fin n → Bool) (u : ℕ) (hm : m ≤ C.gates.length)
    (hu : u < n + m) : W n (truncC C m) x u = W n C x u := by
  have h := prefix_W n (C.gates.take m) [] (C.gates.drop m) C.output C.output x u
    (by rw [List.length_take]; omega)
  have e1 : (⟨C.gates.take m ++ [], C.output⟩ : Circuit) = truncC C m := by simp [truncC]
  have e2 : (⟨C.gates.take m ++ C.gates.drop m, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e1, e2] at h
  exact h
lemma least_out (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false) :
    n ≤ C.output ∧ C.output + 1 = n + C.gates.length := by
  have h1 : n ≤ C.output := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hf⟩ := hV ⟨C.output, h⟩
    have h2 : W n C x C.output = true := (W_input n C x C.output h).trans hx
    have h3 : W n C x C.output = false := hf
    rw [h2] at h3
    exact absurd h3 (by simp)
  have h2 : C.output < n + C.gates.length := by
    by_contra h
    obtain ⟨x, hx⟩ := hT
    have h3 : W n C x C.output = true := hx
    simp only [W] at h3
    rw [getD_ge_length _ _ (by rw [wires_length]; omega)] at h3
    exact absurd h3 (by simp)
  refine ⟨h1, ?_⟩
  by_contra h3
  have hm : C.output - n + 1 < C.gates.length := by omega
  have hfun : ∀ x : Fin n → Bool,
      (truncC C (C.output - n + 1)).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    trunc_W n C (C.output - n + 1) x C.output (by omega) (by omega)
  have h4 := hL.2 _ (trunc_AO n C (C.output - n + 1) hL.1 (by omega)) hfun
  simp [truncC] at h4
  omega
lemma least_read (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j + 1 < C.gates.length) :
    ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  by_contra hno
  push Not at hno
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 j (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j a).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j a (by omega) ha x (Or.inr hno) C.output (by intro h; omega)
  have h1 := hL.2 _ (erase_AO n C j a hL.1 (by omega) ha) hfun
  have h2 := erase_length n C j a (by omega)
  omega
lemma least_nodup (n : ℕ) (C : Circuit) (hL : Least n C) (i j : ℕ) (hij : i < n + j)
    (hj : j < C.gates.length) : ∃ x : Fin n → Bool, W n C x i ≠ W n C x (n + j) := by
  by_contra hsame
  push Not at hsame
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j i).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j i hj hij x (Or.inl (hsame x)) C.output (fun _ => hsame x)
  have h1 := hL.2 _ (erase_AO n C j i hL.1 hj hij) hfun
  have h2 := erase_length n C j i hj
  omega
lemma red (n : ℕ) (C : Circuit) (hA : AO n C) (j r : ℕ) (hr : r < C.gates.length)
    (hmem : n + j ∈ (gateAt C r).inputs) :
    ∃ p, p < n + r ∧
      ∀ x : Fin n → Bool, W n C x (n + j) = false → W n C x p = W n C x (n + r) := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rw [hin] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hop with hop | hop
  · refine ⟨n + j, by rcases hmem with h | h <;> omega, fun x hx => ?_⟩
    rw [W_and n C x r hr hop a b hin ha hb, hx]
    rcases hmem with h | h
    · rw [← h, hx]; simp
    · rw [← h, hx]; simp
  · rcases hmem with h | h
    · refine ⟨b, hb, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp
    · refine ⟨a, ha, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp
lemma two_readers (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hB : Bel n C j) (r1 r2 : ℕ)
    (h12 : r1 < r2) (hr2 : r2 < C.gates.length)
    (hm1 : n + j ∈ (gateAt C r1).inputs) (hm2 : n + j ∈ (gateAt C r2).inputs) : False := by
  have hA := hL.1
  have hj1 : j < r1 := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA r1 (by omega)
    rw [hin] at hm1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
    omega
  obtain ⟨p2, hp2, hv2⟩ := red n C hA j r2 hr2 hm2
  have hA1 := erase_AO n C r2 p2 hA hr2 hp2
  have hl1 := erase_length n C r2 p2 hr2
  have hW1 : ∀ (x : Fin n → Bool) (u : ℕ), u < n + r2 →
      W n (eraseC n C r2 p2) x u = W n C x u := fun x u hu => erase_W_lt n C r2 p2 hr2 x u hu
  have hg1 : gateAt (eraseC n C r2 p2) r1 = gateAt C r1 := erase_gateAt_lt n C r2 p2 r1 hr2 h12
  obtain ⟨p1, hp1, hv1⟩ := red n (eraseC n C r2 p2) hA1 j r1 (by omega) (by rw [hg1]; exact hm1)
  have hA2 := erase_AO n (eraseC n C r2 p2) r1 p1 hA1 (by omega) hp1
  have hl2 := erase_length n (eraseC n C r2 p2) r1 p1 (by omega)
  have ho1 : (eraseC n C r2 p2).output < n + (eraseC n C r2 p2).gates.length :=
    alias_lt (n + r2) p2 C.output _ (by omega) hp2 (by omega)
  have ho2 : (eraseC n (eraseC n C r2 p2) r1 p1).output <
      n + (eraseC n (eraseC n C r2 p2) r1 p1).gates.length :=
    alias_lt (n + r1) p1 (eraseC n C r2 p2).output _ (by omega) hp1 (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
        (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).eval (List.ofFn x) =
        C.eval (List.ofFn x) := by
    intro x
    rw [appOr_eval n _ _ (n + j) x ho2 (by omega)]
    have hj2 : W n (eraseC n (eraseC n C r2 p2) r1 p1) x (n + j) = W n C x (n + j) := by
      rw [erase_W_lt n _ r1 p1 (by omega) x (n + j) (by omega), hW1 x (n + j) (by omega)]
    rw [hj2]
    cases hx : W n C x (n + j)
    · have e2 := erase_wires n C r2 p2 hr2 hp2 x (Or.inl (hv2 x hx)) C.output (fun _ => hv2 x hx)
      have hx1 : W n (eraseC n C r2 p2) x (n + j) = false := by
        rw [hW1 x _ (by omega)]; exact hx
      have e1 := erase_wires n (eraseC n C r2 p2) r1 p1 (by omega) hp1 x (Or.inl (hv1 x hx1))
        (eraseC n C r2 p2).output (fun _ => hv1 x hx1)
      rw [Bool.or_false]
      exact e1.trans e2
    · rw [Bool.or_true]; exact (hB x hx).symm
  have h1 := hL.2 _ (appOr_AO n _ _ (n + j) hA2 ho2 (by omega)) hfun
  have h2 : (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
      (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).gates.length =
      (eraseC n (eraseC n C r2 p2) r1 p1).gates.length + 1 := by simp [appOr]
  omega
lemma one_reader (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j < C.gates.length)
    (hB : Bel n C j) (hne : n + j ≠ C.output) :
    ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
      (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
      (gateAt C r).op = GateOp.or := by
  have hA := hL.1
  obtain ⟨r, hjr, hr, hmr⟩ := least_read n C hL hout j (by omega)
  have huniq : ∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r := by
    intro k hk hmk
    by_contra hkr
    rcases Nat.lt_or_gt_of_ne hkr with h | h
    · exact two_readers n C hL hout j hB k r h hr hmk hmr
    · exact two_readers n C hL hout j hB r k h hk hmr hmk
  refine ⟨r, hr, hmr, huniq, ?_⟩
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rcases hop with hop | hop
  swap
  · exact hop
  exfalso
  have hle : ∀ x : Fin n → Bool, W n C x (n + r) = true → W n C x (n + j) = true := by
    intro x hx
    rw [W_and n C x r hr hop a b hin ha hb] at hx
    have hmr' := hmr
    rw [hin] at hmr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmr'
    rcases hmr' with h | h
    · rw [h]; simp_all
    · rw [h]; simp_all
  by_cases hro : n + r = C.output
  · obtain ⟨x, hx⟩ := least_nodup n C hL (n + j) r (by omega) hr
    apply hx
    cases h1 : W n C x (n + r)
    · cases h2 : W n C x (n + j)
      · rfl
      · have h3 : W n C x C.output = true := hB x h2
        rw [← hro, h1] at h3
        exact absurd h3 (by simp)
    · exact hle x h1
  · obtain ⟨s, hrs, hs, hms⟩ := least_read n C hL hout r (by omega)
    have hv : ∀ x : Fin n → Bool, W n C x (n + j) = false →
        W n C x (n + j) = W n C x (n + r) := by
      intro x hx
      cases h1 : W n C x (n + r)
      · exact hx
      · rw [hle x h1] at hx; exact absurd hx (by simp)
    have hA1 := erase_AO n C r (n + j) hA hr (by omega)
    have hl1 := erase_length n C r (n + j) hr
    have ho1 : (eraseC n C r (n + j)).output < n + (eraseC n C r (n + j)).gates.length :=
      alias_lt (n + r) (n + j) C.output _ (by omega) (by omega) (by omega)
    have hWj : ∀ x : Fin n → Bool, W n (eraseC n C r (n + j)) x (n + j) = W n C x (n + j) :=
      fun x => erase_W_lt n C r (n + j) hr x (n + j) (by omega)
    have hfun : ∀ x : Fin n → Bool,
        (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)).eval (List.ofFn x) =
          C.eval (List.ofFn x) := by
      intro x
      rw [appOr_eval n _ _ (n + j) x ho1 (by omega), hWj x]
      cases hx : W n C x (n + j)
      · rw [Bool.or_false]
        exact erase_wires n C r (n + j) hr (by omega) x (Or.inl (hv x hx)) C.output
          (fun _ => hv x hx)
      · rw [Bool.or_true]; exact (hB x hx).symm
    have hA3 := appOr_AO n _ _ (n + j) hA1 ho1 (by omega)
    have hl3 : (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)).gates.length =
        C.gates.length := by simp [appOr]; omega
    have hL3 : Least n (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)) :=
      ⟨hA3, fun D hD hDf => by
        rw [hl3]; exact hL.2 D hD (fun x => (hDf x).trans (hfun x))⟩
    have hB3 : Bel n (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)) j := by
      intro x hx
      rw [hfun x]
      apply hB x
      rw [appOr_W_lt n _ _ _ x (n + j) (by omega), hWj x] at hx
      exact hx
    refine two_readers n _ hL3 (by simp [appOr]; omega) j hB3 (s - 1) (C.gates.length - 1)
      (by omega) (by rw [hl3]; omega) ?_ ?_
    · rw [appOr_gateAt_lt n _ _ _ (s - 1) (by omega),
        erase_gateAt_ge n C r (n + j) (s - 1) hr (by omega) (by omega)]
      have hs1 : s - 1 + 1 = s := by omega
      rw [hs1]
      simp only [aliasGate, List.mem_map]
      exact ⟨n + r, hms, by simp [aliasWire]⟩
    · have hs2 : C.gates.length - 1 = (eraseC n C r (n + j)).gates.length := by omega
      rw [hs2, appOr_gateAt_last]
      simp
lemma or_children (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (r : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) (hB : Bel n C r) :
    ∃ a b, (gateAt C r).inputs = [n + a, n + b] ∧ a < r ∧ b < r ∧ a ≠ b ∧
      Bel n C a ∧ Bel n C b := by
  obtain ⟨_, a, b, hin, ha, hb⟩ := hL.1 r hr
  have hWr := fun x => W_or n C x r hr hop a b hin ha hb
  have hvar : ∀ c, c < n → (∀ x : Fin n → Bool, W n C x c = true → W n C x (n + r) = true) →
      False := by
    intro c hc hcr
    obtain ⟨x, hx, hf⟩ := hV ⟨c, hc⟩
    have h1 : W n C x c = true := (W_input n C x c hc).trans hx
    have h2 := hB x (hcr x h1)
    rw [hf] at h2
    exact absurd h2 (by simp)
  have hna : n ≤ a := by
    by_contra h
    push Not at h
    exact hvar a h (fun x hx => by rw [hWr x, hx]; rfl)
  have hnb : n ≤ b := by
    by_contra h
    push Not at h
    exact hvar b h (fun x hx => by rw [hWr x, hx]; simp)
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hna
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hnb
  refine ⟨a', b', hin, by omega, by omega, ?_, ?_, ?_⟩
  · intro hab
    subst hab
    obtain ⟨x, hx⟩ := least_nodup n C hL (n + a') r ha hr
    exact hx (by rw [hWr x]; simp)
  · intro x hx; exact hB x (by rw [hWr x, hx]; rfl)
  · intro x hx; exact hB x (by rw [hWr x, hx]; simp)
lemma has_top (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k) :
    ∀ j, j < C.gates.length → Bel n C j →
      ∃ t, t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ Bel n C t ∧ (t = j ∨ Cone t j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hB
    rcases (hL.1 j hj).1 with hop | hop
    · exact ⟨j, hj, hop, hB, Or.inl rfl⟩
    · obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV j hj hop hB
      obtain ⟨t, ht, hopt, hBt, htj⟩ := ih a ha (by omega) hBa
      refine ⟨t, ht, hopt, hBt, Or.inr ?_⟩
      have hmem : n + a ∈ (gateAt C j).inputs := by rw [hin]; simp
      rcases htj with rfl | h
      · exact c1 _ j hj hmem
      · exact c2 t a j hj h hmem
lemma up (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output + 1 = n + C.gates.length)
    (Cone : ℕ → ℕ → Prop)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (t : ℕ) (hTop : ∀ s, s < C.gates.length → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    ∀ d s, s < C.gates.length → C.gates.length - s = d → Cone t s → Bel n C s := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro s hs hd hc
    by_cases hso : n + s = C.output
    · intro x hx
      have h1 : W n C x C.output = true := by rw [← hso]; exact hx
      exact h1
    · obtain ⟨k, hsk, hk, hmk⟩ := least_read n C hL hout s (by omega)
      have hck := c2 t s k hk hc hmk
      have hBk := ih (C.gates.length - k) (by omega) k hk rfl hck
      obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 k hk
      have hopk : (gateAt C k).op = GateOp.or := by
        rcases hop with h | h
        · exact absurd hck (hTop k hk h)
        · exact h
      intro x hx
      apply hBk x
      rw [W_or n C x k hk hopk a b hin ha hb]
      rw [hin] at hmk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmk
      rcases hmk with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
lemma main_abs (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (hTop : ∀ t s, t < C.gates.length → s < C.gates.length → (gateAt C t).op = GateOp.and →
      Bel n C t → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    (∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r) ∧
    (n ≤ C.output ∧ C.output + 1 = n + C.gates.length) ∧
    (∀ O A : Finset ℕ,
      (∀ k, k ∈ O ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ Bel n C k) →
      (∀ k, k ∈ A ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ Bel n C k) →
      O.card + 1 = A.card) := by
  have hout := least_out n C hL hT hV
  have part1 : ∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r := by
    intro j hj hB hne
    obtain ⟨r, hr, hmr, huniq, hopr⟩ := one_reader n C hL hout.2 j hj hB hne
    refine ⟨r, hr, hmr, huniq, hopr, ?_⟩
    obtain ⟨t, ht, hopt, hBt, htj⟩ := has_top n C hL hV Cone c1 c2 j hj hB
    have hc : Cone t r := by
      rcases htj with rfl | h
      · exact c1 _ r hr hmr
      · exact c2 t j r hr h hmr
    exact up n C hL hout.2 Cone c2 t (fun s hs hops => hTop t s ht hs hopt hBt hops) _ r hr rfl hc
  refine ⟨part1, hout, ?_⟩
  intro O A hO hA
  classical
  have hBo : Bel n C (C.gates.length - 1) := by
    intro x hx
    have h1 : n + (C.gates.length - 1) = C.output := by omega
    rw [h1] at hx
    exact hx
  have hoB : C.gates.length - 1 ∈ O ∪ A := by
    rcases (hL.1 (C.gates.length - 1) (by omega)).1 with h | h
    · exact Finset.mem_union_right _ ((hA _).2 ⟨by omega, h, hBo⟩)
    · exact Finset.mem_union_left _ ((hO _).2 ⟨by omega, h, hBo⟩)
  have hdisj : Disjoint O A := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have e1 := ((hO k).1 h1).2.1
    have e2 := ((hA k).1 h2).2.1
    rw [e1] at e2
    cases e2
  obtain ⟨B, hBdef⟩ : ∃ B, B = (O ∪ A).erase (C.gates.length - 1) := ⟨_, rfl⟩
  have hBmem : ∀ j, j ∈ B ↔ j < C.gates.length ∧ Bel n C j ∧ n + j ≠ C.output := by
    intro j
    rw [hBdef, Finset.mem_erase, Finset.mem_union, hO, hA]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, ?_⟩
      rcases (hL.1 j h1).1 with h | h
      · exact Or.inr ⟨h1, h, h2⟩
      · exact Or.inl ⟨h1, h, h2⟩
  have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := B) (t := O)
    (fun j k => n + j ∈ (gateAt C k).inputs)
  have hleft : ∀ j ∈ B,
      (Finset.bipartiteAbove (fun j k => n + j ∈ (gateAt C k).inputs) O j).card = 1 := by
    intro j hj
    obtain ⟨hj1, hj2, hj3⟩ := (hBmem j).1 hj
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := part1 j hj1 hj2 hj3
    rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext k
    simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hmk⟩
      exact huniq k ((hO k).1 hk).1 hmk
    · rintro rfl
      exact ⟨(hO _).2 ⟨hr, hopr, hBr⟩, hmr⟩
  have hright : ∀ k ∈ O,
      (Finset.bipartiteBelow (fun j k => n + j ∈ (gateAt C k).inputs) B k).card = 2 := by
    intro k hk
    obtain ⟨hk1, hk2, hk3⟩ := (hO k).1 hk
    obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV k hk1 hk2 hk3
    rw [Finset.card_eq_two]
    refine ⟨a, b, hab, ?_⟩
    ext j
    simp only [Finset.bipartiteBelow, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      hin, List.mem_cons, List.not_mem_nil, or_false, hBmem]
    constructor
    · rintro ⟨_, h | h⟩
      · left; omega
      · right; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨by omega, hBa, by omega⟩, Or.inl rfl⟩
      · exact ⟨⟨by omega, hBb, by omega⟩, Or.inr rfl⟩
  rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright] at hcount
  simp only [Finset.sum_const, smul_eq_mul] at hcount
  have hBc : B.card = (O ∪ A).card - 1 := by rw [hBdef]; exact Finset.card_erase_of_mem hoB
  have hU : (O ∪ A).card = O.card + A.card := Finset.card_union_of_disjoint hdisj
  have hpos : 0 < (O ∪ A).card := Finset.card_pos.mpr ⟨_, hoB⟩
  omega
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h
lemma inCone_c1 (n : ℕ) (C : Circuit) (hA : AO n C) (i k : ℕ) (hk : k < C.gates.length)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩
lemma inCone_c2 (n : ℕ) (C : Circuit) (hA : AO n C) (t i k : ℕ) (hk : k < C.gates.length)
    (hc : InCone n C t i) (hm : n + i ∈ (gateAt C k).inputs) : InCone n C t k := by
  rw [inCone_iff n C t k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he : n + i - n = i := by omega
  exact ⟨n + i, hm, by omega, hlt, Or.inr (by rw [he]; exact hc)⟩
lemma edge_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) :
    ∃ x : Fin n → Bool, ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  obtain ⟨e, he⟩ := h
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨fun _ => true, u, v, he, rfl, rfl⟩
lemma edge_var (n : ℕ) (G : SimpleGraph (Fin n)) (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  refine ⟨fun w => decide (w = u), by simp, ?_⟩
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha
  subst hb
  exact G.loopless.irrefl _ hab
lemma gf_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  obtain ⟨x, hx⟩ := edge_true n G h
  exact ⟨x, by simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr hx⟩
lemma gf_var (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ graphFun G ∅ x = false := by
  obtain ⟨x, hx, hno⟩ := edge_var n G u
  refine ⟨x, hx, ?_⟩
  simp only [graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨by simp, hno⟩
lemma AO_of_IsAO2 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]; exact List.getElem_mem hk
  have hl := hlen _ hmem
  refine ⟨hao _ hmem, ?_⟩
  match hin : (gateAt C k).inputs, hl with
  | [a, b], _ =>
    exact ⟨a, b, rfl, hrb k hk a (by rw [hin]; simp), hrb k hk b (by rw [hin]; simp)⟩
lemma IsAO2_of_AO (n : ℕ) (C : Circuit) (h : AO n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    exact (h k hk).1
  · intro k hk i hi
    obtain ⟨_, a, b, hin, ha, hb⟩ := h k hk
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    obtain ⟨_, a, b, hin, _, _⟩ := h k hk
    rw [hin]; rfl
lemma main_real (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hne : G.edgeFinset.Nonempty) (hL : PEqualNP.TopForm.IsLeastAO G C)
    (hTF : PEqualNP.TopForm.TopForm G C) :
    (∀ j < C.gates.length, PEqualNP.TopForm.BelowF G C j → n + j ≠ C.output →
      ∃ r, PEqualNP.TopForm.readers n C j = {r} ∧ (gateAt C r).op = GateOp.or ∧
        PEqualNP.TopForm.BelowF G C r) ∧
    PEqualNP.TopForm.readers n C (C.output - n) = ∅ ∧
    (PEqualNP.TopForm.orT G C).card + 1 = (PEqualNP.TopForm.tops G C).card := by
  have hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x =>
    congrFun hL.2.1 x
  have hAO : AO n C := AO_of_IsAO2 n C hL.1
  have hLeast : Least n C := ⟨hAO, fun D hD hDf =>
    hL.2.2 D (IsAO2_of_AO n D hD) (funext fun x => (hDf x).trans (hfun x))⟩
  have hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true := by
    obtain ⟨x, hx⟩ := gf_true n G hne
    exact ⟨x, (hfun x).trans hx⟩
  have hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false := by
    intro u
    obtain ⟨x, hx, hf⟩ := gf_var n G u
    exact ⟨x, hx, (hfun x).trans hf⟩
  have hBel : ∀ j, PEqualNP.TopForm.BelowF G C j ↔ Bel n C j := fun j =>
    ⟨fun h x hx => (hfun x).trans (h x hx), fun h x hx => (hfun x).symm.trans (h x hx)⟩
  obtain ⟨p1, p2, p3⟩ := main_abs n C hLeast hT hV (InCone n C) (inCone_c1 n C hAO)
    (inCone_c2 n C hAO)
    (fun t s ht hs hopt hBt hops => hTF t ht s hs hopt ((hBel t).2 hBt) hops)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hB hne'
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := p1 j hj ((hBel j).1 hB) hne'
    refine ⟨r, ?_, hopr, (hBel r).2 hBr⟩
    ext k
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact huniq k h1 h2
    · rintro rfl
      exact ⟨hr, hmr⟩
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, a, b, hin, ha, hb⟩ := hAO k hk.1
    have h2 := hk.2
    rw [hin] at h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    omega
  · refine p3 _ _ (fun k => ?_) (fun k => ?_)
    · simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]
    · simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]
end S98
lemma cover_g {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset α)
    (hf : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ) (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) :
    f (n + r) ⊆ stops.biUnion f ∧ ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
  have hdown : ∀ k, k ∈ R → f (n + k) ⊆ stops.biUnion f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk u hu
      by_cases hs : k ∈ Z ∨ (g k).op ≠ GateOp.or
      · refine Finset.mem_biUnion.2 ⟨n + k, (hstops _).2 (Or.inr ⟨by omega, ?_, ?_⟩), hu⟩
        · rwa [Nat.add_sub_cancel_left]
        · rwa [Nat.add_sub_cancel_left]
      · have hkZ : k ∉ Z := fun h => hs (Or.inl h)
        have hor : (g k).op = GateOp.or := by
          by_contra h
          exact hs (Or.inr h)
        obtain ⟨w, hw, huw⟩ := (hf k hor u).1 hu
        by_cases hwn : w < n
        · exact Finset.mem_biUnion.2 ⟨w, (hstops _).2 (Or.inl ⟨hwn, k, hk, hkZ, hor, hw⟩), huw⟩
        · have hwk := hback k w hw
          have hweq : n + (w - n) = w := by omega
          have hwR : w - n ∈ R :=
            (hR _).2 (((hR k).1 hk).tail ⟨hkZ, hor, by rwa [hweq]⟩)
          exact ih (w - n) (by omega) hwR (by rwa [hweq])
  have hup : ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
    intro k hk
    have h := (hR k).1 hk
    clear hk
    induction h with
    | refl => exact Finset.Subset.refl _
    | tail _ hbc ih =>
      intro u hu
      exact ih ((hf _ hbc.2.1 u).2 ⟨_, hbc.2.2, hu⟩)
  exact ⟨hdown r ((hR r).2 Relation.ReflTransGen.refl), hup⟩
lemma cover_bound (n : ℕ) (H : SimpleGraph (Fin n)) (T : Finset ℕ) (c : ℕ → Fin n)
    (hcov : ∀ u v : Fin n, H.Adj u v → ∃ a, a ∈ T ∧ (c a = u ∨ c a = v))
    (K : Finset (Fin n)) (hK : IsMinCover H K) : K.card ≤ T.card := by
  classical
  refine (hK.2 (T.image c) ?_).trans Finset.card_image_le
  intro u v huv
  obtain ⟨a, ha, h | h⟩ := hcov u v huv
  · left
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha
  · right
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha
lemma four_split (N : ℕ) (isAnd isOr bel : ℕ → Prop)
    (hAO : ∀ k, k < N → (isAnd k ∧ ¬ isOr k) ∨ (isOr k ∧ ¬ isAnd k))
    (T J O Q : Finset ℕ)
    (hT : ∀ k, k ∈ T ↔ k < N ∧ isAnd k ∧ bel k)
    (hJ : ∀ k, k ∈ J ↔ k < N ∧ isAnd k ∧ ¬ bel k)
    (hO : ∀ k, k ∈ O ↔ k < N ∧ isOr k ∧ bel k)
    (hQ : ∀ k, k ∈ Q ↔ k < N ∧ isOr k ∧ ¬ bel k) :
    T.card + J.card + O.card + Q.card = N := by
  classical
  have h1 : Disjoint T J := by
    rw [Finset.disjoint_left]
    intro k h h'
    exact ((hJ k).1 h').2.2 ((hT k).1 h).2.2
  have h2 : Disjoint (T ∪ J) O := by
    rw [Finset.disjoint_left]
    intro k h h'
    have ho := (hO k).1 h'
    rcases hAO k ho.1 with ha | ha
    · exact ha.2 ho.2.1
    · rcases Finset.mem_union.1 h with h | h
      · exact ha.2 ((hT k).1 h).2.1
      · exact ha.2 ((hJ k).1 h).2.1
  have h3 : Disjoint (T ∪ J ∪ O) Q := by
    rw [Finset.disjoint_left]
    intro k h h'
    have hq := (hQ k).1 h'
    rcases Finset.mem_union.1 h with h | h
    · rcases hAO k hq.1 with ha | ha
      · exact ha.2 hq.2.1
      · rcases Finset.mem_union.1 h with h | h
        · exact ha.2 ((hT k).1 h).2.1
        · exact ha.2 ((hJ k).1 h).2.1
    · exact hq.2.2 ((hO k).1 h).2.2
  have h4 : T ∪ J ∪ O ∪ Q = Finset.range N := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, hT, hJ, hO, hQ]
    constructor
    · rintro (((h | h) | h) | h) <;> exact h.1
    · intro hk
      by_cases hb : bel k
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inl ⟨hk, ha.1, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, ha.1, hb⟩)
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inr ⟨hk, ha.1, hb⟩))
        · exact Or.inr ⟨hk, ha.1, hb⟩
  have h5 := congrArg Finset.card h4
  rw [Finset.card_union_of_disjoint h3, Finset.card_union_of_disjoint h2,
    Finset.card_union_of_disjoint h1, Finset.card_range] at h5
  exact h5
def TwoNe {α : Type} (g : ℕ → Gate) (f : ℕ → Finset α) (k : ℕ) : Prop :=
  ∃ w1 ∈ (g k).inputs, ∃ w2 ∈ (g k).inputs, w1 ≠ w2 ∧ (f w1).Nonempty ∧ (f w2).Nonempty
lemma cone_count2 {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate) (f : ℕ → Finset α)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ)
    (hlen : ∀ k, k ∉ Z → (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)))
    (I : Finset ℕ)
    (hI : ∀ k, k ∈ R → k ∉ Z → (g k).op = GateOp.or → TwoNe g f k → k ∈ I) :
    (stops.filter (fun w => (f w).Nonempty)).card ≤ I.card + 1 := by
  classical
  set E : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or) with hE
  set N : ℕ → Finset ℕ := fun k => (g k).inputs.toFinset.filter (fun w => (f w).Nonempty)
    with hN
  set U : Finset ℕ := insert (n + r) (E.biUnion N) with hU
  set E2 := E.filter (fun k => 2 ≤ (N k).card) with hE2
  set Ene := E.filter (fun k => (f (n + k)).Nonempty) with hEne
  have hE2I : E2 ⊆ I := by
    intro k hk
    simp only [hE2, hE, Finset.mem_filter] at hk
    obtain ⟨⟨hkR, hkZ, hor⟩, h2⟩ := hk
    apply hI k hkR hkZ hor
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (N k).card)
    simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw1 hw2
    exact ⟨w1, hw1.1, w2, hw2.1, hne, hw1.2, hw2.2⟩
  have hNk : ∀ k ∈ E, (N k).card ≤ (if 2 ≤ (N k).card then 1 else 0) +
      (if (f (n + k)).Nonempty then 1 else 0) := by
    intro k hk
    simp only [hE, Finset.mem_filter] at hk
    have hc : (N k).card ≤ 2 := (Finset.card_filter_le _ _).trans
      ((List.toFinset_card_le _).trans (hlen k hk.2.1 hk.2.2))
    have hne : 1 ≤ (N k).card → (f (n + k)).Nonempty := by
      intro h1
      obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < (N k).card)
      simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw
      obtain ⟨u, hu⟩ := hw.2
      exact ⟨u, (hf2 k hk.2.2 u).2 ⟨w, hw.1, hu⟩⟩
    rcases Nat.lt_or_ge (N k).card 1 with h0 | h0
    · omega
    · rw [if_pos (hne h0)]
      split_ifs <;> omega
  have hsum : (E.biUnion N).card ≤ E2.card + Ene.card := by
    calc (E.biUnion N).card ≤ ∑ k ∈ E, (N k).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ E, ((if 2 ≤ (N k).card then 1 else 0) +
          (if (f (n + k)).Nonempty then 1 else 0)) := Finset.sum_le_sum hNk
      _ = E2.card + Ene.card := by
        rw [Finset.sum_add_distrib, hE2, hEne, Finset.card_filter, Finset.card_filter]
  have hUcard : U.card ≤ E2.card + Ene.card + 1 := by
    have hins : U.card ≤ (E.biUnion N).card + 1 := Finset.card_insert_le (n + r) (E.biUnion N)
    omega
  have hmem : ∀ w, (f w).Nonempty → (w = n + r ∨ ∃ k' ∈ E, w ∈ (g k').inputs) → w ∈ U := by
    rintro w hw (h | ⟨k', hk', hin⟩)
    · rw [h]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨k', hk', ?_⟩)
      simp only [hN, Finset.mem_filter, List.mem_toFinset]
      exact ⟨hin, hw⟩
  have hRU : ∀ k, k ∈ R → n + k = n + r ∨ ∃ k' ∈ E, n + k ∈ (g k').inputs := by
    intro k hk
    rcases Relation.ReflTransGen.cases_tail ((hR k).1 hk) with h | ⟨b, hb, hb1, hb2, hb3⟩
    · left
      rw [h]
    · right
      refine ⟨b, ?_, hb3⟩
      rw [hE, Finset.mem_filter]
      exact ⟨(hR b).2 hb, hb1, hb2⟩
  set S2 : Finset ℕ := Ene.image (fun k => n + k) with hS2
  have hS2card : S2.card = Ene.card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  have hdisj : Disjoint (stops.filter (fun w => (f w).Nonempty)) S2 := by
    rw [Finset.disjoint_left]
    intro w hw hw2
    rw [Finset.mem_filter] at hw
    rw [hS2, Finset.mem_image] at hw2
    obtain ⟨k, hk, rfl⟩ := hw2
    rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
    rcases (hstops _).1 hw.1 with ⟨h1, _⟩ | ⟨_, _, h3⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h3
      rcases h3 with h3 | h3
      · exact hk.1.2.1 h3
      · exact h3 hk.1.2.2
  have hsub : (stops.filter (fun w => (f w).Nonempty)) ∪ S2 ⊆ U := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [Finset.mem_filter] at hw
      rcases (hstops _).1 hw.1 with ⟨_, k, hk, hk1, hk2, hk3⟩ | ⟨h1, h2, _⟩
      · refine hmem w hw.2 (Or.inr ⟨k, ?_, hk3⟩)
        rw [hE, Finset.mem_filter]
        exact ⟨hk, hk1, hk2⟩
      · have := hRU _ h2
        rw [Nat.add_sub_cancel' h1] at this
        exact hmem w hw.2 this
    · rw [hS2, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
      exact hmem _ hk.2 (hRU k hk.1.1)
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hS2card] at h3
  have h4 := Finset.card_le_card hE2I
  omega
lemma top_step2 (n : ℕ) (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (Z : Finset ℕ) (ρ : ℕ) (c : Fin n) (E0 : Finset (Sym2 (Fin n)))
    (hZ : ∀ k, k ∈ Z → f (n + k) ⊆ f ρ →
      (∀ v, v ∈ f (n + k) → s(c, v) ∈ E0) ∨ (f (n + k)).card ≤ 1) :
    ∃ Znew : Finset ℕ, Disjoint Z Znew ∧
      (∀ k, k ∈ Znew → (g k).op = GateOp.or ∧ TwoNe g f k ∧ n ≤ ρ ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (ρ - n) k ∧ f (n + k) ⊆ f ρ) ∧
      (((f ρ).image (fun v => s(c, v))) \ E0).card ≤ Znew.card + 1 := by
  classical
  by_cases hρ : ρ < n
  · refine ⟨∅, Finset.disjoint_empty_right _, by simp, ?_⟩
    calc (((f ρ).image (fun v => s(c, v))) \ E0).card
        ≤ ((f ρ).image (fun v => s(c, v))).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ (f ρ).card := Finset.card_image_le
      _ ≤ 1 := hf1 ρ hρ
      _ ≤ (∅ : Finset ℕ).card + 1 := by simp
  · have hρn : n ≤ ρ := Nat.le_of_not_lt hρ
    obtain ⟨r, rfl⟩ : ∃ r, ρ = n + r := ⟨ρ - n, by omega⟩
    have hle : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k → k ≤ r := by
      intro k h
      induction h with
      | refl => exact le_refl _
      | tail _ hbc ih =>
        have := hback _ _ hbc.2.2
        omega
    set R : Finset ℕ := (Finset.range (r + 1)).filter (fun k =>
      Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k) with hRdef
    have hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
      intro k
      rw [hRdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Nat.lt_succ_of_le (hle k h), h⟩
    set stops : Finset ℕ := (Finset.range (n + r + 1)).filter (fun w =>
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) with hsdef
    have hstops : ∀ w, w ∈ stops ↔
        (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
        (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)) := by
      intro w
      rw [hsdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases h with ⟨h1, _⟩ | ⟨h1, h2, _⟩
        · omega
        · have := hle _ ((hR _).1 h2)
          omega
    set Znew : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or ∧ TwoNe g f k)
      with hZn
    obtain ⟨hcov, hup⟩ := cover_g n g hback f hf2 Z r R hR stops hstops
    have hcnt : (stops.filter (fun w => (f w).Nonempty)).card ≤ Znew.card + 1 :=
      cone_count2 n g f hf2 Z (fun k _ h => hlen k h) r R hR stops hstops Znew (by
        intro k hk hkZ hor htwo
        rw [hZn, Finset.mem_filter]
        exact ⟨hk, hkZ, hor, htwo⟩)
    refine ⟨Znew, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro k hk hk2
      rw [hZn, Finset.mem_filter] at hk2
      exact hk2.2.1 hk
    · intro k hk
      rw [hZn, Finset.mem_filter] at hk
      refine ⟨hk.2.2.1, hk.2.2.2, hρn, ?_, hup k hk.1⟩
      rw [Nat.add_sub_cancel_left]
      have hreach : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k →
          Relation.ReflTransGen (fun k k' : ℕ =>
            (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
        intro k h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih => exact ih.tail hbc.2
      exact hreach k ((hR k).1 hk.1)
    · have hsub : ((f (n + r)).image (fun v => s(c, v))) \ E0 ⊆
          (stops.filter (fun w => (f w).Nonempty)).biUnion
            (fun w => ((f w).image (fun v => s(c, v))) \ E0) := by
        intro e he
        rw [Finset.mem_sdiff, Finset.mem_image] at he
        obtain ⟨⟨v, hv, rfl⟩, he0⟩ := he
        obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.1 (hcov hv)
        refine Finset.mem_biUnion.2 ⟨w, Finset.mem_filter.2 ⟨hw, ⟨v, hvw⟩⟩, ?_⟩
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_image_of_mem _ hvw, he0⟩
      have hone : ∀ w, w ∈ stops.filter (fun w => (f w).Nonempty) →
          (((f w).image (fun v => s(c, v))) \ E0).card ≤ 1 := by
        intro w hw'
        have hw := (Finset.mem_filter.1 hw').1
        have himg : ∀ t : Finset (Fin n), t.card ≤ 1 →
            ((t.image (fun v => s(c, v))) \ E0).card ≤ 1 := fun t ht =>
          (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_image_le.trans ht)
        rcases (hstops w).1 hw with ⟨hwn, _⟩ | ⟨hwn, hwR, hw2⟩
        · exact himg _ (hf1 w hwn)
        · have hweq : n + (w - n) = w := by omega
          rcases hw2 with hz | hnor
          · have hsubw : f (n + (w - n)) ⊆ f (n + r) := hup _ hwR
            rcases hZ _ hz hsubw with hall | hc1
            · rw [hweq] at hall
              have hempty : ((f w).image (fun v => s(c, v))) \ E0 = ∅ := by
                rw [Finset.sdiff_eq_empty_iff_subset]
                intro e he
                obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
                exact hall v hv
              rw [hempty]
              simp
            · rw [hweq] at hc1
              exact himg _ hc1
          · have := hf3 _ hnor
            rw [hweq] at this
            exact himg _ this
      calc (((f (n + r)).image (fun v => s(c, v))) \ E0).card
          ≤ ((stops.filter (fun w => (f w).Nonempty)).biUnion
              (fun w => ((f w).image (fun v => s(c, v))) \ E0)).card :=
            Finset.card_le_card hsub
        _ ≤ (stops.filter (fun w => (f w).Nonempty)).card * 1 :=
            Finset.card_biUnion_le_card_mul _ _ _ hone
        _ ≤ Znew.card + 1 := by omega
lemma star_count2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (l : List (Fin n × ℕ))
    (hadj : ∀ p, p ∈ l → ∀ v, v ∈ f p.2 → G.Adj p.1 v) :
    ∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ p, p ∈ l ∧ n ≤ p.2 ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (p.2 - n) k ∧ f (n + k) ⊆ f p.2) ∧
      (l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v)))).card
        ≤ l.length + Z.card := by
  classical
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨Z, hZ1, hZ2⟩ := ih (fun q hq => hadj q (List.mem_cons_of_mem _ hq))
    set E0 := l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v))) with hE0
    obtain ⟨Znew, hd, hn1, hn2⟩ := top_step2 n g hlen hback f hf1 hf2 hf3 (Z ∪ B) p.2 p.1 E0 (by
      intro k hk hsub
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨_, _, _, q, hq, _, _, hfq⟩ := hZ1 k hk
        by_cases hc : q.1 = p.1
        · left
          intro v hv
          rw [hE0]
          refine Finset.mem_biUnion.2 ⟨q, List.mem_toFinset.2 hq, ?_⟩
          rw [← hc]
          exact Finset.mem_image_of_mem _ (hfq hv)
        · right
          by_contra hcard
          have h2 : 1 < (f (n + k)).card := by omega
          obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.1 h2
          have a1 : G.Adj p.1 v := hadj p List.mem_cons_self v (hsub hv)
          have a2 : G.Adj p.1 v' := hadj p List.mem_cons_self v' (hsub hv')
          have b1 : G.Adj q.1 v := hadj q (List.mem_cons_of_mem _ hq) v (hfq hv)
          have b2 : G.Adj q.1 v' := hadj q (List.mem_cons_of_mem _ hq) v' (hfq hv')
          exact h4 p.1 v q.1 v' (fun h => hc h.symm) hne ⟨a1, b1.symm, b2, a2.symm⟩
      · exact Or.inr (hB k hk))
    have hd1 : Disjoint Z Znew := Finset.disjoint_of_subset_left Finset.subset_union_left hd
    refine ⟨Z ∪ Znew, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨h0, h1, ht, q, hq, h2⟩ := hZ1 k hk
        exact ⟨h0, h1, ht, q, List.mem_cons_of_mem _ hq, h2⟩
      · obtain ⟨h1, ht, h2, h3, h5⟩ := hn1 k hk
        refine ⟨?_, h1, ht, p, List.mem_cons_self, h2, h3, h5⟩
        intro hkB
        exact (Finset.disjoint_left.1 hd (Finset.mem_union_right _ hkB)) hk
    · rw [List.toFinset_cons, Finset.biUnion_insert, Finset.card_union_of_disjoint hd1,
        List.length_cons, ← hE0]
      have hsplit : (f p.2).image (fun v => s(p.1, v)) ∪ E0 =
          (((f p.2).image (fun v => s(p.1, v))) \ E0) ∪ E0 := by
        rw [Finset.sdiff_union_self_eq_union]
      have hle := Finset.card_union_le (((f p.2).image (fun v => s(p.1, v))) \ E0) E0
      rw [← hsplit] at hle
      omega
lemma assemble2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (T : Finset ℕ) (o : ℕ → Fin 2 → ℕ)
    (hstar : ∀ a, a ∈ T → (∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) → G.Adj u v) ∧
      ((f (o a 0)).card ≤ 1 ∨ (f (o a 1)).card ≤ 1))
    (Es : Finset (Sym2 (Fin n)))
    (hEs : ∀ e, e ∈ Es → ∃ a, a ∈ T ∧ ∃ u, u ∈ f (o a 0) ∧ ∃ v, v ∈ f (o a 1) ∧ e = s(u, v)) :
    (∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ a, a ∈ T ∧ ∃ b : Fin 2,
        n ≤ o a b ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (o a b - n) k ∧
        f (n + k) ⊆ f (o a b) ∧ (f (o a (1 - b))).card = 1) ∧
      Es.card ≤ T.card + Z.card) ∧
    ∀ (H : SimpleGraph (Fin n)) (K : Finset (Fin n)),
      (∀ u v : Fin n, H.Adj u v → s(u, v) ∈ Es) → IsMinCover H K → K.card ≤ T.card := by
  classical
  by_cases hEe : Es = ∅
  · subst hEe
    refine ⟨⟨∅, by simp, by simp⟩, ?_⟩
    intro H K hH hK
    have h0 := hK.2 ∅ (by
      intro u v huv
      exact absurd (hH u v huv) (Finset.notMem_empty _))
    simp only [Finset.card_empty] at h0
    omega
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hEe
    obtain ⟨_, _, v0, _, _⟩ := hEs e0 he0
    set c : ℕ → Fin n := fun a =>
      if (f (o a 0)).card ≤ 1 then (if h : (f (o a 0)).Nonempty then h.choose else v0)
      else (if h : (f (o a 1)).Nonempty then h.choose else v0) with hc
    set ρ : ℕ → ℕ := fun a => if (f (o a 0)).card ≤ 1 then o a 1 else o a 0 with hρ
    have hkey : ∀ a, a ∈ T → ∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) →
        (c a = u ∧ v ∈ f (ρ a)) ∨ (c a = v ∧ u ∈ f (ρ a)) := by
      intro a ha u hu v hv
      by_cases h0 : (f (o a 0)).card ≤ 1
      · left
        have hne : (f (o a 0)).Nonempty := ⟨u, hu⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h0 _ hne.choose_spec _ hu
        · simp only [hρ, h0, ↓reduceIte]
          exact hv
      · right
        have h1 : (f (o a 1)).card ≤ 1 := by
          rcases (hstar a ha).2 with h | h
          · exact absurd h h0
          · exact h
        have hne : (f (o a 1)).Nonempty := ⟨v, hv⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h1 _ hne.choose_spec _ hv
        · simp only [hρ, h0, ↓reduceIte]
          exact hu
    set T' : Finset ℕ := T.filter (fun a => (f (o a 0)).Nonempty ∧ (f (o a 1)).Nonempty)
      with hT'
    have hT'T : ∀ a, a ∈ T' → a ∈ T := fun a ha => (Finset.mem_filter.1 ha).1
    have hT'card : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hadjc : ∀ a, a ∈ T' → ∀ v, v ∈ f (ρ a) → G.Adj (c a) v := by
      intro a ha' v hv
      have ha := hT'T a ha'
      have hnn := (Finset.mem_filter.1 ha').2
      by_cases h0 : (f (o a 0)).card ≤ 1
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.1
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact (hstar a ha).1 _ hne.choose_spec v hv
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.2
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact ((hstar a ha).1 v hv _ hne.choose_spec).symm
    have hEs' : ∀ e, e ∈ Es → ∃ a, a ∈ T' ∧ ∃ v, v ∈ f (ρ a) ∧ e = s(c a, v) := by
      intro e he
      obtain ⟨a, ha, u, hu, v, hv, rfl⟩ := hEs e he
      have ha' : a ∈ T' := Finset.mem_filter.2 ⟨ha, ⟨u, hu⟩, ⟨v, hv⟩⟩
      rcases hkey a ha u hu v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨a, ha', v, h2, by rw [h1]⟩
      · exact ⟨a, ha', u, h2, by rw [h1]; exact Sym2.eq_swap⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨Z, hZ1, hZ2⟩ := star_count2 n G h4 g hlen hback f hf1 hf2 hf3 B hB
        (T'.toList.map (fun a => (c a, ρ a))) (by
          intro p hp v hv
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
          exact hadjc a (Finset.mem_toList.1 ha) v hv)
      refine ⟨Z, ?_, ?_⟩
      · intro k hk
        obtain ⟨h1, h2, ht, p, hp, h3, h5, h6⟩ := hZ1 k hk
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
        have ha' := Finset.mem_toList.1 ha
        have hnn := (Finset.mem_filter.1 ha').2
        refine ⟨h1, h2, ht, a, hT'T a ha', ?_⟩
        by_cases h0 : (f (o a 0)).card ≤ 1
        · refine ⟨1, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 1 : Fin 2) = 0 := by decide
          rw [e]
          exact ⟨h3, h5, h6, le_antisymm h0 (Finset.card_pos.2 hnn.1)⟩
        · refine ⟨0, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 0 : Fin 2) = 1 := by decide
          rw [e]
          have h1' : (f (o a 1)).card ≤ 1 := by
            rcases (hstar a (hT'T a ha')).2 with h | h
            · exact absurd h h0
            · exact h
          exact ⟨h3, h5, h6, le_antisymm h1' (Finset.card_pos.2 hnn.2)⟩
      · have hsub : Es ⊆ (T'.toList.map (fun a => (c a, ρ a))).toFinset.biUnion
            (fun p => (f p.2).image (fun v => s(p.1, v))) := by
          intro e he
          obtain ⟨a, ha, v, hv, rfl⟩ := hEs' e he
          refine Finset.mem_biUnion.2 ⟨(c a, ρ a), ?_, Finset.mem_image_of_mem _ hv⟩
          exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩)
        have h1 := Finset.card_le_card hsub
        rw [List.length_map, Finset.length_toList] at hZ2
        omega
    · intro H K hH hK
      refine (cover_bound n H T' c ?_ K hK).trans hT'card
      intro u v huv
      obtain ⟨a, ha, w, hw, he⟩ := hEs' _ (hH u v huv)
      refine ⟨a, ha, ?_⟩
      have := Sym2.eq_iff.1 he
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm
lemma gateAt_ge {C : Circuit} {k : ℕ} (hk : C.gates.length ≤ k) :
    gateAt C k = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]
lemma orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C p ↔ Relation.ReflTransGen (S90.OrStep n C) p u.val :=
  ⟨S90.mem_orIn_reach u, S90.reach_mem_orIn u⟩
lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [orIn_iff_reach] at ha hb
  have h1 : ∀ c : Fin n, Relation.ReflTransGen (S90.OrStep n C) w c.val → c.val = w := by
    intro c hc
    rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
    · exact h.symm
    · obtain ⟨k, _, h3, _⟩ := hd
      omega
  exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)
lemma orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
        u ∈ PEqualNP.TopForm.orIn n C w := by
  rw [orIn_iff_reach]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
    · have := u.isLt
      omega
    · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
      have hkk : k' = k := by omega
      subst hkk
      exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
  · rintro ⟨hk, hop, w, hw, hlt, hu⟩
    exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)
lemma junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ PEqualNP.TopForm.BelowF G C k := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hc
    apply h3
    intro x hx
    by_contra hf
    exact hc ⟨x, hx, by simpa using hf⟩
lemma opnd_lt {n : ℕ} {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hRB : ReadsBack n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    PEqualNP.TopForm.opnd C a b < n + a := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem ha))
  have hp : p < n + a := hRB a ha p (by rw [hin]; simp)
  have hq : q < n + a := hRB a ha q (by rw [hin]; simp)
  fin_cases b
  · simpa [PEqualNP.TopForm.opnd, hin] using hp
  · simpa [PEqualNP.TopForm.opnd, hin] using hq
lemma rtg_conv {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (r k : ℕ)
    (h : Relation.ReflTransGen (fun k k' : ℕ =>
      (gateAt C k).op = GateOp.or ∧ n + k' ∈ (gateAt C k).inputs) r k)
    (hr : r < C.gates.length) :
    Relation.ReflTransGen (S90.OrStep n C) (n + r) (n + k) ∧ k < C.gates.length := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hr⟩
  | tail _ hbc ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hlt := hRB _ ih2 _ hbc.2
    exact ⟨ih1.tail ⟨_, ih2, rfl, hbc.1, hbc.2, hlt⟩, by omega⟩
lemma two_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hRB : ReadsBack n C) {k : ℕ}
    (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
    (htwo : TwoNe (gateAt C) (PEqualNP.TopForm.orIn n C) k) :
    ¬ PEqualNP.TopForm.BelowF G C k ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 0)).Nonempty ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 1)).Nonempty := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem hk))
  have e0 : PEqualNP.TopForm.opnd C k 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
  have e1 : PEqualNP.TopForm.opnd C k 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
  obtain ⟨w1, hw1, w2, hw2, hne, hn1, hn2⟩ := htwo
  have hw1lt : w1 < n + k := hRB k hk w1 hw1
  have hw1m := hw1
  rw [hin] at hw1 hw2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1 hw2
  refine ⟨?_, ?_⟩
  · intro hbel
    obtain ⟨u, hu⟩ := hn1
    have hu2 : u ∈ PEqualNP.TopForm.orIn n C (n + k) :=
      (orIn_gate C k u).2 ⟨hk, hor, w1, hw1m, hw1lt, hu⟩
    have hr := (orIn_iff_reach _ u).1 hu2
    have hv := S90.reach_var_val (PEqualNP.EdgeOwnership.pairInput u u) (n + k) u hr
      (S90.pairInput_left u u)
    have hF := hbel _ (by rw [S90.gateVal_eq_val]; exact hv)
    exact G.irrefl ((S90.graphFun_pair G u u).1 hF)
  · rw [e0, e1]
    rcases hw1 with h1 | h1 <;> rcases hw2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn1, hn2⟩
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn2, hn1⟩
    · exact absurd (h1.trans h2.symm) hne
lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : PEqualNP.TopForm.NoFourCycle G) (hne : G.edgeFinset.Nonempty)
    (hL : PEqualNP.TopForm.IsLeastAO G C) (hTF : PEqualNP.TopForm.TopForm G C) :
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  classical
  obtain ⟨⟨hAO, hRB, h2⟩, _, _⟩ := id hL
  have hlen : ∀ k, (gateAt C k).op = GateOp.or → (gateAt C k).inputs.length ≤ 2 := by
    intro k _
    by_cases hk : k < C.gates.length
    · rw [h2 _ (S90.gateAt_mem hk)]
    · rw [gateAt_ge (by omega)]
      simp
  have hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k := by
    intro k i hi
    by_cases hk : k < C.gates.length
    · exact hRB k hk i hi
    · rw [gateAt_ge (by omega)] at hi
      simp at hi
  have hf2 : ∀ k, (gateAt C k).op = GateOp.or → ∀ u,
      u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔
        ∃ w ∈ (gateAt C k).inputs, u ∈ PEqualNP.TopForm.orIn n C w := by
    intro k hop u
    rw [orIn_gate]
    constructor
    · rintro ⟨_, _, w, hw, _, hu⟩
      exact ⟨w, hw, hu⟩
    · rintro ⟨w, hw, hu⟩
      have hk : k < C.gates.length := by
        by_contra hk
        rw [gateAt_ge (by omega)] at hw
        simp at hw
      exact ⟨hk, hop, w, hw, hRB k hk w hw, hu⟩
  have hf3 : ∀ k, (gateAt C k).op ≠ GateOp.or →
      (PEqualNP.TopForm.orIn n C (n + k)).card ≤ 1 := by
    intro k hop
    rw [Finset.card_le_one]
    intro a ha
    exact absurd ((orIn_gate C k a).1 ha).2.1 hop
  have h4' : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro a b c d hac hbd ⟨h1, h2', h3, h5⟩
    have hsub : ({b, d} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨h1, h2'.symm⟩
      · exact ⟨h5.symm, h3⟩
    have := (Finset.card_le_card hsub).trans (h4 a c hac)
    rw [Finset.card_pair hbd] at this
    omega
  have hstar : ∀ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C →
      (∀ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) →
        ∀ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) → G.Adj u v) ∧
      ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0)).card ≤ 1 ∨
        (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)).card ≤ 1) := by
    intro a ha
    have hf := S90.top_facts G C h4 hL a (Finset.mem_sdiff.1 ha).1
    exact ⟨hf.2.1, hf.2.2⟩
  have hEs : ∀ e, e ∈ G.edgeFinset \ PEqualNP.TopForm.Ustar G C →
      ∃ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C ∧
        ∃ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧
        ∃ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) ∧ e = s(u, v) := by
    intro e he
    have he' : e ∈ PEqualNP.TopForm.starEdges G C := by
      simp only [PEqualNP.TopForm.Ustar, Finset.mem_sdiff, not_and, not_not] at he
      exact he.2 he.1
    simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_product] at he'
    obtain ⟨a, ha, p, hp, hpe⟩ := he'
    refine ⟨a, ?_, p.1, hp.1, p.2, hp.2, hpe.symm⟩
    rw [Finset.mem_sdiff]
    refine ⟨ha, fun hc => ?_⟩
    simp only [PEqualNP.TopForm.centreless, Finset.mem_filter] at hc
    rcases hc.2 with h | h
    · have := hp.1
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
    · have := hp.2
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
  obtain ⟨⟨Z, hZ1, hZ2⟩, hcov⟩ := assemble2 n G h4' (gateAt C) hlen hback
    (fun w => PEqualNP.TopForm.orIn n C w) (fun w hw => orIn_input C w hw) hf2 hf3 ∅ (by simp)
    (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C) (PEqualNP.TopForm.opnd C)
    hstar (G.edgeFinset \ PEqualNP.TopForm.Ustar G C) hEs
  refine ⟨?_, ?_⟩
  · have hZlam : Z ⊆ PEqualNP.TopForm.lam G C := by
      intro k hk
      obtain ⟨-, hor, htwo, a, ha, b, hnb, hrt, -, hcard⟩ := hZ1 k hk
      have hatop := (Finset.mem_sdiff.1 ha).1
      have halen : a < C.gates.length := by
        simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
          Finset.mem_range] at hatop
        exact hatop.1
      have hlt := opnd_lt h2 hRB halen b
      obtain ⟨hreach, hklen⟩ := rtg_conv C hRB _ k hrt (by omega)
      rw [show n + (PEqualNP.TopForm.opnd C a b - n) = PEqualNP.TopForm.opnd C a b by omega]
        at hreach
      have hOR := S90.reach_orReaches hreach k rfl hklen
      obtain ⟨hnbel, hn0, hn1⟩ := two_facts G C h2 hRB hklen hor htwo
      simp only [PEqualNP.TopForm.lam, PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨hklen, hor, hnbel⟩, hn0, hn1, a, hatop, b, hcard, hOR⟩
    have hAO' : ∀ k, k < C.gates.length →
        ((gateAt C k).op = GateOp.and ∧ ¬ (gateAt C k).op = GateOp.or) ∨
        ((gateAt C k).op = GateOp.or ∧ ¬ (gateAt C k).op = GateOp.and) := by
      intro k hk
      rcases hAO _ (S90.gateAt_mem hk) with h | h
      · exact Or.inl ⟨h, fun h' => by rw [h] at h'; cases h'⟩
      · exact Or.inr ⟨h, fun h' => by rw [h] at h'; cases h'⟩
    have hsplit := four_split C.gates.length (fun k => (gateAt C k).op = GateOp.and)
      (fun k => (gateAt C k).op = GateOp.or) (fun k => PEqualNP.TopForm.BelowF G C k) hAO'
      (PEqualNP.TopForm.tops G C) (PEqualNP.TopForm.junk G C) (PEqualNP.TopForm.orT G C)
      (PEqualNP.TopForm.orN G C)
      (fun k => by simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => junk_iff G C k)
      (fun k => by simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => by simp only [PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
    have hm := (S98.main_real n G C hne hL hTF).2.2
    have hsize : C.size = C.gates.length := rfl
    have hU := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.Ustar G C ⊆ G.edgeFinset from Finset.sdiff_subset)
    have hTc := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.centreless G C ⊆ PEqualNP.TopForm.tops G C from
        Finset.filter_subset _ _)
    have hlam := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.lam G C ⊆ PEqualNP.TopForm.orN G C from
        Finset.filter_subset _ _)
    have hZl := Finset.card_le_card hZlam
    omega
  · intro K hK
    refine hcov _ K ?_ hK
    intro u v huv
    rw [SimpleGraph.deleteEdges_adj] at huv
    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    exact ⟨huv.1, fun h => huv.2 (Finset.mem_coe.2 h)⟩
end Ledger
namespace Star
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open Ledger.S98 (W AO gateAt_eq W_input W_or W_and prefix_W IsAO2_of_AO)
def orTreeGates (base : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([], 0)
  | [w] => ([], w)
  | w :: ws =>
    let (gs, out) := orTreeGates base ws
    (gs ++ [⟨GateOp.or, [w, out]⟩], base + gs.length)
lemma orTreeGates_length (base : ℕ) (ws : List ℕ) (hne : ws ≠ []) :
    (orTreeGates base ws).1.length + 1 = ws.length := by
  induction ws with
  | nil => contradiction
  | cons w ws ih =>
    cases ws with
    | nil => simp [orTreeGates]
    | cons w2 ws2 =>
      have h := ih (by simp)
      simp only [orTreeGates, List.length_append, List.length_cons, List.length_nil] at h ⊢
      omega
lemma orTreeGates_out_lt (base : ℕ) (ws : List ℕ) (hne : ws ≠ [])
    (hws : ∀ w ∈ ws, w < base) :
    (orTreeGates base ws).2 < base + (orTreeGates base ws).1.length := by
  induction ws with
  | nil => contradiction
  | cons w ws ih =>
    cases ws with
    | nil =>
      simp only [orTreeGates, List.length_nil, add_zero]
      exact hws w (by simp)
    | cons w2 ws2 =>
      simp only [orTreeGates, List.length_append, List.length_singleton]
      omega
lemma orTreeGates_eval (n : ℕ) (pre : List Gate) (ws : List ℕ) (hne : ws ≠ [])
    (hws : ∀ w ∈ ws, w < n + pre.length) (x : Fin n → Bool) :
    let res := orTreeGates (n + pre.length) ws
    let C' : Circuit := ⟨pre ++ res.1, res.2⟩
    (∀ k (hk : k < res.1.length),
      let g := res.1[k]'hk
      (g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a < n + pre.length + k ∧ b < n + pre.length + k) ∧
    (W n C' x res.2 = true ↔ ∃ w ∈ ws, W n ⟨pre, 0⟩ x w = true) := by
  induction ws with
  | nil => contradiction
  | cons w ws ih =>
    cases ws with
    | nil =>
      simp only [orTreeGates, List.append_nil]
      refine ⟨fun k hk => by simp at hk, ?_⟩
      simp only [List.mem_singleton, exists_eq_left]
      have hpre : W n ⟨pre, w⟩ x w = W n ⟨pre, 0⟩ x w := by
        simp [W, Circuit.wires]
      rw [hpre]
    | cons w2 ws2 =>
      have hne' : w2 :: ws2 ≠ [] := by simp
      have hws' : ∀ u ∈ w2 :: ws2, u < n + pre.length := fun u hu => hws u (by simp [hu])
      have hw : w < n + pre.length := hws w (by simp)
      obtain ⟨hAO', heval'⟩ := ih hne' hws'
      set gs := (orTreeGates (n + pre.length) (w2 :: ws2)).1
      set out := (orTreeGates (n + pre.length) (w2 :: ws2)).2
      have hout_lt : out < n + pre.length + gs.length :=
        orTreeGates_out_lt (n + pre.length) (w2 :: ws2) hne' hws'
      have hres_eq : orTreeGates (n + pre.length) (w :: w2 :: ws2) =
          (gs ++ [⟨GateOp.or, [w, out]⟩], n + pre.length + gs.length) := rfl
      dsimp only
      rw [hres_eq]
      constructor
      · intro k hk
        have hk' : k < gs.length + 1 := by simpa [List.length_append] using hk
        by_cases hkl : k < gs.length
        · have hget : (gs ++ [⟨GateOp.or, [w, out]⟩])[k]'hk = gs[k]'hkl :=
            List.getElem_append_left hkl
          rw [hget]
          exact hAO' k hkl
        · have hkeq : k = gs.length := by omega
          subst hkeq
          have hget : (gs ++ [⟨GateOp.or, [w, out]⟩])[gs.length]'hk = ⟨GateOp.or, [w, out]⟩ := by
            simp
          rw [hget]
          exact ⟨rfl, w, out, rfl, by omega, by omega⟩
      · let C1 : Circuit := ⟨pre ++ gs, out⟩
        let C2 : Circuit := ⟨pre ++ (gs ++ [⟨GateOp.or, [w, out]⟩]), n + pre.length + gs.length⟩
        change W n C2 x (n + pre.length + gs.length) = true ↔ _
        have hlen : C2.gates.length = pre.length + gs.length + 1 := by simp [C2]; omega
        have hidx : pre.length + gs.length < C2.gates.length := by omega
        have hgate : gateAt C2 (pre.length + gs.length) = ⟨GateOp.or, [w, out]⟩ := by
          rw [gateAt_eq C2 (pre.length + gs.length) hidx]
          simp [C2, ← List.append_assoc]
        have hWlast : W n C2 x (n + (pre.length + gs.length)) =
            (W n C2 x w || W n C2 x out) := by
          exact W_or n C2 x (pre.length + gs.length) hidx (by rw [hgate]) w out (by rw [hgate])
            (by omega) (by omega)
        have hCw : W n C2 x w = W n ⟨pre, 0⟩ x w := by
          have := prefix_W n pre (gs ++ [⟨GateOp.or, [w, out]⟩]) []
            (n + pre.length + gs.length) 0 x w hw
          simpa [C2] using this
        have hCout : W n C2 x out = W n C1 x out := by
          have h2 : C2 = ⟨(pre ++ gs) ++ [⟨GateOp.or, [w, out]⟩], n + pre.length + gs.length⟩ := by
            simp [C2, List.append_assoc]
          have h1 : C1 = ⟨(pre ++ gs) ++ [], out⟩ := by simp [C1]
          rw [h2, h1]
          exact prefix_W n (pre ++ gs) [⟨GateOp.or, [w, out]⟩] []
            (n + pre.length + gs.length) out x out (by simp; omega)
        have hadd : n + pre.length + gs.length = n + (pre.length + gs.length) := by omega
        rw [hadd, hWlast, hCw, hCout, Bool.or_eq_true, heval']
        simp
lemma star_cover_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (K0 : Finset (Fin n)) (hcov : ∀ e ∈ G.edgeFinset, ∃ v ∈ K0, v ∈ e) :
    C.size + 1 ≤ G.edgeFinset.card + K0.card := by
  classical
  let owner : Sym2 (Fin n) → Fin n := fun e =>
    if h : e ∈ G.edgeFinset then (hcov e h).choose else (hE.choose.out).1
  have howner_mem : ∀ e (he : e ∈ G.edgeFinset), owner e ∈ K0 ∧ owner e ∈ e := by
    intro e he
    simp only [owner, dite_eq_left, he]
    exact (hcov e he).choose_spec
  let L : Fin n → Finset (Fin n) := fun v =>
    Finset.univ.filter fun u => ∃ h : s(v, u) ∈ G.edgeFinset, owner s(v, u) = v
  have hL_adj : ∀ v u, u ∈ L v → G.Adj v u := by
    intro v u hu
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact SimpleGraph.mem_edgeFinset.mp hu.1
  have hL_edge_iff : ∀ u v, G.Adj u v → (v ∈ L u ∨ u ∈ L v) ∧ (u ∈ K0 ∧ v ∈ L u ∨ v ∈ K0 ∧ u ∈ L v) := by
    intro u v huv
    have he : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    obtain ⟨hK, hmem⟩ := howner_mem s(u, v) he
    rcases Sym2.mem_iff.mp hmem with h | h
    · have hu : v ∈ L u := by
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨he, h⟩
      exact ⟨Or.inl hu, Or.inl ⟨h ▸ hK, hu⟩⟩
    · have hv : u ∈ L v := by
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        have he' : s(v, u) ∈ G.edgeFinset := by rw [Sym2.eq_swap]; exact he
        exact ⟨he', by rw [Sym2.eq_swap]; exact h⟩
      exact ⟨Or.inr hv, Or.inr ⟨h ▸ hK, hv⟩⟩
  have hsum : (∑ v ∈ K0, (L v).card) = G.edgeFinset.card := by
    have hbij : (K0.sigma L).card = G.edgeFinset.card := by
      refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_sigma] at hp
        exact SimpleGraph.mem_edgeFinset.mpr (hL_adj p.1 p.2 hp.2)
      · intro p1 hp1 p2 hp2 heq
        simp only [Finset.mem_sigma, L, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
        have h1 : p1.1 = p2.1 := by
          rw [← hp1.2.2, heq, hp2.2.2]
        have h2 : p1.2 = p2.2 := by
          have : s(p1.1, p1.2) = s(p1.1, p2.2) := by rw [← h1] at heq; exact heq
          rcases Sym2.eq_iff.mp this with ⟨_, hb⟩ | ⟨_, hb⟩
          · exact hb
          · have hadj : G.Adj p1.1 p1.2 := SimpleGraph.mem_edgeFinset.mp hp1.2.1
            rw [hb] at hadj
            exact (G.irrefl hadj).elim
        exact Sigma.ext h1 (heq_of_eq h2)
      · intro e he
        induction e using Sym2.ind with
        | _ u v =>
          have huv := SimpleGraph.mem_edgeFinset.mp he
          rcases (hL_edge_iff u v huv).2 with ⟨huK, hvL⟩ | ⟨hvK, huL⟩
          · exact ⟨⟨u, v⟩, Finset.mem_sigma.mpr ⟨huK, hvL⟩, rfl⟩
          · exact ⟨⟨v, u⟩, Finset.mem_sigma.mpr ⟨hvK, huL⟩, Sym2.eq_swap⟩
    rw [Finset.card_sigma] at hbij
    exact hbij
  let M := K0.filter fun v => (L v).Nonempty
  have hM_sub : M ⊆ K0 := Finset.filter_subset _ _
  have hM_ne : M.Nonempty := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ u v =>
      rcases (hL_edge_iff u v (SimpleGraph.mem_edgeFinset.mp he)).2 with ⟨huK, hvL⟩ | ⟨hvK, huL⟩
      · exact ⟨u, Finset.mem_filter.mpr ⟨huK, ⟨v, hvL⟩⟩⟩
      · exact ⟨v, Finset.mem_filter.mpr ⟨hvK, ⟨u, huL⟩⟩⟩
  have hsumM : (∑ v ∈ M, (L v).card) = G.edgeFinset.card := by
    rw [← hsum]
    refine Finset.sum_subset hM_sub ?_
    intro v hv hnotM
    simp only [M, Finset.mem_filter, not_and, Finset.not_nonempty_iff_eq_empty] at hnotM
    rw [hnotM hv, Finset.card_empty]
  let buildStars : List (Fin n) → List Gate × List ℕ :=
    List.foldl (fun (acc : List Gate × List ℕ) (v : Fin n) =>
      let ws := (L v).toList.map Fin.val
      let (gs, out) := orTreeGates (n + acc.1.length) ws
      let andGate : Gate := ⟨GateOp.and, [v.val, out]⟩
      let andWire := n + acc.1.length + gs.length
      (acc.1 ++ gs ++ [andGate], acc.2 ++ [andWire])) ([], [])
  have hbuild_aux : ∀ (vs : List (Fin n)), (∀ v ∈ vs, (L v).Nonempty) →
      let res := buildStars vs
      res.1.length = (vs.map fun v => (L v).card).sum ∧
      res.2.length = vs.length ∧
      (∀ w ∈ res.2, w < n + res.1.length) ∧
      AO n ⟨res.1, 0⟩ ∧
      (∀ x : Fin n → Bool, ∀ w ∈ res.2, W n ⟨res.1, 0⟩ x w = true →
        ∃ v ∈ vs, x v = true ∧ ∃ u ∈ L v, x u = true) ∧
      (∀ x : Fin n → Bool, ∀ v ∈ vs, x v = true → (∃ u ∈ L v, x u = true) →
        ∃ w ∈ res.2, W n ⟨res.1, 0⟩ x w = true) := by
    intro vs
    induction vs using List.reverseRecOn with
    | nil =>
      intro _
      simp [buildStars, AO]
    | append_singleton vs v ih =>
      intro hne
      have hne_vs : ∀ u ∈ vs, (L u).Nonempty := fun u hu => hne u (by simp [hu])
      have hne_v : (L v).Nonempty := hne v (by simp)
      obtain ⟨hlen, hlen2, hlt, hAO, hsound, hcomp⟩ := ih hne_vs
      set acc := buildStars vs
      set ws := (L v).toList.map Fin.val
      have hws_ne : ws ≠ [] := by
        simp only [ws, ne_eq, List.map_eq_nil_iff, Finset.toList_eq_nil]
        exact Finset.nonempty_iff_ne_empty.mp hne_v
      have hws_lt : ∀ w ∈ ws, w < n + acc.1.length := by
        intro w hw
        simp only [ws, List.mem_map] at hw
        obtain ⟨u, _, rfl⟩ := hw
        have := u.isLt; omega
      set ot := orTreeGates (n + acc.1.length) ws
      have hot_len : ot.1.length + 1 = (L v).card := by
        have := orTreeGates_length (n + acc.1.length) ws hws_ne
        simpa [ot, ws] using this
      have hot_out_lt : ot.2 < n + acc.1.length + ot.1.length :=
        orTreeGates_out_lt (n + acc.1.length) ws hws_ne hws_lt
      let andGate : Gate := ⟨GateOp.and, [v.val, ot.2]⟩
      let andWire := n + acc.1.length + ot.1.length
      let newGs := acc.1 ++ ot.1 ++ [andGate]
      have hbuild_eq : buildStars (vs ++ [v]) = (newGs, acc.2 ++ [andWire]) := by
        simp [buildStars, List.foldl_append, acc, newGs, ot, ws, andGate, andWire]
      rw [hbuild_eq]
      have hnewLen : newGs.length = acc.1.length + (L v).card := by
        simp only [newGs, List.length_append, List.length_singleton]
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hnewLen, hlen]
      · simp [hlen2]
      · intro w hw
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · have h1 := hlt w hw
          have h2 : newGs.length = acc.1.length + (L v).card := hnewLen
          change w < n + newGs.length
          omega
        · simp only [andWire, newGs, List.length_append, List.length_singleton]; omega
      · intro k hk
        have hAO_ot := (orTreeGates_eval n acc.1 ws hws_ne hws_lt (fun _ => false)).1
        by_cases hk1 : k < acc.1.length
        · have hg : gateAt ⟨newGs, 0⟩ k = gateAt ⟨acc.1, 0⟩ k := by
            rw [gateAt_eq ⟨newGs, 0⟩ k hk, gateAt_eq ⟨acc.1, 0⟩ k hk1]
            simp only [newGs, List.append_assoc]
            exact List.getElem_append_left hk1
          rw [hg]; exact hAO k hk1
        · by_cases hk2 : k < acc.1.length + ot.1.length
          · have hidx : k - acc.1.length < ot.1.length := by omega
            have hg : gateAt ⟨newGs, 0⟩ k = ot.1[k - acc.1.length]'hidx := by
              rw [gateAt_eq ⟨newGs, 0⟩ k hk]
              simp only [newGs]
              rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
            rw [hg]
            obtain ⟨hop, a, b, hin, ha, hb⟩ := hAO_ot (k - acc.1.length) hidx
            exact ⟨Or.inr hop, a, b, hin, by omega, by omega⟩
          · have hkeq : k = acc.1.length + ot.1.length := by
              simp only [newGs, List.length_append, List.length_singleton] at hk; omega
            subst hkeq
            have hg : gateAt ⟨newGs, 0⟩ (acc.1.length + ot.1.length) = andGate := by
              rw [gateAt_eq ⟨newGs, 0⟩ _ hk]
              simp [newGs]
            rw [hg]
            exact ⟨Or.inl rfl, v.val, ot.2, rfl, by have := v.isLt; omega, by omega⟩
      · intro x w hw hW
        have hpre_eq : ∀ u, u < n + acc.1.length → W n ⟨newGs, 0⟩ x u = W n ⟨acc.1, 0⟩ x u := by
          intro u hu
          have := prefix_W n acc.1 (ot.1 ++ [andGate]) [] 0 0 x u hu
          simpa [newGs, List.append_assoc] using this
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · rw [hpre_eq w (hlt w hw)] at hW
          obtain ⟨u0, hu0, hxu0, z, hzL, hxz⟩ := hsound x w hw hW
          exact ⟨u0, by simp [hu0], hxu0, z, hzL, hxz⟩
        · have hk : acc.1.length + ot.1.length < newGs.length := by
            simp [newGs]
          have hg : gateAt ⟨newGs, 0⟩ (acc.1.length + ot.1.length) = andGate := by
            rw [gateAt_eq ⟨newGs, 0⟩ _ hk]; simp [newGs]
          have hadd : andWire = n + (acc.1.length + ot.1.length) := by simp [andWire]; omega
          rw [hadd, W_and n ⟨newGs, 0⟩ x _ hk (by rw [hg]) v.val ot.2 (by rw [hg])
            (by have := v.isLt; omega) (by omega), Bool.and_eq_true] at hW
          rw [W_input n ⟨newGs, 0⟩ x v.val v.isLt] at hW
          have hot_eq : W n ⟨newGs, 0⟩ x ot.2 = W n ⟨acc.1 ++ ot.1, ot.2⟩ x ot.2 := by
            have := prefix_W n (acc.1 ++ ot.1) [andGate] [] 0 ot.2 x ot.2
              (by simp; omega)
            simpa [newGs] using this
          rw [hot_eq, (orTreeGates_eval n acc.1 ws hws_ne hws_lt x).2] at hW
          obtain ⟨uval, huval, hWu⟩ := hW.2
          simp only [ws, List.mem_map, Finset.mem_toList] at huval
          obtain ⟨u, huL, rfl⟩ := huval
          rw [W_input n ⟨acc.1, 0⟩ x u.val u.isLt] at hWu
          exact ⟨v, by simp, hW.1, u, huL, hWu⟩
      · intro x v0 hv0 hxv0 ⟨u, huL, hxu⟩
        have hpre_eq : ∀ u', u' < n + acc.1.length → W n ⟨newGs, 0⟩ x u' = W n ⟨acc.1, 0⟩ x u' := by
          intro u' hu'
          have := prefix_W n acc.1 (ot.1 ++ [andGate]) [] 0 0 x u' hu'
          simpa [newGs, List.append_assoc] using this
        simp only [List.mem_append, List.mem_singleton] at hv0
        rcases hv0 with hv0 | rfl
        · obtain ⟨w, hw, hW⟩ := hcomp x v0 hv0 hxv0 ⟨u, huL, hxu⟩
          exact ⟨w, by simp [hw], by rw [hpre_eq w (hlt w hw)]; exact hW⟩
        · refine ⟨andWire, by simp, ?_⟩
          have hk : acc.1.length + ot.1.length < newGs.length := by simp [newGs]
          have hg : gateAt ⟨newGs, 0⟩ (acc.1.length + ot.1.length) = andGate := by
            rw [gateAt_eq ⟨newGs, 0⟩ _ hk]; simp [newGs]
          have hadd : andWire = n + (acc.1.length + ot.1.length) := by simp [andWire]; omega
          rw [hadd, W_and n ⟨newGs, 0⟩ x _ hk (by rw [hg]) v0.val ot.2 (by rw [hg])
            (by have := v0.isLt; omega) (by omega), Bool.and_eq_true,
            W_input n ⟨newGs, 0⟩ x v0.val v0.isLt]
          refine ⟨hxv0, ?_⟩
          have hot_eq : W n ⟨newGs, 0⟩ x ot.2 = W n ⟨acc.1 ++ ot.1, ot.2⟩ x ot.2 := by
            have := prefix_W n (acc.1 ++ ot.1) [andGate] [] 0 ot.2 x ot.2
              (by simp; omega)
            simpa [newGs] using this
          rw [hot_eq, (orTreeGates_eval n acc.1 ws hws_ne hws_lt x).2]
          refine ⟨u.val, List.mem_map.mpr ⟨u, Finset.mem_toList.mpr huL, rfl⟩, ?_⟩
          rw [W_input n ⟨acc.1, 0⟩ x u.val u.isLt]
          exact hxu
  let vs := M.toList
  have hvs_ne : ∀ v ∈ vs, (L v).Nonempty := by
    intro v hv
    simp only [vs, Finset.mem_toList, M, Finset.mem_filter] at hv
    exact hv.2
  obtain ⟨hlen1, hlen2, hlt, hAO1, hsound1, hcomp1⟩ := hbuild_aux vs hvs_ne
  set bs := buildStars vs
  have hbs2_ne : bs.2 ≠ [] := by
    intro h
    have h1 : vs.length = 0 := by rw [← hlen2, h]; rfl
    have : M = ∅ := by
      rw [← Finset.card_eq_zero, ← Finset.length_toList, h1]
    exact Finset.nonempty_iff_ne_empty.mp hM_ne this
  set top := orTreeGates (n + bs.1.length) bs.2
  let D : Circuit := ⟨bs.1 ++ top.1, top.2⟩
  have hD_AO : AO n D := by
    intro k hk
    have hAO_top := (orTreeGates_eval n bs.1 bs.2 hbs2_ne hlt (fun _ => false)).1
    by_cases hk1 : k < bs.1.length
    · have hg : gateAt D k = gateAt ⟨bs.1, 0⟩ k := by
        rw [gateAt_eq D k hk, gateAt_eq ⟨bs.1, 0⟩ k hk1]
        exact List.getElem_append_left hk1
      rw [hg]; exact hAO1 k hk1
    · have hidx : k - bs.1.length < top.1.length := by simp [D] at hk; omega
      have hg : gateAt D k = top.1[k - bs.1.length]'hidx := by
        rw [gateAt_eq D k hk]
        exact List.getElem_append_right (by omega)
      rw [hg]
      obtain ⟨hop, a, b, hin, ha, hb⟩ := hAO_top (k - bs.1.length) hidx
      exact ⟨Or.inr hop, a, b, hin, by omega, by omega⟩
  have hD_fun : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [Bool.eq_iff_iff]
    have hDeval : circuitFun n D x = W n D x top.2 := rfl
    rw [hDeval, (orTreeGates_eval n bs.1 bs.2 hbs2_ne hlt x).2]
    constructor
    · rintro ⟨w, hw, hW⟩
      obtain ⟨v, hv, hxv, u, huL, hxu⟩ := hsound1 x w hw hW
      have hadj : G.Adj v u := hL_adj v u huL
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨v, u, hadj, hxv, hxu⟩
    · intro hG
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] at hG
      obtain ⟨u, v, hadj, hxu, hxv⟩ := hG
      rcases (hL_edge_iff u v hadj).2 with ⟨huK, hvL⟩ | ⟨hvK, huL⟩
      · have huM : u ∈ vs := by
          simp only [vs, Finset.mem_toList, M, Finset.mem_filter]
          exact ⟨huK, ⟨v, hvL⟩⟩
        exact hcomp1 x u huM hxu ⟨v, hvL, hxv⟩
      · have hvM : v ∈ vs := by
          simp only [vs, Finset.mem_toList, M, Finset.mem_filter]
          exact ⟨hvK, ⟨u, huL⟩⟩
        exact hcomp1 x v hvM hxv ⟨u, huL, hxu⟩
  have hD_size : D.size + 1 = G.edgeFinset.card + M.card := by
    have htop_len : top.1.length + 1 = bs.2.length :=
      orTreeGates_length (n + bs.1.length) bs.2 hbs2_ne
    have hsum_vs : (vs.map fun v => (L v).card).sum = G.edgeFinset.card := by
      rw [← hsumM]
      simp [vs]
    have hvs_len : vs.length = M.card := Finset.length_toList M
    have h1 : bs.1.length = G.edgeFinset.card := by rw [hlen1, hsum_vs]
    have h2 : bs.2.length = M.card := by rw [hlen2, hvs_len]
    simp only [Circuit.size, D, List.length_append]
    omega
  have hle := hL.2.2 D (IsAO2_of_AO n D hD_AO) hD_fun
  have hM_le : M.card ≤ K0.card := Finset.card_le_card hM_sub
  omega
end Star
lemma finite_min_cover_exists
    (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ K : Finset (Fin n), IsMinCover G K := by
  classical
  let P : ℕ → Prop := fun k => ∃ K : Finset (Fin n),
    G.IsVertexCover (K : Set (Fin n)) ∧ K.card = k
  have hex : ∃ k, P k := by
    refine ⟨n, Finset.univ, ?_, by simp⟩
    simp
  obtain ⟨K, hK, hcard⟩ := Nat.find_spec hex
  refine ⟨K, hK, ?_⟩
  intro K' hK'
  rw [hcard]
  exact Nat.find_min' hex ⟨K', hK', rfl⟩
lemma complete_deleted_edge_cover
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U : Finset (Sym2 (Fin n))) (K : Finset (Fin n))
    (hK : (G.deleteEdges (U : Set (Sym2 (Fin n)))).IsVertexCover
      (K : Set (Fin n))) :
    ∃ K' : Finset (Fin n),
      (∀ e ∈ G.edgeFinset, ∃ v ∈ K', v ∈ e) ∧
      K'.card ≤ K.card + U.card := by
  classical
  let X := U.image fun e => e.out.1
  refine ⟨K ∪ X, ?_, ?_⟩
  · intro e he
    by_cases heU : e ∈ U
    · exact ⟨e.out.1, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e, heU, rfl⟩), Sym2.out_fst_mem e⟩
    · induction e using Sym2.ind with
      | h u v =>
        have hadj : (G.deleteEdges (U : Set (Sym2 (Fin n)))).Adj u v :=
          SimpleGraph.deleteEdges_adj.mpr ⟨SimpleGraph.mem_edgeFinset.mp he, heU⟩
        rcases hK hadj with hu | hv
        · exact ⟨u, Finset.mem_union_left _ hu, by simp⟩
        · exact ⟨v, Finset.mem_union_left _ hv, by simp⟩
  · have hX : X.card ≤ U.card := Finset.card_image_le
    have hUnion := Finset.card_union_le K X
    omega
lemma bipartite_two_junk_penalty_four
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hfour : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hleast : IsLeastAO G C) (htop : TopForm G C)
    (hjunk : 2 ≤ (junk G C).card) :
    4 ≤ 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card := by
  classical
  by_contra hfourP
  have hbudget : 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card ≤ 3 := by omega
  have hu := budget_three_ustar_card_le_one n G C color hbip hfour hleast htop hjunk hbudget
  obtain ⟨hledger, hresidual⟩ := Ledger.main n G C hfour hE hleast htop
  obtain ⟨K, hK⟩ := finite_min_cover_exists n (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n))))
  have hKsize := hresidual K hK
  obtain ⟨K', hfull, hcompletion⟩ := complete_deleted_edge_cover n G (Ustar G C) K hK.1
  have hupper := Star.star_cover_bound G C hE hleast K' hfull
  have hPle : 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card ≤ 2 * (Ustar G C).card := by omega
  by_cases hUne : (Ustar G C).Nonempty
  · have hpair : ∃ u v : Fin n, s(u, v) ∈ Ustar G C := by
      obtain ⟨e, he⟩ := hUne
      induction e using Sym2.ind with
      | h u v => exact ⟨u, v, he⟩
    have hthree := (Budget.finish hleast htop hjunk hbudget hpair).1
    omega
  · have hzero : (Ustar G C).card = 0 := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hUne]
    omega
lemma incidence_moment_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (I : α → β → Prop) [DecidableRel I]
    (q : ℕ) (hrow : ∀ p ∈ S, (T.filter (I p)).card = q + 1) :
    ∑ l ∈ T, (S.filter (fun p => I p l)).card = S.card * (q + 1) := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ p ∈ S, ∑ l ∈ T, (if I p l then 1 else 0)) = ∑ p ∈ S, (q + 1) := by
      apply Finset.sum_congr rfl
      intro p hp
      simpa only [Finset.card_filter] using hrow p hp
    _ = _ := by simp
lemma incidence_moment_two {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (I : α → β → Prop) [DecidableRel I]
    (q : ℕ) (hrow : ∀ p ∈ S, (T.filter (I p)).card = q + 1)
    (hpair : ∀ p ∈ S, ∀ r ∈ S, p ≠ r →
      (T.filter (fun l => I p l ∧ I r l)).card = 1) :
    ∑ l ∈ T, (S.filter (fun p => I p l)).card ^ 2 = S.card * (q + S.card) := by
  classical
  have h_expand : ∀ l ∈ T, (S.filter (fun p => I p l)).card ^ 2 =
      ∑ p ∈ S, ∑ r ∈ S, if I p l ∧ I r l then 1 else 0 := by
    intro l hl
    rw [pow_two]
    simp only [Finset.card_filter, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hp' : I p l <;> by_cases hr' : I r l <;> simp [hp', hr']
  simp_rw [Finset.sum_congr rfl h_expand]
  rw [Finset.sum_comm]
  have h_each : ∀ p ∈ S,
      ∑ l ∈ T, ∑ r ∈ S, (if I p l ∧ I r l then 1 else 0) = q + S.card := by
    intro p hp
    rw [Finset.sum_comm]
    have h_inside : ∀ r ∈ S,
        ∑ l ∈ T, (if I p l ∧ I r l then 1 else 0) = if r = p then q + 1 else 1 := by
      intro r hr
      by_cases h : r = p
      · subst r
        simpa only [Finset.card_filter, and_self, ite_true] using hrow p hp
      · simpa only [Finset.card_filter, ite_eq_right h] using hpair p hp r hr (Ne.symm h)
    rw [Finset.sum_congr rfl h_inside]
    rw [← Finset.sum_erase_add _ _ hp]
    have he : ∑ r ∈ S.erase p, (if r = p then q + 1 else 1) = (S.erase p).card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro r hr
      have hne := (Finset.mem_erase.mp hr).1
      simp [hne]
    rw [he]
    simp only [ite_true]
    have hcard := Finset.card_erase_add_one hp
    omega
  rw [Finset.sum_congr rfl h_each]
  simp
lemma contained_lines_pair_bound (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (S B : Finset (Fin N))
    (hrow : ∀ p : Fin N, (Finset.univ.filter (I p)).card = q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (hcontained : ∀ l ∈ B, ∀ p, I p l → p ∈ S) :
    B.card * (q + 1) * q ≤ S.card * (S.card - 1) := by
  classical
  let c : Fin N → ℕ := fun l => (S.filter (fun p => I p l)).card
  have hrowS : ∀ p ∈ S, (Finset.univ.filter (I p)).card = q + 1 :=
    fun p _ => hrow p
  have hpairS : ∀ p ∈ S, ∀ r ∈ S, p ≠ r →
      (Finset.univ.filter (fun l => I p l ∧ I r l)).card = 1 := by
    intro p hp r hr hpr
    obtain ⟨l, hl, hu⟩ := hpair p r hpr
    apply Finset.card_eq_one.mpr
    refine ⟨l, ?_⟩
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hk => hu k hk, fun hk => hk ▸ hl⟩
  have hm1 := incidence_moment_one S Finset.univ I q hrowS
  have hm2 := incidence_moment_two S Finset.univ I q hrowS hpairS
  have hc : ∀ l ∈ B, c l = q + 1 := by
    intro l hl
    have heq : S.filter (fun p => I p l) = Finset.univ.filter (fun p => I p l) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun hp => ⟨hcontained l hl p hp, hp⟩⟩
    dsimp [c]
    rw [heq]
    exact hcol l
  have hid : ∀ a : ℕ, a * (a - 1) + a = a ^ 2 := by
    intro a
    by_cases h : a = 0
    · simp [h]
    · have ha : a - 1 + 1 = a := by omega
      nlinarith
  have hsum : (∑ l, c l * (c l - 1)) + S.card * (q + 1) = S.card * (q + S.card) := by
    rw [← hm1, ← hm2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    exact hid (c l)
  have hrestrict : (∑ l ∈ B, c l * (c l - 1)) ≤ ∑ l, c l * (c l - 1) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ B)
  have hB : (∑ l ∈ B, c l * (c l - 1)) = B.card * (q + 1) * q := by
    calc
      _ = ∑ l ∈ B, (q + 1) * q := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hc l hl]
        simp
      _ = _ := by simp [Nat.mul_assoc]
  rw [hB] at hrestrict
  have hs := hid S.card
  nlinarith
lemma small_cut_forces_contained (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (S B : Finset (Fin N))
    (hrow : ∀ p : Fin N, (Finset.univ.filter (I p)).card = q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hsize : S.card = B.card + 1)
    (hcut : (∑ l ∈ Finset.univ \ B, (S.filter (fun p => I p l)).card) ≤ q + 1) :
    ∀ l ∈ B, ∀ p, I p l → p ∈ S := by
  classical
  let c : Fin N → ℕ := fun l => (S.filter (fun p => I p l)).card
  have hcmax : ∀ l, c l ≤ q + 1 := by
    intro l
    rw [← hcol l]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))
  have hm1 : ∑ l, c l = S.card * (q + 1) :=
    incidence_moment_one S Finset.univ I q (fun p _ => hrow p)
  have hpartition := Finset.sum_sdiff (f := c) (Finset.subset_univ B)
  intro l hl p hpl
  have hcard : c l = q + 1 := by
    have hsummax : (∑ k ∈ B.erase l, c k) ≤ (B.erase l).card * (q + 1) := by
      calc
        _ ≤ ∑ k ∈ B.erase l, (q + 1) := Finset.sum_le_sum (fun k _ => hcmax k)
        _ = _ := by simp
    have herase := Finset.sum_erase_add B c hl
    have herasecard := Finset.card_erase_add_one hl
    have hcut' : (∑ l ∈ Finset.univ \ B, c l) ≤ q + 1 := hcut
    have hmax := hcmax l
    nlinarith
  have heq : S.filter (fun p => I p l) = Finset.univ.filter (fun p => I p l) := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.filter_subset_filter _ (Finset.subset_univ S)
    · change (Finset.univ.filter (fun p => I p l)).card ≤ c l
      rw [hcol l, hcard]
  have hp : p ∈ S.filter (fun p => I p l) := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩
  exact (Finset.mem_filter.mp hp).1
lemma small_cut_rigidity (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (S B : Finset (Fin N)) (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hrow : ∀ p : Fin N, (Finset.univ.filter (I p)).card = q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (hsize : S.card = B.card + 1)
    (hcut : (∑ l ∈ Finset.univ \ B, (S.filter (fun p => I p l)).card) ≤ q + 1) :
    S.card = 1 ∨ S = Finset.univ := by
  classical
  by_cases hs : S.card = 1
  · exact Or.inl hs
  by_cases hS : S = Finset.univ
  · exact Or.inr hS
  have hcontained := small_cut_forces_contained q N I S B hrow hcol hsize hcut
  have hbound := contained_lines_pair_bound q N I S B hrow hcol hpair hcontained
  have hb : 0 < B.card := by omega
  have hsub : S.card - 1 = B.card := by omega
  rw [hsub] at hbound
  have hslarge : (q + 1) * q ≤ S.card := by
    by_contra h
    have hlt := Nat.mul_lt_mul_of_pos_right (by omega : S.card < (q + 1) * q) hb
    nlinarith
  obtain ⟨p, hp⟩ : ∃ p : Fin N, p ∉ S := by
    by_contra! h
    exact hS (Finset.eq_univ_iff_forall.mpr h)
  let L := Finset.univ.filter (I p)
  have hBsub : B ⊆ Finset.univ \ L := by
    intro l hl
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hL
    exact hp (hcontained l hl p (Finset.mem_filter.mp hL).2)
  have hBcard := Finset.card_le_card hBsub
  have hLcard : L.card = q + 1 := hrow p
  have hpartition := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ L)
  simp only [Finset.card_univ, Fintype.card_fin] at hpartition
  rw [hLcard] at hpartition
  have hbmax : B.card + (q + 1) ≤ N := by omega
  exfalso
  nlinarith
lemma uncovered_card_eq_sum (N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (A B : Finset (Fin N)) :
    (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card =
      ∑ l ∈ Finset.univ \ B, ((Finset.univ \ A).filter (fun p => I p l)).card := by
  classical
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have hA : Finset.univ \ A = Finset.univ.filter (fun p => p ∉ A) := by
    ext p
    simp
  have hB : Finset.univ \ B = Finset.univ.filter (fun l => l ∉ B) := by
    ext l
    simp
  simp only [hA, hB, Finset.card_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hlB : l ∈ B
  · simp [hlB]
  · simp only [hlB, not_false_eq_true, ite_true]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpA : p ∈ A <;> by_cases hpI : I p l <;> simp [hpA, hpI]
lemma small_uncovered_cover_is_pure (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (A B : Finset (Fin N)) (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hrow : ∀ p : Fin N, (Finset.univ.filter (I p)).card = q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (hsize : A.card + B.card + 1 = N)
    (hmissing : (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card ≤ q + 1) :
    A = ∅ ∨ B = ∅ := by
  classical
  let S := Finset.univ \ A
  have hpart : S.card + A.card = N := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hSB : S.card = B.card + 1 := by omega
  have hcut : (∑ l ∈ Finset.univ \ B, (S.filter (fun p => I p l)).card) ≤ q + 1 := by
    rw [uncovered_card_eq_sum] at hmissing
    exact hmissing
  rcases small_cut_rigidity q N I S B hq hN hrow hcol hpair hSB hcut with hs | hs
  · right
    apply Finset.card_eq_zero.mp
    omega
  · left
    have hScard : S.card = N := by simp [hs]
    exact Finset.card_eq_zero.mp (by omega)
lemma plane_point_degree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (p : Fin N) : (Finset.univ.filter (I p)).card = q + 1 := by
  classical
  let L := Finset.univ.filter (I p)
  have hsum : ∑ l ∈ L, (Finset.univ.filter (fun r => I r l)).card = L.card * (q + 1) := by
    simp_rw [hcol]
    simp
  have hcommon : ∀ r : Fin N, r ≠ p → (L.filter (I r)).card = 1 := by
    intro r hr
    obtain ⟨l, hl, huniq⟩ := hunique p r (Ne.symm hr)
    apply Finset.card_eq_one.mpr
    refine ⟨l, ?_⟩
    ext k
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hk => huniq k hk, fun hk => hk ▸ hl⟩
  have hself : (L.filter (I p)).card = L.card := by
    congr 1
    ext l
    simp [L]
  have hswap : ∑ l ∈ L, (Finset.univ.filter (fun r => I r l)).card =
      ∑ r : Fin N, (L.filter (I r)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hrow : ∑ r : Fin N, (L.filter (I r)).card = N - 1 + L.card := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ p), hself]
    have he : ∑ r ∈ Finset.univ.erase p, (L.filter (I r)).card = N - 1 := by
      calc
        _ = ∑ r ∈ Finset.univ.erase p, 1 := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hcommon r (Finset.mem_erase.mp hr).1
        _ = _ := by simp
    rw [he]
  rw [hswap, hrow] at hsum
  have hNm : N - 1 = q ^ 2 + q := by omega
  rw [hNm] at hsum
  have hcancel : L.card * q = (q + 1) * q := by
    nlinarith
  exact Nat.eq_of_mul_eq_mul_right hq hcancel
lemma finset_missing_one (N : ℕ) (A : Finset (Fin N)) (hsize : A.card + 1 = N) :
    ∃ p : Fin N, A = Finset.univ.erase p := by
  classical
  have hpart := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  simp only [Finset.card_univ, Fintype.card_fin] at hpart
  have hc : (Finset.univ \ A).card = 1 := by omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  refine ⟨p, ?_⟩
  ext x
  have hx : x ∉ A ↔ x = p := by
    have h := Finset.ext_iff.mp hp x
    simpa using h
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto
lemma small_uncovered_cover_is_single_star_complement
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A B : Finset (Fin N)) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (hsize : A.card + B.card + 1 = N)
    (hmissing : (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card ≤ q + 1) :
    (∃ p, A = Finset.univ.erase p ∧ B = ∅) ∨
    (∃ l, A = ∅ ∧ B = Finset.univ.erase l) := by
  have hrow := plane_point_degree q N I (by omega) hN hcol hpair
  rcases small_uncovered_cover_is_pure q N I A B hq hN hrow hcol hpair hsize hmissing with hA | hB
  · right
    have hsz : B.card + 1 = N := by simpa [hA] using hsize
    obtain ⟨l, hl⟩ := finset_missing_one N B hsz
    exact ⟨l, hA, hl⟩
  · left
    have hsz : A.card + 1 = N := by simpa [hB] using hsize
    obtain ⟨p, hp⟩ := finset_missing_one N A hsz
    exact ⟨p, hp, hB⟩
lemma small_uncovered_counterexample_shape (q N t u P size : ℕ)
    (hq : 3 ≤ q) (hP : 4 ≤ P) (hu : u ≤ 4)
    (hdensity : N * (q + 1) ≤ (q + 1) * t + u)
    (hledger : N * (q + 1) + t + P ≤ size + u + 1)
    (hbad : size + 1 < N * (q + 1) + N) :
    q = 3 ∧ u = 4 ∧ P = 4 ∧ t + 1 = N := by
  have hcost : t + P + 1 ≤ N + u := by omega
  have ht : t + 1 ≤ N := by omega
  have hdeficit : 0 < N - t := by omega
  have hN : N = t + (N - t) := by omega
  have hproduct : (N - t) * (q + 1) ≤ u := by nlinarith
  have hqbound : q + 1 ≤ u := by
    have hmul := Nat.mul_le_mul_right (q + 1) hdeficit
    nlinarith
  have hqeq : q = 3 := by omega
  have hueq : u = 4 := by omega
  rw [hqeq, hueq] at hproduct
  have htight : N - t = 1 := by omega
  omega
lemma full_star_clean_pencil_card_le_one
    {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (U : Finset (Sym2 V)) (p t : V)
    (hstar : ∀ u v, s(u, v) ∈ U ↔ G.Adj u v ∧ (u = p ∨ v = p))
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m)
    (hpencil : ∀ u v, s(u, v) ∈ U →
      ∃ w, (w = u ∨ w = v) ∧ G.Adj t w ∧ s(t, w) ∉ U) :
    U.card ≤ 1 := by
  have orient : ∀ e ∈ U, ∃ w,
      e = s(p, w) ∧ G.Adj p w ∧ G.Adj t w ∧ s(t, w) ∉ U := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨w, hend, htw, hclean⟩ := hpencil u v he
      have hwp : w ≠ p := by
        intro h
        apply hclean
        exact (hstar t w).mpr ⟨htw, Or.inr h⟩
      have hrepr : s(u, v) = s(p, w) := by
        rcases (hstar u v).mp he with ⟨_, hp | hp⟩
        · rcases hend with hw | hw
          · exact (hwp (hw.trans hp)).elim
          · rw [hp, ← hw]
        · rcases hend with hw | hw
          · rw [hp, ← hw]
            exact Sym2.eq_swap
          · exact (hwp (hw.trans hp)).elim
      have hpw : G.Adj p w := ((hstar p w).mp (hrepr ▸ he)).1
      exact ⟨w, hrepr, hpw, htw, hclean⟩
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨w0, rfl, hp0, ht0, hc0⟩ := orient e he
  obtain ⟨w1, rfl, hp1, ht1, _⟩ := orient f hf
  have hpt : p ≠ t := by
    intro h
    exact hc0 (h ▸ he)
  have hw : w0 = w1 := hfour p t hpt w0 w1 hp0 ht0 hp1 ht1
  exact congrArg (fun w => s(p, w)) hw
namespace ZeroExtra
open Budget
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma coneLt {i j : ℕ} (h : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨_, k, hkj, _, hik⟩ := (inCone_iff n C i j).mp h
    rcases hik with rfl | hik
    · exact hkj
    · exact (ih k hkj hik).trans hkj
lemma coneTrans {i j k : ℕ} (hij : InCone n C i j) (hjk : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨hk,l,hl,hm,hjl⟩ := (inCone_iff n C j k).mp hjk
    apply (inCone_iff n C i k).mpr
    refine ⟨hk,l,hl,hm,Or.inr ?_⟩
    rcases hjl with rfl | hjl
    · exact hij
    · exact ih l hl hjl
lemma lowerAndJunk (ht : TopForm G C) {i j : ℕ}
    (hj : (gateAt C j).op = GateOp.and) (hi : (gateAt C i).op = GateOp.and)
    (hcone : InCone n C i j) : i ∈ junk G C := by
  classical
  have hj' := ((inCone_iff n C i j).mp hcone).1
  have hi' := (coneLt hcone).trans hj'
  have hnb : ¬ BelowF G C i := fun h => ht i hi' j hj' hi h hj hcone
  have hex : ∃ x : Fin n → Bool, gateVal n C i x = true ∧ graphFun G ∅ x = false := by
    by_contra h
    exact hnb (fun x hx => Bool.eq_true_of_not_eq_false fun hf => h ⟨x,hx,hf⟩)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi', hi, hi', hex⟩
lemma or_below_top_raw (hAO : IsAO2 n C) (hT : TopForm G C)
    (hzero : orN G C \ lam G C = ∅) {a m : ℕ}
    (ha : (gateAt C a).op = GateOp.and) (_hm : m < C.gates.length)
    (hmo : (gateAt C m).op = GateOp.or) (hc : InCone n C m a)
    {p v : Fin n} (hv : gateVal n C m (pairInput p v) = true)
    (hp : gateVal n C m (pairInput p p) = false) :
    v ∈ orIn n C (n + m) := by
  rcases operand_trace p v (n + m) hv with ⟨w, hw, hr⟩ | ⟨j, hj, hjo, hr, _⟩
  · rcases hw with hw | hw
    · subst w
      have h := reach_var_val (pairInput p p) (n + m) p hr (pairInput_left p p)
      exact (Bool.false_ne_true (hp.symm.trans h)).elim
    · subst w
      exact reach_mem_orIn v hr
  · have hjop : (gateAt C j).op = GateOp.and :=
      (hAO.1 _ (gateAt_mem hj)).resolve_right hjo
    have hjm : InCone n C j m := by
      rcases orStep_cone hr m j rfl rfl with he | hc'
      · subst j
        rw [hmo] at hjop
        contradiction
      · exact hc'
    have hjunk : j ∈ junk G C := lowerAndJunk hT ha hjop (coneTrans hjm hc)
    rcases lastOrBefore hr with he | ⟨l, hl, hlo, hli, hlb, _⟩
    · have : m = j := by omega
      subst j
      exact (hjo hmo).elim
    · have hmem := lastOrOutside hAO hjunk hl hlo hli hlb
      simp [hzero] at hmem
lemma find_or_separating (hAO : IsAO2 n C)
    {p v w : Fin n} (hvw : v ≠ w) {a : ℕ}
    (ha : a < C.gates.length) (hao : (gateAt C a).op = GateOp.and)
    (hv : gateVal n C a (pairInput p v) = true)
    (hw : gateVal n C a (pairInput p w) = true)
    (hp : gateVal n C a (pairInput p p) = false) :
    ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ InCone n C m a ∧
      gateVal n C m (pairInput p v) = true ∧
      gateVal n C m (pairInput p w) = true ∧
      gateVal n C m (pairInput p p) = false := by
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    have hfalse : ∃ i ∈ (gateAt C a).inputs,
        val C (List.ofFn (pairInput p p)) i = false := by
      by_contra hn
      have ht : gateVal n C a (pairInput p p) = true :=
        (val_and (n := n) (by simp) ha hao).mpr fun i hi =>
          ⟨hAO.2.1 a ha i hi, Bool.eq_true_of_not_eq_false (fun hf => hn ⟨i, hi, hf⟩)⟩
      exact Bool.false_ne_true (hp.symm.trans ht)
    obtain ⟨i, hi, hip⟩ := hfalse
    have hiBound := hAO.2.1 a ha i hi
    have hiv := ((val_and (n := n) (by simp) ha hao).mp hv i hi).2
    have hiw := ((val_and (n := n) (by simp) ha hao).mp hw i hi).2
    by_cases hin : i < n
    · let z : Fin n := ⟨i, hin⟩
      have hzv : z = p ∨ z = v := (pairInput_true p v z).mp
        ((val_ofFn C (pairInput p v) z).symm.trans hiv)
      have hzw : z = p ∨ z = w := (pairInput_true p w z).mp
        ((val_ofFn C (pairInput p w) z).symm.trans hiw)
      have hzp : z ≠ p := by
        intro h
        have ht := (val_ofFn C (pairInput p p) z).trans
          (by simpa [h] using pairInput_left p p)
        exact Bool.false_ne_true (hip.symm.trans ht)
      exact (hvw ((hzv.resolve_left hzp).symm.trans (hzw.resolve_left hzp))).elim
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hja : j < a := by omega
      have hj : j < C.gates.length := hja.trans ha
      have hjc : InCone n C j a :=
        (inCone_iff n C j a).mpr ⟨ha, j, hja, hi, Or.inl rfl⟩
      rcases hAO.1 _ (gateAt_mem hj) with hjo | hjo
      · obtain ⟨m, hm, hmo, hmc, hmv, hmw, hmp⟩ := ih j hja hj hjo hiv hiw hip
        exact ⟨m, hm, hmo, coneTrans hmc hjc, hmv, hmw, hmp⟩
      · exact ⟨j, hj, hjo, hjc, hiv, hiw, hip⟩
lemma lambda_clean_pencil (hAO : IsAO2 n C) {m : ℕ} (hm : m ∈ lam G C) :
    ∃ t : Fin n, ∀ v ∈ orIn n C (n + m),
      (G.deleteEdges ↑(Ustar G C)).Adj t v := by
  obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hm
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hone
  refine ⟨t, ?_⟩
  intro v hv
  have htv : t ∈ side C a (1 - b) := by simp [ht]
  have hv' : v ∈ side C a b :=
    reach_mem_orIn v ((orReaches_reach m _ hr).1.trans (mem_orIn_reach v hv))
  exact (cleanAdj hAO ha b hv' htv).symm
lemma zero_or_residual_centreless (hleast : IsLeastAO G C) (hT : TopForm G C)
    (hzero : orN G C \ lam G C = ∅) {u v : Fin n}
    (he : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ centreless G C, gateVal n C a (pairInput u v) = true := by
  obtain ⟨a, ha, b, j, hj, hv, hr, _⟩ := residualTrace hleast hT he
  rcases lastOrBefore (orReaches_reach j _ hr).1 with heq | ⟨m, hm, hmo, hmi, hmb, _⟩
  · have hside : side (n := n) C a b = ∅ := by
      change orIn n C (opnd C a b) = ∅
      rw [heq, andRawEmpty (junkData hj).2.1]
    refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩, hv⟩
    fin_cases b
    · exact Or.inl hside
    · exact Or.inr hside
  · have hm' := lastOrOutside hleast.1 hj hm hmo hmi hmb
    simp [hzero] at hm'
end ZeroExtra
lemma penalty_le_twice_uncovered
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfour : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hleast : IsLeastAO G C) (htop : TopForm G C) :
    2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card ≤ 2 * (Ustar G C).card := by
  classical
  obtain ⟨hledger, hresidual⟩ := Ledger.main n G C hfour hE hleast htop
  obtain ⟨K, hK⟩ := finite_min_cover_exists n (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n))))
  have hKsize := hresidual K hK
  obtain ⟨K', hfull, hcompletion⟩ := complete_deleted_edge_cover n G (Ustar G C) K hK.1
  have hupper := Star.star_cover_bound G C hE hleast K' hfull
  omega
namespace ZeroExtraGlobal
open Budget ZeroExtra
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma find_or_separating_inputs (hAO : IsAO2 n C)
    {x y z : Fin n → Bool} (hinter : ∀ v, x v = true → y v = true → z v = true) {a : ℕ}
    (ha : a < C.gates.length) (hao : (gateAt C a).op = GateOp.and)
    (hv : gateVal n C a x = true)
    (hw : gateVal n C a y = true)
    (hp : gateVal n C a z = false) :
    ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ InCone n C m a ∧
      gateVal n C m x = true ∧
      gateVal n C m y = true ∧
      gateVal n C m z = false := by
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    have hfalse : ∃ i ∈ (gateAt C a).inputs,
        val C (List.ofFn z) i = false := by
      by_contra hn
      have ht : gateVal n C a z = true :=
        (val_and (n := n) (by simp) ha hao).mpr fun i hi =>
          ⟨hAO.2.1 a ha i hi, Bool.eq_true_of_not_eq_false (fun hf => hn ⟨i, hi, hf⟩)⟩
      exact Bool.false_ne_true (hp.symm.trans ht)
    obtain ⟨i, hi, hip⟩ := hfalse
    have hiBound := hAO.2.1 a ha i hi
    have hiv := ((val_and (n := n) (by simp) ha hao).mp hv i hi).2
    have hiw := ((val_and (n := n) (by simp) ha hao).mp hw i hi).2
    by_cases hin : i < n
    · let v : Fin n := ⟨i, hin⟩
      have hxv : x v = true := (val_ofFn C x v).symm.trans hiv
      have hyv : y v = true := (val_ofFn C y v).symm.trans hiw
      have hzv := (val_ofFn C z v).trans (hinter v hxv hyv)
      exact (Bool.false_ne_true (hip.symm.trans hzv)).elim
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hja : j < a := by omega
      have hj : j < C.gates.length := hja.trans ha
      have hjc : InCone n C j a :=
        (inCone_iff n C j a).mpr ⟨ha, j, hja, hi, Or.inl rfl⟩
      rcases hAO.1 _ (gateAt_mem hj) with hjo | hjo
      · obtain ⟨m, hm, hmo, hmc, hmv, hmw, hmp⟩ := ih j hja hj hjo hiv hiw hip
        exact ⟨m, hm, hmo, coneTrans hmc hjc, hmv, hmw, hmp⟩
      · exact ⟨j, hj, hjo, hjc, hiv, hiw, hip⟩
lemma or_below_and_raw (hAO : IsAO2 n C) (hT : TopForm G C)
    (hzero : orN G C \ lam G C = ∅) {a m : ℕ}
    (ha : (gateAt C a).op = GateOp.and)
    (hmo : (gateAt C m).op = GateOp.or) (hc : InCone n C m a)
    {p v : Fin n} (hv : gateVal n C m (pairInput p v) = true) :
    ∃ t ∈ orIn n C (n + m), t = p ∨ t = v := by
  rcases operand_trace p v (n + m) hv with ⟨w, hw, hr⟩ | ⟨j, hj, hjo, hr, _⟩
  · exact ⟨w, reach_mem_orIn w hr, hw⟩
  · have hjop : (gateAt C j).op = GateOp.and :=
      (hAO.1 _ (gateAt_mem hj)).resolve_right hjo
    have hjm : InCone n C j m := by
      rcases orStep_cone hr m j rfl rfl with he | hc'
      · subst j
        rw [hmo] at hjop
        contradiction
      · exact hc'
    have hjunk : j ∈ junk G C := lowerAndJunk hT ha hjop (coneTrans hjm hc)
    rcases lastOrBefore hr with he | ⟨l, hl, hlo, hli, hlb, _⟩
    · have : m = j := by omega
      subst j
      exact (hjo hmo).elim
    · have hmem := lastOrOutside hAO hjunk hl hlo hli hlb
      simp [hzero] at hmem
lemma top_accepts_cross (hAO : IsAO2 n C) (hT : TopForm G C)
    (hzero : orN G C \ lam G C = ∅)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    {a : ℕ} (ha : a ∈ tops G C) {u v p q : Fin n}
    (hcolor : color v ≠ color p)
    (hv : gateVal n C a (pairInput u v) = true)
    (hw : gateVal n C a (pairInput p q) = true) :
    gateVal n C a (pairInput u q) = true := by
  by_contra hn
  have hfalse : gateVal n C a (pairInput u q) = false := Bool.eq_false_iff.mpr hn
  have hinter : ∀ t, pairInput u v t = true → pairInput p q t = true →
      pairInput u q t = true := by
    intro t ht ht'
    rcases (pairInput_true u v t).mp ht with htu | htv
    · exact (pairInput_true u q t).mpr (Or.inl htu)
    · rcases (pairInput_true p q t).mp ht' with htp | htq
      · exact (hcolor (congrArg color (htv.symm.trans htp))).elim
      · exact (pairInput_true u q t).mpr (Or.inr htq)
  obtain ⟨hal, hao, _⟩ := topData ha
  obtain ⟨m, hm, hmo, hmc, hmv, hmw, hmf⟩ :=
    find_or_separating_inputs hAO hinter hal hao hv hw hfalse
  obtain ⟨l, hl, hll⟩ := or_below_and_raw hAO hT hzero hao hmo hmc hmv
  have hrawV : v ∈ orIn n C (n + m) := by
    rcases hll with hlu | hlv
    · have ht := reach_var_val (pairInput u q) (n + m) l (mem_orIn_reach l hl)
        ((pairInput_true u q l).mpr (Or.inl hlu))
      exact (Bool.false_ne_true (hmf.symm.trans ht)).elim
    · simpa only [hlv] using hl
  obtain ⟨l, hl, hll⟩ := or_below_and_raw hAO hT hzero hao hmo hmc hmw
  have hrawP : p ∈ orIn n C (n + m) := by
    rcases hll with hlp | hlq
    · simpa only [hlp] using hl
    · have ht := reach_var_val (pairInput u q) (n + m) l (mem_orIn_reach l hl)
        ((pairInput_true u q l).mpr (Or.inr hlq))
      exact (Bool.false_ne_true (hmf.symm.trans ht)).elim
  have hmn : m ∈ orN G C := by
    have hnb : ¬ BelowF G C m := by
      intro hb
      have htrue := reach_var_val (pairInput v v) (n + m) v
        (mem_orIn_reach v hrawV) (pairInput_left v v)
      exact G.irrefl ((graphFun_pair G v v).mp (hb _ htrue))
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro hmo hnb)
  have hml : m ∈ lam G C := by
    by_contra h
    have he : m ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hmn, h⟩
    simp [hzero] at he
  obtain ⟨t, ht⟩ := lambda_clean_pencil hAO hml
  have htv := (SimpleGraph.deleteEdges_adj.mp (ht v hrawV)).1
  have htp := (SimpleGraph.deleteEdges_adj.mp (ht p hrawP)).1
  exact hcolor (bool_eq_of_ne_common (color v) (color p) (color t)
    (hbip v t htv.symm) (hbip p t htp.symm))
lemma shared_top_at_most_one (hAO : IsAO2 n C) (hT : TopForm G C)
    (hfour : NoFourCycle G) (hzero : orN G C \ lam G C = ∅)
    (p : Fin n)
    {a : ℕ} (ha : a ∈ tops G C) {v w : Fin n}
    (hev : s(p, v) ∈ Ustar G C) (hew : s(p, w) ∈ Ustar G C)
    (hv : gateVal n C a (pairInput p v) = true)
    (hw : gateVal n C a (pairInput p w) = true) : v = w := by
  by_contra hvw
  obtain ⟨hal, hao, hab⟩ := topData ha
  have hp : gateVal n C a (pairInput p p) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact G.irrefl ((graphFun_pair G p p).mp (hab _ h))
  obtain ⟨m, hm, hmo, hmc, hmv, hmw, hmp⟩ := find_or_separating hAO hvw hal hao hv hw hp
  have hvr := or_below_top_raw hAO hT hzero hao hm hmo hmc hmv hmp
  have hwr := or_below_top_raw hAO hT hzero hao hm hmo hmc hmw hmp
  have hmn : m ∈ orN G C := by
    have hnb : ¬ BelowF G C m := by
      intro hb
      have htrue := reach_var_val (pairInput v v) (n + m) v
        (mem_orIn_reach v hvr) (pairInput_left v v)
      exact G.irrefl ((graphFun_pair G v v).mp (hb _ htrue))
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro hmo hnb)
  have hml : m ∈ lam G C := by
    by_contra h
    have he : m ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hmn, h⟩
    simp [hzero] at he
  obtain ⟨t, ht⟩ := lambda_clean_pencil hAO hml
  obtain ⟨htv, hcv⟩ := SimpleGraph.deleteEdges_adj.mp (ht v hvr)
  obtain ⟨htw, _⟩ := SimpleGraph.deleteEdges_adj.mp (ht w hwr)
  have hpt : p ≠ t := by
    intro he
    exact hcv (he ▸ hev)
  exact hvw (common_neighbors_unique_of_card_le_one G hfour p t hpt v w
    (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hev).1) htv
    (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hew).1) htw)
lemma top_uncovered_edges_equal (hAO : IsAO2 n C) (hT : TopForm G C)
    (hfour : NoFourCycle G) (hzero : orN G C \ lam G C = ∅)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    {a : ℕ} (ha : a ∈ tops G C) {u v p q : Fin n}
    (heu : s(u, v) ∈ Ustar G C) (hep : s(p, q) ∈ Ustar G C)
    (hv : gateVal n C a (pairInput u v) = true)
    (hw : gateVal n C a (pairInput p q) = true) : s(u, v) = s(p, q) := by
  have same_start : ∀ {u v p q : Fin n}, color u = color p →
      s(u, v) ∈ Ustar G C → s(p, q) ∈ Ustar G C →
      gateVal n C a (pairInput u v) = true → gateVal n C a (pairInput p q) = true →
      s(u, v) = s(p, q) := by
    intro u v p q hc he1 he2 ht1 ht2
    have huv := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he1).1
    have hpq := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he2).1
    have share : ∀ {p v w : Fin n}, s(p, v) ∈ Ustar G C → s(p, w) ∈ Ustar G C →
        gateVal n C a (pairInput p v) = true → gateVal n C a (pairInput p w) = true → v = w := by
      intro p v w he1 he2 ht1 ht2
      exact shared_top_at_most_one hAO hT hfour hzero p ha he1 he2 ht1 ht2
    by_cases hup : u = p
    · subst p
      exact congrArg (fun v => s(u, v)) (share he1 he2 ht1 ht2)
    · have hvc : color v ≠ color p := by simpa only [← hc] using hbip v u huv.symm
      have hqc : color q ≠ color u := by simpa only [hc] using hbip q p hpq.symm
      have htUQ := top_accepts_cross hAO hT hzero color hbip ha hvc ht1 ht2
      have htPV := top_accepts_cross hAO hT hzero color hbip ha hqc ht2 ht1
      have huq := (graphFun_pair G u q).mp ((topData ha).2.2 _ htUQ)
      have hpv := (graphFun_pair G p v).mp ((topData ha).2.2 _ htPV)
      have hvq := common_neighbors_unique_of_card_le_one G hfour u p hup v q huv hpv huq hpq
      subst q
      have h1 : s(v, u) ∈ Ustar G C := by simpa only [Sym2.eq_swap] using he1
      have h2 : s(v, p) ∈ Ustar G C := by simpa only [Sym2.eq_swap] using he2
      have hvu : pairInput v u = pairInput u v := by funext z; simp [pairInput, or_comm]
      have hvp : pairInput v p = pairInput p v := by funext z; simp [pairInput, or_comm]
      exact (hup (share h1 h2 (hvu ▸ ht1) (hvp ▸ ht2))).elim
  by_cases hc : color u = color p
  · exact same_start hc heu hep hv hw
  · have hpq := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hep).1
    have hcuq : color u = color q := bool_eq_of_ne_common _ _ _ hc (hbip q p hpq.symm)
    have heq : s(q, p) ∈ Ustar G C := by simpa only [Sym2.eq_swap] using hep
    have hpqi : pairInput q p = pairInput p q := by funext z; simp [pairInput, or_comm]
    exact (same_start hcuq heu heq hv (hpqi ▸ hw)).trans Sym2.eq_swap
lemma zero_extra_or_ustar_le_centreless
    (hleast : IsLeastAO G C) (hT : TopForm G C)
    (hfour : NoFourCycle G) (hzero : orN G C \ lam G C = ∅)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b) :
    (Ustar G C).card ≤ (centreless G C).card := by
  classical
  have assign : ∀ e : Sym2 (Fin n), ∃ a : ℕ,
      e ∈ Ustar G C → a ∈ centreless G C ∧
        gateVal n C a (pairInput e.out.1 e.out.2) = true := by
    intro e
    by_cases he : e ∈ Ustar G C
    · have he' : s(e.out.1, e.out.2) ∈ Ustar G C := by
        simpa only [Sym2.mk_fst_out_snd_out] using he
      obtain ⟨a, ha, hav⟩ := zero_or_residual_centreless hleast hT hzero he'
      exact ⟨a, fun _ => ⟨ha, hav⟩⟩
    · exact ⟨0, fun h => (he h).elim⟩
  choose f hf using assign
  apply Finset.card_le_card_of_injOn f (fun e he => (hf e he).1)
  intro e he d hd heq
  change e ∈ Ustar G C at he
  change d ∈ Ustar G C at hd
  have hav := (hf e he).2
  have had : gateVal n C (f e) (pairInput d.out.1 d.out.2) = true := heq ▸ (hf d hd).2
  have he' : s(e.out.1, e.out.2) ∈ Ustar G C := by
    simpa only [Sym2.mk_fst_out_snd_out] using he
  have hd' : s(d.out.1, d.out.2) ∈ Ustar G C := by
    simpa only [Sym2.mk_fst_out_snd_out] using hd
  have hpair := top_uncovered_edges_equal hleast.1 hT hfour hzero color hbip
    (Finset.mem_filter.mp (hf e he).1).1 he' hd' hav had
  simpa only [Sym2.mk_fst_out_snd_out] using hpair
end ZeroExtraGlobal
lemma bipartite_zero_extra_or_junk_empty
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfour : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hleast : IsLeastAO G C) (htop : TopForm G C)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hzero : orN G C \ lam G C = ∅) : junk G C = ∅ := by
  have hu := ZeroExtraGlobal.zero_extra_or_ustar_le_centreless hleast htop hfour hzero color hbip
  have hP := penalty_le_twice_uncovered n G C hfour hE hleast htop
  apply Finset.card_eq_zero.mp
  omega
open PEqualNP.CleanedNonEdge

namespace MixingOne
open PEqualNP.TopForm
end MixingOne
namespace MixingOne
open PEqualNP.TopForm
section CleanClauses
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {I : Type*} {S : I → Finset (Fin n)} {U : Finset (Sym2 (Fin n))}
end CleanClauses
end MixingOne
namespace MixingOne
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583_aux.Budget
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
end MixingOne
namespace MixingOne
open PEqualNP.TopForm
section Anchored
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
  {I : Type*} {S : I → Finset (Fin n)} {U : Finset (Sym2 (Fin n))}
end Anchored
end MixingOne
namespace MixingOne
private def boundarySlots (n : ℕ) (D : Finset ℕ) (wire : ℕ → Fin 2 → ℕ) :
    Finset (ℕ × Fin 2) := by
  classical
  exact (D.product (Finset.univ : Finset (Fin 2))).filter
    (fun k => ¬ ∃ h ∈ D, wire k.1 k.2 = n+h)
lemma binaryBoundaryCard (n : ℕ) (D : Finset ℕ) (wire : ℕ → Fin 2 → ℕ)
    {r : ℕ} (root : r ∈ D)
    (parent : ∀ g ∈ D, g ≠ r → ∃ h ∈ D, ∃ i, wire h i = n+g) :
    (boundarySlots n D wire).card ≤ D.card+1 := by
  classical
  let pool := D.product (Finset.univ : Finset (Fin 2))
  let leaves := boundarySlots n D wire
  let internal := pool \ leaves
  have sub : leaves ⊆ pool := Finset.filter_subset _ _
  have assigns (g : D.erase r) : ∃ k : internal, wire k.val.1 k.val.2 = n+g.val := by
    obtain ⟨hne,hg⟩ := Finset.mem_erase.mp g.2
    obtain ⟨h,hh,i,he⟩ := parent g.val hg hne
    have selected : (h,i) ∈ pool := Finset.mem_product.mpr ⟨hh,Finset.mem_univ _⟩
    have noLeaf : (h,i) ∉ leaves := by
      intro hleaf
      exact (Finset.mem_filter.mp hleaf).2 ⟨g.val,hg,he⟩
    exact ⟨⟨(h,i),Finset.mem_sdiff.mpr ⟨selected,noLeaf⟩⟩,he⟩
  choose f hf using assigns
  have inj : Function.Injective f := by
    intro g h eq
    apply Subtype.ext
    have hg := hf g
    have hh := hf h
    rw [eq] at hg
    omega
  have charge : (D.erase r).card ≤ internal.card := by simpa using Fintype.card_le_of_injective f inj
  have removed := Finset.card_erase_add_one root
  have split : internal.card = pool.card - leaves.card := Finset.card_sdiff_of_subset sub
  have both : pool.card = D.card * 2 := by simp [pool]
  have hsize := Finset.card_le_card sub
  change leaves.card ≤ D.card+1
  omega
end MixingOne
namespace MixingOne
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583_aux.Budget
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
private lemma oneMixingSource (least : IsLeastAO G C) (top : TopForm G C)
    (nonempty : (Ustar G C).Nonempty) (empty : centreless G C = ∅)
    {m : ℕ} (only : orN G C \ lam G C = {m}) :
    ∃ j ∈ junk G C, j < m ∧ ∃ t : Fin n,
      (∀ u v : Fin n, s(u,v) ∈ Ustar G C → gateVal n C j (pairInput u v) = true) ∧
      ∀ e ∈ Ustar G C, ∃ p b : Fin n, e = s(p,b) ∧ (G.deleteEdges ↑(Ustar G C)).Adj p t ∧
        ∀ x : Fin n → Bool, x p = true → graphFun G ∅ x = false → gateVal n C j x = false := by
  have hm : m ∈ orN G C \ lam G C := by simp [only]
  obtain ⟨e,he⟩ := nonempty
  have he' : ∃ u v : Fin n, s(u,v) ∈ Ustar G C := by
    induction e using Sym2.ind with
    | _ u v => exact ⟨u,v,he⟩
  obtain ⟨u,v,huv⟩ := he'
  obtain ⟨a,ha,i,j,hj,_,hr,_⟩ := residualTrace least top huv
  obtain ⟨l,hl,hin,path⟩ := residualPath least.1 empty ha hj hr
  have eq : l = m := by simpa [only] using hl
  subst l
  obtain ⟨t,ht⟩ := mixingRaw least.1 empty only hm ha path
  have hmdata := orData hm
  have hlt := least.1.2.1 m hmdata.1 _ hin
  refine ⟨j,hj,by omega,t,?_,?_⟩
  · intro p q hpq
    obtain ⟨a',ha',i',k,hk,_,hr',hv⟩ := residualTrace least top hpq
    obtain ⟨r,hro,hki,_⟩ := residualPath least.1 empty ha' hk hr'
    have heq : r = m := by simpa [only] using hro
    subst r
    have same := singleJunkInput least.1 hm ⟨t,ht⟩ hj hk hin hki
    rwa [same]
  · intro f hf
    induction f using Sym2.ind with
    | _ p q =>
      obtain ⟨a',ha',i',k,hk,hav,reach,_⟩ := residualTrace least top hf
      obtain ⟨r,hro,_,path'⟩ := residualPath least.1 empty ha' hk reach
      have heq : r = m := by simpa [only] using hro
      subst r
      obtain ⟨w,hw,hend⟩ := oppositeEndpoint least top empty only hm ha' hav path'
      have ta : t ∈ side C a' i' := reach_mem_orIn t (path'.trans (mem_orIn_reach t ht))
      have old := (cleanAdj least.1 ha' i' ta hw).symm
      have safe (x : Fin n → Bool) (hx : x w = true) (hn : graphFun G ∅ x = false) :
          gateVal n C j x = false := by
        apply Bool.eq_false_iff.mpr
        intro on
        have mx : gateVal n C m x = true := (val_or (n := n) (by simp) hmdata.1 hmdata.2.1).mpr
          ⟨_,hin,hlt,on⟩
        exact Bool.false_ne_true (hn.symm.trans (firingTop least.1 ha' path' hw x mx hx))
      rcases hend with rfl | rfl
      · exact ⟨w,q,rfl,old,safe⟩
      · exact ⟨w,p,Sym2.eq_swap,old,safe⟩
private lemma dirtyRootCNF (least : IsLeastAO G C) (top : TopForm G C)
    {m r : ℕ} (only : orN G C \ lam G C = {m}) (hr : r ∈ junk G C) (hrm : r < m)
    (rootPos : ∀ u v : Fin n, s(u,v) ∈ Ustar G C → gateVal n C r (pairInput u v) = true) :
    ∃ F : Finset (ℕ × Fin 2), F.card ≤ (junk G C).card+1 ∧
      (∀ k ∈ F, (side (n := n) C k.1 k.2).card ≤ 1 ∨
        ∃ z : Fin n, ∀ w ∈ side C k.1 k.2, (G.deleteEdges ↑(Ustar G C)).Adj w z) ∧
      (∀ u v : Fin n, s(u,v) ∈ Ustar G C → ∀ k ∈ F, u ∈ side C k.1 k.2 ∨ v ∈ side C k.1 k.2) ∧
      ∀ x : Fin n → Bool, (∀ k ∈ F, ∃ w ∈ side C k.1 k.2, x w = true) → gateVal n C r x = true := by
  classical
  let step (g h : ℕ) := g ∈ junk G C ∧ h ∈ junk G C ∧ ∃ i : Fin 2, opnd C g i = n+h
  let D := (junk G C).filter fun g => Relation.ReflTransGen step r g
  have root : r ∈ D := Finset.mem_filter.mpr ⟨hr,.refl⟩
  have dirty {g : ℕ} (hg : g ∈ D) : g ∈ junk G C := (Finset.mem_filter.mp hg).1
  have reach {g : ℕ} (hg : g ∈ D) : Relation.ReflTransGen step r g := (Finset.mem_filter.mp hg).2
  have descend {g h : ℕ} (s : step g h) : h < g := by
    obtain ⟨hg,_,i,eq⟩ := s
    have := opndBound least.1 (junkData hg).1 i
    omega
  have before {g : ℕ} (hg : g ∈ D) : g < m := by
    have p := reach hg
    induction p with
    | refl => exact hrm
    | tail p s ih => exact (descend s).trans (ih (Finset.mem_filter.mpr ⟨s.1,p⟩))
  have parent (g : ℕ) (hg : g ∈ D) (hne : g ≠ r) : ∃ h ∈ D, ∃ i, opnd C h i = n+g := by
    rcases Relation.ReflTransGen.cases_tail (reach hg) with eq | ⟨h,p,k⟩
    · exact (hne eq).elim
    · exact ⟨h,Finset.mem_filter.mpr ⟨k.1,p⟩,k.2.2⟩
  have grows {g h : ℕ} (hg : g ∈ D) (hh : h ∈ junk G C) {i : Fin 2}
      (edge : opnd C g i = n+h) : h ∈ D :=
    Finset.mem_filter.mpr ⟨hh,(reach hg).tail ⟨dirty hg,hh,i,edge⟩⟩
  have allPos {g : ℕ} (hg : g ∈ D) (u v : Fin n) (he : s(u,v) ∈ Ustar G C) :
      gateVal n C g (pairInput u v) = true := by
    have p := reach hg
    induction p with
    | refl => exact rootPos u v he
    | tail p s ih =>
      obtain ⟨h₁,h₂,i,edge⟩ := s
      have prior := ih (Finset.mem_filter.mpr ⟨h₁,p⟩)
      have hv := (andValOperands least.1 (junkData h₁).1 (junkData h₁).2.1 _).mp prior i
      rw [edge] at hv
      exact hv
  let F := boundarySlots n D (opnd C)
  have source {k : ℕ × Fin 2} (hk : k ∈ F) : k.1 ∈ D :=
    (Finset.mem_product.mp (Finset.mem_filter.mp hk).1).1
  have hm : m ∈ orN G C \ lam G C := by simp [only]
  have Ds : D ⊆ junk G C := Finset.filter_subset _ _
  refine ⟨F,(binaryBoundaryCard n D (opnd C) root parent).trans (by have := Finset.card_le_card Ds; omega),?_,?_,?_⟩
  · intro k hk
    apply rawCoverShape least.1 only hm
    have bd := opndBound least.1 (junkData (dirty (source hk))).1 k.2
    have := before (source hk)
    omega
  · intro u v he k hk
    have hD := source hk
    obtain ⟨gl,go,_⟩ := junkData (dirty hD)
    have hv := (andValOperands least.1 gl go _).mp (allPos hD u v he) k.2
    rcases operandSupport least.1 top gl go hv with ⟨t,ht,rfl | rfl⟩ | ⟨h,hh,path,_⟩
    · exact Or.inl ht
    · exact Or.inr ht
    · have eq : opnd C k.1 k.2 = n+h := by
        rcases lastOrBefore (orReaches_reach h _ path).1 with direct | ⟨v,hl,ho,hi,hle,rest⟩
        · exact direct
        · have same : v = m := by simpa [only] using lastOrOutside least.1 hh hl ho hi hle
          have earlier := orStep_le rest
          have bd := opndBound least.1 gl k.2
          have prior := before hD
          omega
      exact ((Finset.mem_filter.mp hk).2 ⟨h,grows hD hh eq,eq⟩).elim
  · intro x fires
    have on (g : ℕ) : g ∈ D → gateVal n C g x = true := by
      induction g using Nat.strong_induction_on with
      | ind g ih =>
        intro hg
        obtain ⟨gl,go,_⟩ := junkData (dirty hg)
        apply (andValOperands least.1 gl go _).mpr
        intro i
        by_cases inner : ∃ h ∈ D, opnd C g i = n+h
        · obtain ⟨h,hh,eq⟩ := inner
          have bd := opndBound least.1 gl i
          rw [eq]
          exact ih h (by omega) hh
        · have entry : (g,i) ∈ F := Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hg,Finset.mem_univ _⟩,inner⟩
          obtain ⟨w,hw,hx⟩ := fires (g,i) entry
          exact sideVal hw hx
    exact on r root
lemma bipartite_one_extra_or_ustar_card_le_one
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hfour : NoFourCycle G) (hleast : IsLeastAO G C) (htop : TopForm G C)
    (hzero : centreless G C = ∅) (hor : (orN G C \ lam G C).card = 1) :
    (Ustar G C).card ≤ 1 := by
  classical
  by_cases hU : (Ustar G C).Nonempty
  · obtain ⟨m, honly⟩ := Finset.card_eq_one.mp hor
    obtain ⟨j, hj, hbefore, t, hpos, hsource⟩ := oneMixingSource hleast htop hU hzero honly
    obtain ⟨F, _, hshape, hcover, hsafe⟩ := dirtyRootCNF hleast htop honly hj hbefore hpos
    apply PEqualNP.Outside.L_meta_2583_aux.cover_property_card_le_one G (Ustar G C) color hbip
      (PEqualNP.Outside.L_meta_2583_aux.common_neighbors_unique_of_card_le_one G hfour)
      (fun u v huv => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp huv).1) t
    intro u v huv
    obtain ⟨p, b, hrepr, hclean, hoff⟩ := hsource s(u, v) huv
    have hend : p = u ∨ p = v := by
      have hp : p ∈ s(u, v) := hrepr.symm ▸ (by simp : p ∈ s(p, b))
      simpa using hp
    refine ⟨p, hend, (SimpleGraph.deleteEdges_adj.mp hclean).1.symm, ?_, ?_⟩
    · have hn := (SimpleGraph.deleteEdges_adj.mp hclean).2
      change s(p, t) ∉ Ustar G C at hn
      simpa only [Sym2.eq_swap] using hn
    · intro x hx hind
      have hnone : ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
        rintro ⟨a, b, hab, ha, hb⟩
        exact Bool.false_ne_true ((hind a b hab ha).symm.trans hb)
      have hF : graphFun G ∅ x = false := by simp [graphFun, hnone]
      have hno : ¬ ∀ k ∈ F, ∃ w ∈ side C k.1 k.2, x w = true := by
        intro hall
        exact Bool.false_ne_true ((hoff x hx hF).symm.trans (hsafe x hall))
      push Not at hno
      obtain ⟨k, hk, hmiss⟩ := hno
      refine ⟨side C k.1 k.2, ?_, fun a b hab => hcover a b hab k hk, ?_⟩
      · rcases hshape k hk with hs | ⟨z, hz⟩
        · exact Or.inl hs
        · exact Or.inr ⟨z, fun w hw => SimpleGraph.deleteEdges_adj.mp (hz w hw)⟩
      · intro w hw
        exact Bool.eq_false_iff.mpr (hmiss w hw)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hU]
end MixingOne
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
lemma bipartite_no_centreless_junk_two_extra_or
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfour : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hleast : IsLeastAO G C) (htop : TopForm G C)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hzero : centreless G C = ∅) (hjunk : 2 ≤ (junk G C).card) :
    2 ≤ (orN G C \ lam G C).card := by
  by_contra h
  have hr : (orN G C \ lam G C).card ≤ 1 := by omega
  by_cases hz : (orN G C \ lam G C).card = 0
  · have he := bipartite_zero_extra_or_junk_empty n G C hfour hE hleast htop color hbip
      (Finset.card_eq_zero.mp hz)
    simp [he] at hjunk
  · have hr1 : (orN G C \ lam G C).card = 1 := by omega
    have hu := MixingOne.bipartite_one_extra_or_ustar_card_le_one color hbip hfour hleast htop hzero hr1
    have hP := penalty_le_twice_uncovered n G C hfour hE hleast htop
    omega
lemma bipartite_penalty_four_shape
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfour : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hleast : IsLeastAO G C) (htop : TopForm G C)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hjunk : 2 ≤ (junk G C).card)
    (hP : 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card = 4) :
    (junk G C).card = 2 ∧ centreless G C = ∅ ∧ (orN G C \ lam G C).card = 2 := by
  have hrpos : 0 < (orN G C \ lam G C).card := by
    by_contra h
    have hz : orN G C \ lam G C = ∅ := Finset.card_eq_zero.mp (by omega)
    have he := bipartite_zero_extra_or_junk_empty n G C hfour hE hleast htop color hbip hz
    simp [he] at hjunk
  have hz : centreless G C = ∅ := Finset.card_eq_zero.mp (by omega)
  have hr := bipartite_no_centreless_junk_two_extra_or n G C hfour hE hleast htop color hbip hz hjunk
  exact ⟨by omega, hz, by omega⟩
namespace PureExtra
open Budget ZeroExtra
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma minimal_false_junk_has_extra_or
    (hAO : IsAO2 n C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (p v w : Fin n) (hvw : v ≠ w)
    (hev : s(p, v) ∈ Ustar G C) (hew : s(p, w) ∈ Ustar G C)
    (j : ℕ) (hj : j ∈ junk G C)
    (hjv : gateVal n C j (pairInput p v) = true)
    (hjw : gateVal n C j (pairInput p w) = true)
    (hjp : gateVal n C j (pairInput p p) = false)
    (hmin : ∀ l ∈ junk G C, gateVal n C l (pairInput p p) = false → j ≤ l) :
    ∃ m ∈ orN G C \ lam G C, ∀ l ∈ junk G C,
      ¬ Relation.ReflTransGen (OrStep n C) (n + m) (n + l) := by
  obtain ⟨hjl, hjo, _⟩ := junkData hj
  obtain ⟨m, hm, hmo, hmj, hmv, hmw, hmp⟩ :=
    find_or_separating hAO hvw hjl hjo hjv hjw hjp
  have hmjlt : m < j := coneLt hmj
  have hblocked : ∀ l ∈ junk G C,
      ¬ Relation.ReflTransGen (OrStep n C) (n + m) (n + l) := by
    intro l hl hr
    have hlp : gateVal n C l (pairInput p p) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have hmtrue := orStep_up (n := n) (by simp) hr ht
      exact Bool.false_ne_true (hmp.symm.trans hmtrue)
    have hle := hmin l hl hlp
    have hpath := orStep_le hr
    omega
  have raw : ∀ {z : Fin n}, gateVal n C m (pairInput p z) = true →
      z ∈ orIn n C (n + m) := by
    intro z hz
    rcases operand_trace p z (n + m) hz with ⟨t, ht, hr⟩ | ⟨l, hl, hlo, hr, _⟩
    · rcases ht with htp | htz
      · have hmtrue := reach_var_val (pairInput p p) (n + m) t hr
          ((pairInput_true p p t).mpr (Or.inl htp))
        exact (Bool.false_ne_true (hmp.symm.trans hmtrue)).elim
      · simpa only [htz] using reach_mem_orIn t hr
    · have hlop : (gateAt C l).op = GateOp.and :=
        (hAO.1 _ (gateAt_mem hl)).resolve_right hlo
      have hlm : InCone n C l m := by
        rcases orStep_cone hr m l rfl rfl with he | hcone
        · subst l
          rw [hmo] at hlop
          contradiction
        · exact hcone
      have hljunk := lowerAndJunk hT hjo hlop (coneTrans hlm hmj)
      exact (hblocked l hljunk hr).elim
  have hrawv := raw hmv
  have hraww := raw hmw
  have hmn : m ∈ orN G C := by
    have hnb : ¬ BelowF G C m := by
      intro hb
      have htrue := reach_var_val (pairInput v v) (n + m) v
        (mem_orIn_reach v hrawv) (pairInput_left v v)
      exact G.irrefl ((graphFun_pair G v v).mp (hb _ htrue))
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro hmo hnb)
  have hnlam : m ∉ lam G C := by
    intro hml
    obtain ⟨t, ht⟩ := lambda_clean_pencil hAO hml
    obtain ⟨htv, hcv⟩ := SimpleGraph.deleteEdges_adj.mp (ht v hrawv)
    obtain ⟨htw, _⟩ := SimpleGraph.deleteEdges_adj.mp (ht w hraww)
    have hpt : p ≠ t := by
      intro he
      exact hcv (he ▸ hev)
    exact hvw (common_neighbors_unique_of_card_le_one G hfour p t hpt v w
      (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hev).1) htv
      (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hew).1) htw)
  exact ⟨m, Finset.mem_sdiff.mpr ⟨hmn, hnlam⟩, hblocked⟩
lemma two_joint_junk_star_pairs_extra_or
    (hAO : IsAO2 n C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (p v w : Fin n) (hvw : v ≠ w)
    (hev : s(p, v) ∈ Ustar G C) (hew : s(p, w) ∈ Ustar G C)
    (j k : ℕ) (hpair : junk G C = {j, k})
    (hjoint : ∀ x, gateVal n C j x = true → gateVal n C k x = true →
      graphFun G ∅ x = true)
    (hjv : gateVal n C j (pairInput p v) = true)
    (hjw : gateVal n C j (pairInput p w) = true)
    (hkv : gateVal n C k (pairInput p v) = true)
    (hkw : gateVal n C k (pairInput p w) = true) :
    ∃ m ∈ orN G C \ lam G C, ∀ l ∈ junk G C,
      ¬ Relation.ReflTransGen (OrStep n C) (n + m) (n + l) := by
  have hj : j ∈ junk G C := by simp [hpair]
  have hk : k ∈ junk G C := by simp [hpair]
  have hbad : gateVal n C j (pairInput p p) = false ∨
      gateVal n C k (pairInput p p) = false := by
    by_contra hn
    have htj : gateVal n C j (pairInput p p) = true :=
      Bool.eq_true_of_not_eq_false fun hf => hn (Or.inl hf)
    have htk : gateVal n C k (pairInput p p) = true :=
      Bool.eq_true_of_not_eq_false fun hf => hn (Or.inr hf)
    exact G.irrefl ((graphFun_pair G p p).mp (hjoint _ htj htk))
  have member : ∀ l ∈ junk G C, l = j ∨ l = k := by
    intro l hl
    simpa only [hpair, Finset.mem_insert, Finset.mem_singleton] using hl
  by_cases hjp : gateVal n C j (pairInput p p) = false
  · by_cases hkp : gateVal n C k (pairInput p p) = false
    · by_cases hle : j ≤ k
      · apply minimal_false_junk_has_extra_or hAO hT hfour p v w hvw hev hew j hj hjv hjw hjp
        intro l hl _
        rcases member l hl with rfl | rfl
        · exact le_rfl
        · exact hle
      · apply minimal_false_junk_has_extra_or hAO hT hfour p v w hvw hev hew k hk hkv hkw hkp
        intro l hl _
        rcases member l hl with rfl | rfl
        · omega
        · exact le_rfl
    · apply minimal_false_junk_has_extra_or hAO hT hfour p v w hvw hev hew j hj hjv hjw hjp
      intro l hl hf
      rcases member l hl with rfl | rfl
      · exact le_rfl
      · exact (hkp hf).elim
  · have hkp := hbad.resolve_left hjp
    apply minimal_false_junk_has_extra_or hAO hT hfour p v w hvw hev hew k hk hkv hkw hkp
    intro l hl hf
    rcases member l hl with rfl | rfl
    · exact (hjp hf).elim
    · exact le_rfl
end PureExtra
namespace EffectiveExtra
open Budget
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma extra_or_direct_path (hAO : IsAO2 n C) {m j : ℕ}
    (hm : m ∈ orN G C \ lam G C) (hin : n + j ∈ (gateAt C m).inputs) :
    Relation.ReflTransGen (OrStep n C) (n + m) (n + j) :=
  .head ⟨m, (orData hm).1, rfl, (orData hm).2.1, hin,
    hAO.2.1 m (orData hm).1 (n + j) hin⟩ .refl
lemma one_effective_extra_or_pencil
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hempty : centreless G C = ∅)
    (m : ℕ)
    (hactive : ∀ l ∈ orN G C \ lam G C, ∀ j ∈ junk G C,
      Relation.ReflTransGen (OrStep n C) (n + l) (n + j) → l = m)
    (hU : (Ustar G C).Nonempty) :
    ∃ t : Fin n, ∀ u v, s(u, v) ∈ Ustar G C →
      ∃ w, (w = u ∨ w = v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj t w := by
  obtain ⟨e, he⟩ := hU
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨a, ha, b, j, hj, _, hr, _⟩ := residualTrace hleast hT he
    obtain ⟨l, hl, hli, path⟩ := residualPath hleast.1 hempty ha hj hr
    have hlpath := extra_or_direct_path hleast.1 hl hli
    have hlm := hactive l hl j hj hlpath
    subst l
    have hraw : (orIn n C (n + m)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hz
      rcases lastOrBefore path with heq | ⟨k, hk, hko, hki, hkb, _⟩
      · have hne := topSides hempty ha b
        change (orIn n C (opnd C a b)).Nonempty at hne
        rw [heq, hz] at hne
        exact Finset.not_nonempty_empty hne
      · have hkR := emptyInputOutside hleast.1 (orData hl).2.2 hz hk hko hki
        have hkpath : Relation.ReflTransGen (OrStep n C) (n + k) (n + j) :=
          (extra_or_direct_path hleast.1 hkR hki).trans hlpath
        have hkm := hactive k hkR j hj hkpath
        omega
    obtain ⟨t, ht⟩ := hraw
    refine ⟨t, ?_⟩
    intro p q hpq
    obtain ⟨a', ha', b', k, hk, hav, hr', _⟩ := residualTrace hleast hT hpq
    obtain ⟨l, hl', hli', hp⟩ := residualPath hleast.1 hempty ha' hk hr'
    have hlm := hactive l hl' k hk (extra_or_direct_path hleast.1 hl' hli')
    subst l
    have hend : ∃ w ∈ side C a' (1 - b'), w = p ∨ w = q := by
      obtain ⟨al, ao, ab⟩ := topData ha'
      have hv := (andValOperands hleast.1 al ao _).mp hav (1 - b')
      rcases operandSupport hleast.1 hT al ao hv with h | ⟨d, hd, hdreach, _⟩
      · exact h
      · obtain ⟨l, hl'', hli'', hp'⟩ := residualPath hleast.1 hempty ha' hd hdreach
        have hlm := hactive l hl'' d hd (extra_or_direct_path hleast.1 hl'' hli'')
        subst l
        exfalso
        apply (orData hl).2.2
        intro x hx
        apply ab x ((andValOperands hleast.1 al ao x).mpr ?_)
        intro c
        rcases opposite b' c with rfl | rfl
        · exact orStep_up (n := n) (by simp) hp hx
        · exact orStep_up (n := n) (by simp) hp' hx
    obtain ⟨w, hw, hend⟩ := hend
    have ht' : t ∈ side C a' b' :=
      reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
    exact ⟨w, hend, cleanAdj hleast.1 ha' b' ht' hw⟩
lemma two_extra_or_pure_full_star_card_le_one
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (hempty : centreless G C = ∅) (hcard : (orN G C \ lam G C).card ≤ 2)
    (m0 : ℕ) (hm0 : m0 ∈ orN G C \ lam G C)
    (hblocked : ∀ j ∈ junk G C,
      ¬ Relation.ReflTransGen (OrStep n C) (n + m0) (n + j))
    (p : Fin n)
    (hstar : ∀ u v, s(u, v) ∈ Ustar G C ↔ G.Adj u v ∧ (u = p ∨ v = p)) :
    (Ustar G C).card ≤ 1 := by
  classical
  by_cases hU : (Ustar G C).Nonempty
  · obtain ⟨e, he⟩ := hU
    have hpair : ∃ u v : Fin n, s(u, v) ∈ Ustar G C := by
      induction e using Sym2.ind with
      | h u v => exact ⟨u, v, he⟩
    obtain ⟨u, v, huv⟩ := hpair
    obtain ⟨a, ha, b, j, hj, _, hr, _⟩ := residualTrace hleast hT huv
    obtain ⟨m, hm, hmi, _⟩ := residualPath hleast.1 hempty ha hj hr
    have hm0m : m0 ≠ m := by
      intro h
      exact hblocked j hj (h ▸ extra_or_direct_path hleast.1 hm hmi)
    have active : ∀ l ∈ orN G C \ lam G C, ∀ k ∈ junk G C,
        Relation.ReflTransGen (OrStep n C) (n + l) (n + k) → l = m := by
      intro l hl k hk hp
      by_contra hlm
      have hm0l : m0 ≠ l := by
        intro h
        exact hblocked k hk (h ▸ hp)
      have hsub : {m0, m, l} ⊆ orN G C \ lam G C := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hm0
        · exact hm
        · exact hl
      have hbound := Finset.card_le_card hsub
      have hthree : ({m0, m, l} : Finset ℕ).card = 3 := by
        simp [hm0m, hm0l, Ne.symm hlm]
      omega
    obtain ⟨t, ht⟩ := one_effective_extra_or_pencil hleast hT hempty m active ⟨s(u, v), huv⟩
    apply full_star_clean_pencil_card_le_one G (Ustar G C) p t hstar
      (common_neighbors_unique_of_card_le_one G hfour)
    intro u v huv
    obtain ⟨w, hw, hc⟩ := ht u v huv
    exact ⟨w, hw, (SimpleGraph.deleteEdges_adj.mp hc).1, (SimpleGraph.deleteEdges_adj.mp hc).2⟩
  · simp [Finset.not_nonempty_iff_eq_empty.mp hU]
end EffectiveExtra
namespace OrdinaryCharge
open Budget PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma raw_extra_on_dirty_path (hAO : IsAO2 n C) {j w : ℕ}
    (hj : j ∈ junk G C)
    (hr : Relation.ReflTransGen (OrStep n C) w (n + j))
    (hraw : (orIn n C w).Nonempty) :
    ∃ m ∈ orN G C \ lam G C, (orIn n C (n + m)).Nonempty ∧
      Relation.ReflTransGen (OrStep n C) w (n + m) ∧
      Relation.ReflTransGen (OrStep n C) (n + m) (n + j) := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rw [andRawEmpty (junkData hj).2.1] at hraw
    exact (Finset.not_nonempty_empty hraw).elim
  | @head w c hstep hrest ih =>
    obtain ⟨m, hm, rfl, hmo, hmi, hmb⟩ := hstep
    by_cases hc : (orIn n C c).Nonempty
    · obtain ⟨l, hl, hlraw, hcl, hlj⟩ := ih hc
      exact ⟨l, hl, hlraw, .head ⟨m, hm, rfl, hmo, hmi, hmb⟩ hcl, hlj⟩
    · have hcn := orStep_le hrest
      obtain ⟨k, rfl⟩ : ∃ k, c = n + k := ⟨c - n, by omega⟩
      have hkempty : orIn n C (n + k) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
      have hkdirty : ¬ BelowF G C k := by
        intro hb
        obtain ⟨_, _, x, hjx, hFx⟩ := junkData hj
        have hkx := orStep_up (n := n) (by simp) hrest hjx
        exact Bool.false_ne_true (hFx.symm.trans (hb x hkx))
      exact ⟨m, emptyInputOutside hAO hkdirty hkempty hm hmo hmi, hraw, .refl,
        .head ⟨m, hm, rfl, hmo, hmi, hmb⟩ hrest⟩
lemma full_star_anchor_edges_equal
    (hfour : NoFourCycle G) (p t : Fin n)
    (hstar : ∀ u v, s(u, v) ∈ Ustar G C ↔ G.Adj u v ∧ (u = p ∨ v = p))
    {e d : Sym2 (Fin n)} (he : e ∈ Ustar G C) (hd : d ∈ Ustar G C)
    {v w : Fin n} (hv : v ∈ e) (hw : w ∈ d)
    (htv : (G.deleteEdges ↑(Ustar G C)).Adj t v)
    (htw : (G.deleteEdges ↑(Ustar G C)).Adj t w) : e = d := by
  have orient : ∀ e ∈ Ustar G C, ∀ v, v ∈ e →
      (G.deleteEdges ↑(Ustar G C)).Adj t v → e = s(p, v) := by
    intro e he v hv htv
    have hvp : v ≠ p := by
      intro h
      exact (SimpleGraph.deleteEdges_adj.mp htv).2
        ((hstar t v).mpr ⟨(SimpleGraph.deleteEdges_adj.mp htv).1, Or.inr h⟩)
    induction e using Sym2.ind with
    | h u w =>
      rcases ((hstar u w).mp he).2 with hup | hwp
      · rcases Sym2.mem_iff.mp hv with hvu | hvw
        · exact (hvp (hvu.trans hup)).elim
        · rw [hup, ← hvw]
      · rcases Sym2.mem_iff.mp hv with hvu | hvw
        · rw [hwp, ← hvu]
          exact Sym2.eq_swap
        · exact (hvp (hvw.trans hwp)).elim
  have heq := orient e he v hv htv
  have hdq := orient d hd w hw htw
  have hpv : G.Adj p v := ((hstar p v).mp (heq ▸ he)).1
  have hpw : G.Adj p w := ((hstar p w).mp (hdq ▸ hd)).1
  have hpt : p ≠ t := by
    intro h
    exact (SimpleGraph.deleteEdges_adj.mp htv).2 (h ▸ (heq ▸ he))
  have hvw := common_neighbors_unique_of_card_le_one G hfour p t hpt v w hpv
    (SimpleGraph.deleteEdges_adj.mp htv).1 hpw (SimpleGraph.deleteEdges_adj.mp htw).1
  exact heq.trans ((congrArg (fun v => s(p, v)) hvw).trans hdq.symm)
def HasRawOpposite (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (e : Sym2 (Fin n)) : Prop :=
  ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
    OrReaches n C (opnd C a b) j ∧ ∃ w ∈ side C a (1 - b), w ∈ e
lemma ordinary_full_star_card_le_extra
    (hAO : IsAO2 n C) (hfour : NoFourCycle G) (hempty : centreless G C = ∅)
    (p : Fin n)
    (hstar : ∀ u v, s(u, v) ∈ Ustar G C ↔ G.Adj u v ∧ (u = p ∨ v = p))
    (O : Finset (Sym2 (Fin n))) (hOU : O ⊆ Ustar G C)
    (hroute : ∀ e ∈ O, HasRawOpposite G C e) :
    O.card ≤ (orN G C \ lam G C).card := by
  classical
  have witness : ∀ e : Sym2 (Fin n), ∃ m : ℕ, e ∈ O →
      m ∈ orN G C \ lam G C ∧ (orIn n C (n + m)).Nonempty ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2,
        Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m) ∧
        ∃ w ∈ side C a (1 - b), w ∈ e := by
    intro e
    by_cases he : e ∈ O
    · obtain ⟨a, ha, b, j, hj, hr, w, hw, hwe⟩ := hroute e he
      obtain ⟨m, hm, hraw, hp, _⟩ := raw_extra_on_dirty_path hAO hj
        (orReaches_reach j _ hr).1 (topSides hempty ha b)
      exact ⟨m, fun _ => ⟨hm, hraw, a, ha, b, hp, w, hw, hwe⟩⟩
    · exact ⟨0, fun h => (he h).elim⟩
  choose f hf using witness
  apply Finset.card_le_card_of_injOn f (fun e he => (hf e he).1)
  intro e he d hd heq
  change e ∈ O at he
  change d ∈ O at hd
  obtain ⟨_, hraw, a, ha, b, hp, w, hw, hwe⟩ := hf e he
  obtain ⟨_, _, a', ha', b', hp', w', hw', hwd⟩ := hf d hd
  obtain ⟨t, ht⟩ := hraw
  have ht1 : t ∈ side C a b := reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
  have ht' : t ∈ orIn n C (n + f d) := heq ▸ ht
  have ht2 : t ∈ side C a' b' := reach_mem_orIn t (hp'.trans (mem_orIn_reach t ht'))
  exact full_star_anchor_edges_equal hfour p t hstar (hOU he) (hOU hd) hwe hwd
    (cleanAdj hAO ha b ht1 hw) (cleanAdj hAO ha' b' ht2 hw')
end OrdinaryCharge
lemma two_joint_full_star_pairs_equal
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (hempty : centreless G C = ∅) (hcard : (orN G C \ lam G C).card ≤ 2)
    (p : Fin n)
    (hstar : ∀ u v, s(u, v) ∈ Ustar G C ↔ G.Adj u v ∧ (u = p ∨ v = p))
    (j k : ℕ) (hpair : junk G C = {j, k})
    (hjoint : ∀ x, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true)
    {v w : Fin n} (hev : s(p, v) ∈ Ustar G C) (hew : s(p, w) ∈ Ustar G C)
    (hjv : gateVal n C j (pairInput p v) = true)
    (hjw : gateVal n C j (pairInput p w) = true)
    (hkv : gateVal n C k (pairInput p v) = true)
    (hkw : gateVal n C k (pairInput p w) = true) : v = w := by
  by_contra hvw
  obtain ⟨m, hm, hblocked⟩ := PureExtra.two_joint_junk_star_pairs_extra_or
    hleast.1 hT hfour p v w hvw hev hew j k hpair hjoint hjv hjw hkv hkw
  have hu := EffectiveExtra.two_extra_or_pure_full_star_card_le_one
    hleast hT hfour hempty hcard m hm hblocked p hstar
  have heq := Finset.card_le_one.mp hu s(p, v) hev s(p, w) hew
  apply hvw
  rcases Sym2.eq_iff.mp heq with ⟨_, heq⟩ | ⟨hpw, hvp⟩
  · exact heq
  · exact hvp.trans hpw
lemma gate_accepts_pair_of_gammaE
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {j : ℕ} {p v : Fin n} (he : s(p, v) ∈ gammaE G C j) :
    gateVal n C j (pairInput p v) = true := by
  obtain ⟨_, a, b, hab, hv⟩ := Finset.mem_filter.mp he
  rcases Sym2.eq_iff.mp hab with ⟨hpa, hvb⟩ | ⟨hpb, hva⟩
  · rw [← hpa, ← hvb] at hv
    exact hv
  · rw [← hva, ← hpb] at hv
    have hsym : pairInput v p = pairInput p v := by funext z; simp [pairInput, or_comm]
    simpa only [hsym] using hv
lemma two_joint_full_star_card_le_one
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (hempty : centreless G C = ∅) (hcard : (orN G C \ lam G C).card ≤ 2)
    (p : Fin n)
    (hstar : ∀ u v, s(u, v) ∈ Ustar G C ↔ G.Adj u v ∧ (u = p ∨ v = p))
    (j k : ℕ) (hpair : junk G C = {j, k})
    (hjoint : ∀ x, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true) :
    (Ustar G C ∩ gammaE G C j ∩ gammaE G C k).card ≤ 1 := by
  have orient : ∀ e ∈ Ustar G C, ∃ v, e = s(p, v) := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rcases ((hstar u v).mp he).2 with h | h
      · exact ⟨v, by rw [h]⟩
      · exact ⟨u, by rw [h]; exact Sym2.eq_swap⟩
  apply Finset.card_le_one.mpr
  intro e he d hd
  obtain ⟨he', hek⟩ := Finset.mem_inter.mp he
  obtain ⟨heU, hej⟩ := Finset.mem_inter.mp he'
  obtain ⟨hd', hdk⟩ := Finset.mem_inter.mp hd
  obtain ⟨hdU, hdj⟩ := Finset.mem_inter.mp hd'
  obtain ⟨v, rfl⟩ := orient e heU
  obtain ⟨w, rfl⟩ := orient d hdU
  have hvw := two_joint_full_star_pairs_equal G C hleast hT hfour hempty hcard p hstar j k hpair
    hjoint heU hdU (gate_accepts_pair_of_gammaE hej) (gate_accepts_pair_of_gammaE hdj)
    (gate_accepts_pair_of_gammaE hek) (gate_accepts_pair_of_gammaE hdk)
  exact congrArg (fun v => s(p, v)) hvw
namespace TwoJunkFullStar
open Budget OrdinaryCharge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma residual_ordinary_or_joint
    (hleast : IsLeastAO G C) (hT : TopForm G C)
    (j k : ℕ) (hpair : junk G C = {j, k})
    {e : Sym2 (Fin n)} (he : e ∈ Ustar G C) :
    HasRawOpposite G C e ∨
      (∀ x, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true) ∧
      e ∈ gammaE G C j ∩ gammaE G C k := by
  have member : ∀ d ∈ junk G C, d = j ∨ d = k := by
    intro d hd
    simpa only [hpair, Finset.mem_insert, Finset.mem_singleton] using hd
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨a, ha, b, d, hd, hav, hr, hdv⟩ := residualTrace hleast hT he
    obtain ⟨al, ao, ab⟩ := topData ha
    have hv := (andValOperands hleast.1 al ao _).mp hav (1 - b)
    rcases operandSupport hleast.1 hT al ao hv with ⟨w, hw, hwe⟩ | ⟨l, hl, hlr, hlv⟩
    · left
      exact ⟨a, ha, b, d, hd, hr, w, hw, Sym2.mem_iff.mpr hwe⟩
    · have hJ : ∀ x, gateVal n C d x = true → gateVal n C l x = true → graphFun G ∅ x = true := by
        intro x hdx hlx
        apply ab x ((andValOperands hleast.1 al ao x).mpr ?_)
        intro c
        rcases opposite b c with rfl | rfl
        · exact orStep_up (n := n) (by simp) (orReaches_reach d _ hr).1 hdx
        · exact orStep_up (n := n) (by simp) (orReaches_reach l _ hlr).1 hlx
      have hdl : d ≠ l := by
        intro heq
        obtain ⟨_, _, x, hx, hFx⟩ := junkData hl
        exact Bool.false_ne_true (hFx.symm.trans (hJ x (heq ▸ hx) hx))
      have hdE : s(u, v) ∈ gammaE G C d :=
        Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, u, v, rfl, hdv⟩
      have hlE : s(u, v) ∈ gammaE G C l :=
        Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, u, v, rfl, hlv⟩
      rcases member d hd with rfl | rfl <;> rcases member l hl with rfl | rfl
      · exact (hdl rfl).elim
      · exact Or.inr ⟨hJ, Finset.mem_inter.mpr ⟨hdE, hlE⟩⟩
      · exact Or.inr ⟨fun x hxj hxk => hJ x hxk hxj, Finset.mem_inter.mpr ⟨hlE, hdE⟩⟩
      · exact (hdl rfl).elim
lemma two_junk_two_extra_or_full_star_card_le_three
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (hempty : centreless G C = ∅) (hcard : (orN G C \ lam G C).card ≤ 2)
    (p : Fin n)
    (hstar : ∀ u v, s(u, v) ∈ Ustar G C ↔ G.Adj u v ∧ (u = p ∨ v = p))
    (j k : ℕ) (hpair : junk G C = {j, k}) :
    (Ustar G C).card ≤ 3 := by
  classical
  let O := (Ustar G C).filter (HasRawOpposite G C)
  have hOU : O ⊆ Ustar G C := Finset.filter_subset _ _
  have hroute : ∀ e ∈ O, HasRawOpposite G C e := fun e he => (Finset.mem_filter.mp he).2
  have hordinary := ordinary_full_star_card_le_extra hleast.1 hfour hempty p hstar O hOU hroute
  by_cases hJ : ∀ x, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true
  · let D := Ustar G C ∩ gammaE G C j ∩ gammaE G C k
    have hD : D.card ≤ 1 := two_joint_full_star_card_le_one G C hleast hT hfour hempty hcard p
      hstar j k hpair hJ
    have hcover : Ustar G C ⊆ O ∪ D := by
      intro e he
      rcases residual_ordinary_or_joint hleast hT j k hpair he with hraw | ⟨_, hboth⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hraw⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
          ⟨Finset.mem_inter.mpr ⟨he, (Finset.mem_inter.mp hboth).1⟩, (Finset.mem_inter.mp hboth).2⟩)
    have hcount := Finset.card_le_card hcover
    have hsum := Finset.card_union_le O D
    omega
  · have hUO : Ustar G C ⊆ O := by
      intro e he
      rcases residual_ordinary_or_joint hleast hT j k hpair he with hraw | ⟨hjoint, _⟩
      · exact Finset.mem_filter.mpr ⟨he, hraw⟩
      · exact (hJ hjoint).elim
    have hcount := Finset.card_le_card hUO
    omega
end TwoJunkFullStar
namespace EarlySources

open Budget OrdinaryCharge PEqualNP.CleanedNonEdge

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma early_raw_cover_shape (ao : IsAO2 n C) {m w : ℕ}
    (hm : m ∈ junk G C)
    (order : ∀ j ∈ junk G C, ∀ r ∈ orN G C \ lam G C, j < r)
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
  have hkl := hkm.trans (junkData hm).1
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
    have hmk := order m hm k hk
    omega
  obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hkL
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1 - b)).card)
  exact Or.inr ⟨z, fun t ht => cleanAdj ao ha b
    (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz⟩

lemma early_false_junk_cover (ao : IsAO2 n C) (top : TopForm G C)
    (order : ∀ j ∈ junk G C, ∀ r ∈ orN G C \ lam G C, j < r)
    (T : Finset (Sym2 (Fin n)))
    (x : Fin n → Bool) :
    ∀ j, j ∈ junk G C →
      (∀ u v : Fin n, s(u, v) ∈ T → gateVal n C j (pairInput u v) = true) →
      gateVal n C j x = false →
      ∃ S : Finset (Fin n), (S.card ≤ 1 ∨
        ∃ z : Fin n, ∀ t ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj t z) ∧
        (∀ u v : Fin n, s(u, v) ∈ T → u ∈ S ∨ v ∈ S) ∧
        ∀ t ∈ S, x t = false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj fires hx
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
    have firesOp (u v : Fin n) (he : s(u, v) ∈ T) :
        val C (List.ofFn (pairInput u v)) (opnd C j b) = true :=
      (andValOperands ao jl jo _).mp (fires u v he) b
    have direct (k : ℕ) (hk : k ∈ junk G C) (hr : OrReaches n C (opnd C j b) k) :
        opnd C j b = n + k := by
      rcases lastOrBefore (orReaches_reach k _ hr).1 with h | ⟨r, rl, ro, ri, rb, rp⟩
      · exact h
      · have hr' := lastOrOutside ao hk rl ro ri rb
        have hjr := order j hj r hr'
        have hle := orStep_le rp
        have hlt := opndBound ao jl b
        omega
    by_cases hd : ∃ k, k ∈ junk G C ∧ opnd C j b = n + k
    · obtain ⟨k, hk, he⟩ := hd
      have hbnd := opndBound ao jl b
      have hkj : k < j := by omega
      apply ih k hkj hk
      · intro u v hu
        have hv := firesOp u v hu
        rw [he] at hv
        exact hv
      · rw [he] at hb
        exact hb
    · refine ⟨orIn n C (opnd C j b), early_raw_cover_shape ao hj order (by
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


def Served (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j m : ℕ) (e : Sym2 (Fin n)) : Prop :=
  ∃ a ∈ tops G C, ∃ b : Fin 2,
    OrReaches n C (opnd C a b) j ∧
    Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m) ∧
    e ∈ gammaE G C j ∧ ∃ w ∈ side C a (1 - b), w ∈ e

lemma early_served_card_le_one
    (hAO : IsAO2 n C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (order : ∀ j ∈ junk G C, ∀ r ∈ orN G C \ lam G C, j < r)
    (T : Finset (Sym2 (Fin n))) (hTU : T ⊆ Ustar G C)
    (j m : ℕ) (hj : j ∈ junk G C) (hm : (orIn n C (n + m)).Nonempty)
    (hserved : ∀ e ∈ T, Served G C j m e) : T.card ≤ 1 := by
  obtain ⟨t, ht⟩ := hm
  have fires : ∀ u v : Fin n, s(u, v) ∈ T → gateVal n C j (pairInput u v) = true := by
    intro u v huv
    obtain ⟨a, ha, b, hr, hp, hgamma, _⟩ := hserved s(u, v) huv
    exact gate_accepts_pair_of_gammaE hgamma
  apply cover_property_card_le_one G T color hbip
    (common_neighbors_unique_of_card_le_one G hfour)
    (fun u v huv => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hTU huv)).1) t
  intro u v huv
  obtain ⟨a, ha, b, hr, hp, _, w, hw, hwe⟩ := hserved s(u, v) huv
  have ht' : t ∈ side C a b := reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
  have hclean := cleanAdj hAO ha b ht' hw
  refine ⟨w, Sym2.mem_iff.mp hwe, (SimpleGraph.deleteEdges_adj.mp hclean).1,
    fun h => (SimpleGraph.deleteEdges_adj.mp hclean).2 (hTU h), ?_⟩
  intro x hx hind
  have hnone : ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
    rintro ⟨a, b, hab, ha, hb⟩
    exact Bool.false_ne_true ((hind a b hab ha).symm.trans hb)
  have hF : graphFun G ∅ x = false := by simp [graphFun, hnone]
  have hjfalse : gateVal n C j x = false := by
    apply Bool.eq_false_iff.mpr
    intro hjtrue
    have hFx := firingTop hAO ha (orReaches_reach j _ hr).1 hw x hjtrue hx
    exact Bool.false_ne_true (hF.symm.trans hFx)
  obtain ⟨S, hshape, hcover, hfalse⟩ := early_false_junk_cover hAO hT order T x j hj fires hjfalse
  refine ⟨S, ?_, hcover, hfalse⟩
  rcases hshape with hsmall | ⟨z, hz⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨z, fun y hy => ⟨(SimpleGraph.deleteEdges_adj.mp (hz y hy)).1,
      fun h => (SimpleGraph.deleteEdges_adj.mp (hz y hy)).2 (hTU h)⟩⟩

lemma early_served_edges_equal
    (hAO : IsAO2 n C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (order : ∀ j ∈ junk G C, ∀ r ∈ orN G C \ lam G C, j < r)
    (j m : ℕ) (hj : j ∈ junk G C) (hm : (orIn n C (n + m)).Nonempty)
    {e d : Sym2 (Fin n)} (he : e ∈ Ustar G C) (hd : d ∈ Ustar G C)
    (heS : Served G C j m e) (hdS : Served G C j m d) : e = d := by
  classical
  have hsub : ({e, d} : Finset (Sym2 (Fin n))) ⊆ Ustar G C := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact he
    · exact hd
  have hs : ∀ f ∈ ({e, d} : Finset (Sym2 (Fin n))), Served G C j m f := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact heS
    · exact hdS
  have hcard := early_served_card_le_one hAO hT hfour color hbip order {e, d} hsub j m hj hm hs
  exact Finset.card_le_one.mp hcard e (by simp) d (by simp)

end EarlySources
namespace EarlySources

open Budget OrdinaryCharge PEqualNP.CleanedNonEdge

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def RootedOrdinary (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (e : Sym2 (Fin n)) : Prop :=
  ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
    OrReaches n C (opnd C a b) j ∧ e ∈ gammaE G C j ∧
      ∃ w ∈ side C a (1 - b), w ∈ e

lemma raw_boundary_on_dirty_path (hAO : IsAO2 n C) {j w : ℕ}
    (hj : j ∈ junk G C)
    (hr : Relation.ReflTransGen (OrStep n C) w (n + j))
    (hraw : (orIn n C w).Nonempty) :
    ∃ m ∈ orN G C \ lam G C, (orIn n C (n + m)).Nonempty ∧
      Relation.ReflTransGen (OrStep n C) w (n + m) ∧
      ∃ c ∈ (gateAt C m).inputs, orIn n C c = ∅ ∧
        Relation.ReflTransGen (OrStep n C) c (n + j) := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rw [andRawEmpty (junkData hj).2.1] at hraw
    exact (Finset.not_nonempty_empty hraw).elim
  | @head w c hstep hrest ih =>
    obtain ⟨m, hm, rfl, hmo, hmi, hmb⟩ := hstep
    by_cases hc : (orIn n C c).Nonempty
    · obtain ⟨l, hl, hlraw, hcl, hd⟩ := ih hc
      exact ⟨l, hl, hlraw, .head ⟨m, hm, rfl, hmo, hmi, hmb⟩ hcl, hd⟩
    · have hcn := orStep_le hrest
      obtain ⟨k, rfl⟩ : ∃ k, c = n + k := ⟨c - n, by omega⟩
      have hkempty : orIn n C (n + k) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
      have hkdirty : ¬ BelowF G C k := by
        intro hb
        obtain ⟨_, _, x, hjx, hFx⟩ := junkData hj
        have hkx := orStep_up (n := n) (by simp) hrest hjx
        exact Bool.false_ne_true (hFx.symm.trans (hb x hkx))
      exact ⟨m, emptyInputOutside hAO hkdirty hkempty hm hmo hmi, hraw, .refl,
        n + k, hmi, hkempty, hrest⟩

lemma empty_raw_path_direct (hAO : IsAO2 n C)
    (hall : ∀ m ∈ orN G C \ lam G C, (orIn n C (n + m)).Nonempty)
    {c j : ℕ} (hj : j ∈ junk G C) (hc : orIn n C c = ∅)
    (hr : Relation.ReflTransGen (OrStep n C) c (n + j)) : c = n + j := by
  rcases lastOrBefore hr with h | ⟨m, hm, hmo, hmi, hmb, hp⟩
  · exact h
  · have hmR := lastOrOutside hAO hj hm hmo hmi hmb
    obtain ⟨v, hv⟩ := hall m hmR
    have hvc := reach_mem_orIn v (hp.trans (mem_orIn_reach v hv))
    simp [hc] at hvc

lemma rooted_ordinary_boundary (hAO : IsAO2 n C) (hempty : centreless G C = ∅)
    {e : Sym2 (Fin n)} (he : RootedOrdinary G C e) :
    ∃ j ∈ junk G C, ∃ m ∈ orN G C \ lam G C,
      (orIn n C (n + m)).Nonempty ∧ Served G C j m e ∧
      ∃ c ∈ (gateAt C m).inputs, orIn n C c = ∅ ∧
        Relation.ReflTransGen (OrStep n C) c (n + j) := by
  obtain ⟨a, ha, b, j, hj, hr, hgamma, w, hw, hwe⟩ := he
  obtain ⟨m, hm, hraw, hp, hboundary⟩ := raw_boundary_on_dirty_path hAO hj
    (orReaches_reach j _ hr).1 (topSides hempty ha b)
  exact ⟨j, hj, m, hm, hraw, ⟨a, ha, b, hr, hp, hgamma, w, hw, hwe⟩, hboundary⟩

lemma nonempty_extra_unique_of_empty
    (hcard : (orN G C \ lam G C).card ≤ 2)
    {m0 m l : ℕ} (hm0 : m0 ∈ orN G C \ lam G C) (hz : orIn n C (n + m0) = ∅)
    (hm : m ∈ orN G C \ lam G C) (hnm : (orIn n C (n + m)).Nonempty)
    (hl : l ∈ orN G C \ lam G C) (hnl : (orIn n C (n + l)).Nonempty) : m = l := by
  classical
  by_contra hml
  have hm0m : m0 ≠ m := by intro h; rw [← h, hz] at hnm; exact Finset.not_nonempty_empty hnm
  have hm0l : m0 ≠ l := by intro h; rw [← h, hz] at hnl; exact Finset.not_nonempty_empty hnl
  have hsub : {m0, m, l} ⊆ orN G C \ lam G C := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hm0
    · exact hm
    · exact hl
  have hbound := Finset.card_le_card hsub
  have hthree : ({m0, m, l} : Finset ℕ).card = 3 := by simp [hm0m, hm0l, hml]
  omega


end EarlySources
def GlobalCoverProperty {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (U : Finset (Sym2 V)) : Prop :=
  ∀ x : V → Bool,
    (∀ a b, G.Adj a b → x a = true → x b = false) →
    ∃ S : Finset V,
      (S.card ≤ 1 ∨ ∃ z, ∀ y ∈ S, G.Adj y z ∧ s(y, z) ∉ U) ∧
      (∀ p q, s(p, q) ∈ U → p ∈ S ∨ q ∈ S) ∧
      ∀ y ∈ S, x y = false
lemma global_cover_property_card_le_one {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (U : Finset (Sym2 V)) (color : V → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m)
    (hUadj : ∀ u v, s(u, v) ∈ U → G.Adj u v)
    (hproperty : GlobalCoverProperty G U) : U.card ≤ 1 := by
  classical
  have finish (S : Finset V) (z : V)
      (hz : ∀ w ∈ S, G.Adj w z ∧ s(w, z) ∉ U)
      (hcover : ∀ u v, s(u, v) ∈ U → u ∈ S ∨ v ∈ S) : U.card ≤ 1 := by
    apply cover_property_card_le_one G U color hbip hfour hUadj z
    intro u v huv
    have hex : ∃ w ∈ S, w = u ∨ w = v := by
      rcases hcover u v huv with hu | hv
      · exact ⟨u, hu, Or.inl rfl⟩
      · exact ⟨v, hv, Or.inr rfl⟩
    obtain ⟨w, hw, hend⟩ := hex
    refine ⟨w, hend, (hz w hw).1.symm, ?_, ?_⟩
    · simpa only [Sym2.eq_swap] using (hz w hw).2
    · intro x _ hind
      exact hproperty x hind
  by_cases hU : U.Nonempty
  · obtain ⟨S, hshape, hcover, _⟩ := hproperty (fun _ => false)
      (by intro a b hab ha; exact (Bool.false_ne_true ha).elim)
    rcases hshape with hsmall | ⟨z, hz⟩
    · have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := hU
        induction e using Sym2.ind with
        | h u v =>
          rcases hcover u v he with hu | hv
          · exact ⟨u, hu⟩
          · exact ⟨v, hv⟩
      obtain ⟨t, ht⟩ := hSne
      have hsingle : ∀ v ∈ S, v = t := fun v hv =>
        Finset.card_le_one.mp hsmall v hv t ht
      let x : V → Bool := fun v => decide (v = t)
      have hxt : x t = true := by simp [x]
      have hind : ∀ a b, G.Adj a b → x a = true → x b = false := by
        intro a b hab ha
        have hat : a = t := by simpa [x] using ha
        have hbt : b ≠ t := by
          intro h
          subst a
          subst b
          exact G.irrefl hab
        simpa [x] using hbt
      obtain ⟨T, hTshape, hTcover, hTfalse⟩ := hproperty x hind
      have hnt : t ∉ T := by
        intro htT
        exact Bool.false_ne_true ((hTfalse t htT).symm.trans hxt)
      rcases hTshape with hTsmall | ⟨z, hz⟩
      · have orient : ∀ e ∈ U, ∃ w ∈ T, e = s(t, w) := by
          intro e he
          induction e using Sym2.ind with
          | h u v =>
            rcases hcover u v he with hu | hv
            · have hut := hsingle u hu
              have hvT : v ∈ T := (hTcover u v he).resolve_left (hut ▸ hnt)
              exact ⟨v, hvT, by rw [hut]⟩
            · have hvt := hsingle v hv
              have huT : u ∈ T := (hTcover u v he).resolve_right (hvt ▸ hnt)
              exact ⟨u, huT, by rw [hvt]; exact Sym2.eq_swap⟩
        apply Finset.card_le_one.mpr
        intro e he d hd
        obtain ⟨v, hv, rfl⟩ := orient e he
        obtain ⟨w, hw, rfl⟩ := orient d hd
        exact congrArg (fun w => s(t, w)) (Finset.card_le_one.mp hTsmall v hv w hw)
      · exact finish T z hz hTcover
    · exact finish S z hz hcover
  · simp [Finset.not_nonempty_iff_eq_empty.mp hU]
lemma basic_clean_cnf_card_le_one {V I : Type} [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) (U : Finset (Sym2 V)) (color : V → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m)
    (hUadj : ∀ u v, s(u, v) ∈ U → G.Adj u v)
    (F : Finset I) (clause : I → Finset V)
    (hshape : ∀ i ∈ F, (clause i).card ≤ 1 ∨
      ∃ z, ∀ y ∈ clause i, G.Adj y z ∧ s(y, z) ∉ U)
    (hcover : ∀ u v, s(u, v) ∈ U → ∀ i ∈ F, u ∈ clause i ∨ v ∈ clause i)
    (hsound : ∀ x : V → Bool, (∀ i ∈ F, ∃ w ∈ clause i, x w = true) →
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) : U.card ≤ 1 := by
  classical
  apply global_cover_property_card_le_one G U color hbip hfour hUadj
  intro x hind
  have missing : ∃ i ∈ F, ∀ w ∈ clause i, x w = false := by
    by_contra hn
    have hall : ∀ i ∈ F, ∃ w ∈ clause i, x w = true := by
      intro i hi
      by_contra hmiss
      apply hn
      exact ⟨i, hi, fun w hw => Bool.eq_false_iff.mpr (fun hx => hmiss ⟨w, hw, hx⟩)⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsound x hall
    exact Bool.false_ne_true ((hind a b hab ha).symm.trans hb)
  obtain ⟨i, hi, hmiss⟩ := missing
  exact ⟨clause i, hshape i hi, fun u v huv => hcover u v huv i hi, hmiss⟩
namespace EarlySources

open Budget OrdinaryCharge PEqualNP.CleanedNonEdge

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma early_joint_card_le_one
    (hAO : IsAO2 n C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (order : ∀ j ∈ junk G C, ∀ r ∈ orN G C \ lam G C, j < r)
    (T : Finset (Sym2 (Fin n))) (hTU : T ⊆ Ustar G C)
    (j k : ℕ) (hj : j ∈ junk G C) (hk : k ∈ junk G C)
    (hposj : ∀ e ∈ T, e ∈ gammaE G C j) (hposk : ∀ e ∈ T, e ∈ gammaE G C k)
    (hjoint : ∀ x, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true) :
    T.card ≤ 1 := by
  apply global_cover_property_card_le_one G T color hbip
    (common_neighbors_unique_of_card_le_one G hfour)
    (fun u v huv => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hTU huv)).1)
  intro x hind
  have hnone : ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
    rintro ⟨a, b, hab, ha, hb⟩
    exact Bool.false_ne_true ((hind a b hab ha).symm.trans hb)
  have hF : graphFun G ∅ x = false := by simp [graphFun, hnone]
  have finish (r : ℕ) (hr : r ∈ junk G C)
      (hpos : ∀ e ∈ T, e ∈ gammaE G C r) (hrfalse : gateVal n C r x = false) :
      ∃ S : Finset (Fin n),
        (S.card ≤ 1 ∨ ∃ z, ∀ y ∈ S, G.Adj y z ∧ s(y, z) ∉ T) ∧
        (∀ p q, s(p, q) ∈ T → p ∈ S ∨ q ∈ S) ∧ ∀ y ∈ S, x y = false := by
    have fires : ∀ u v : Fin n, s(u, v) ∈ T → gateVal n C r (pairInput u v) = true :=
      fun u v huv => gate_accepts_pair_of_gammaE (hpos s(u, v) huv)
    obtain ⟨S, hshape, hcover, hfalse⟩ := early_false_junk_cover hAO hT order T x r hr fires hrfalse
    refine ⟨S, ?_, hcover, hfalse⟩
    rcases hshape with hsmall | ⟨z, hz⟩
    · exact Or.inl hsmall
    · exact Or.inr ⟨z, fun y hy => ⟨(SimpleGraph.deleteEdges_adj.mp (hz y hy)).1,
        fun h => (SimpleGraph.deleteEdges_adj.mp (hz y hy)).2 (hTU h)⟩⟩
  by_cases hjfalse : gateVal n C j x = false
  · exact finish j hj hposj hjfalse
  · have hjtrue := Bool.eq_true_of_not_eq_false hjfalse
    have hkfalse : gateVal n C k x = false := by
      apply Bool.eq_false_iff.mpr
      intro hktrue
      exact Bool.false_ne_true (hF.symm.trans (hjoint x hjtrue hktrue))
    exact finish k hk hposk hkfalse

lemma residual_rooted_ordinary_or_joint
    (hleast : IsLeastAO G C) (hT : TopForm G C)
    (j k : ℕ) (hpair : junk G C = {j, k})
    {e : Sym2 (Fin n)} (he : e ∈ Ustar G C) :
    RootedOrdinary G C e ∨
      (∀ x, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true) ∧
      e ∈ gammaE G C j ∩ gammaE G C k := by
  have member : ∀ d ∈ junk G C, d = j ∨ d = k := by
    intro d hd
    simpa only [hpair, Finset.mem_insert, Finset.mem_singleton] using hd
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨a, ha, b, d, hd, hav, hr, hdv⟩ := residualTrace hleast hT he
    obtain ⟨al, ao, ab⟩ := topData ha
    have hv := (andValOperands hleast.1 al ao _).mp hav (1 - b)
    rcases operandSupport hleast.1 hT al ao hv with ⟨w, hw, hwe⟩ | ⟨l, hl, hlr, hlv⟩
    · left
      exact ⟨a, ha, b, d, hd, hr,
        Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, u, v, rfl, hdv⟩,
        w, hw, Sym2.mem_iff.mpr hwe⟩
    · have hJ : ∀ x, gateVal n C d x = true → gateVal n C l x = true → graphFun G ∅ x = true := by
        intro x hdx hlx
        apply ab x ((andValOperands hleast.1 al ao x).mpr ?_)
        intro c
        rcases opposite b c with rfl | rfl
        · exact orStep_up (n := n) (by simp) (orReaches_reach d _ hr).1 hdx
        · exact orStep_up (n := n) (by simp) (orReaches_reach l _ hlr).1 hlx
      have hdl : d ≠ l := by
        intro heq
        obtain ⟨_, _, x, hx, hFx⟩ := junkData hl
        exact Bool.false_ne_true (hFx.symm.trans (hJ x (heq ▸ hx) hx))
      have hdE : s(u, v) ∈ gammaE G C d :=
        Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, u, v, rfl, hdv⟩
      have hlE : s(u, v) ∈ gammaE G C l :=
        Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, u, v, rfl, hlv⟩
      rcases member d hd with rfl | rfl <;> rcases member l hl with rfl | rfl
      · exact (hdl rfl).elim
      · exact Or.inr ⟨hJ, Finset.mem_inter.mpr ⟨hdE, hlE⟩⟩
      · exact Or.inr ⟨fun x hxj hxk => hJ x hxk hxj, Finset.mem_inter.mpr ⟨hlE, hdE⟩⟩
      · exact (hdl rfl).elim



end EarlySources
namespace ExceptionalCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583_aux.Budget
variable {n : ℕ}
def Basic (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) : Prop :=
  S.card ≤ 1 ∨ ∃ z, ∀ y ∈ S, G.Adj y z ∧ s(y, z) ∉ U
def Property (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n)))
    (w : Fin n) (S0 : Finset (Fin n)) : Prop :=
  ∀ x : Fin n → Bool, x w = true →
    (∀ a b, G.Adj a b → x a = true → x b = false) →
    ∃ S : Finset (Fin n), (Basic G U S ∨ S = S0) ∧
      (∀ p q, s(p, q) ∈ U → p ∈ S ∨ q ∈ S) ∧ ∀ y ∈ S, x y = false
lemma basic_same_color (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n)))
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    {S : Finset (Fin n)} (hS : Basic G U S) {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S) :
    color a = color b := by
  rcases hS with hsmall | ⟨z, hz⟩
  · exact congrArg color (Finset.card_le_one.mp hsmall a ha b hb)
  · exact bool_eq_of_ne_common _ _ _ (hbip a z (hz a ha).1) (hbip b z (hz b hb).1)
lemma basic_star_endpoints_equal (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n)))
    (hfour : ∀ a b, a ≠ b → ∀ l m, G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m)
    {S : Finset (Fin n)} (hS : Basic G U S) {p q w : Fin n}
    (hp : p ∈ S) (hq : q ∈ S) (hpU : s(p, w) ∈ U) (hqU : s(q, w) ∈ U)
    (hpw : G.Adj p w) (hqw : G.Adj q w) : p = q := by
  rcases hS with hsmall | ⟨z, hz⟩
  · exact Finset.card_le_one.mp hsmall p hp q hq
  · have hwz : w ≠ z := by
      intro h
      exact (hz p hp).2 (h ▸ hpU)
    exact hfour w z hwz p q hpw.symm (hz p hp).1.symm hqw.symm (hz q hq).1.symm
lemma exceptional_cover_card_le_two
    (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m, G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m)
    (hUadj : ∀ u v, s(u, v) ∈ U → G.Adj u v)
    (t : Fin n) (A B : Finset (Fin n)) (hA : Basic G U A) (hB : Basic G U B)
    (hcover : ∀ p q, s(p, q) ∈ U → p ∈ A ∪ B ∨ q ∈ A ∪ B)
    (hsource : ∀ u v, s(u, v) ∈ U → ∃ w,
      (w = u ∨ w = v) ∧ G.Adj t w ∧ s(t, w) ∉ U ∧ Property G U w (A ∪ B)) :
    U.card ≤ 2 := by
  classical
  have orient : ∀ e ∈ U, ∃ p w, e = s(p, w) ∧ G.Adj p w ∧ G.Adj t w ∧
      s(t, w) ∉ U ∧ Property G U w (A ∪ B) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨w, hw, htw, hclean, hlocal⟩ := hsource a b he
      rcases hw with ha | hb
      · subst w
        exact ⟨b, a, Sym2.eq_swap, (hUadj a b he).symm, htw, hclean, hlocal⟩
      · subst w
        exact ⟨a, b, rfl, hUadj a b he, htw, hclean, hlocal⟩
  choose p w hd using (fun e : U => orient e.val e.property)
  have hmem (e : U) : s(p e, w e) ∈ U := (hd e).1 ▸ e.property
  have hadj (e : U) : G.Adj (p e) (w e) := (hd e).2.1
  have hclean (e : U) : s(t, w e) ∉ U := (hd e).2.2.2.1
  have hpencil (e : U) : G.Adj t (w e) := (hd e).2.2.1
  have hprop (e : U) : Property G U (w e) (A ∪ B) := (hd e).2.2.2.2
  by_cases hex : ∃ e : U, w e ∈ A ∪ B
  · obtain ⟨e, he⟩ := hex
    have hlocal : LocalCoverProperty G U (w e) := by
      intro x hx hind
      obtain ⟨S, hS, hcov, hfalse⟩ := hprop e x hx hind
      rcases hS with hs | rfl
      · exact ⟨S, hs, hcov, hfalse⟩
      · exact (Bool.false_ne_true ((hfalse (w e) he).symm.trans hx)).elim
    have hall : ∀ f : U, e.val = f.val := by
      intro f
      rw [(hd e).1, (hd f).1]
      exact clean_pencil_edges_equal G U color hbip hfour t (p e) (w e) (p f) (w f)
        (hmem e) (hmem f) (hadj e) (hadj f) (hpencil e) (hpencil f) (hclean e) hlocal
    have hcard : U.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb =>
      (hall ⟨a, ha⟩).symm.trans (hall ⟨b, hb⟩))
    omega
  · have hwout : ∀ e : U, w e ∉ A ∪ B := fun e he => hex ⟨e, he⟩
    have hpin (e : U) : p e ∈ A ∪ B := (hcover _ _ (hmem e)).resolve_right (hwout e)
    have hwcommon : ∀ e f : U, w e = w f := by
      intro e f
      by_contra hne
      have hpft : p f ≠ t := by
        intro h
        exact hclean f (h ▸ hmem f)
      have hcross : ¬ G.Adj (w e) (p f) := by
        intro hc
        exact hne (hfour (p f) t hpft (w e) (w f) hc.symm (hpencil e) (hadj f) (hpencil f))
      let x := pairInput (w e) (p f)
      have hind : ∀ a b, G.Adj a b → x a = true → x b = false := by
        intro a b hab ha
        apply Bool.eq_false_iff.mpr
        intro hb
        rcases (pairInput_true (w e) (p f) a).mp ha with rfl | rfl <;>
          rcases (pairInput_true (w e) (p f) b).mp hb with rfl | rfl
        · exact G.irrefl hab
        · exact hcross hab
        · exact hcross hab.symm
        · exact G.irrefl hab
      obtain ⟨S, hS, hcov, hfalse⟩ := hprop e x (pairInput_left _ _) hind
      have hbasic : Basic G U S := by
        rcases hS with hs | rfl
        · exact hs
        · exact (Bool.false_ne_true ((hfalse (p f) (hpin f)).symm.trans (pairInput_right _ _))).elim
      have hpe : p e ∈ S := by
        rcases hcov _ _ (hmem e) with hp | hw
        · exact hp
        · exact (Bool.false_ne_true ((hfalse (w e) hw).symm.trans (pairInput_left _ _))).elim
      have hwf : w f ∈ S := by
        rcases hcov _ _ (hmem f) with hp | hw
        · exact (Bool.false_ne_true ((hfalse (p f) hp).symm.trans (pairInput_right _ _))).elim
        · exact hw
      have hc := basic_same_color G U color hbip hbasic hpe hwf
      have hwc : color (w e) = color (w f) := bool_eq_of_ne_common _ _ _
        (hbip _ _ (hpencil e).symm) (hbip _ _ (hpencil f).symm)
      exact hbip _ _ (hadj e) (hc.trans hwc.symm)
    let tag : U → Bool := fun e => decide (p e ∈ A)
    have hinj : Function.Injective tag := by
      intro e f htag
      have hpepf : p e = p f := by
        by_cases heA : p e ∈ A
        · have hfA : p f ∈ A := by simpa [tag, heA] using htag.symm
          apply basic_star_endpoints_equal G U hfour hA heA hfA (hmem e)
          · simpa only [hwcommon f e] using hmem f
          · exact hadj e
          · simpa only [hwcommon f e] using hadj f
        · have hfA : p f ∉ A := by simpa [tag, heA] using htag.symm
          have heB : p e ∈ B := (Finset.mem_union.mp (hpin e)).resolve_left heA
          have hfB : p f ∈ B := (Finset.mem_union.mp (hpin f)).resolve_left hfA
          apply basic_star_endpoints_equal G U hfour hB heB hfB (hmem e)
          · simpa only [hwcommon f e] using hmem f
          · exact hadj e
          · simpa only [hwcommon f e] using hadj f
      apply Subtype.ext
      rw [(hd e).1, (hd f).1, hpepf, hwcommon e f]
    have hcard := Fintype.card_le_of_injective tag hinj
    simpa using hcard
end ExceptionalCover
namespace EffectiveExtra
open Budget
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma one_effective_extra_or_source
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hempty : centreless G C = ∅)
    (m : ℕ)
    (hactive : ∀ l ∈ orN G C \ lam G C, ∀ j ∈ junk G C,
      Relation.ReflTransGen (OrStep n C) (n + l) (n + j) → l = m)
    (hU : (Ustar G C).Nonempty) :
    ∃ j ∈ junk G C, j < m ∧ ∃ t : Fin n,
      (∀ u v, s(u, v) ∈ Ustar G C → gateVal n C j (pairInput u v) = true) ∧
      ∀ e ∈ Ustar G C, ∃ p b : Fin n,
        e = s(p, b) ∧ (G.deleteEdges ↑(Ustar G C)).Adj p t ∧
        ∀ x : Fin n → Bool, x p = true → graphFun G ∅ x = false →
          gateVal n C j x = false := by
  obtain ⟨e, he⟩ := hU
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨a, ha, b, j, hj, _, hr, _⟩ := residualTrace hleast hT he
    obtain ⟨l, hl, hli, path⟩ := residualPath hleast.1 hempty ha hj hr
    have hlpath := extra_or_direct_path hleast.1 hl hli
    have hlm := hactive l hl j hj hlpath
    subst l
    have hraw : (orIn n C (n + m)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hz
      rcases lastOrBefore path with heq | ⟨k, hk, hko, hki, hkb, _⟩
      · have hne := topSides hempty ha b
        change (orIn n C (opnd C a b)).Nonempty at hne
        rw [heq, hz] at hne
        exact Finset.not_nonempty_empty hne
      · have hkR := emptyInputOutside hleast.1 (orData hl).2.2 hz hk hko hki
        have hkpath : Relation.ReflTransGen (OrStep n C) (n + k) (n + j) :=
          (extra_or_direct_path hleast.1 hkR hki).trans hlpath
        have hkm := hactive k hkR j hj hkpath
        omega
    obtain ⟨t, ht⟩ := hraw
    have hlt := hleast.1.2.1 m (orData hl).1 (n + j) hli
    refine ⟨j, hj, by omega, t, ?_, ?_⟩
    · intro p q hpq
      obtain ⟨a', ha', b', k, hk, _, hr', hkv⟩ := residualTrace hleast hT hpq
      obtain ⟨l, hl', hli', _⟩ := residualPath hleast.1 hempty ha' hk hr'
      have hlm := hactive l hl' k hk (extra_or_direct_path hleast.1 hl' hli')
      subst l
      have hjk := singleJunkInput hleast.1 hl ⟨t, ht⟩ hj hk hli hli'
      rwa [hjk]
    · intro f hf
      induction f using Sym2.ind with
      | h p q =>
        obtain ⟨a', ha', b', k, hk, hav, hr', _⟩ := residualTrace hleast hT hf
        obtain ⟨l, hl', hli', hp⟩ := residualPath hleast.1 hempty ha' hk hr'
        have hlm := hactive l hl' k hk (extra_or_direct_path hleast.1 hl' hli')
        subst l
        have hend : ∃ w ∈ side C a' (1 - b'), w = p ∨ w = q := by
          obtain ⟨al, ao, ab⟩ := topData ha'
          have hv := (andValOperands hleast.1 al ao _).mp hav (1 - b')
          rcases operandSupport hleast.1 hT al ao hv with h | ⟨d, hd, hdreach, _⟩
          · exact h
          · obtain ⟨l, hl'', hli'', hp'⟩ := residualPath hleast.1 hempty ha' hd hdreach
            have hlm := hactive l hl'' d hd (extra_or_direct_path hleast.1 hl'' hli'')
            subst l
            exfalso
            apply (orData hl).2.2
            intro x hx
            apply ab x ((andValOperands hleast.1 al ao x).mpr ?_)
            intro c
            rcases opposite b' c with rfl | rfl
            · exact orStep_up (n := n) (by simp) hp hx
            · exact orStep_up (n := n) (by simp) hp' hx
        obtain ⟨w, hw, hend⟩ := hend
        have ht' : t ∈ side C a' b' :=
          reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
        have hclean := (cleanAdj hleast.1 ha' b' ht' hw).symm
        have safe (x : Fin n → Bool) (hx : x w = true) (hF : graphFun G ∅ x = false) :
            gateVal n C j x = false := by
          apply Bool.eq_false_iff.mpr
          intro hjx
          have hmx : gateVal n C m x = true :=
            (val_or (n := n) (by simp) (orData hl).1 (orData hl).2.1).mpr
              ⟨n + j, hli, hlt, hjx⟩
          exact Bool.false_ne_true (hF.symm.trans (firingTop hleast.1 ha' hp hw x hmx hx))
        rcases hend with hwp | hwq
        · exact ⟨w, q, by rw [hwp], hclean, safe⟩
        · exact ⟨w, p, by rw [hwq]; exact Sym2.eq_swap, hclean, safe⟩
end EffectiveExtra
namespace PureExceptional
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge Budget ExceptionalCover
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma raw_shape_or_extra (ao : IsAO2 n C) {w : ℕ}
    (hw : w < n + C.gates.length) :
    Basic G (Ustar G C) (orIn n C w) ∨
      ∃ r ∈ orN G C \ lam G C, w = n + r := by
  by_cases hcard : (orIn n C w).card ≤ 1
  · exact Or.inl (Or.inl hcard)
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
  have hkl : k < C.gates.length := by omega
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
  by_cases hkL : k ∈ lam G C
  swap
  · exact Or.inr ⟨k, Finset.mem_sdiff.mpr ⟨hkN, hkL⟩, rfl⟩
  obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hkL
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1 - b)).card)
  exact Or.inl (Or.inr ⟨z, fun t ht => SimpleGraph.deleteEdges_adj.mp (cleanAdj ao ha b
    (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz)⟩)
lemma raw_shape_before_mix (ao : IsAO2 n C) {m0 m w : ℕ}
    (hm : m ∈ orN G C \ lam G C)
    (only : ∀ r ∈ orN G C \ lam G C, r = m0 ∨ r = m)
    (hw : w < n + m) :
    Basic G (Ustar G C) (orIn n C w) ∨ m0 < m ∧ orIn n C w = orIn n C (n + m0) := by
  rcases raw_shape_or_extra (G := G) ao (hw.trans (Nat.add_lt_add_left (orData hm).1 n)) with hs | ⟨r, hr, he⟩
  · exact Or.inl hs
  · rcases only r hr with rfl | rfl
    · exact Or.inr ⟨by omega, congrArg (orIn n C) he⟩
    · omega
lemma raw_union_operands (ao : IsAO2 n C) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    orIn n C (n + r) = orIn n C (opnd C r 0) ∪ orIn n C (opnd C r 1) := by
  ext t
  constructor
  · intro ht
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach t ht) with h | ⟨w, hs, hp⟩
    · have htlt := t.isLt
      omega
    · obtain ⟨k, hk, he, hko, hwi, hwb⟩ := hs
      have hkr : k = r := by omega
      subst k
      obtain ⟨b, rfl⟩ := inputsAsOpnd ao hr hwi
      have hmem := reach_mem_orIn t hp
      fin_cases b
      · exact Finset.mem_union_left _ hmem
      · exact Finset.mem_union_right _ hmem
  · intro ht
    rcases Finset.mem_union.mp ht with h0 | h1
    · exact reach_mem_orIn t (.head ⟨r, hr, rfl, hop, opndMem ao hr 0, opndBound ao hr 0⟩
        (mem_orIn_reach t h0))
    · exact reach_mem_orIn t (.head ⟨r, hr, rfl, hop, opndMem ao hr 1, opndBound ao hr 1⟩
        (mem_orIn_reach t h1))
lemma exceptional_raw_two_basic (ao : IsAO2 n C) {m0 m : ℕ}
    (hm0 : m0 ∈ orN G C \ lam G C) (hlt : m0 < m)
    (only : ∀ r ∈ orN G C \ lam G C, r = m0 ∨ r = m) :
    ∃ A B : Finset (Fin n), Basic G (Ustar G C) A ∧ Basic G (Ustar G C) B ∧
      orIn n C (n + m0) = A ∪ B := by
  have basic (b : Fin 2) : Basic G (Ustar G C) (orIn n C (opnd C m0 b)) := by
    have hw := opndBound ao (orData hm0).1 b
    rcases raw_shape_or_extra (G := G) ao (hw.trans (Nat.add_lt_add_left (orData hm0).1 n)) with hs | ⟨r, hr, he⟩
    · exact hs
    · rcases only r hr with rfl | rfl <;> omega
  exact ⟨orIn n C (opnd C m0 0), orIn n C (opnd C m0 1), basic 0, basic 1,
    raw_union_operands ao (orData hm0).1 (orData hm0).2.1⟩
lemma exceptional_false_junk_cover (ao : IsAO2 n C) (top : TopForm G C)
    {m0 m : ℕ} (hm : m ∈ orN G C \ lam G C)
    (only : ∀ r ∈ orN G C \ lam G C, r = m0 ∨ r = m)
    (blocked : ∀ j ∈ junk G C,
      ¬ Relation.ReflTransGen (OrStep n C) (n + m0) (n + j))
    (T : Finset (Sym2 (Fin n)))
    (x : Fin n → Bool) :
    ∀ j, j ∈ junk G C → j < m →
      (∀ u v : Fin n, s(u, v) ∈ T → gateVal n C j (pairInput u v) = true) →
      gateVal n C j x = false →
      ∃ S : Finset (Fin n), (Basic G (Ustar G C) S ∨ m0 < m ∧ S = orIn n C (n + m0)) ∧
        (∀ u v : Fin n, s(u, v) ∈ T → u ∈ S ∨ v ∈ S) ∧
        ∀ t ∈ S, x t = false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hjm fires hx
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
    have firesOp (u v : Fin n) (he : s(u, v) ∈ T) :
        val C (List.ofFn (pairInput u v)) (opnd C j b) = true :=
      (andValOperands ao jl jo _).mp (fires u v he) b
    have direct (k : ℕ) (hk : k ∈ junk G C) (hr : OrReaches n C (opnd C j b) k) :
        opnd C j b = n + k := by
      rcases lastOrBefore (orReaches_reach k _ hr).1 with h | ⟨r, rl, ro, ri, rb, rp⟩
      · exact h
      · have hr' := lastOrOutside ao hk rl ro ri rb
        rcases only r hr' with he | he
        · subst r
          exact (blocked k hk (EffectiveExtra.extra_or_direct_path ao hr' ri)).elim
        · subst r
          have hle := orStep_le rp
          have hlt := opndBound ao jl b
          omega
    by_cases hd : ∃ k, k ∈ junk G C ∧ opnd C j b = n + k
    · obtain ⟨k, hk, he⟩ := hd
      have hbnd := opndBound ao jl b
      have hkj : k < j := by omega
      apply ih k hkj hk (hkj.trans hjm)
      · intro u v hu
        have hv := firesOp u v hu
        rw [he] at hv
        exact hv
      · rw [he] at hb
        exact hb
    · refine ⟨orIn n C (opnd C j b), raw_shape_before_mix ao hm only (by
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
lemma exceptional_local_cover_card_le_two
    (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m, G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m)
    (hUadj : ∀ u v, s(u, v) ∈ U → G.Adj u v)
    (t : Fin n) (A B : Finset (Fin n)) (hA : Basic G U A) (hB : Basic G U B)
    (hsource : ∀ u v, s(u, v) ∈ U → ∃ w,
      (w = u ∨ w = v) ∧ G.Adj t w ∧ s(t, w) ∉ U ∧ Property G U w (A ∪ B)) :
    U.card ≤ 2 := by
  by_cases hcover : ∀ p q, s(p, q) ∈ U → p ∈ A ∪ B ∨ q ∈ A ∪ B
  · exact exceptional_cover_card_le_two G U color hbip hfour hUadj t A B hA hB hcover hsource
  · have hone : U.card ≤ 1 := by
      apply cover_property_card_le_one G U color hbip hfour hUadj t
      intro u v huv
      obtain ⟨w, hw, ht, hc, hl⟩ := hsource u v huv
      refine ⟨w, hw, ht, hc, ?_⟩
      intro x hx hind
      obtain ⟨S, hS, hcov, hfalse⟩ := hl x hx hind
      rcases hS with hs | rfl
      · exact ⟨S, hs, hcov, hfalse⟩
      · exact (hcover hcov).elim
    omega
lemma two_extra_or_one_pure_card_le_two
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅) (hcard : (orN G C \ lam G C).card ≤ 2)
    (m0 : ℕ) (hm0 : m0 ∈ orN G C \ lam G C)
    (hblocked : ∀ j ∈ junk G C,
      ¬ Relation.ReflTransGen (OrStep n C) (n + m0) (n + j)) :
    (Ustar G C).card ≤ 2 := by
  classical
  by_cases hU : (Ustar G C).Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hU]
  obtain ⟨e, he⟩ := hU
  have hpair : ∃ u v : Fin n, s(u, v) ∈ Ustar G C := by
    induction e using Sym2.ind with
    | h u v => exact ⟨u, v, he⟩
  obtain ⟨u, v, huv⟩ := hpair
  obtain ⟨a, ha, b, j0, hj0, _, hr, _⟩ := residualTrace hleast hT huv
  obtain ⟨m, hm, hmi, _⟩ := residualPath hleast.1 hempty ha hj0 hr
  have hm0m : m0 ≠ m := by
    intro h
    exact hblocked j0 hj0 (h ▸ EffectiveExtra.extra_or_direct_path hleast.1 hm hmi)
  have only : ∀ r ∈ orN G C \ lam G C, r = m0 ∨ r = m := by
    intro r hr
    by_contra hn
    have hr0 : r ≠ m0 := fun h => hn (Or.inl h)
    have hrm : r ≠ m := fun h => hn (Or.inr h)
    have hsub : {m0, m, r} ⊆ orN G C \ lam G C := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hm0
      · exact hm
      · exact hr
    have hbound := Finset.card_le_card hsub
    have hthree : ({m0, m, r} : Finset ℕ).card = 3 := by
      simp [hm0m, Ne.symm hr0, Ne.symm hrm]
    omega
  have active : ∀ r ∈ orN G C \ lam G C, ∀ k ∈ junk G C,
      Relation.ReflTransGen (OrStep n C) (n + r) (n + k) → r = m := by
    intro r hr k hk hp
    rcases only r hr with rfl | h
    · exact (hblocked k hk hp).elim
    · exact h
  obtain ⟨j, hj, hjm, t, hpos, hsource⟩ :=
    EffectiveExtra.one_effective_extra_or_source hleast hT hempty m active ⟨s(u, v), huv⟩
  have hnone (x : Fin n → Bool)
      (hind : ∀ a b, G.Adj a b → x a = true → x b = false) : graphFun G ∅ x = false := by
    have hn : ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
      rintro ⟨a, b, hab, ha, hb⟩
      exact Bool.false_ne_true ((hind a b hab ha).symm.trans hb)
    simp [graphFun, hn]
  have orient : ∀ p q, s(p, q) ∈ Ustar G C → ∃ w,
      (w = p ∨ w = q) ∧ G.Adj t w ∧ s(t, w) ∉ Ustar G C ∧
      ∀ x : Fin n → Bool, x w = true →
        (∀ a b, G.Adj a b → x a = true → x b = false) →
        ∃ S : Finset (Fin n),
          (Basic G (Ustar G C) S ∨ m0 < m ∧ S = orIn n C (n + m0)) ∧
          (∀ a b, s(a, b) ∈ Ustar G C → a ∈ S ∨ b ∈ S) ∧
          ∀ y ∈ S, x y = false := by
    intro p q hpq
    obtain ⟨w, z, he, hc, hs⟩ := hsource s(p, q) hpq
    have hw : w = p ∨ w = q := by
      rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨_, h⟩
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    refine ⟨w, hw, (SimpleGraph.deleteEdges_adj.mp hc.symm).1,
      (SimpleGraph.deleteEdges_adj.mp hc.symm).2, ?_⟩
    intro x hx hind
    exact exceptional_false_junk_cover hleast.1 hT hm only hblocked (Ustar G C) x j hj hjm
      hpos (hs x hx (hnone x hind))
  have hadj : ∀ p q, s(p, q) ∈ Ustar G C → G.Adj p q := fun p q hpq =>
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hpq).1
  by_cases hlt : m0 < m
  · obtain ⟨A, B, hA, hB, hraw⟩ := exceptional_raw_two_basic hleast.1 hm0 hlt only
    apply exceptional_local_cover_card_le_two G (Ustar G C) color hbip
      (common_neighbors_unique_of_card_le_one G hfour) hadj t A B hA hB
    intro p q hpq
    obtain ⟨w, hw, ht, hc, hs⟩ := orient p q hpq
    refine ⟨w, hw, ht, hc, ?_⟩
    intro x hx hind
    obtain ⟨S, hS, hcov, hf⟩ := hs x hx hind
    refine ⟨S, ?_, hcov, hf⟩
    rcases hS with hs | ⟨_, heq⟩
    · exact Or.inl hs
    · exact Or.inr (heq.trans hraw)
  · have hone : (Ustar G C).card ≤ 1 := by
      apply cover_property_card_le_one G (Ustar G C) color hbip
        (common_neighbors_unique_of_card_le_one G hfour) hadj t
      intro p q hpq
      obtain ⟨w, hw, ht, hc, hs⟩ := orient p q hpq
      refine ⟨w, hw, ht, hc, ?_⟩
      intro x hx hind
      obtain ⟨S, hS, hcov, hf⟩ := hs x hx hind
      refine ⟨S, ?_, hcov, hf⟩
      rcases hS with hs | ⟨hl, _⟩
      · exact hs
      · exact (hlt hl).elim
    omega
end PureExceptional
namespace PrefixSources
open Budget PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma prefix_raw_cover_shape (ao : IsAO2 n C) {m w : ℕ}
    (hml : m ≤ C.gates.length)
    (first : ∀ r ∈ orN G C \ lam G C, m ≤ r)
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
  have hkl := hkm.trans_le hml
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
    have hmk := first k hk
    omega
  obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hkL
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1 - b)).card)
  exact Or.inr ⟨z, fun t ht => cleanAdj ao ha b
    (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz⟩
lemma prefix_false_junk_cover (ao : IsAO2 n C) (top : TopForm G C) {m : ℕ}
    (hml : m ≤ C.gates.length)
    (first : ∀ r ∈ orN G C \ lam G C, m ≤ r)
    (T : Finset (Sym2 (Fin n)))
    (x : Fin n → Bool) :
    ∀ j < m, j ∈ junk G C →
      (∀ u v : Fin n, s(u, v) ∈ T → gateVal n C j (pairInput u v) = true) →
      gateVal n C j x = false →
      ∃ S : Finset (Fin n), (S.card ≤ 1 ∨
        ∃ z : Fin n, ∀ t ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj t z) ∧
        (∀ u v : Fin n, s(u, v) ∈ T → u ∈ S ∨ v ∈ S) ∧
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
    have firesOp (u v : Fin n) (he : s(u, v) ∈ T) :
        val C (List.ofFn (pairInput u v)) (opnd C j b) = true :=
      (andValOperands ao jl jo _).mp (fires u v he) b
    have direct (k : ℕ) (hk : k ∈ junk G C) (hr : OrReaches n C (opnd C j b) k) :
        opnd C j b = n + k := by
      rcases lastOrBefore (orReaches_reach k _ hr).1 with h | ⟨r, rl, ro, ri, rb, rp⟩
      · exact h
      · have hr' := lastOrOutside ao hk rl ro ri rb
        have hmr := first r hr'
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
    · refine ⟨orIn n C (opnd C j b), prefix_raw_cover_shape ao hml first (by
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
end PrefixSources
namespace RemainingOrder


open Budget PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma junk_ne_extra {j r : ℕ} (hj : j ∈ junk G C) (hr : r ∈ orN G C \ lam G C) : j ≠ r := by
  intro h
  have hjop := (junkData hj).2.1
  have hrop := (orData hr).2.1
  rw [h, hrop] at hjop
  contradiction
lemma least_dirty_has_reader (hleast : IsLeastAO G C) {j : ℕ} (hj : j ∈ junk G C) :
    ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  have hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x :=
    fun x => congrFun hleast.2.1 x
  have hAO : Ledger.S98.AO n C := Ledger.S98.AO_of_IsAO2 n C hleast.1
  have hLeast : Ledger.S98.Least n C := ⟨hAO, fun D hD hDf =>
    hleast.2.2 D (Ledger.S98.IsAO2_of_AO n D hD) (funext fun x => (hDf x).trans (hfun x))⟩
  obtain ⟨hjl, _, x, hjx, hFx⟩ := junkData hj
  have hout : C.output ≠ n + j := by
    intro heq
    have hcx : C.eval (List.ofFn x) = true := by
      change (C.wires (List.ofFn x)).getD C.output false = true
      rw [heq]
      exact hjx
    exact Bool.false_ne_true (hFx.symm.trans ((hfun x).symm.trans hcx))
  by_contra hno
  push Not at hno
  obtain ⟨_, a, b, hin, ha, hb⟩ := hLeast.1 j hjl
  have hsame : ∀ x : Fin n → Bool,
      (Ledger.S98.eraseC n C j a).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    Ledger.S98.erase_wires n C j a hjl ha x (Or.inr hno) C.output (fun h => (hout h).elim)
  have hsize := hLeast.2 _ (Ledger.S98.erase_AO n C j a hLeast.1 hjl ha) hsame
  have hlength := Ledger.S98.erase_length n C j a hjl
  omega
lemma last_junk_has_extra_reader (hleast : IsLeastAO G C) (hempty : centreless G C = ∅)
    {j : ℕ} (hj : j ∈ junk G C) (hlast : ∀ k ∈ junk G C, k ≤ j) :
    ∃ r ∈ orN G C \ lam G C, j < r ∧ n + j ∈ (gateAt C r).inputs := by
  obtain ⟨r, hjr, hrl, hri⟩ := least_dirty_has_reader hleast hj
  rcases hleast.1.1 _ (gateAt_mem hrl) with hro | hro
  · by_cases hbelow : BelowF G C r
    · have htop : r ∈ tops G C := by
        simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
          And.intro hrl (And.intro hro hbelow)
      obtain ⟨b, hb⟩ := inputsAsOpnd hleast.1 hrl hri
      have hne := topSides hempty htop b
      change (orIn n C (opnd C r b)).Nonempty at hne
      rw [← hb, andRawEmpty (junkData hj).2.1] at hne
      exact (Finset.not_nonempty_empty hne).elim
    · have hdirty : ∃ x : Fin n → Bool, gateVal n C r x = true ∧ graphFun G ∅ x = false := by
        by_contra hn
        apply hbelow
        intro x hx
        exact Bool.eq_true_of_not_eq_false fun hf => hn ⟨x, hx, hf⟩
      have hrjunk : r ∈ junk G C :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrl, hro, hrl, hdirty⟩
      have hle := hlast r hrjunk
      omega
  · exact ⟨r, lastOrOutside hleast.1 hj hrl hro hri (by omega), hjr, hri⟩
end RemainingOrder
namespace ChainMixed
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
def Hit (S : Finset (Fin n)) (x : Fin n → Bool) : Prop := ∃ w ∈ S, x w = true
def CNF (F : Finset (Finset (Fin n))) (x : Fin n → Bool) : Prop := ∀ S ∈ F, Hit S x
def Basic (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (S : Finset (Fin n)) : Prop :=
  S.card ≤ 1 ∨ ∃ z, ∀ w ∈ S, G.Adj w z ∧ s(w,z) ∉ Ustar G C
def EdgeCNF (F : Finset (Finset (Fin n))) (e : Sym2 (Fin n)) : Prop :=
  ∀ S ∈ F, ∃ w ∈ S, w ∈ e
lemma edgeCNF_pair_iff (F : Finset (Finset (Fin n))) (u v : Fin n) :
    EdgeCNF F s(u,v) ↔ CNF F (pairInput u v) := by
  unfold EdgeCNF CNF Hit
  simp only [Sym2.mem_iff, pairInput_true]
lemma cnf_three (A B S : Finset (Fin n)) (x : Fin n → Bool) :
    CNF {A,B,S} x ↔ Hit A x ∧ Hit B x ∧ Hit S x := by simp [CNF]
def RoutedThrough (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (m : ℕ) (e : Sym2 (Fin n)) : Prop :=
  (orIn n C (n+m)).Nonempty ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+m) ∧
    ∃ w ∈ side C a (1-b), w ∈ e
noncomputable def termEdges (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (m : ℕ) (F : Finset (Finset (Fin n))) : Finset (Sym2 (Fin n)) := by
  classical
  exact (Ustar G C).filter fun e => RoutedThrough G C m e ∧ EdgeCNF F e
lemma termEdges_mem {m : ℕ} {F : Finset (Finset (Fin n))} {e : Sym2 (Fin n)} :
    e ∈ termEdges G C m F ↔ e ∈ Ustar G C ∧ RoutedThrough G C m e ∧ EdgeCNF F e := by
  classical
  simp only [termEdges, Finset.mem_filter]
lemma termEdges_card_le_one
    (hAO : IsAO2 n C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (m : ℕ) (F : Finset (Finset (Fin n)))
    (hbasic : ∀ S ∈ F, Basic G C S)
    (himp : ∀ x, CNF F x → gateVal n C m x = true) :
    (termEdges G C m F).card ≤ 1 := by
  classical
  by_cases hE : (termEdges G C m F).Nonempty
  · obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht⟩ := (termEdges_mem.mp he).2.1.1
    have sub : termEdges G C m F ⊆ Ustar G C := fun e he => (termEdges_mem.mp he).1
    apply cover_property_card_le_one G (termEdges G C m F) color hbip
      (common_neighbors_unique_of_card_le_one G hfour)
      (fun u v he => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (sub he)).1) t
    intro u v huv
    obtain ⟨_, ⟨_, a, ha, b, hp, w, hw, hwe⟩, hedge⟩ := termEdges_mem.mp huv
    have hta : t ∈ side C a b := reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
    have clean := cleanAdj hAO ha b hta hw
    refine ⟨w, Sym2.mem_iff.mp hwe, (SimpleGraph.deleteEdges_adj.mp clean).1,
      fun h => (SimpleGraph.deleteEdges_adj.mp clean).2 (sub h), ?_⟩
    intro x hx hind
    have hfalse : graphFun G ∅ x = false := by
      have hnone : ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
        rintro ⟨a,b,hab,ha,hb⟩
        exact Bool.false_ne_true ((hind a b hab ha).symm.trans hb)
      simp [graphFun, hnone]
    have hnot : ¬ CNF F x := by
      intro hc
      exact Bool.false_ne_true (hfalse.symm.trans (firingTop hAO ha hp hw x (himp x hc) hx))
    have missing : ∃ S ∈ F, ∀ w ∈ S, x w = false := by
      by_contra hn
      apply hnot
      intro S hS
      by_contra hmiss
      exact hn ⟨S,hS,fun w hw => Bool.eq_false_iff.mpr (fun h => hmiss ⟨w,hw,h⟩)⟩
    obtain ⟨S,hS,hmiss⟩ := missing
    refine ⟨S, ?_, ?_, hmiss⟩
    · rcases hbasic S hS with small | ⟨z,hz⟩
      · exact Or.inl small
      · exact Or.inr ⟨z, fun w hw => ⟨(hz w hw).1, fun h => (hz w hw).2 (sub h)⟩⟩
    · intro a b hab
      obtain ⟨w,hw,hwe⟩ := (termEdges_mem.mp hab).2.2 S hS
      rcases Sym2.mem_iff.mp hwe with rfl | rfl
      · exact Or.inl hw
      · exact Or.inr hw
  · simp [Finset.not_nonempty_iff_eq_empty.mp hE]
lemma operand_support_general (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and)
    (b : Fin 2) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (opnd C a b) = true) :
    Hit (side C a b) x ∨ ∃ d ∈ junk G C,
      OrReaches n C (opnd C a b) d ∧ gateVal n C d x = true := by
  obtain ⟨w,hr,hw,hkind⟩ := or_trace (n := n) (by simp) (opnd C a b) hv
  rcases hkind with hinput | ⟨d,hd,rfl,hnot⟩
  · let t : Fin n := ⟨w,hinput⟩
    have ht : t ∈ side C a b := reach_mem_orIn t hr
    exact Or.inl ⟨t,ht,(val_ofFn C x t).symm.trans hw⟩
  · have hreach := reach_orReaches hr d rfl hd
    have hand := (hAO.1 _ (gateAt_mem hd)).resolve_right hnot
    exact Or.inr ⟨d,operandOrAndJunk hAO hT ha ho hreach hand,hreach,hw⟩
lemma lower_junk_operand_pure
    (hAO : IsAO2 n C) (hT : TopForm G C)
    {j k : ℕ} (hpair : junk G C = {j,k}) (hjk : j < k)
    (b : Fin 2) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C j b) = true ↔ Hit (side C j b) x := by
  have hj : j ∈ junk G C := by simp [hpair]
  obtain ⟨hjl,hjo,_⟩ := junkData hj
  constructor
  · intro hx
    rcases operand_support_general hAO hT hjl hjo b x hx with h | ⟨d,hd,hr,_⟩
    · exact h
    · have hle := orStep_le (orReaches_reach d _ hr).1
      have hbound := opndBound hAO hjl b
      have hdk : d = j ∨ d = k := by simpa only [hpair, Finset.mem_insert, Finset.mem_singleton] using hd
      rcases hdk with rfl | rfl <;> omega
  · rintro ⟨w,hw,hx⟩
    exact sideVal hw hx
lemma upper_junk_operand_normal_form
    (hAO : IsAO2 n C) (hT : TopForm G C)
    {j k : ℕ} (hpair : junk G C = {j,k})
    (b : Fin 2) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C k b) = true ↔
      Hit (side C k b) x ∨ (OrReaches n C (opnd C k b) j ∧ gateVal n C j x = true) := by
  have hk : k ∈ junk G C := by simp [hpair]
  obtain ⟨hkl,hko,_⟩ := junkData hk
  constructor
  · intro hx
    rcases operand_support_general hAO hT hkl hko b x hx with h | ⟨d,hd,hr,hx⟩
    · exact Or.inl h
    · have hle := orStep_le (orReaches_reach d _ hr).1
      have hbound := opndBound hAO hkl b
      have hdk : d = j ∨ d = k := by simpa only [hpair, Finset.mem_insert, Finset.mem_singleton] using hd
      rcases hdk with rfl | rfl
      · exact Or.inr ⟨hr,hx⟩
      · omega
  · rintro (⟨w,hw,hx⟩ | ⟨hr,hx⟩)
    · exact sideVal hw hx
    · exact orStep_up (n := n) (by simp) (orReaches_reach j _ hr).1 hx
lemma prefix_raw_cover_shape_local (ao : IsAO2 n C) {m w : ℕ}
    (hml : m ≤ C.gates.length)
    (first : ∀ r ∈ orN G C \ lam G C, m ≤ r)
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
  have hkl := hkm.trans_le hml
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
    have hmk := first k hk
    omega
  obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hkL
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1 - b)).card)
  exact Or.inr ⟨z, fun t ht => cleanAdj ao ha b
    (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz⟩
lemma basic_of_clean_shape {S : Finset (Fin n)}
    (h : S.card ≤ 1 ∨ ∃ z, ∀ w ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj w z) :
    Basic G C S := by
  rcases h with h | ⟨z,hz⟩
  · exact Or.inl h
  · exact Or.inr ⟨z,fun w hw => SimpleGraph.deleteEdges_adj.mp (hz w hw)⟩
lemma raw_or_step (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.or) (b : Fin 2) :
    OrStep n C (n+m) (opnd C m b) :=
  ⟨m,hm,rfl,hop,opndMem hAO hm b,opndBound hAO hm b⟩
lemma raw_or_union (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.or) :
    orIn n C (n+m) = side C m 0 ∪ side C m 1 := by
  ext x
  constructor
  · intro hx
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach x hx) with he | ⟨z,hst,hrem⟩
    · have := x.isLt
      omega
    · obtain ⟨k,hk,he,_,hz,_⟩ := hst
      have eq : k = m := by omega
      subst k
      obtain ⟨b,rfl⟩ := inputsAsOpnd hAO hm hz
      have hx' := reach_mem_orIn x hrem
      apply Finset.mem_union.mpr
      fin_cases b
      · exact Or.inl hx'
      · exact Or.inr hx'
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact reach_mem_orIn x ((Relation.ReflTransGen.single (raw_or_step hAO hm hop 0)).trans (mem_orIn_reach x hx))
    · exact reach_mem_orIn x ((Relation.ReflTransGen.single (raw_or_step hAO hm hop 1)).trans (mem_orIn_reach x hx))
lemma first_mixed_raw_basic
    (hAO : IsAO2 n C) {m j : ℕ}
    (hm : m ∈ orN G C \ lam G C) (first : ∀ r ∈ orN G C \ lam G C, m ≤ r)
    (hj : j ∈ junk G C)
    (hpath : Relation.ReflTransGen (OrStep n C) (n+m) (n+j)) :
    Basic G C (orIn n C (n+m)) := by
  have hmd := orData hm
  have direct : n+j ∈ (gateAt C m).inputs := by
    rcases lastOrBefore hpath with he | ⟨l,hl,hlo,hli,hlb,hml⟩
    · have eq : m = j := by omega
      have ho := (junkData hj).2.1
      rw [← eq,hmd.2.1] at ho
      contradiction
    · have hlR := lastOrOutside hAO hj hl hlo hli hlb
      have hle := first l hlR
      have hge := orStep_le hml
      have eq : l = m := by omega
      simpa only [eq] using hli
  obtain ⟨b,hb⟩ := inputsAsOpnd hAO hmd.1 direct
  have hbempty : side (n := n) C m b = ∅ := by
    change orIn n C (opnd C m b) = ∅
    rw [← hb,andRawEmpty (junkData hj).2.1]
  have hbasic (b : Fin 2) : Basic G C (side C m b) :=
    basic_of_clean_shape (prefix_raw_cover_shape_local hAO hmd.1.le first (opndBound hAO hmd.1 b))
  rw [raw_or_union hAO hmd.1 hmd.2.1]
  fin_cases b
  · have hz : side (n := n) C m 0 = ∅ := by simpa using hbempty
    rw [hz,Finset.empty_union]
    exact hbasic 1
  · have hz : side (n := n) C m 1 = ∅ := by simpa using hbempty
    rw [hz,Finset.union_empty]
    exact hbasic 0
lemma raw_before_upper_basic
    (hAO : IsAO2 n C) {m j k w : ℕ}
    (hm : m ∈ orN G C \ lam G C) (first : ∀ r ∈ orN G C \ lam G C, m ≤ r)
    (only_before : ∀ r ∈ orN G C \ lam G C, r < k → r = m)
    (hk : k ≤ C.gates.length) (hj : j ∈ junk G C)
    (hpath : Relation.ReflTransGen (OrStep n C) (n+m) (n+j))
    (hw : w < n+k) : Basic G C (orIn n C w) := by
  by_cases hpre : w < n+m
  · exact basic_of_clean_shape (prefix_raw_cover_shape_local hAO (orData hm).1.le first hpre)
  obtain ⟨l,rfl⟩ : ∃ l, w = n+l := ⟨w-n,by omega⟩
  by_cases heq : l = m
  · subst l
    exact first_mixed_raw_basic hAO hm first hj hpath
  by_cases hsmall : (orIn n C (n+l)).card ≤ 1
  · exact Or.inl hsmall
  have hne : (orIn n C (n+l)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v,hv⟩ := hne
  have hll : l < C.gates.length := by omega
  have hlo : (gateAt C l).op = GateOp.or := by
    rcases hAO.1 _ (gateAt_mem hll) with hand | hor
    · rw [andRawEmpty hand] at hv
      exact (Finset.notMem_empty _ hv).elim
    · exact hor
  have hnb : ¬ BelowF G C l := by
    intro hb
    have hon := reach_var_val (pairInput v v) _ v (mem_orIn_reach v hv) (pairInput_left v v)
    exact G.irrefl ((graphFun_pair G v v).mp (hb _ hon))
  have hlN : l ∈ orN G C := by
    simpa only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range] using And.intro hll (And.intro hlo hnb)
  have hlL : l ∈ lam G C := by
    by_contra hn
    exact heq (only_before l (Finset.mem_sdiff.mpr ⟨hlN,hn⟩) (by omega))
  obtain ⟨z,hz⟩ := ZeroExtra.lambda_clean_pencil hAO hlL
  exact Or.inr ⟨z,fun v hv => SimpleGraph.deleteEdges_adj.mp (hz v hv).symm⟩
end ChainMixed
namespace TwoJunkAllCases
open Budget
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
end TwoJunkAllCases
lemma small_counterexample_cover_shape
    (q N t u P size : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (A B : Finset (Fin N)) (hq : 3 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (hP : 4 ≤ P) (hu : u ≤ 4) (hcoverSize : A.card + B.card ≤ t)
    (hdensity : N * (q + 1) ≤ (q + 1) * (A.card + B.card) + u)
    (hmissing : (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card ≤ u)
    (hledger : N * (q + 1) + t + P ≤ size + u + 1)
    (hbad : size + 1 < N * (q + 1) + N) :
    q = 3 ∧ u = 4 ∧ P = 4 ∧ A.card + B.card = t ∧ t + 1 = N ∧
      ((∃ p, A = Finset.univ.erase p ∧ B = ∅) ∨
       (∃ l, A = ∅ ∧ B = Finset.univ.erase l)) := by
  have htDensity : N * (q + 1) ≤ (q + 1) * t + u := by
    have hmul := Nat.mul_le_mul_left (q + 1) hcoverSize
    omega
  obtain ⟨hq3, hu4, hP4, htN⟩ := small_uncovered_counterexample_shape
    q N t u P size hq hP hu htDensity hledger hbad
  have hsize : A.card + B.card = t := by
    rw [hq3, hu4] at hdensity
    nlinarith
  have hstar := small_uncovered_cover_is_single_star_complement q N I A B (by omega)
    hN hcol hpair (by omega) (by omega)
  exact ⟨hq3, hu4, hP4, hsize, htN, hstar⟩
namespace VisibleRoots
open Budget PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma binary_inputs_exhaust (ao : IsAO2 n C) {m u v : ℕ}
    (hm : m < C.gates.length) (hu : u ∈ (gateAt C m).inputs)
    (hv : v ∈ (gateAt C m).inputs) (hne : u ≠ v) :
    ∀ w ∈ (gateAt C m).inputs, w = u ∨ w = v := by
  obtain ⟨p, q, hpq⟩ := binaryInputs ao hm
  intro w hw
  simp only [hpq, List.mem_cons, List.not_mem_nil, or_false] at hu hv hw
  omega
lemma empty_input_unique (ao : IsAO2 n C) {m u v : ℕ}
    (hm : m < C.gates.length) (hne : (orIn n C (n + m)).Nonempty)
    (hu : u ∈ (gateAt C m).inputs) (hv : v ∈ (gateAt C m).inputs)
    (hue : orIn n C u = ∅) (hve : orIn n C v = ∅) : u = v := by
  by_contra h
  obtain ⟨t, ht⟩ := hne
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach t ht) with he | ⟨w, hs, hrest⟩
  · have := t.isLt
    omega
  · obtain ⟨l, _, he, _, hin, _⟩ := hs
    have hl : l = m := by omega
    subst l
    have ht' := reach_mem_orIn t hrest
    rcases binary_inputs_exhaust ao hm hu hv h w hin with rfl | rfl
    · rw [hue] at ht'
      exact Finset.notMem_empty _ ht'
    · rw [hve] at ht'
      exact Finset.notMem_empty _ ht'

lemma visible_empty_extra_has_reader (ao : IsAO2 n C)
    (hempty : centreless G C = ∅) {m a : ℕ} {b : Fin 2}
    (hm : m ∈ orN G C \ lam G C) (he : orIn n C (n + m) = ∅)
    (ha : a ∈ tops G C)
    (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m)) :
    ∃ p ∈ orN G C \ lam G C, m < p ∧ n + m ∈ (gateAt C p).inputs ∧
      Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + p) := by
  rcases lastOrBefore path with h | ⟨p, hpl, hpo, hpi, hlt, hp⟩
  · have hn := topSides hempty ha b
    change (orIn n C (opnd C a b)).Nonempty at hn
    rw [h, he] at hn
    exact (Finset.not_nonempty_empty hn).elim
  · exact ⟨p, emptyInputOutside ao (orData hm).2.2 he hpl hpo hpi,
      by omega, hpi, hp⟩

end VisibleRoots

namespace VisibleForest

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def TopOrVisible (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (r : ℕ) : Prop :=
  ∃ a ∈ tops G C, ∃ b : Fin 2,
    Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + r)

lemma empty_input_excludes_two_raw (ao : IsAO2 n C) {r w : ℕ}
    (hr : r < C.gates.length) (hw : w ∈ (gateAt C r).inputs)
    (he : orIn n C w = ∅) :
    ¬ ((orIn n C (opnd C r 0)).Nonempty ∧ (orIn n C (opnd C r 1)).Nonempty) := by
  intro h
  obtain ⟨b, hb⟩ := inputsAsOpnd ao hr hw
  have hne : (orIn n C (opnd C r b)).Nonempty := by
    fin_cases b
    · exact h.1
    · exact h.2
  rw [← hb, he] at hne
  exact Finset.not_nonempty_empty hne

end VisibleForest

namespace VisibleForestGeneral

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget VisibleForest

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma empty_source_reader_or_top (ao : IsAO2 n C) {s a : ℕ} {b : Fin 2}
    (hdirty : ¬ BelowF G C s) (hraw : orIn n C (n + s) = ∅)
    (ha : a ∈ tops G C)
    (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + s)) :
    (∃ r ∈ orN G C \ lam G C, TopOrVisible G C r ∧ n + s ∈ (gateAt C r).inputs) ∨
      (∃ t ∈ centreless G C, ∃ c : Fin 2, opnd C t c = n + s) := by
  rcases lastOrBefore path with h | ⟨r, hrl, hro, hri, hrb, hp⟩
  · have he : side (n := n) C a b = ∅ := by
      change orIn n C (opnd C a b) = ∅
      rw [h, hraw]
    have haz : a ∈ centreless G C := by
      apply Finset.mem_filter.mpr
      refine ⟨ha, ?_⟩
      fin_cases b
      · exact Or.inl he
      · exact Or.inr he
    exact Or.inr ⟨a, haz, b, h⟩
  · exact Or.inl ⟨r, emptyInputOutside ao hdirty hraw hrl hro hri,
      ⟨a, ha, b, hp⟩, hri⟩

lemma visible_junk_add_two_raw_extra_le_extra_add_twice_centreless
    (ao : IsAO2 n C) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, j ∈ junk G C ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
      OrReaches n C (opnd C a b) j) :
    J.card + ((orN G C \ lam G C).filter fun r =>
      (orIn n C (opnd C r 0)).Nonempty ∧ (orIn n C (opnd C r 1)).Nonempty).card ≤
      (orN G C \ lam G C).card + 2 * (centreless G C).card := by
  classical
  let R := orN G C \ lam G C
  let B := R.filter fun r =>
    (orIn n C (opnd C r 0)).Nonempty ∧ (orIn n C (opnd C r 1)).Nonempty
  let A := R \ B
  let E := R.filter fun r => orIn n C (n + r) = ∅ ∧ TopOrVisible G C r
  let Z := centreless G C
  let S := J ∪ E
  have source : ∀ s ∈ S, orIn n C (n + s) = ∅ ∧
      ((∃ r ∈ A, TopOrVisible G C r ∧ n + s ∈ (gateAt C r).inputs) ∨
        (∃ t ∈ Z, ∃ c : Fin 2, opnd C t c = n + s)) := by
    intro s hs
    have hex : orIn n C (n + s) = ∅ ∧
        ((∃ r ∈ R, TopOrVisible G C r ∧ n + s ∈ (gateAt C r).inputs) ∨
          (∃ t ∈ Z, ∃ c : Fin 2, opnd C t c = n + s)) := by
      rcases Finset.mem_union.mp hs with hJmem | hEmem
      · obtain ⟨hjs, a, ha, b, hp⟩ := hJ s hJmem
        obtain ⟨_, hjo, x, hx, hFx⟩ := junkData hjs
        have hd : ¬ BelowF G C s := by
          intro h
          exact Bool.false_ne_true (hFx.symm.trans (h x hx))
        have hraw := andRawEmpty (n := n) hjo
        exact ⟨hraw, empty_source_reader_or_top ao hd hraw ha (orReaches_reach s _ hp).1⟩
      · obtain ⟨hrR, hraw, a, ha, b, hp⟩ := Finset.mem_filter.mp hEmem
        exact ⟨hraw, empty_source_reader_or_top ao (orData hrR).2.2 hraw ha hp⟩
    obtain ⟨hse, hreader⟩ := hex
    refine ⟨hse, ?_⟩
    rcases hreader with ⟨r, hr, hvis, hin⟩ | hterminal
    · refine Or.inl ⟨r, Finset.mem_sdiff.mpr ⟨hr, ?_⟩, hvis, hin⟩
      intro hB
      exact empty_input_excludes_two_raw ao (orData hr).1 hin hse (Finset.mem_filter.mp hB).2
    · exact Or.inr hterminal
  have witness : ∀ s : ℕ, ∃ r : ℕ, ∃ b : Fin 2, s ∈ S →
      ((r ∈ A ∧ TopOrVisible G C r) ∨ r ∈ Z) ∧ opnd C r b = n + s := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨_, hnext⟩ := source s hs
      rcases hnext with ⟨r, hrA, hvis, hin⟩ | ⟨r, hrZ, b, hwire⟩
      · obtain ⟨b, hb⟩ := inputsAsOpnd ao (orData (Finset.mem_sdiff.mp hrA).1).1 hin
        exact ⟨r, b, fun _ => ⟨Or.inl ⟨hrA, hvis⟩, hb.symm⟩⟩
      · exact ⟨r, b, fun _ => ⟨Or.inr hrZ, hwire⟩⟩
    · exact ⟨0, 0, fun h => (hs h).elim⟩
  choose reader slot hreader using witness
  let f := fun s : ℕ => (reader s, if reader s ∈ E ∨ reader s ∈ Z then slot s else (0 : Fin 2))
  let T := (A ×ˢ {(0 : Fin 2)}) ∪ (E ×ˢ {(1 : Fin 2)}) ∪ (Z ×ˢ (Finset.univ : Finset (Fin 2)))
  have hinject : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn f
    · intro s hs
      have hr := (hreader s hs).1
      change (reader s, if reader s ∈ E ∨ reader s ∈ Z then slot s else (0 : Fin 2)) ∈ T
      by_cases hz : reader s ∈ Z
      · rw [ite_eq_left (Or.inr hz)]
        exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hz, Finset.mem_univ _⟩)
      have hrA : reader s ∈ A := by
        rcases hr with h | h
        · exact h.1
        · exact (hz h).elim
      by_cases he : reader s ∈ E
      · have hslot : slot s = 0 ∨ slot s = 1 := by
          simpa using opposite (0 : Fin 2) (slot s)
        rcases hslot with hzero | hone
        · rw [ite_eq_left (Or.inl he), hzero]
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_product.mpr ⟨hrA, by simp⟩))
        · rw [ite_eq_left (Or.inl he), hone]
          exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_product.mpr ⟨he, by simp⟩))
      · rw [ite_eq_right (not_or.mpr ⟨he, hz⟩)]
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_product.mpr ⟨hrA, by simp⟩))
    · intro s hs t ht heq
      have hrst : reader s = reader t := congrArg Prod.fst heq
      obtain ⟨hrs, hswire⟩ := hreader s hs
      obtain ⟨hrt, htwire⟩ := hreader t ht
      by_cases he : reader s ∈ E ∨ reader s ∈ Z
      · have he' : reader t ∈ E ∨ reader t ∈ Z := hrst ▸ he
        have hslots : slot s = slot t := by
          have h := congrArg Prod.snd heq
          simpa only [f, he, he', ite_true] using h
        rw [hrst, hslots] at hswire
        omega
      · have hnotE : reader s ∉ E := fun h => he (Or.inl h)
        have hnotZ : reader s ∉ Z := fun h => he (Or.inr h)
        have hsA : reader s ∈ A ∧ TopOrVisible G C (reader s) := hrs.resolve_right hnotZ
        have htA : reader t ∈ A ∧ TopOrVisible G C (reader t) := by
          apply hrt.resolve_right
          intro htZ
          exact hnotZ (hrst.symm ▸ htZ)
        have hraw : (orIn n C (n + reader s)).Nonempty := by
          by_contra hn
          have hz := Finset.not_nonempty_iff_eq_empty.mp hn
          exact hnotE (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hsA.1).1, hz, hsA.2⟩)
        have hsin : n + s ∈ (gateAt C (reader s)).inputs := by
          rw [← hswire]
          exact opndMem ao (orData (Finset.mem_sdiff.mp hsA.1).1).1 (slot s)
        have htin : n + t ∈ (gateAt C (reader s)).inputs := by
          rw [hrst, ← htwire]
          exact opndMem ao (orData (Finset.mem_sdiff.mp htA.1).1).1 (slot t)
        have hew := VisibleRoots.empty_input_unique ao
          (orData (Finset.mem_sdiff.mp hsA.1).1).1 hraw hsin htin
          (source s hs).1 (source t ht).1
        omega
  have hdisjoint : Disjoint J E := by
    apply Finset.disjoint_left.mpr
    intro s hsJ hsE
    have hjop := (junkData (hJ s hsJ).1).2.1
    have hrop := (orData (Finset.mem_filter.mp hsE).1).2.1
    rw [hrop] at hjop
    contradiction
  have hScard : S.card = J.card + E.card := Finset.card_union_of_disjoint hdisjoint
  have hTcard : T.card ≤ A.card + E.card + 2 * Z.card := by
    have h0 := Finset.card_union_le (A ×ˢ {(0 : Fin 2)}) (E ×ˢ {(1 : Fin 2)})
    have h1 := Finset.card_union_le ((A ×ˢ {(0 : Fin 2)}) ∪ (E ×ˢ {(1 : Fin 2)}))
      (Z ×ˢ (Finset.univ : Finset (Fin 2)))
    have hc0 : ((A ×ˢ {(0 : Fin 2)}) ∪ (E ×ˢ {(1 : Fin 2)})).card ≤ A.card + E.card := by
      simpa using h0
    have hc1 : T.card ≤ ((A ×ˢ {(0 : Fin 2)}) ∪ (E ×ˢ {(1 : Fin 2)})).card + 2 * Z.card := by
      simpa [T, Nat.mul_comm] using h1
    omega
  have hJA : J.card ≤ A.card + 2 * Z.card := by omega
  have hBA : A.card + B.card = R.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  change J.card + B.card ≤ R.card + 2 * Z.card
  omega

lemma visible_junk_card_le_extra_add_twice_centreless (ao : IsAO2 n C) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, j ∈ junk G C ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
      OrReaches n C (opnd C a b) j) :
    J.card ≤ (orN G C \ lam G C).card + 2 * (centreless G C).card := by
  have h := visible_junk_add_two_raw_extra_le_extra_add_twice_centreless ao J hJ
  omega

end VisibleForestGeneral
namespace GlobalExceptional
open ExceptionalCover
lemma basic_mono {n : ℕ} (G : SimpleGraph (Fin n))
    {U T : Finset (Sym2 (Fin n))} (hTU : T ⊆ U)
    {S : Finset (Fin n)} (hS : Basic G U S) : Basic G T S := by
  rcases hS with hsmall | ⟨z, hz⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨z, fun y hy => ⟨(hz y hy).1, fun he => (hz y hy).2 (hTU he)⟩⟩
lemma global_exceptional_cover_card_le_two {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m)
    (hUadj : ∀ u v, s(u, v) ∈ U → G.Adj u v)
    (A B : Finset (Fin n)) (hA : Basic G U A) (hB : Basic G U B)
    (hproperty : ∀ x : Fin n → Bool,
      (∀ a b, G.Adj a b → x a = true → x b = false) →
      ∃ S : Finset (Fin n), (Basic G U S ∨ S = A ∪ B) ∧
        (∀ u v, s(u, v) ∈ U → u ∈ S ∨ v ∈ S) ∧ ∀ y ∈ S, x y = false) :
    U.card ≤ 2 := by
  classical
  by_cases hcover : ∀ u v, s(u, v) ∈ U → u ∈ A ∪ B ∨ v ∈ A ∪ B
  · let part (D : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
      U.filter fun e => ∃ w ∈ D, w ∈ e
    have sub (D : Finset (Fin n)) : part D ⊆ U := Finset.filter_subset _ _
    have bound (D : Finset (Fin n)) (hD : Basic G U D) (hDsub : D ⊆ A ∪ B) :
        (part D).card ≤ 1 := by
      apply global_cover_property_card_le_one G (part D) color hbip hfour
        (fun u v huv => hUadj u v (sub D huv))
      intro x hind
      obtain ⟨S, hS, hScov, hSfalse⟩ := hproperty x hind
      rcases hS with hs | rfl
      · exact ⟨S, basic_mono G (sub D) hs,
          fun u v huv => hScov u v (sub D huv), hSfalse⟩
      · refine ⟨D, basic_mono G (sub D) hD, ?_, fun y hy => hSfalse y (hDsub hy)⟩
        intro u v huv
        obtain ⟨_, w, hwD, hwe⟩ := Finset.mem_filter.mp huv
        rcases Sym2.mem_iff.mp hwe with hw | hw
        · exact Or.inl (hw ▸ hwD)
        · exact Or.inr (hw ▸ hwD)
    have hAc := bound A hA (Finset.subset_union_left)
    have hBc := bound B hB (Finset.subset_union_right)
    have hparts : U ⊆ part A ∪ part B := by
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        rcases hcover u v he with hu | hv
        · rcases Finset.mem_union.mp hu with huA | huB
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, u, huA, by simp⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, u, huB, by simp⟩)
        · rcases Finset.mem_union.mp hv with hvA | hvB
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, v, hvA, by simp⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, v, hvB, by simp⟩)
    have hcount := Finset.card_le_card hparts
    have hsum := Finset.card_union_le (part A) (part B)
    omega
  · have hone : U.card ≤ 1 := by
      apply global_cover_property_card_le_one G U color hbip hfour hUadj
      intro x hind
      obtain ⟨S, hS, hScov, hSfalse⟩ := hproperty x hind
      rcases hS with hs | rfl
      · exact ⟨S, hs, hScov, hSfalse⟩
      · exact (hcover hScov).elim
    omega
end GlobalExceptional
namespace OneCentreless
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget ChainMixed
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma two_source_top_cnf
    (J K H : (Fin n → Bool) → Prop)
    (A B R S T : Finset (Fin n))
    (hbasic : ∀ Q ∈ ({A,B,R,S,T} : Finset (Finset (Fin n))), Basic G C Q)
    (a b l0 l1 r0 r1 : Prop)
    (hdis0 : ¬ (l0 ∧ r0)) (hdis1 : ¬ (l1 ∧ r1))
    (hJ : ∀ x, J x ↔ Hit A x ∧ Hit B x)
    (hK : ∀ x, K x ↔ (Hit R x ∨ (a ∧ J x)) ∧ (Hit S x ∨ (b ∧ J x)))
    (hH : ∀ x, H x ↔ ((l0 ∧ J x) ∨ (l1 ∧ K x)) ∧
      (Hit T x ∨ (r0 ∧ J x) ∨ (r1 ∧ K x))) :
    ∃ F0 F1 : Finset (Finset (Fin n)),
      (∀ Q ∈ F0, Basic G C Q) ∧ (∀ Q ∈ F1, Basic G C Q) ∧
      ∀ x, H x ↔ CNF F0 x ∨ CNF F1 x := by
  classical
  let D : Finset (Finset (Fin n)) := {A,B} ∪ (if a then ∅ else {R}) ∪ (if b then ∅ else {S})
  have hD (x : Fin n → Bool) : CNF D x ↔ J x ∧ K x := by
    rw [hJ x, hK x, hJ x]
    by_cases ha : a <;> by_cases hb : b <;> simp [D,CNF,ha,hb] <;> tauto
  have hKsplit (x : Fin n → Bool) : K x ↔ (Hit R x ∧ Hit S x) ∨ CNF D x := by
    rw [hD x,hK x]
    tauto
  have hJKsplit (x : Fin n → Bool) : J x ∨ K x ↔ J x ∨ (Hit R x ∧ Hit S x) := by
    rw [hKsplit x,hD x]
    tauto
  have hdsub : D ⊆ ({A,B,R,S,T} : Finset (Finset (Fin n))) := by
    intro Q hQ
    by_cases ha : a <;> by_cases hb : b <;> simp [D,ha,hb] at hQ ⊢ <;> tauto
  have hdgood : ∀ Q ∈ D, Basic G C Q := fun Q hQ => hbasic Q (hdsub hQ)
  have hgood (F : Finset (Finset (Fin n)))
      (hF : F ⊆ ({A,B,R,S,T} : Finset (Finset (Fin n)))) : ∀ Q ∈ F, Basic G C Q :=
    fun Q hQ => hbasic Q (hF hQ)
  have htgood : ∀ Q ∈ insert T D, Basic G C Q := by
    intro Q hQ
    rcases Finset.mem_insert.mp hQ with heq | hQ
    · subst Q
      exact hbasic T (by simp)
    · exact hdgood Q hQ
  by_cases hl0 : l0
  · have hr0 : ¬ r0 := fun h => hdis0 ⟨hl0,h⟩
    by_cases hl1 : l1
    · have hr1 : ¬ r1 := fun h => hdis1 ⟨hl1,h⟩
      refine ⟨{A,B,T},{R,S,T},hgood _ (by intro Q hQ; simp at hQ ⊢; tauto),
        hgood _ (by intro Q hQ; simp at hQ ⊢; tauto),?_⟩
      intro x
      rw [hH x]
      simp only [hl0,hl1,hr0,hr1,true_and,false_and,or_false,false_or]
      rw [hJKsplit x,hJ x]
      simp only [cnf_three]
      tauto
    · by_cases hr1 : r1
      · refine ⟨{A,B,T},D,hgood _ (by intro Q hQ; simp at hQ ⊢; tauto),hdgood,?_⟩
        intro x
        rw [hH x]
        simp only [hl0,hl1,hr0,hr1,true_and,false_and,or_false,false_or]
        rw [hD x,cnf_three,hJ x]
        tauto
      · refine ⟨{A,B,T},{A,B,T},hgood _ (by intro Q hQ; simp at hQ ⊢; tauto),
          hgood _ (by intro Q hQ; simp at hQ ⊢; tauto),?_⟩
        intro x
        rw [hH x]
        simp only [hl0,hl1,hr0,hr1,true_and,false_and,or_false,false_or,or_self]
        rw [cnf_three,hJ x]
        tauto
  · by_cases hl1 : l1
    · have hr1 : ¬ r1 := fun h => hdis1 ⟨hl1,h⟩
      by_cases hr0 : r0
      · refine ⟨{R,S,T},D,hgood _ (by intro Q hQ; simp at hQ ⊢; tauto),hdgood,?_⟩
        intro x
        rw [hH x]
        simp only [hl0,hl1,hr0,hr1,true_and,false_and,or_false,false_or]
        rw [hKsplit x,cnf_three]
        have hd := hD x
        have hk := hKsplit x
        tauto
      · refine ⟨{R,S,T},insert T D,hgood _ (by intro Q hQ; simp at hQ ⊢; tauto),htgood,?_⟩
        intro x
        rw [hH x]
        simp only [hl0,hl1,hr0,hr1,true_and,false_and,or_false,false_or]
        rw [hKsplit x,cnf_three]
        have hi : CNF (insert T D) x ↔ Hit T x ∧ CNF D x := by simp [CNF]
        rw [hi]
        tauto
    · refine ⟨{∅},{∅},?_,?_,?_⟩
      · intro Q hQ
        have : Q = ∅ := Finset.mem_singleton.mp hQ
        subst Q
        exact Or.inl (by simp)
      · intro Q hQ
        have : Q = ∅ := Finset.mem_singleton.mp hQ
        subst Q
        exact Or.inl (by simp)
      · intro x
        rw [hH x]
        simp [hl0,hl1,CNF,Hit]
lemma operand_two_junk_nf (hAO : IsAO2 n C) (hT : TopForm G C)
    {j k a : ℕ} (hpair : junk G C = {j,k})
    (ha : a < C.gates.length) (hao : (gateAt C a).op = GateOp.and)
    (b : Fin 2) (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C a b) = true ↔ Hit (side C a b) x ∨
      (OrReaches n C (opnd C a b) j ∧ gateVal n C j x = true) ∨
      (OrReaches n C (opnd C a b) k ∧ gateVal n C k x = true) := by
  constructor
  · intro hx
    rcases operand_support_general hAO hT ha hao b x hx with h | ⟨d,hd,hr,hv⟩
    · exact Or.inl h
    · have he : d = j ∨ d = k := by
        simpa only [hpair,Finset.mem_insert,Finset.mem_singleton] using hd
      rcases he with rfl | rfl
      · exact Or.inr (Or.inl ⟨hr,hv⟩)
      · exact Or.inr (Or.inr ⟨hr,hv⟩)
  · rintro (⟨w,hw,hx⟩ | ⟨hr,hx⟩ | ⟨hr,hx⟩)
    · exact sideVal hw hx
    · exact orStep_up (n := n) (by simp) (orReaches_reach j _ hr).1 hx
    · exact orStep_up (n := n) (by simp) (orReaches_reach k _ hr).1 hx
lemma centreless_two_junk_cnf
    (hAO : IsAO2 n C) (hT : TopForm G C)
    (j k a : ℕ) (hpair : junk G C = {j,k}) (hjk : j < k)
    (ha : a ∈ centreless G C)
    (hraw : ∀ w < n + C.gates.length, Basic G C (orIn n C w)) :
    ∃ F0 F1 : Finset (Finset (Fin n)),
      (∀ Q ∈ F0, Basic G C Q) ∧ (∀ Q ∈ F1, Basic G C Q) ∧
      ∀ x, gateVal n C a x = true ↔ CNF F0 x ∨ CNF F1 x := by
  have hj : j ∈ junk G C := by simp [hpair]
  have hk : k ∈ junk G C := by simp [hpair]
  have hjd := junkData hj
  have hkd := junkData hk
  obtain ⟨hatop,hempty⟩ := Finset.mem_filter.mp ha
  have had := topData hatop
  obtain ⟨b,hb⟩ : ∃ b : Fin 2, side (n := n) C a b = ∅ := by
    rcases hempty with h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  have hs (t : ℕ) (ht : t < C.gates.length) (b : Fin 2) : Basic G C (side C t b) :=
    hraw _ ((opndBound hAO ht b).trans_le (by omega))
  have hJ (x : Fin n → Bool) : gateVal n C j x = true ↔
      Hit (side C j 0) x ∧ Hit (side C j 1) x :=
    (andValBoth hAO hjd.1 hjd.2.1 x).trans (and_congr
      (lower_junk_operand_pure hAO hT hpair hjk 0 x)
      (lower_junk_operand_pure hAO hT hpair hjk 1 x))
  have hK (x : Fin n → Bool) : gateVal n C k x = true ↔
      (Hit (side C k 0) x ∨ (OrReaches n C (opnd C k 0) j ∧ gateVal n C j x = true)) ∧
      (Hit (side C k 1) x ∨ (OrReaches n C (opnd C k 1) j ∧ gateVal n C j x = true)) :=
    (andValBoth hAO hkd.1 hkd.2.1 x).trans (and_congr
      (upper_junk_operand_normal_form hAO hT hpair 0 x)
      (upper_junk_operand_normal_form hAO hT hpair 1 x))
  have disjoint (d : ℕ) (hd : d ∈ junk G C) :
      ¬ (OrReaches n C (opnd C a b) d ∧ OrReaches n C (opnd C a (1-b)) d) := by
    rintro ⟨hl,hr⟩
    obtain ⟨_,_,x,hx,hfalse⟩ := junkData hd
    have hav : gateVal n C a x = true := by
      apply (andValOperands hAO had.1 had.2.1 x).mpr
      intro c
      rcases opposite b c with rfl | rfl
      · exact orStep_up (n := n) (by simp) (orReaches_reach d _ hl).1 hx
      · exact orStep_up (n := n) (by simp) (orReaches_reach d _ hr).1 hx
    exact Bool.false_ne_true (hfalse.symm.trans (had.2.2 x hav))
  refine two_source_top_cnf
    (fun x => gateVal n C j x = true) (fun x => gateVal n C k x = true)
    (fun x => gateVal n C a x = true)
    (side C j 0) (side C j 1) (side C k 0) (side C k 1) (side C a (1-b))
    ?_ (OrReaches n C (opnd C k 0) j) (OrReaches n C (opnd C k 1) j)
    (OrReaches n C (opnd C a b) j) (OrReaches n C (opnd C a b) k)
    (OrReaches n C (opnd C a (1-b)) j) (OrReaches n C (opnd C a (1-b)) k)
    (disjoint j hj) (disjoint k hk) hJ hK ?_
  · intro Q hQ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hQ
    rcases hQ with rfl | rfl | rfl | rfl | rfl
    · exact hs j hjd.1 0
    · exact hs j hjd.1 1
    · exact hs k hkd.1 0
    · exact hs k hkd.1 1
    · exact hs a had.1 (1-b)
  · intro x
    have hab : gateVal n C a x = true ↔
        val C (List.ofFn x) (opnd C a b) = true ∧
        val C (List.ofFn x) (opnd C a (1-b)) = true := by
      fin_cases b
      · simpa using andValBoth hAO had.1 had.2.1 x
      · change gateVal n C a x = true ↔ val C (List.ofFn x) (opnd C a 1) = true ∧ val C (List.ofFn x) (opnd C a 0) = true
        exact (andValBoth hAO had.1 had.2.1 x).trans and_comm
    rw [hab,operand_two_junk_nf hAO hT hpair had.1 had.2.1 b x,
      operand_two_junk_nf hAO hT hpair had.1 had.2.1 (1-b) x]
    simp [hb,Hit]
lemma safe_cnf_subset_card_le_one
    (hfour : NoFourCycle G) (color : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (E : Finset (Sym2 (Fin n))) (hEU : E ⊆ Ustar G C)
    (F : Finset (Finset (Fin n))) (hbasic : ∀ Q ∈ F, Basic G C Q)
    (hcover : ∀ u v, s(u,v) ∈ E → CNF F (pairInput u v))
    (hsafe : ∀ x, CNF F x → graphFun G ∅ x = true) : E.card ≤ 1 := by
  classical
  apply basic_clean_cnf_card_le_one G E color hbip
    (common_neighbors_unique_of_card_le_one G hfour)
    (fun u v he => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hEU he)).1) F id
  · intro Q hQ
    rcases hbasic Q hQ with h | ⟨z,hz⟩
    · exact Or.inl h
    · exact Or.inr ⟨z,fun w hw => ⟨(hz w hw).1,fun he => (hz w hw).2 (hEU he)⟩⟩
  · intro u v he Q hQ
    obtain ⟨w,hw,hx⟩ := hcover u v he Q hQ
    rcases (pairInput_true u v w).mp hx with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw
  · intro x hx
    simpa [graphFun] using hsafe x hx
lemma centreless_two_junk_card_le_two
    (hAO : IsAO2 n C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (j k a : ℕ) (hpair : junk G C = {j,k}) (hjk : j < k)
    (ha : a ∈ centreless G C)
    (hraw : ∀ w < n + C.gates.length, Basic G C (orIn n C w)) :
    (Ustar G C ∩ gammaE G C a).card ≤ 2 := by
  classical
  obtain ⟨F0,F1,hB0,hB1,hNF⟩ := centreless_two_junk_cnf hAO hT j k a hpair hjk ha hraw
  let E := Ustar G C ∩ gammaE G C a
  let E0 := E.filter (EdgeCNF F0)
  let E1 := E.filter (EdgeCNF F1)
  have hEa : E ⊆ Ustar G C := fun e he => (Finset.mem_inter.mp he).1
  have hb := (topData (Finset.mem_filter.mp ha).1).2.2
  have h0 : E0.card ≤ 1 := by
    apply safe_cnf_subset_card_le_one hfour color hbip E0
      (fun e he => hEa (Finset.mem_filter.mp he).1) F0 hB0
    · intro u v he
      exact (edgeCNF_pair_iff F0 u v).mp (Finset.mem_filter.mp he).2
    · intro x hx
      exact hb x ((hNF x).mpr (Or.inl hx))
  have h1 : E1.card ≤ 1 := by
    apply safe_cnf_subset_card_le_one hfour color hbip E1
      (fun e he => hEa (Finset.mem_filter.mp he).1) F1 hB1
    · intro u v he
      exact (edgeCNF_pair_iff F1 u v).mp (Finset.mem_filter.mp he).2
    · intro x hx
      exact hb x ((hNF x).mpr (Or.inr hx))
  have cover : E ⊆ E0 ∪ E1 := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      have hav := gate_accepts_pair_of_gammaE (Finset.mem_inter.mp he).2
      rcases (hNF (pairInput u v)).mp hav with hx | hx
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
          ⟨he,(edgeCNF_pair_iff F0 u v).mpr hx⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨he,(edgeCNF_pair_iff F1 u v).mpr hx⟩))
  have hc := Finset.card_le_card cover
  have hu := Finset.card_union_le E0 E1
  change E.card ≤ 2
  omega
lemma one_active_extra_all_raw_basic
    (hAO : IsAO2 n C) (m d : ℕ)
    (hextra : orN G C \ lam G C = {m}) (hd : d ∈ junk G C)
    (hpath : Relation.ReflTransGen (OrStep n C) (n+m) (n+d)) :
    ∀ w < n + C.gates.length, Basic G C (orIn n C w) := by
  have hm : m ∈ orN G C \ lam G C := by simp [hextra]
  have hfirst : ∀ r ∈ orN G C \ lam G C, m ≤ r := by
    intro r hr
    have : r = m := by simpa only [hextra,Finset.mem_singleton] using hr
    omega
  have hmb := first_mixed_raw_basic hAO hm hfirst hd hpath
  intro w hw
  rcases PureExceptional.raw_shape_or_extra (G := G) hAO hw with hb | ⟨r,hr,rfl⟩
  · exact hb
  · have : r = m := by simpa only [hextra,Finset.mem_singleton] using hr
    simpa only [this] using hmb
end OneCentreless
namespace OneCentreless
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget ChainMixed EarlySources
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma prefix_served_card_le_one
    (hAO : IsAO2 n C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
        (T : Finset (Sym2 (Fin n))) (hTU : T ⊆ Ustar G C)
    (j m : ℕ) (hml : m ≤ C.gates.length)
    (first : ∀ r ∈ orN G C \ lam G C, m ≤ r) (hjm : j < m) (hj : j ∈ junk G C) (hm : (orIn n C (n + m)).Nonempty)
    (hserved : ∀ e ∈ T, Served G C j m e) : T.card ≤ 1 := by
  obtain ⟨t, ht⟩ := hm
  have fires : ∀ u v : Fin n, s(u, v) ∈ T → gateVal n C j (pairInput u v) = true := by
    intro u v huv
    obtain ⟨a, ha, b, hr, hp, hgamma, _⟩ := hserved s(u, v) huv
    exact gate_accepts_pair_of_gammaE hgamma
  apply cover_property_card_le_one G T color hbip
    (common_neighbors_unique_of_card_le_one G hfour)
    (fun u v huv => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hTU huv)).1) t
  intro u v huv
  obtain ⟨a, ha, b, hr, hp, _, w, hw, hwe⟩ := hserved s(u, v) huv
  have ht' : t ∈ side C a b := reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
  have hclean := cleanAdj hAO ha b ht' hw
  refine ⟨w, Sym2.mem_iff.mp hwe, (SimpleGraph.deleteEdges_adj.mp hclean).1,
    fun h => (SimpleGraph.deleteEdges_adj.mp hclean).2 (hTU h), ?_⟩
  intro x hx hind
  have hnone : ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
    rintro ⟨a, b, hab, ha, hb⟩
    exact Bool.false_ne_true ((hind a b hab ha).symm.trans hb)
  have hF : graphFun G ∅ x = false := by simp [graphFun, hnone]
  have hjfalse : gateVal n C j x = false := by
    apply Bool.eq_false_iff.mpr
    intro hjtrue
    have hFx := firingTop hAO ha (orReaches_reach j _ hr).1 hw x hjtrue hx
    exact Bool.false_ne_true (hF.symm.trans hFx)
  obtain ⟨S, hshape, hcover, hfalse⟩ := PrefixSources.prefix_false_junk_cover hAO hT hml first T x j hjm hj fires hjfalse
  refine ⟨S, ?_, hcover, hfalse⟩
  rcases hshape with hsmall | ⟨z, hz⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨z, fun y hy => ⟨(SimpleGraph.deleteEdges_adj.mp (hz y hy)).1,
      fun h => (SimpleGraph.deleteEdges_adj.mp (hz y hy)).2 (hTU h)⟩⟩
lemma noncentreless_sides {a : ℕ} (ha : a ∈ tops G C) (hnot : a ∉ centreless G C)
    (b : Fin 2) : (side (n := n) C a b).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  apply hnot
  apply Finset.mem_filter.mpr
  refine ⟨ha,?_⟩
  fin_cases b
  · exact Or.inl he
  · exact Or.inr he
lemma noncentreless_single_path (hAO : IsAO2 n C)
    {a m d : ℕ} (ha : a ∈ tops G C) (hnot : a ∉ centreless G C)
    (hextra : orN G C \ lam G C = {m})
    (hd : d ∈ junk G C) {b : Fin 2} (hr : OrReaches n C (opnd C a b) d) :
    n+d ∈ (gateAt C m).inputs ∧
      Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+m) ∧
      (orIn n C (n+m)).Nonempty := by
  have hside := noncentreless_sides ha hnot b
  rcases lastOrBefore (orReaches_reach d _ hr).1 with he | ⟨r,rl,ro,ri,rb,rp⟩
  · change (orIn n C (opnd C a b)).Nonempty at hside
    rw [he,andRawEmpty (junkData hd).2.1] at hside
    exact (Finset.not_nonempty_empty hside).elim
  · have hrR := lastOrOutside hAO hd rl ro ri rb
    have hrm : r = m := by simpa only [hextra,Finset.mem_singleton] using hrR
    subst r
    refine ⟨ri,rp,?_⟩
    rw [Finset.nonempty_iff_ne_empty]
    intro hz
    rcases lastOrBefore rp with he | ⟨l,ll,lo,li,lb,lp⟩
    · change (orIn n C (opnd C a b)).Nonempty at hside
      rw [he,hz] at hside
      exact Finset.not_nonempty_empty hside
    · have hlR := emptyInputOutside hAO (orData hrR).2.2 hz ll lo li
      have hlm : l = m := by simpa only [hextra,Finset.mem_singleton] using hlR
      omega
lemma residual_at_top (hAO : IsAO2 n C) (hT : TopForm G C)
    {a : ℕ} (ha : a ∈ tops G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) (hv : gateVal n C a (pairInput u v) = true) :
    ∃ b : Fin 2, ∃ j ∈ junk G C,
      OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
  obtain ⟨hl,ho,_⟩ := topData ha
  have h := (andValOperands hAO hl ho _).mp hv
  rcases operandSupport hAO hT hl ho (b := 0) (h 0) with ⟨x,hx,hex⟩ | ⟨j,hj,hr,hjv⟩
  · rcases operandSupport hAO hT hl ho (b := 1) (h 1) with ⟨y,hy,hey⟩ | ⟨j,hj,hr,hjv⟩
    · have hxy : x ≠ y := (topAdj hAO ha hx hy).ne
      apply ((Finset.mem_sdiff.mp he).2 ?_).elim
      unfold starEdges
      refine Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr
        ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,?_⟩⟩
      rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    · exact ⟨1,j,hj,hr,hjv⟩
  · exact ⟨0,j,hj,hr,hjv⟩
lemma noncentreless_single_extra_card_le_one
    (hAO : IsAO2 n C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (m : ℕ) (hextra : orN G C \ lam G C = {m})
    (O : Finset (Sym2 (Fin n))) (hOU : O ⊆ Ustar G C)
    (hroute : ∀ e ∈ O, ∃ a ∈ tops G C, a ∉ centreless G C ∧ e ∈ gammaE G C a) :
    O.card ≤ 1 := by
  classical
  by_cases hO : O.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hO]
  obtain ⟨e,he⟩ := hO
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨a,ha,hnot,hgamma⟩ := hroute s(u,v) he
    obtain ⟨b,j,hj,hr,hjv⟩ := residual_at_top hAO hT ha (hOU he) (gate_accepts_pair_of_gammaE hgamma)
    obtain ⟨hji,hp,hraw⟩ := noncentreless_single_path hAO ha hnot hextra hj hr
    have hm : m ∈ orN G C \ lam G C := by simp [hextra]
    have hml := (orData hm).1
    have hjm : j < m := by
      have := hAO.2.1 m hml (n+j) hji
      omega
    apply prefix_served_card_le_one hAO hT hfour color hbip O hOU j m hml.le
      (fun r h => by
        have : r = m := by simpa only [hextra,Finset.mem_singleton] using h
        omega)
      hjm hj hraw
    intro f hf
    induction f using Sym2.ind with
    | h p q =>
      obtain ⟨a',ha',hnot',hgamma'⟩ := hroute s(p,q) hf
      have hav := gate_accepts_pair_of_gammaE hgamma'
      obtain ⟨b',d,hd,hdr,hdv⟩ := residual_at_top hAO hT ha' (hOU hf) hav
      obtain ⟨hdi,hdp,_⟩ := noncentreless_single_path hAO ha' hnot' hextra hd hdr
      have hdj := singleJunkInput hAO hm hraw hd hj hdi hji
      subst d
      have hend : ∃ w ∈ side C a' (1-b'), w = p ∨ w = q := by
        obtain ⟨al,ao,ab⟩ := topData ha'
        have hv := (andValOperands hAO al ao _).mp hav (1-b')
        rcases operandSupport hAO hT al ao hv with h | ⟨l,hl,hlr,hlv⟩
        · exact h
        · obtain ⟨hli,hlp,_⟩ := noncentreless_single_path hAO ha' hnot' hextra hl hlr
          exfalso
          apply (orData hm).2.2
          intro x hx
          apply ab x ((andValOperands hAO al ao x).mpr ?_)
          intro c
          rcases opposite b' c with rfl | rfl
          · exact orStep_up (n := n) (by simp) hdp hx
          · exact orStep_up (n := n) (by simp) hlp hx
      obtain ⟨w,hw,hwe⟩ := hend
      exact ⟨a',ha',b',hdr,hdp,Finset.mem_filter.mpr
        ⟨(Finset.mem_sdiff.mp (hOU hf)).1,p,q,rfl,hdv⟩,w,hw,Sym2.mem_iff.mpr hwe⟩
end OneCentreless
namespace OneCentreless
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget ChainMixed
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma one_centreless_single_extra_raw_basic_card_le_three
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hcentre : (centreless G C).card ≤ 1)
    (j k m : ℕ) (hpair : junk G C = {j,k}) (hjk : j < k)
    (hextra : orN G C \ lam G C = {m})
    (hraw : ∀ w < n + C.gates.length, Basic G C (orIn n C w)) :
    (Ustar G C).card ≤ 3 := by
  classical
  let O := (Ustar G C).filter fun e =>
    ∃ a ∈ tops G C, a ∉ centreless G C ∧ e ∈ gammaE G C a
  have hOU : O ⊆ Ustar G C := fun e he => (Finset.mem_filter.mp he).1
  have hO : O.card ≤ 1 := noncentreless_single_extra_card_le_one hleast.1 hT hfour color hbip
    m hextra O hOU (fun e he => (Finset.mem_filter.mp he).2)
  by_cases hz : (centreless G C).Nonempty
  · obtain ⟨a,ha⟩ := hz
    let E := Ustar G C ∩ gammaE G C a
    have hE : E.card ≤ 2 := centreless_two_junk_card_le_two hleast.1 hT hfour color hbip
      j k a hpair hjk ha hraw
    have hcover : Ustar G C ⊆ O ∪ E := by
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        obtain ⟨b,hb,hv⟩ := acceptedTop hleast (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1)
        have hg : s(u,v) ∈ gammaE G C b := Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp he).1,u,v,rfl,hv⟩
        by_cases hbc : b ∈ centreless G C
        · have hba : b = a := Finset.card_le_one.mp hcentre b hbc a ha
          subst b
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨he,hg⟩))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨he,b,hb,hbc,hg⟩))
    have hc := Finset.card_le_card hcover
    have hu := Finset.card_union_le O E
    omega
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hz
    have hcover : Ustar G C ⊆ O := by
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        obtain ⟨a,ha,hv⟩ := acceptedTop hleast (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1)
        refine Finset.mem_filter.mpr ⟨he,a,ha,by simp [hempty],?_⟩
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1,u,v,rfl,hv⟩
    have hc := Finset.card_le_card hcover
    omega
lemma one_centreless_single_active_extra_card_le_three
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hcentre : (centreless G C).card ≤ 1)
    (j k m d : ℕ) (hpair : junk G C = {j,k}) (hjk : j < k)
    (hextra : orN G C \ lam G C = {m}) (hd : d ∈ junk G C)
    (hpath : Relation.ReflTransGen (OrStep n C) (n+m) (n+d)) :
    (Ustar G C).card ≤ 3 :=
  one_centreless_single_extra_raw_basic_card_le_three hleast hT hfour color hbip hcentre
    j k m hpair hjk hextra (one_active_extra_all_raw_basic hleast.1 m d hextra hd hpath)
end OneCentreless
namespace OneCentreless
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget ChainMixed
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma singleton_extra_raw_union_basic
    (hAO : IsAO2 n C) (m : ℕ) (hextra : orN G C \ lam G C = {m}) :
    ∃ A B : Finset (Fin n), Basic G C A ∧ Basic G C B ∧ orIn n C (n+m) = A ∪ B := by
  have hm : m ∈ orN G C \ lam G C := by simp [hextra]
  have hmd := orData hm
  have first : ∀ r ∈ orN G C \ lam G C, m ≤ r := by
    intro r hr
    have : r = m := by simpa only [hextra,Finset.mem_singleton] using hr
    omega
  refine ⟨side C m 0,side C m 1,?_,?_,raw_or_union hAO hmd.1 hmd.2.1⟩
  · exact basic_of_clean_shape (prefix_raw_cover_shape_local hAO hmd.1.le first (opndBound hAO hmd.1 0))
  · exact basic_of_clean_shape (prefix_raw_cover_shape_local hAO hmd.1.le first (opndBound hAO hmd.1 1))
lemma blocked_extra_false_and_cover
    (hAO : IsAO2 n C) (hT : TopForm G C)
    (m : ℕ) (hextra : orN G C \ lam G C = {m})
    (hblocked : ∀ j ∈ junk G C, ¬ Relation.ReflTransGen (OrStep n C) (n+m) (n+j))
    (T : Finset (Sym2 (Fin n))) (x : Fin n → Bool) :
    ∀ a, a < C.gates.length → (gateAt C a).op = GateOp.and →
      (∀ u v, s(u,v) ∈ T → gateVal n C a (pairInput u v) = true) →
      gateVal n C a x = false →
      ∃ S : Finset (Fin n), (Basic G C S ∨ S = orIn n C (n+m)) ∧
        (∀ u v, s(u,v) ∈ T → u ∈ S ∨ v ∈ S) ∧ ∀ w ∈ S, x w = false := by
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    intro al ao fires hx
    have hfalse : ∃ b : Fin 2, val C (List.ofFn x) (opnd C a b) = false := by
      by_contra hn
      have hv := (andValOperands hAO al ao x).mpr (fun b => by
        cases hval : val C (List.ofFn x) (opnd C a b) with
        | true => rfl
        | false => exact (hn ⟨b,hval⟩).elim)
      exact Bool.false_ne_true (hx.symm.trans hv)
    obtain ⟨b,hb⟩ := hfalse
    have firesOp (u v : Fin n) (he : s(u,v) ∈ T) :
        val C (List.ofFn (pairInput u v)) (opnd C a b) = true :=
      (andValOperands hAO al ao _).mp (fires u v he) b
    have direct (k : ℕ) (hk : k ∈ junk G C) (hr : OrReaches n C (opnd C a b) k) :
        opnd C a b = n+k := by
      rcases lastOrBefore (orReaches_reach k _ hr).1 with h | ⟨r,rl,ro,ri,rb,rp⟩
      · exact h
      · have hrR := lastOrOutside hAO hk rl ro ri rb
        have hrm : r = m := by simpa only [hextra,Finset.mem_singleton] using hrR
        subst r
        exact (hblocked k hk (EffectiveExtra.extra_or_direct_path hAO hrR ri)).elim
    by_cases hd : ∃ k, k ∈ junk G C ∧ opnd C a b = n+k
    · obtain ⟨k,hk,he⟩ := hd
      have hbound := opndBound hAO al b
      have hka : k < a := by omega
      obtain ⟨kl,ko,_⟩ := junkData hk
      apply ih k hka kl ko
      · intro u v hu
        have hv := firesOp u v hu
        rw [he] at hv
        exact hv
      · rw [he] at hb
        exact hb
    · refine ⟨orIn n C (opnd C a b),?_,?_,?_⟩
      · rcases PureExceptional.raw_shape_or_extra (G := G) hAO
          ((opndBound hAO al b).trans_le (by omega)) with hs | ⟨r,hr,he⟩
        · exact Or.inl hs
        · have hrm : r = m := by simpa only [hextra,Finset.mem_singleton] using hr
          exact Or.inr (congrArg (orIn n C) (he.trans (by omega)))
      · intro u v he
        rcases operandSupport hAO hT al ao (firesOp u v he) with ⟨t,ht,rfl | rfl⟩ | ⟨k,hk,hr,_⟩
        · exact Or.inl ht
        · exact Or.inr ht
        · exact (hd ⟨k,hk,direct k hk hr⟩).elim
      · intro t ht
        apply Bool.eq_false_iff.mpr
        intro ht'
        exact Bool.false_ne_true (hb.symm.trans (reach_var_val x _ t (mem_orIn_reach t ht) ht'))
lemma blocked_extra_no_noncentreless_residual
    (hAO : IsAO2 n C) (hT : TopForm G C)
    (m : ℕ) (hextra : orN G C \ lam G C = {m})
    (hblocked : ∀ j ∈ junk G C, ¬ Relation.ReflTransGen (OrStep n C) (n+m) (n+j))
    {a : ℕ} (ha : a ∈ tops G C) (hnot : a ∉ centreless G C)
    {u v : Fin n} (he : s(u,v) ∈ Ustar G C) : gateVal n C a (pairInput u v) ≠ true := by
  intro hv
  obtain ⟨b,j,hj,hr,hjv⟩ := residual_at_top hAO hT ha he hv
  obtain ⟨hji,_,_⟩ := noncentreless_single_path hAO ha hnot hextra hj hr
  have hm : m ∈ orN G C \ lam G C := by simp [hextra]
  exact hblocked j hj (EffectiveExtra.extra_or_direct_path hAO hm hji)
end OneCentreless
namespace OneCentreless
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget ChainMixed
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma one_centreless_single_blocked_extra_card_le_two
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hcentre : (centreless G C).card ≤ 1)
    (m : ℕ) (hextra : orN G C \ lam G C = {m})
    (hblocked : ∀ j ∈ junk G C, ¬ Relation.ReflTransGen (OrStep n C) (n+m) (n+j)) :
    (Ustar G C).card ≤ 2 := by
  classical
  by_cases hU : (Ustar G C).Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hU]
  obtain ⟨e,he⟩ := hU
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨a,ha,hav⟩ := acceptedTop hleast (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1)
    have hac : a ∈ centreless G C := by
      by_contra hnot
      exact blocked_extra_no_noncentreless_residual hleast.1 hT m hextra hblocked ha hnot he hav
    have fires (p q : Fin n) (hpq : s(p,q) ∈ Ustar G C) : gateVal n C a (pairInput p q) = true := by
      obtain ⟨b,hb,hbv⟩ := acceptedTop hleast (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hpq).1)
      have hbc : b ∈ centreless G C := by
        by_contra hnot
        exact blocked_extra_no_noncentreless_residual hleast.1 hT m hextra hblocked hb hnot hpq hbv
      have hba : b = a := Finset.card_le_one.mp hcentre b hbc a hac
      simpa only [hba] using hbv
    obtain ⟨A,B,hA,hB,hunion⟩ := singleton_extra_raw_union_basic hleast.1 m hextra
    apply GlobalExceptional.global_exceptional_cover_card_le_two G (Ustar G C) color hbip
      (common_neighbors_unique_of_card_le_one G hfour)
      (fun p q hpq => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hpq).1) A B hA hB
    intro x hind
    have hnone : ¬ ∃ p q, G.Adj p q ∧ x p = true ∧ x q = true := by
      rintro ⟨p,q,hpq,hp,hq⟩
      exact Bool.false_ne_true ((hind p q hpq hp).symm.trans hq)
    have hF : graphFun G ∅ x = false := by simp [graphFun,hnone]
    have had := topData ha
    have hax : gateVal n C a x = false := by
      apply Bool.eq_false_iff.mpr
      intro hx
      exact Bool.false_ne_true (hF.symm.trans (had.2.2 x hx))
    obtain ⟨S,hS,hcover,hfalse⟩ := blocked_extra_false_and_cover hleast.1 hT m hextra hblocked
      (Ustar G C) x a had.1 had.2.1 fires hax
    refine ⟨S,?_,hcover,hfalse⟩
    rcases hS with hS | hS
    · exact Or.inl hS
    · exact Or.inr (hS.trans hunion)
lemma one_centreless_two_junk_single_extra_card_le_three
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hcentre : (centreless G C).card ≤ 1)
    (j k m : ℕ) (hpair : junk G C = {j,k}) (hjk : j < k)
    (hextra : orN G C \ lam G C = {m}) : (Ustar G C).card ≤ 3 := by
  by_cases hactive : ∃ d ∈ junk G C, Relation.ReflTransGen (OrStep n C) (n+m) (n+d)
  · obtain ⟨d,hd,hpath⟩ := hactive
    exact one_centreless_single_active_extra_card_le_three hleast hT hfour color hbip hcentre
      j k m d hpair hjk hextra hd hpath
  · have hblocked : ∀ d ∈ junk G C, ¬ Relation.ReflTransGen (OrStep n C) (n+m) (n+d) := by
      intro d hd hp
      exact hactive ⟨d,hd,hp⟩
    have := one_centreless_single_blocked_extra_card_le_two hleast hT hfour color hbip hcentre
      m hextra hblocked
    omega
end OneCentreless
lemma bipartite_penalty_five_positive_centreless_ustar_card_le_three
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfour : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hleast : IsLeastAO G C) (hT : TopForm G C)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hjunk : 2 ≤ (junk G C).card) (hcentre : 0 < (centreless G C).card)
    (hP : 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card = 5) :
    (Ustar G C).card ≤ 3 := by
  have hRpos : 0 < (orN G C \ lam G C).card := by
    by_contra h
    have hRzero : orN G C \ lam G C = ∅ := Finset.card_eq_zero.mp (by omega)
    have hJzero := bipartite_zero_extra_or_junk_empty n G C hfour hE hleast hT color hbip hRzero
    simp [hJzero] at hjunk
  have hJcard : (junk G C).card = 2 := by omega
  have hRcard : (orN G C \ lam G C).card = 1 := by omega
  have hjpair : ∃ j k : ℕ, j < k ∧ junk G C = {j, k} := by
    obtain ⟨j, k, hne, he⟩ := Finset.card_eq_two.mp hJcard
    by_cases hlt : j < k
    · exact ⟨j, k, hlt, he⟩
    · exact ⟨k, j, by omega, by simpa only [Finset.pair_comm] using he⟩
  obtain ⟨j, k, hjk, hpair⟩ := hjpair
  obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hRcard
  exact OneCentreless.one_centreless_two_junk_single_extra_card_le_three
    hleast hT hfour color hbip (by omega) j k m hpair hjk hm
lemma deleted_cover_density
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U : Finset (Sym2 (Fin n))) (K : Finset (Fin n))
    (hcover : (G.deleteEdges (U : Set (Sym2 (Fin n)))).IsVertexCover (K : Set (Fin n)))
    (d : ℕ) (hdegree : ∀ v ∈ K, G.degree v ≤ d) :
    G.edgeFinset.card ≤ d * K.card + U.card := by
  classical
  have hsub : G.edgeFinset ⊆ U ∪ K.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    by_cases heU : e ∈ U
    · exact Finset.mem_union_left _ heU
    · apply Finset.mem_union_right
      induction e using Sym2.ind with
      | h u v =>
        have hadj := SimpleGraph.mem_edgeFinset.mp he
        have hdel := SimpleGraph.deleteEdges_adj.mpr ⟨hadj, heU⟩
        rcases hcover hdel with hu | hv
        · exact Finset.mem_biUnion.mpr ⟨u, hu,
            SimpleGraph.mem_incidenceFinset.mpr (G.mk'_mem_incidenceSet_left_iff.mpr hadj)⟩
        · exact Finset.mem_biUnion.mpr ⟨v, hv,
            SimpleGraph.mem_incidenceFinset.mpr (G.mk'_mem_incidenceSet_right_iff.mpr hadj)⟩
  have hcount := Finset.card_le_card hsub
  have hsum := Finset.card_biUnion_le (s := K) (t := fun v => G.incidenceFinset v)
  have hdegs : ∑ v ∈ K, (G.incidenceFinset v).card ≤ d * K.card := by
    calc
      _ ≤ ∑ v ∈ K, d := Finset.sum_le_sum (fun v hv => by
        simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using hdegree v hv)
      _ = _ := by simp [Nat.mul_comm]
  have hunion := Finset.card_union_le U (K.biUnion (fun v => G.incidenceFinset v))
  omega
namespace PlaneP4
def pointPart (N : ℕ) (K : Finset (Fin (N + N))) : Finset (Fin N) :=
  Finset.univ.filter (fun p => Fin.castAdd N p ∈ K)
def linePart (N : ℕ) (K : Finset (Fin (N + N))) : Finset (Fin N) :=
  Finset.univ.filter (fun l => Fin.natAdd N l ∈ K)
lemma parts_card (N : ℕ) (K : Finset (Fin (N + N))) :
    (pointPart N K).card + (linePart N K).card = K.card := by
  calc
    _ = (∑ p : Fin N, if Fin.castAdd N p ∈ K then 1 else 0) +
      ∑ l : Fin N, if Fin.natAdd N l ∈ K then 1 else 0 := by
        simp only [pointPart, linePart, Finset.card_filter]
    _ = ∑ v : Fin (N + N), if v ∈ K then 1 else 0 := by
      rw [Fin.sum_univ_add]
    _ = K.card := by simp
lemma edge_map_injective (N : ℕ) : Function.Injective
    (fun e : Fin N × Fin N => s(Fin.castAdd N e.1, Fin.natAdd N e.2)) := by
  intro e f h
  rcases Sym2.eq_iff.mp h with ⟨hp, hl⟩ | ⟨hp, hl⟩
  · apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun x : Fin (N + N) => x.val) hp
    · apply Fin.ext
      have he := congrArg Fin.val hl
      simp only [Fin.val_natAdd] at he
      omega
  · have he := congrArg Fin.val hp
    simp only [Fin.val_castAdd, Fin.val_natAdd] at he
    have := e.1.isLt
    omega
lemma missing_card_le
    (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (hinc : ∀ p l, I p l → G.Adj (Fin.castAdd N p) (Fin.natAdd N l))
    (U : Finset (Sym2 (Fin (N + N)))) (K : Finset (Fin (N + N)))
    (hcover : (G.deleteEdges (U : Set (Sym2 (Fin (N + N))))).IsVertexCover (K : Set (Fin (N + N)))) :
    (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ pointPart N K ∧ e.2 ∉ linePart N K)).card ≤ U.card := by
  classical
  let M := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ e.1 ∉ pointPart N K ∧ e.2 ∉ linePart N K)
  apply Finset.card_le_card_of_injOn
    (fun e : Fin N × Fin N => s(Fin.castAdd N e.1, Fin.natAdd N e.2))
  · intro e he
    obtain ⟨_, hi, hp, hl⟩ := Finset.mem_filter.mp he
    by_contra hn
    rcases hcover (SimpleGraph.deleteEdges_adj.mpr ⟨hinc e.1 e.2 hi, hn⟩) with hpK | hlK
    · exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpK⟩)
    · exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlK⟩)
  · intro e he f hf h
    exact edge_map_injective N h
lemma incidence_subset_deleted
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U : Finset (Sym2 (Fin n))) (K : Finset (Fin n))
    (hcover : (G.deleteEdges (U : Set (Sym2 (Fin n)))).IsVertexCover (K : Set (Fin n)))
    (p : Fin n) (hp : p ∉ K) (hneigh : ∀ v, G.Adj p v → v ∉ K) :
    G.incidenceFinset p ⊆ U := by
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨hadj, hpu | hpv⟩ := G.mk'_mem_incidenceSet_iff.mp (SimpleGraph.mem_incidenceFinset.mp he)
    · subst u
      by_contra hn
      exact (hcover (SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hn⟩)).elim hp (hneigh v hadj)
    · subst v
      by_contra hn
      exact (hcover (SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hn⟩)).elim (hneigh u hadj.symm) hp
lemma encoded_plane_small_uncovered_lower
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 3 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (hinc : ∀ p l, I p l → G.Adj (Fin.castAdd N p) (Fin.natAdd N l))
    (hbip : ∀ a b, G.Adj a b → decide (a.val < N) ≠ decide (b.val < N))
    (hdegree : ∀ v, G.degree v = q + 1)
    (hedges : G.edgeFinset.card = N * (q + 1))
    (hfour : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (C : Circuit) (hleast : IsLeastAO G C) (hT : TopForm G C)
    (hjunk : 2 ≤ (junk G C).card)
    (hU : (Ustar G C).card ≤ 4) :
    N * (q + 1) + N ≤ C.size + 1 := by
  classical
  let color : Fin (N + N) → Bool := fun v => decide (v.val < N)
  let P := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  have hPlower : 4 ≤ P := bipartite_two_junk_penalty_four
    (N + N) G C color hbip hfour hE hleast hT hjunk
  obtain ⟨hledger, hcoverBound⟩ := Ledger.main (N + N) G C hfour hE hleast hT
  obtain ⟨K, hK⟩ := finite_min_cover_exists (N + N) (G.deleteEdges (Ustar G C : Set (Sym2 (Fin (N + N)))))
  have hKbound := hcoverBound K hK
  have hdensity := deleted_cover_density G (Ustar G C) K hK.1 (q + 1)
    (fun v _ => by rw [hdegree])
  have hparts := parts_card N K
  have hmissing := missing_card_le N I G hinc (Ustar G C) K hK.1
  by_contra hnot
  have hbad : C.size + 1 < N * (q + 1) + N := by omega
  have hledger' : N * (q + 1) + (tops G C \ centreless G C).card + P ≤
      C.size + (Ustar G C).card + 1 := by
    rw [hedges] at hledger
    dsimp only [P]
    omega
  have hdensity' : N * (q + 1) ≤
      (q + 1) * ((pointPart N K).card + (linePart N K).card) + (Ustar G C).card := by
    rw [hedges, ← hparts] at hdensity
    exact hdensity
  obtain ⟨_, _, hP4, _, _, hshape⟩ := small_counterexample_cover_shape
    q N (tops G C \ centreless G C).card (Ustar G C).card P C.size I
    (pointPart N K) (linePart N K) hq hN hcol hpair hPlower hU
    (by omega) hdensity' hmissing hledger' hbad
  obtain ⟨hJ, hz, hr⟩ := bipartite_penalty_four_shape (N + N) G C hfour hE hleast hT color hbip hjunk hP4
  obtain ⟨j, k, _, hJK⟩ := Finset.card_eq_two.mp hJ
  have forbidden (v : Fin (N + N)) (hsub : G.incidenceFinset v ⊆ Ustar G C) : False := by
    have hcard : (Ustar G C).card ≤ (G.incidenceFinset v).card := by
      rw [G.card_incidenceFinset_eq_degree, hdegree]
      omega
    have heq : G.incidenceFinset v = Ustar G C := Finset.eq_of_subset_of_card_le hsub hcard
    have hstar : ∀ u w, s(u, w) ∈ Ustar G C ↔ G.Adj u w ∧ (u = v ∨ w = v) := by
      intro u w
      rw [← heq]
      simp [G.incidenceFinset_eq_filter, Sym2.mem_iff, eq_comm]
    have hsmall := TwoJunkFullStar.two_junk_two_extra_or_full_star_card_le_three
      hleast hT hfour hz (by omega) v hstar j k hJK
    rw [← heq, G.card_incidenceFinset_eq_degree, hdegree] at hsmall
    omega
  rcases hshape with ⟨p, hA, hB⟩ | ⟨l, hA, hB⟩
  · apply forbidden (Fin.castAdd N p)
    apply incidence_subset_deleted G (Ustar G C) K hK.1
    · intro hpK
      have hpA : p ∈ pointPart N K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpK⟩
      rw [hA] at hpA
      exact (Finset.mem_erase.mp hpA).1 rfl
    · intro v
      refine Fin.addCases ?_ ?_ v
      · intro p'
        intro hv hp'K
        have h := hbip (Fin.castAdd N p) (Fin.castAdd N p') hv
        simp only [Fin.val_castAdd, Fin.is_lt, decide_true] at h
        exact h rfl
      · intro l'
        intro hv hl'K
        have hlB : l' ∈ linePart N K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'K⟩
        rw [hB] at hlB
        exact Finset.notMem_empty _ hlB
  · apply forbidden (Fin.natAdd N l)
    apply incidence_subset_deleted G (Ustar G C) K hK.1
    · intro hlK
      have hlB : l ∈ linePart N K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlK⟩
      rw [hB] at hlB
      exact (Finset.mem_erase.mp hlB).1 rfl
    · intro v
      refine Fin.addCases ?_ ?_ v
      · intro p'
        intro hv hp'K
        have hpA : p' ∈ pointPart N K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp'K⟩
        rw [hA] at hpA
        exact Finset.notMem_empty _ hpA
      · intro l'
        intro hv hl'K
        have h := hbip (Fin.natAdd N l) (Fin.natAdd N l') hv
        have hc : decide ((Fin.natAdd N l).val < N) = false := by simp
        have hc' : decide ((Fin.natAdd N l').val < N) = false := by simp
        exact h (hc.trans hc'.symm)
lemma encoded_plane_subcanonical_uncovered_ge_five
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 3 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (hinc : ∀ p l, I p l → G.Adj (Fin.castAdd N p) (Fin.natAdd N l))
    (hbip : ∀ a b, G.Adj a b → decide (a.val < N) ≠ decide (b.val < N))
    (hdegree : ∀ v, G.degree v = q + 1)
    (hedges : G.edgeFinset.card = N * (q + 1))
    (hfour : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (C : Circuit) (hleast : IsLeastAO G C) (hT : TopForm G C)
    (hjunk : 2 ≤ (junk G C).card)
    (hbad : C.size + 1 < N * (q + 1) + N) : 5 ≤ (Ustar G C).card := by
  by_contra h
  have hbound := encoded_plane_small_uncovered_lower q N I hq hN hcol hpair
    G hinc hbip hdegree hedges hfour hE C hleast hT hjunk (by omega)
  omega
end PlaneP4
namespace SharedSource
open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma cnf_union (S T : Finset (Finset (Fin n))) (x : Fin n → Bool) :
    CNF (S ∪ T) x ↔ CNF S x ∧ CNF T x := by
  classical
  simp only [CNF, Finset.mem_union, or_imp, forall_and]
lemma first_extra_direct_junk (ao : IsAO2 n C) {m j : ℕ}
    (hm : m ∈ orN G C \ lam G C) (first : ∀ r ∈ orN G C \ lam G C, m ≤ r)
    (hj : j ∈ junk G C)
    (path : Relation.ReflTransGen (OrStep n C) (n + m) (n + j)) :
    n + j ∈ (gateAt C m).inputs := by
  rcases lastOrBefore path with he | ⟨l, hl, hlo, hli, hlb, hml⟩
  · have eq : m = j := by omega
    have ho := (junkData hj).2.1
    rw [← eq, (orData hm).2.1] at ho
    contradiction
  · have hlR := lastOrOutside ao hj hl hlo hli hlb
    have hle := first l hlR
    have hge := orStep_le hml
    have eq : l = m := by omega
    simpa only [eq] using hli
lemma shared_source_cnf_normal_form
    (ao : IsAO2 n C) (top : TopForm G C) {m j B : ℕ}
    (hm : m ∈ orN G C \ lam G C) (first : ∀ r ∈ orN G C \ lam G C, m ≤ r)
    (only_before : ∀ r ∈ orN G C \ lam G C, r < B → r = m)
    (hB : B ≤ C.gates.length) (hj : j ∈ junk G C)
    (path : Relation.ReflTransGen (OrStep n C) (n + m) (n + j))
    (hmraw : (orIn n C (n + m)).Nonempty) :
    ∀ k < B, k ∈ junk G C → ∃ S T : Finset (Finset (Fin n)),
      (∀ A ∈ S, Basic G C A) ∧ (∀ A ∈ T, Basic G C A) ∧
      ∀ x : Fin n → Bool, gateVal n C k x = true ↔
        CNF S x ∧ (gateVal n C j x = true ∨ CNF T x) := by
  classical
  have hjin := first_extra_direct_junk ao hm first hj path
  have rawbasic : ∀ w < n + B, Basic G C (orIn n C w) :=
    fun w hw => raw_before_upper_basic ao hm first only_before hB hj path hw
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hkB hkj
    by_cases hkj_eq : k = j
    · subst k
      refine ⟨∅, {∅}, by simp, ?_, ?_⟩
      · intro A hA
        have hA' : A = ∅ := Finset.mem_singleton.mp hA
        subst A
        exact Or.inl (by simp)
      · intro x
        simp [CNF, Hit]
    obtain ⟨hkl, hko, _⟩ := junkData hkj
    have op_nf : ∀ b : Fin 2, ∃ S T : Finset (Finset (Fin n)),
        (∀ A ∈ S, Basic G C A) ∧ (∀ A ∈ T, Basic G C A) ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C k b) = true ↔
          CNF S x ∧ (gateVal n C j x = true ∨ CNF T x) := by
      intro b
      have hbound := opndBound ao hkl b
      by_cases hdirect : ∃ d ∈ junk G C, opnd C k b = n + d
      · obtain ⟨d, hd, he⟩ := hdirect
        have hdk : d < k := by omega
        obtain ⟨S, T, hS, hT, hNF⟩ := ih d hdk (by omega) hd
        exact ⟨S, T, hS, hT, fun x => by rw [he]; exact hNF x⟩
      have only_j : ∀ d ∈ junk G C, OrReaches n C (opnd C k b) d → d = j := by
        intro d hd hr
        rcases lastOrBefore (orReaches_reach d _ hr).1 with he | ⟨r, hrl, hro, hri, hrb, hp⟩
        · exact (hdirect ⟨d, hd, he⟩).elim
        · have hrR := lastOrOutside ao hd hrl hro hri hrb
          have hrle := orStep_le hp
          have hrm := only_before r hrR (by omega)
          rw [hrm] at hri
          exact singleJunkInput ao hm hmraw hd hj hri hjin
      have hop : ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C k b) = true ↔
          Hit (side C k b) x ∨ (OrReaches n C (opnd C k b) j ∧ gateVal n C j x = true) := by
        intro x
        constructor
        · intro hx
          rcases operand_support_general ao top hkl hko b x hx with h | ⟨d, hd, hr, hv⟩
          · exact Or.inl h
          · have hdj := only_j d hd hr
            subst d
            exact Or.inr ⟨hr, hv⟩
        · rintro (⟨w, hw, hx⟩ | ⟨hr, hx⟩)
          · exact sideVal hw hx
          · exact orStep_up (n := n) (by simp) (orReaches_reach j _ hr).1 hx
      have hbasic : Basic G C (side C k b) := rawbasic _ (by omega)
      by_cases hreach : OrReaches n C (opnd C k b) j
      · refine ⟨∅, {side C k b}, by simp, ?_, ?_⟩
        · intro A hA
          exact Finset.mem_singleton.mp hA ▸ hbasic
        · intro x
          simpa only [CNF, Finset.notMem_empty, false_implies, forall_const,
            Finset.mem_singleton, forall_eq, true_and, hreach, or_comm] using hop x
      · refine ⟨{side C k b}, ∅, ?_, by simp, ?_⟩
        · intro A hA
          exact Finset.mem_singleton.mp hA ▸ hbasic
        · intro x
          simpa [CNF, hreach] using hop x
    obtain ⟨S0, T0, hS0, hT0, hNF0⟩ := op_nf 0
    obtain ⟨S1, T1, hS1, hT1, hNF1⟩ := op_nf 1
    refine ⟨S0 ∪ S1, T0 ∪ T1, ?_, ?_, ?_⟩
    · intro A hA
      exact (Finset.mem_union.mp hA).elim (hS0 A) (hS1 A)
    · intro A hA
      exact (Finset.mem_union.mp hA).elim (hT0 A) (hT1 A)
    · intro x
      have hand : gateVal n C k x = true ↔
          val C (List.ofFn x) (opnd C k 0) = true ∧
          val C (List.ofFn x) (opnd C k 1) = true := by
        rw [andValOperands ao hkl hko x]
        constructor
        · intro h
          exact ⟨h 0, h 1⟩
        · intro h b
          fin_cases b
          · exact h.1
          · exact h.2
      rw [hand, hNF0 x, hNF1 x, cnf_union, cnf_union]
      tauto
end SharedSource
namespace PrefixCNF
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget ChainMixed
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma prefix_junk_basic_cnf (ao : IsAO2 n C) (top : TopForm G C) {m : ℕ}
    (hml : m ≤ C.gates.length)
    (first : ∀ r ∈ orN G C \ lam G C, m ≤ r) :
    ∀ j < m, j ∈ junk G C → ∃ F : Finset (Finset (Fin n)),
      (∀ S ∈ F, Basic G C S) ∧
      ∀ x : Fin n → Bool, gateVal n C j x = true ↔ CNF F x := by
  classical
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjm hj
    obtain ⟨jl, jo, _⟩ := junkData hj
    have operand (b : Fin 2) : ∃ F : Finset (Finset (Fin n)),
        (∀ S ∈ F, Basic G C S) ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C j b) = true ↔ CNF F x := by
      have direct (k : ℕ) (hk : k ∈ junk G C) (hr : OrReaches n C (opnd C j b) k) :
          opnd C j b = n + k := by
        rcases lastOrBefore (orReaches_reach k _ hr).1 with h | ⟨r, rl, ro, ri, rb, rp⟩
        · exact h
        · have hr' := lastOrOutside ao hk rl ro ri rb
          have hmr := first r hr'
          have hle := orStep_le rp
          have hlt := opndBound ao jl b
          omega
      by_cases hd : ∃ k, k ∈ junk G C ∧ opnd C j b = n + k
      · obtain ⟨k, hk, he⟩ := hd
        have hbnd := opndBound ao jl b
        have hkj : k < j := by omega
        obtain ⟨F, hF, hsem⟩ := ih k hkj (hkj.trans hjm) hk
        refine ⟨F, hF, ?_⟩
        intro x
        rw [he]
        exact hsem x
      · refine ⟨{side C j b}, ?_, ?_⟩
        · intro S hS
          have hS' : S = side C j b := Finset.mem_singleton.mp hS
          subst S
          have hshape := PrefixSources.prefix_raw_cover_shape ao hml first (w := opnd C j b) (by
            have := opndBound ao jl b
            omega)
          rcases hshape with hsmall | ⟨z, hz⟩
          · exact Or.inl hsmall
          · exact Or.inr ⟨z, fun y hy => SimpleGraph.deleteEdges_adj.mp (hz y hy)⟩
        · intro x
          have hpure : val C (List.ofFn x) (opnd C j b) = true ↔ Hit (side C j b) x := by
            constructor
            · intro hx
              rcases operand_support_general ao top jl jo b x hx with hraw | ⟨k, hk, hr, _⟩
              · exact hraw
              · exact (hd ⟨k, hk, direct k hk hr⟩).elim
            · rintro ⟨w, hw, hx⟩
              exact sideVal hw hx
          simpa only [CNF, Finset.mem_singleton, forall_eq] using hpure
    obtain ⟨F0, hF0, h0⟩ := operand 0
    obtain ⟨F1, hF1, h1⟩ := operand 1
    refine ⟨F0 ∪ F1, ?_, ?_⟩
    · intro S hS
      rcases Finset.mem_union.mp hS with h | h
      · exact hF0 S h
      · exact hF1 S h
    · intro x
      constructor
      · intro hx
        have hboth := (andValOperands ao jl jo x).mp hx
        intro S hS
        rcases Finset.mem_union.mp hS with h | h
        · exact (h0 x).mp (hboth 0) S h
        · exact (h1 x).mp (hboth 1) S h
      · intro hx
        apply (andValOperands ao jl jo x).mpr
        intro b
        fin_cases b
        · exact (h0 x).mpr (fun S hS => hx S (Finset.mem_union_left _ hS))
        · exact (h1 x).mpr (fun S hS => hx S (Finset.mem_union_right _ hS))
end PrefixCNF
namespace SharedSourceCount
open Budget ChainMixed SharedSource PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma visible_edge_positive_charged_or_joint
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hempty : centreless G C = ∅)
    (j k : ℕ) (hpair : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ d ∈ junk G C,
      OrReaches n C (opnd C a b) d → d = j ∨ d = k)
    {u v : Fin n} (he : s(u,v) ∈ Ustar G C) :
    (∃ m ∈ orN G C \ lam G C, ∃ d ∈ junk G C, (d = j ∨ d = k) ∧
      gateVal n C d (pairInput u v) = true ∧
      Relation.ReflTransGen (OrStep n C) (n+m) (n+d) ∧ RoutedThrough G C m s(u,v)) ∨
    (∀ x, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true) ∧
      s(u,v) ∈ gammaE G C j ∩ gammaE G C k := by
  obtain ⟨a,ha,b,d,hd,hav,hr,hdv⟩ := residualTrace hleast hT he
  obtain ⟨al,ao,ab⟩ := topData ha
  have hv := (andValOperands hleast.1 al ao _).mp hav (1-b)
  rcases operandSupport hleast.1 hT al ao hv with ⟨w,hw,hwe⟩ | ⟨l,hl,hlr,hlv⟩
  · obtain ⟨m,hm,hraw,hp,hmd⟩ := OrdinaryCharge.raw_extra_on_dirty_path hleast.1 hd
      (orReaches_reach d _ hr).1 (topSides hempty ha b)
    exact Or.inl ⟨m,hm,d,hd,hpair a ha b d hd hr,hdv,hmd,hraw,a,ha,b,hp,w,hw,Sym2.mem_iff.mpr hwe⟩
  · have hJ : ∀ x, gateVal n C d x = true → gateVal n C l x = true → graphFun G ∅ x = true := by
      intro x hdx hlx
      apply ab x ((andValOperands hleast.1 al ao x).mpr ?_)
      intro c
      rcases opposite b c with rfl | rfl
      · exact orStep_up (n := n) (by simp) (orReaches_reach d _ hr).1 hdx
      · exact orStep_up (n := n) (by simp) (orReaches_reach l _ hlr).1 hlx
    have hdl : d ≠ l := by
      intro eq
      obtain ⟨_,_,x,hx,hFx⟩ := junkData hl
      exact Bool.false_ne_true (hFx.symm.trans (hJ x (eq ▸ hx) hx))
    have hdE : s(u,v) ∈ gammaE G C d :=
      Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1,u,v,rfl,hdv⟩
    have hlE : s(u,v) ∈ gammaE G C l :=
      Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1,u,v,rfl,hlv⟩
    rcases hpair a ha b d hd hr with rfl | rfl <;>
      rcases hpair a ha (1-b) l hl hlr with rfl | rfl
    · exact (hdl rfl).elim
    · exact Or.inr ⟨hJ, Finset.mem_inter.mpr ⟨hdE,hlE⟩⟩
    · exact Or.inr ⟨fun x hx hy => hJ x hy hx, Finset.mem_inter.mpr ⟨hlE,hdE⟩⟩
    · exact (hdl rfl).elim
lemma visible_two_extra_or_clean_terms_card_le_four
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (j k m0 m1 : ℕ) (hpair : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ d ∈ junk G C,
      OrReaches n C (opnd C a b) d → d = j ∨ d = k)
    (hextra : orN G C \ lam G C = {m0,m1}) (hfirstOnly : ∀ d ∈ junk G C,
      Relation.ReflTransGen (OrStep n C) (n+m0) (n+d) → d = j)
    (F0 F1 F2 FJ : Finset (Finset (Fin n)))
    (hB0 : ∀ S ∈ F0, Basic G C S) (hB1 : ∀ S ∈ F1, Basic G C S)
    (hB2 : ∀ S ∈ F2, Basic G C S) (hBJ : ∀ S ∈ FJ, Basic G C S)
    (hlo : ∀ x, gateVal n C j x = true → CNF F0 x)
    (hfirst : ∀ x, CNF F0 x → gateVal n C m0 x = true)
    (hcoverJ : Relation.ReflTransGen (OrStep n C) (n+m1) (n+j) →
      ∀ x, gateVal n C j x = true → CNF F1 x)
    (hcoverK : ∀ x, gateVal n C k x = true → CNF F1 x ∨ CNF F2 x)
    (hsecond1 : ∀ x, CNF F1 x → gateVal n C m1 x = true)
    (hsecond2 : ∀ x, CNF F2 x → gateVal n C m1 x = true)
    (hjointNF : ∀ x, (gateVal n C j x = true ∧ gateVal n C k x = true) ↔ CNF FJ x) :
    (Ustar G C).card ≤ 4 := by
  classical
  let E0 := termEdges G C m0 F0
  let E1 := termEdges G C m1 F1
  let E2 := termEdges G C m1 F2
  let D := (Ustar G C ∩ gammaE G C j ∩ gammaE G C k).filter fun _ =>
    ∀ x, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true
  have h0 : E0.card ≤ 1 := termEdges_card_le_one hleast.1 hfour color hbip m0 F0 hB0 hfirst
  have h1 : E1.card ≤ 1 := termEdges_card_le_one hleast.1 hfour color hbip m1 F1 hB1 hsecond1
  have h2 : E2.card ≤ 1 := termEdges_card_le_one hleast.1 hfour color hbip m1 F2 hB2 hsecond2
  have hDU : D ⊆ Ustar G C := fun e he =>
    (Finset.mem_inter.mp (Finset.mem_inter.mp (Finset.mem_filter.mp he).1).1).1
  have hd : D.card ≤ 1 := by
    by_cases hD : D.Nonempty
    · obtain ⟨e, he⟩ := hD
      have hjoint := (Finset.mem_filter.mp he).2
      apply basic_clean_cnf_card_le_one G D color hbip
        (common_neighbors_unique_of_card_le_one G hfour)
        (fun u v huv => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hDU huv)).1) FJ id
      · intro S hS
        rcases hBJ S hS with small | ⟨z,hz⟩
        · exact Or.inl small
        · exact Or.inr ⟨z, fun w hw => ⟨(hz w hw).1, fun h => (hz w hw).2 (hDU h)⟩⟩
      · intro u v huv S hS
        obtain ⟨huvj, huvk⟩ := Finset.mem_inter.mp (Finset.mem_filter.mp huv).1
        obtain ⟨huvU, huvj⟩ := Finset.mem_inter.mp huvj
        have hc := (hjointNF (pairInput u v)).mp
          ⟨gate_accepts_pair_of_gammaE huvj, gate_accepts_pair_of_gammaE huvk⟩
        obtain ⟨w,hw,hon⟩ := hc S hS
        rcases (pairInput_true u v w).mp hon with rfl | rfl
        · exact Or.inl hw
        · exact Or.inr hw
      · intro x hx
        have h := (hjointNF x).mpr hx
        have ht := hjoint x h.1 h.2
        simpa [graphFun] using ht
    · simp [Finset.not_nonempty_iff_eq_empty.mp hD]
  have cover : Ustar G C ⊆ E0 ∪ E1 ∪ E2 ∪ D := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      simp only [Finset.mem_union, or_assoc]
      rcases visible_edge_positive_charged_or_joint hleast hT hempty j k hpair he with
        ⟨m,hm,d,hd,hdd,hval,hpath,hroute⟩ | ⟨hjoint,hboth⟩
      · have hmm : m = m0 ∨ m = m1 := by simpa only [hextra, Finset.mem_insert, Finset.mem_singleton] using hm
        rcases hmm with rfl | rfl
        · have hdj := hfirstOnly d hd hpath
          subst d
          exact Or.inl (termEdges_mem.mpr ⟨he,hroute,(edgeCNF_pair_iff F0 u v).mpr (hlo _ hval)⟩)
        · rcases hdd with rfl | rfl
          · exact Or.inr (Or.inl (termEdges_mem.mpr
              ⟨he,hroute,(edgeCNF_pair_iff F1 u v).mpr (hcoverJ hpath _ hval)⟩))
          · rcases hcoverK _ hval with hF1 | hF2
            · exact Or.inr (Or.inl (termEdges_mem.mpr ⟨he,hroute,(edgeCNF_pair_iff F1 u v).mpr hF1⟩))
            · exact Or.inr (Or.inr (Or.inl (termEdges_mem.mpr ⟨he,hroute,(edgeCNF_pair_iff F2 u v).mpr hF2⟩)))
      · right; right; right
        exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr
          ⟨Finset.mem_inter.mpr ⟨he,(Finset.mem_inter.mp hboth).1⟩,(Finset.mem_inter.mp hboth).2⟩,hjoint⟩
  have hc := Finset.card_le_card cover
  have h01 := Finset.card_union_le E0 E1
  have h012 := Finset.card_union_le (E0 ∪ E1) E2
  have h012d := Finset.card_union_le (E0 ∪ E1 ∪ E2) D
  omega
lemma visible_shared_source_card_le_four
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (j k m0 m1 : ℕ) (hpair : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ d ∈ junk G C,
      OrReaches n C (opnd C a b) d → d = j ∨ d = k)
    (hextra : orN G C \ lam G C = {m0,m1})
    (hfirstOnly : ∀ d ∈ junk G C,
      Relation.ReflTransGen (OrStep n C) (n+m0) (n+d) → d = j)
    (h0j : Relation.ReflTransGen (OrStep n C) (n+m0) (n+j))
    (h1k : Relation.ReflTransGen (OrStep n C) (n+m1) (n+k))
    (F S T : Finset (Finset (Fin n)))
    (hF : ∀ A ∈ F, Basic G C A) (hS : ∀ A ∈ S, Basic G C A) (hTT : ∀ A ∈ T, Basic G C A)
    (hlo : ∀ x, gateVal n C j x = true ↔ CNF F x)
    (hhi : ∀ x, gateVal n C k x = true ↔ CNF S x ∧ (gateVal n C j x = true ∨ CNF T x)) :
    (Ustar G C).card ≤ 4 := by
  classical
  let F1 := if Relation.ReflTransGen (OrStep n C) (n+m1) (n+j) then F else F ∪ S
  have hFS : ∀ A ∈ F ∪ S, Basic G C A := fun A hA =>
    (Finset.mem_union.mp hA).elim (hF A) (hS A)
  have hST : ∀ A ∈ S ∪ T, Basic G C A := fun A hA =>
    (Finset.mem_union.mp hA).elim (hS A) (hTT A)
  have hF1 : ∀ A ∈ F1, Basic G C A := by
    by_cases hp : Relation.ReflTransGen (OrStep n C) (n+m1) (n+j)
    · simpa only [F1, if_pos hp] using hF
    · simpa only [F1, if_neg hp] using hFS
  apply visible_two_extra_or_clean_terms_card_le_four hleast hT hfour color hbip hempty
    j k m0 m1 hpair hextra hfirstOnly F F1 (S ∪ T) (F ∪ S) hF hF1 hST hFS
  · intro x hx
    exact (hlo x).mp hx
  · intro x hx
    exact orStep_up (n := n) (by simp) h0j ((hlo x).mpr hx)
  · intro hp x hx
    change CNF (if Relation.ReflTransGen (OrStep n C) (n+m1) (n+j) then F else F ∪ S) x
    rw [if_pos hp]
    exact (hlo x).mp hx
  · intro x hx
    obtain ⟨hSx, hjx | hTx⟩ := (hhi x).mp hx
    · left
      by_cases hp : Relation.ReflTransGen (OrStep n C) (n+m1) (n+j)
      · simpa only [F1, if_pos hp] using (hlo x).mp hjx
      · simpa only [F1, if_neg hp] using (cnf_union F S x).mpr ⟨(hlo x).mp hjx, hSx⟩
    · exact Or.inr ((cnf_union S T x).mpr ⟨hSx, hTx⟩)
  · intro x hx
    by_cases hp : Relation.ReflTransGen (OrStep n C) (n+m1) (n+j)
    · have hFx : CNF F x := by simpa only [F1, if_pos hp] using hx
      exact orStep_up (n := n) (by simp) hp ((hlo x).mpr hFx)
    · have hFSx : CNF F x ∧ CNF S x := (cnf_union F S x).mp (by
        simpa only [F1, if_neg hp] using hx)
      exact orStep_up (n := n) (by simp) h1k ((hhi x).mpr
        ⟨hFSx.2, Or.inl ((hlo x).mpr hFSx.1)⟩)
  · intro x hx
    have hSTx := (cnf_union S T x).mp hx
    exact orStep_up (n := n) (by simp) h1k ((hhi x).mpr ⟨hSTx.1, Or.inr hSTx.2⟩)
  · intro x
    rw [hhi x, cnf_union, ← hlo x]
    tauto
end SharedSourceCount
namespace SharedSourceCount
open Budget ChainMixed SharedSource PrefixCNF PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma two_nonempty_active_extra_ustar_card_le_four
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (m0 m1 : ℕ) (h01 : m0 < m1) (hextra : orN G C \ lam G C = {m0,m1})
    (hraw : ∀ m ∈ orN G C \ lam G C, (orIn n C (n+m)).Nonempty)
    (hactive : ∀ m ∈ orN G C \ lam G C, ∃ j ∈ junk G C,
      Relation.ReflTransGen (OrStep n C) (n+m) (n+j)) :
    (Ustar G C).card ≤ 4 := by
  classical
  have hm0 : m0 ∈ orN G C \ lam G C := by simp [hextra]
  have hm1 : m1 ∈ orN G C \ lam G C := by simp [hextra]
  have member : ∀ m ∈ orN G C \ lam G C, m = m0 ∨ m = m1 := by
    intro m hm
    simpa only [hextra, Finset.mem_insert, Finset.mem_singleton] using hm
  have first : ∀ m ∈ orN G C \ lam G C, m0 ≤ m := by
    intro m hm
    rcases member m hm with rfl | rfl <;> omega
  have only_before : ∀ m ∈ orN G C \ lam G C, m < m1 → m = m0 := by
    intro m hm hlt
    rcases member m hm with h | h
    · exact h
    · omega
  obtain ⟨j, hj, h0j⟩ := hactive m0 hm0
  have hjin := first_extra_direct_junk hleast.1 hm0 first hj h0j
  have hjlt : j < m0 := by
    have hlt := hleast.1.2.1 m0 (orData hm0).1 (n+j) hjin
    omega
  have hfirstOnly : ∀ d ∈ junk G C,
      Relation.ReflTransGen (OrStep n C) (n+m0) (n+d) → d = j := by
    intro d hd hp
    have hdin := first_extra_direct_junk hleast.1 hm0 first hd hp
    exact singleJunkInput hleast.1 hm0 (hraw m0 hm0) hd hj hdin hjin
  have hsecond : ∃ k ∈ junk G C,
      Relation.ReflTransGen (OrStep n C) (n+m1) (n+k) ∧
      ∀ d ∈ junk G C, n+d ∈ (gateAt C m1).inputs → d = k := by
    by_cases hdirect : ∃ k ∈ junk G C, n+k ∈ (gateAt C m1).inputs
    · obtain ⟨k, hk, hkin⟩ := hdirect
      have hkb := hleast.1.2.1 m1 (orData hm1).1 (n+k) hkin
      refine ⟨k, hk, .head ⟨m1, (orData hm1).1, rfl, (orData hm1).2.1, hkin, hkb⟩ .refl, ?_⟩
      intro d hd hdin
      exact singleJunkInput hleast.1 hm1 (hraw m1 hm1) hd hk hdin hkin
    · obtain ⟨d, hd, hpd⟩ := hactive m1 hm1
      have hdj : d = j := by
        rcases lastOrBefore hpd with he | ⟨r, hrl, hro, hri, hrb, hp⟩
        · have heq : m1 = d := by omega
          have ho := (orData hm1).2.1
          rw [heq, (junkData hd).2.1] at ho
          contradiction
        · have hrR := lastOrOutside hleast.1 hd hrl hro hri hrb
          rcases member r hrR with hr | hr
          · subst r
            exact hfirstOnly d hd (.head ⟨m0, hrl, rfl, hro, hri, hrb⟩ .refl)
          · subst r
            exact (hdirect ⟨d, hd, hri⟩).elim
      subst d
      exact ⟨j, hj, hpd, fun d hd hdin => (hdirect ⟨d, hd, hdin⟩).elim⟩
  obtain ⟨k, hk, h1k, hsole⟩ := hsecond
  have hklt : k < m1 := by
    have hle := orStep_le h1k
    have hne : k ≠ m1 := by
      intro heq
      have ho := (junkData hk).2.1
      rw [heq, (orData hm1).2.1] at ho
      contradiction
    omega
  have hpair : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ d ∈ junk G C,
      OrReaches n C (opnd C a b) d → d = j ∨ d = k := by
    intro a ha b d hd hp
    obtain ⟨m, hm, hdin, _⟩ := residualPath hleast.1 hempty ha hd hp
    rcases member m hm with hmem | hmem
    · subst m
      have hdb := hleast.1.2.1 m0 (orData hm0).1 (n+d) hdin
      exact Or.inl (hfirstOnly d hd (.head ⟨m0, (orData hm0).1, rfl,
        (orData hm0).2.1, hdin, hdb⟩ .refl))
    · subst m
      exact Or.inr (hsole d hd hdin)
  obtain ⟨F, hF, hlo⟩ := prefix_junk_basic_cnf hleast.1 hT (orData hm0).1.le first j hjlt hj
  obtain ⟨S, T, hS, hTT, hhi⟩ := shared_source_cnf_normal_form hleast.1 hT hm0 first
    only_before (orData hm1).1.le hj h0j (hraw m0 hm0) k hklt hk
  exact visible_shared_source_card_le_four hleast hT hfour color hbip hempty j k m0 m1
    hpair hextra hfirstOnly h0j h1k F S T hF hS hTT hlo hhi
end SharedSourceCount
namespace LastExtra
open Budget PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma least_nonbelow_has_reader (hleast : IsLeastAO G C) {j : ℕ}
    (hjl : j < C.gates.length) (hdirty : ¬ BelowF G C j) :
    ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  have hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x :=
    fun x => congrFun hleast.2.1 x
  have hAO : Ledger.S98.AO n C := Ledger.S98.AO_of_IsAO2 n C hleast.1
  have hLeast : Ledger.S98.Least n C := ⟨hAO, fun D hD hDf =>
    hleast.2.2 D (Ledger.S98.IsAO2_of_AO n D hD) (funext fun x => (hDf x).trans (hfun x))⟩
  have hwit : ∃ x : Fin n → Bool, gateVal n C j x = true ∧ graphFun G ∅ x = false := by
    by_contra hn
    apply hdirty
    intro x hx
    exact Bool.eq_true_of_not_eq_false fun hf => hn ⟨x, hx, hf⟩
  obtain ⟨x, hjx, hFx⟩ := hwit
  have hout : C.output ≠ n + j := by
    intro heq
    have hcx : C.eval (List.ofFn x) = true := by
      change (C.wires (List.ofFn x)).getD C.output false = true
      rw [heq]
      exact hjx
    exact Bool.false_ne_true (hFx.symm.trans ((hfun x).symm.trans hcx))
  by_contra hno
  push Not at hno
  obtain ⟨_, a, b, hin, ha, hb⟩ := hLeast.1 j hjl
  have hsame : ∀ x : Fin n → Bool,
      (Ledger.S98.eraseC n C j a).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    Ledger.S98.erase_wires n C j a hjl ha x (Or.inr hno) C.output (fun h => (hout h).elim)
  have hsize := hLeast.2 _ (Ledger.S98.erase_AO n C j a hLeast.1 hjl ha) hsame
  have hlength := Ledger.S98.erase_length n C j a hjl
  omega
lemma all_junk_before_last_extra (hleast : IsLeastAO G C) (hempty : centreless G C = ∅)
    {m : ℕ} (hmax : ∀ r ∈ orN G C \ lam G C, r ≤ m) :
    ∀ j ∈ junk G C, j < m := by
  classical
  intro j hj
  have hne : (junk G C).Nonempty := ⟨j, hj⟩
  let k := (junk G C).max' hne
  have hk : k ∈ junk G C := Finset.max'_mem _ _
  have hlast : ∀ d ∈ junk G C, d ≤ k := fun d hd => Finset.le_max' _ d hd
  obtain ⟨r, hr, hkr, _⟩ := RemainingOrder.last_junk_has_extra_reader hleast hempty hk hlast
  have hjk := hlast j hj
  have hrm := hmax r hr
  omega
lemma last_extra_raw_nonempty (hleast : IsLeastAO G C) (hempty : centreless G C = ∅)
    {m : ℕ} (hm : m ∈ orN G C \ lam G C)
    (hmax : ∀ r ∈ orN G C \ lam G C, r ≤ m) :
    (orIn n C (n+m)).Nonempty := by
  by_contra hn
  have hzero := Finset.not_nonempty_iff_eq_empty.mp hn
  obtain ⟨k, hmk, hkl, hki⟩ := least_nonbelow_has_reader hleast (orData hm).1 (orData hm).2.2
  rcases hleast.1.1 _ (gateAt_mem hkl) with hka | hko
  · by_cases hbelow : BelowF G C k
    · have htop : k ∈ tops G C := by
        simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
          And.intro hkl (And.intro hka hbelow)
      obtain ⟨b, hb⟩ := inputsAsOpnd hleast.1 hkl hki
      have hne := topSides hempty htop b
      change (orIn n C (opnd C k b)).Nonempty at hne
      rw [← hb, hzero] at hne
      exact (Finset.not_nonempty_empty hne).elim
    · have hdirty : ∃ x : Fin n → Bool, gateVal n C k x = true ∧ graphFun G ∅ x = false := by
        by_contra hh
        apply hbelow
        intro x hx
        exact Bool.eq_true_of_not_eq_false fun hf => hh ⟨x, hx, hf⟩
      have hkj : k ∈ junk G C := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hkl, hka, hkl, hdirty⟩
      have hkm := all_junk_before_last_extra hleast hempty hmax k hkj
      omega
  · have hkR := emptyInputOutside hleast.1 (orData hm).2.2 hzero hkl hko hki
    have hkm := hmax k hkR
    omega
end LastExtra
namespace EmptyExtra
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget ChainMixed
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma empty_path_direct_before (ao : IsAO2 n C) {m B w : ℕ}
    (hm : m ∈ orN G C \ lam G C) (hempty : orIn n C (n + m) = ∅)
    (only : ∀ r ∈ orN G C \ lam G C, r < B → r = m)
    (hw : w < n + B)
    (path : Relation.ReflTransGen (OrStep n C) w (n + m)) : w = n + m := by
  rcases lastOrBefore path with h | ⟨r, hrl, hro, hri, hrb, hp⟩
  · exact h
  · have hrR := emptyInputOutside ao (orData hm).2.2 hempty hrl hro hri
    have hle := orStep_le hp
    have hrm := only r hrR (by omega)
    omega
lemma empty_exception_raw_basic (ao : IsAO2 n C) {m B w : ℕ}
    (hempty : orIn n C (n + m) = ∅)
    (only : ∀ r ∈ orN G C \ lam G C, r < B → r = m)
    (hB : B ≤ C.gates.length) (hw : w < n + B) : Basic G C (orIn n C w) := by
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
  have hkB : k < B := by omega
  have hkl := hkB.trans_le hB
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
    have hkm := only k (Finset.mem_sdiff.mpr ⟨hkN, hn⟩) hkB
    rw [hkm, hempty] at hu
    exact Finset.notMem_empty _ hu
  obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hkL
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1 - b)).card)
  refine Or.inr ⟨z, ?_⟩
  intro t ht
  exact SimpleGraph.deleteEdges_adj.mp (cleanAdj ao ha b
    (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz)
lemma cnf_union (S T : Finset (Finset (Fin n))) (x : Fin n → Bool) :
    CNF (S ∪ T) x ↔ CNF S x ∧ CNF T x := by
  classical
  simp only [CNF, Finset.mem_union, or_imp, forall_and]
lemma junk_empty_atom_normal_form (ao : IsAO2 n C) (top : TopForm G C) {m B : ℕ}
    (hm : m ∈ orN G C \ lam G C) (hempty : orIn n C (n + m) = ∅)
    (only : ∀ r ∈ orN G C \ lam G C, r < B → r = m)
    (hB : B ≤ C.gates.length) :
    ∀ k < B, k ∈ junk G C → ∃ S : Finset (Finset (Fin n)), ∃ used : Bool,
      (∀ A ∈ S, Basic G C A) ∧
      (used = true → ∃ d < B, d ∈ junk G C ∧ ∃ b : Fin 2, opnd C d b = n + m) ∧
      ∀ x : Fin n → Bool, gateVal n C k x = true ↔
        CNF S x ∧ (used = false ∨ gateVal n C m x = true) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hkB hkj
    obtain ⟨hkl, hko, _⟩ := junkData hkj
    have opNF (b : Fin 2) : ∃ S : Finset (Finset (Fin n)), ∃ used : Bool,
        (∀ A ∈ S, Basic G C A) ∧
        (used = true → ∃ d < B, d ∈ junk G C ∧ ∃ c : Fin 2, opnd C d c = n + m) ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C k b) = true ↔
          CNF S x ∧ (used = false ∨ gateVal n C m x = true) := by
      have hbound := opndBound ao hkl b
      by_cases hdirect : ∃ d ∈ junk G C, opnd C k b = n + d
      · obtain ⟨d, hd, he⟩ := hdirect
        have hdk : d < k := by omega
        obtain ⟨S, used, hS, hctx, hNF⟩ := ih d hdk (by omega) hd
        exact ⟨S, used, hS, hctx, fun x => by rw [he]; exact hNF x⟩
      by_cases hatom : opnd C k b = n + m
      · refine ⟨∅, true, by simp, fun _ => ⟨k, hkB, hkj, b, hatom⟩, ?_⟩
        intro x
        rw [hatom]
        change gateVal n C m x = true ↔ _
        simp [CNF]
      have hraw : ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C k b) = true ↔
          Hit (side C k b) x := by
        intro x
        constructor
        · intro hx
          rcases operand_support_general ao top hkl hko b x hx with h | ⟨d, hd, hr, hv⟩
          · exact h
          · rcases lastOrBefore (orReaches_reach d _ hr).1 with he | ⟨r, hrl, hro, hri, hrb, hp⟩
            · exact (hdirect ⟨d, hd, he⟩).elim
            · have hrR := lastOrOutside ao hd hrl hro hri hrb
              have hrle := orStep_le hp
              have hrm := only r hrR (by omega)
              rw [hrm] at hp
              exact (hatom (empty_path_direct_before ao hm hempty only (by omega) hp)).elim
        · rintro ⟨w, hw, hx⟩
          exact sideVal hw hx
      refine ⟨{side C k b}, false, ?_, by simp, ?_⟩
      · intro A hA
        have hbasic : Basic G C (side C k b) := empty_exception_raw_basic ao hempty only hB (by omega)
        exact Finset.mem_singleton.mp hA ▸ hbasic
      · intro x
        simpa [CNF] using hraw x
    obtain ⟨S0, u0, hS0, hctx0, hNF0⟩ := opNF 0
    obtain ⟨S1, u1, hS1, hctx1, hNF1⟩ := opNF 1
    refine ⟨S0 ∪ S1, u0 || u1, ?_, ?_, ?_⟩
    · intro A hA
      exact (Finset.mem_union.mp hA).elim (hS0 A) (hS1 A)
    · intro h
      cases u0 <;> cases u1 <;> simp at h
      · exact hctx1 rfl
      · exact hctx0 rfl
      · exact hctx0 rfl
    · intro x
      have hand : gateVal n C k x = true ↔
          val C (List.ofFn x) (opnd C k 0) = true ∧
          val C (List.ofFn x) (opnd C k 1) = true := by
        rw [andValOperands ao hkl hko x]
        constructor
        · intro h
          exact ⟨h 0, h 1⟩
        · intro h b
          fin_cases b
          · exact h.1
          · exact h.2
      rw [hand, hNF0 x, hNF1 x, cnf_union]
      cases u0 <;> cases u1 <;> simp <;> tauto
lemma first_extra_direct_source (ao : IsAO2 n C) {m j : ℕ}
    (hm : m ∈ orN G C \ lam G C) (first : ∀ r ∈ orN G C \ lam G C, m ≤ r)
    (hj : j ∈ junk G C)
    (path : Relation.ReflTransGen (OrStep n C) (n + m) (n + j)) :
    n + j ∈ (gateAt C m).inputs := by
  rcases lastOrBefore path with he | ⟨r, hrl, hro, hri, hrb, hp⟩
  · have hmj : m = j := by omega
    have hop := (junkData hj).2.1
    rw [← hmj, (orData hm).2.1] at hop
    contradiction
  · have hrR := lastOrOutside ao hj hrl hro hri hrb
    have hrm := first r hrR
    have hmr := orStep_le hp
    have heq : r = m := by omega
    simpa only [heq] using hri
lemma empty_source_two_cnf (ao : IsAO2 n C) (top : TopForm G C) {m d : ℕ} {b : Fin 2}
    (hm : m ∈ orN G C \ lam G C) (first : ∀ r ∈ orN G C \ lam G C, m ≤ r)
    (hempty : orIn n C (n + m) = ∅)
    (hd : d ∈ junk G C) (hcontext : opnd C d b = n + m) :
    ∃ F0 F1 : Finset (Finset (Fin n)),
      (∀ S ∈ F0, Basic G C S) ∧ (∀ S ∈ F1, Basic G C S) ∧
      ∀ x : Fin n → Bool, gateVal n C m x = true ↔ CNF F0 x ∨ CNF F1 x := by
  classical
  have hml := (orData hm).1
  have hand := (junkData hd).2.1
  have sourceNF (c : Fin 2) : ∃ F : Finset (Finset (Fin n)),
      (∀ S ∈ F, Basic G C S) ∧ ∀ x : Fin n → Bool,
      CNF F x ↔ ∃ j ∈ junk G C, opnd C m c = n + j ∧ gateVal n C j x = true := by
    by_cases hj : ∃ j ∈ junk G C, opnd C m c = n + j
    · obtain ⟨j, hj, hwire⟩ := hj
      have hlt : j < m := by
        have := opndBound ao hml c
        omega
      obtain ⟨F, hF, hsem⟩ := PrefixCNF.prefix_junk_basic_cnf ao top hml.le first j hlt hj
      refine ⟨F, hF, ?_⟩
      intro x
      constructor
      · intro hx
        exact ⟨j, hj, hwire, (hsem x).mpr hx⟩
      · rintro ⟨j', hj', hwire', hx⟩
        have heq : j' = j := by omega
        subst j'
        exact (hsem x).mp hx
    · refine ⟨{∅}, ?_, ?_⟩
      · intro S hS
        have he : S = ∅ := Finset.mem_singleton.mp hS
        subst S
        exact Or.inl (by simp)
      · intro x
        constructor
        · intro hx
          have he : Hit ∅ x := hx ∅ (by simp)
          simpa [Hit] using he
        · rintro ⟨j, hj', hwire, _⟩
          exact (hj ⟨j, hj', hwire⟩).elim
  obtain ⟨F0, hF0, h0⟩ := sourceNF 0
  obtain ⟨F1, hF1, h1⟩ := sourceNF 1
  refine ⟨F0, F1, hF0, hF1, ?_⟩
  intro x
  constructor
  · intro hx
    have hv : val C (List.ofFn x) (opnd C d b) = true := by rw [hcontext]; exact hx
    rcases operand_support_general ao top (junkData hd).1 hand b x hv with hraw | ⟨j, hj, hp, hjx⟩
    · obtain ⟨w, hw, _⟩ := hraw
      change w ∈ orIn n C (opnd C d b) at hw
      rw [hcontext, hempty] at hw
      exact (Finset.notMem_empty _ hw).elim
    · have hpath := (orReaches_reach j _ hp).1
      rw [hcontext] at hpath
      have hin := first_extra_direct_source ao hm first hj hpath
      obtain ⟨c, heq⟩ := inputsAsOpnd ao hml hin
      have hs : ∃ l ∈ junk G C, opnd C m c = n + l ∧ gateVal n C l x = true :=
        ⟨j, hj, heq.symm, hjx⟩
      fin_cases c
      · exact Or.inl ((h0 x).mpr hs)
      · exact Or.inr ((h1 x).mpr hs)
  · intro hx
    have hf (c : Fin 2) (hs : ∃ j ∈ junk G C, opnd C m c = n + j ∧ gateVal n C j x = true) :
        gateVal n C m x = true := by
      obtain ⟨j, hj, hwire, hjx⟩ := hs
      have hin : n + j ∈ (gateAt C m).inputs := by
        rw [← hwire]
        exact opndMem ao hml c
      apply (val_or (n := n) (by simp) hml (orData hm).2.1).mpr
      exact ⟨n + j, hin, ao.2.1 _ hml _ hin, hjx⟩
    rcases hx with h | h
    · exact hf 0 ((h0 x).mp h)
    · exact hf 1 ((h1 x).mp h)
lemma junk_before_second_two_cnf (ao : IsAO2 n C) (top : TopForm G C) {m B : ℕ}
    (hm : m ∈ orN G C \ lam G C) (first : ∀ r ∈ orN G C \ lam G C, m ≤ r)
    (hempty : orIn n C (n + m) = ∅)
    (only : ∀ r ∈ orN G C \ lam G C, r < B → r = m)
    (hB : B ≤ C.gates.length) :
    ∀ k < B, k ∈ junk G C → ∃ F0 F1 : Finset (Finset (Fin n)),
      (∀ A ∈ F0, Basic G C A) ∧ (∀ A ∈ F1, Basic G C A) ∧
      ∀ x : Fin n → Bool, gateVal n C k x = true ↔ CNF F0 x ∨ CNF F1 x := by
  classical
  intro k hkB hkj
  obtain ⟨S, used, hS, hctx, hNF⟩ := junk_empty_atom_normal_form ao top hm hempty only hB k hkB hkj
  cases used with
  | false =>
    refine ⟨S, S, hS, hS, ?_⟩
    intro x
    simpa using hNF x
  | true =>
    obtain ⟨d, hdB, hd, b, hdb⟩ := hctx rfl
    obtain ⟨F0, F1, hF0, hF1, hmNF⟩ := empty_source_two_cnf ao top hm first hempty hd hdb
    refine ⟨S ∪ F0, S ∪ F1, ?_, ?_, ?_⟩
    · intro A hA
      exact (Finset.mem_union.mp hA).elim (hS A) (hF0 A)
    · intro A hA
      exact (Finset.mem_union.mp hA).elim (hS A) (hF1 A)
    · intro x
      rw [hNF x, hmNF x, cnf_union, cnf_union]
      simp <;> tauto
end EmptyExtra
namespace EmptyCount
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget ChainMixed EmptyExtra
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma single_visible_two_cnf_card_le_two
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅) (m0 m1 k : ℕ)
    (hextra : orN G C \ lam G C = {m0, m1})
    (hm0empty : orIn n C (n + m0) = ∅) (hk : k ∈ junk G C)
    (hpair : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ d ∈ junk G C,
      OrReaches n C (opnd C a b) d → d = k)
    (hpath : Relation.ReflTransGen (OrStep n C) (n + m1) (n + k))
    (F0 F1 : Finset (Finset (Fin n)))
    (hF0 : ∀ A ∈ F0, Basic G C A) (hF1 : ∀ A ∈ F1, Basic G C A)
    (hNF : ∀ x : Fin n → Bool, gateVal n C k x = true ↔ CNF F0 x ∨ CNF F1 x) :
    (Ustar G C).card ≤ 2 := by
  classical
  have safe (x : Fin n → Bool) (hx : gateVal n C k x = true) : gateVal n C m1 x = true :=
    orStep_up (n := n) (by simp) hpath hx
  let E0 := termEdges G C m1 F0
  let E1 := termEdges G C m1 F1
  have h0 : E0.card ≤ 1 := termEdges_card_le_one hleast.1 hfour color hbip m1 F0 hF0
    (fun x hx => safe x ((hNF x).mpr (Or.inl hx)))
  have h1 : E1.card ≤ 1 := termEdges_card_le_one hleast.1 hfour color hbip m1 F1 hF1
    (fun x hx => safe x ((hNF x).mpr (Or.inr hx)))
  have hcover : Ustar G C ⊆ E0 ∪ E1 := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rcases SharedSourceCount.visible_edge_positive_charged_or_joint hleast hT hempty k k
        (fun a ha b d hd hp => Or.inl (hpair a ha b d hd hp)) he with
        ⟨m, hm, d, hd, hdk, hdx, hp, hr⟩ | ⟨hjoint, _⟩
      · have hdeq : d = k := hdk.elim id id
        subst d
        have hmeq : m = m1 := by
          have hmem : m = m0 ∨ m = m1 := by
            simpa only [hextra, Finset.mem_insert, Finset.mem_singleton] using hm
          rcases hmem with h | h
          · have hn := hr.1
            rw [h, hm0empty] at hn
            exact (Finset.not_nonempty_empty hn).elim
          · exact h
        subst m
        rcases (hNF _).mp hdx with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨he, hr, (edgeCNF_pair_iff F0 u v).mpr hx⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨he, hr, (edgeCNF_pair_iff F1 u v).mpr hx⟩)
      · obtain ⟨_, _, x, hx, hFx⟩ := junkData hk
        exact (Bool.false_ne_true (hFx.symm.trans (hjoint x hx hx))).elim
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le E0 E1
  omega
lemma two_visible_pure_cnf_card_le_three
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅) (m0 m1 j k : ℕ)
    (hextra : orN G C \ lam G C = {m0, m1})
    (hm0empty : orIn n C (n + m0) = ∅)
    (hpair : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ d ∈ junk G C,
      OrReaches n C (opnd C a b) d → d = j ∨ d = k)
    (hjpath : Relation.ReflTransGen (OrStep n C) (n + m1) (n + j))
    (hkpath : Relation.ReflTransGen (OrStep n C) (n + m1) (n + k))
    (F0 F1 : Finset (Finset (Fin n)))
    (hF0 : ∀ A ∈ F0, Basic G C A) (hF1 : ∀ A ∈ F1, Basic G C A)
    (hjNF : ∀ x : Fin n → Bool, gateVal n C j x = true ↔ CNF F0 x)
    (hkNF : ∀ x : Fin n → Bool, gateVal n C k x = true ↔ CNF F1 x) :
    (Ustar G C).card ≤ 3 := by
  classical
  let E0 := termEdges G C m1 F0
  let E1 := termEdges G C m1 F1
  let D := (Ustar G C ∩ gammaE G C j ∩ gammaE G C k).filter fun _ =>
    ∀ x, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true
  have h0 : E0.card ≤ 1 := termEdges_card_le_one hleast.1 hfour color hbip m1 F0 hF0
    (fun x hx => orStep_up (n := n) (by simp) hjpath ((hjNF x).mpr hx))
  have h1 : E1.card ≤ 1 := termEdges_card_le_one hleast.1 hfour color hbip m1 F1 hF1
    (fun x hx => orStep_up (n := n) (by simp) hkpath ((hkNF x).mpr hx))
  have hD : D.card ≤ 1 := by
    by_cases hDn : D.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.mp hDn]
      simp
    obtain ⟨e, he⟩ := hDn
    have hjoint := (Finset.mem_filter.mp he).2
    apply basic_clean_cnf_card_le_one G D color hbip (common_neighbors_unique_of_card_le_one G hfour)
      (fun u v huv => SimpleGraph.mem_edgeFinset.mp
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_inter.mp (Finset.mem_filter.mp huv).1).1).1).1)
      (F0 ∪ F1) (fun S => S)
    · intro S hS
      rcases Finset.mem_union.mp hS with h | h
      · rcases hF0 S h with hsmall | ⟨z, hz⟩
        · exact Or.inl hsmall
        · exact Or.inr ⟨z, fun w hw => ⟨(hz w hw).1, fun heD => (hz w hw).2
            (Finset.mem_inter.mp (Finset.mem_inter.mp (Finset.mem_filter.mp heD).1).1).1⟩⟩
      · rcases hF1 S h with hsmall | ⟨z, hz⟩
        · exact Or.inl hsmall
        · exact Or.inr ⟨z, fun w hw => ⟨(hz w hw).1, fun heD => (hz w hw).2
            (Finset.mem_inter.mp (Finset.mem_inter.mp (Finset.mem_filter.mp heD).1).1).1⟩⟩
    · intro u v huv S hS
      have hbase := (Finset.mem_filter.mp huv).1
      have hjfires := gate_accepts_pair_of_gammaE (Finset.mem_inter.mp (Finset.mem_inter.mp hbase).1).2
      have hkfires := gate_accepts_pair_of_gammaE (Finset.mem_inter.mp hbase).2
      have hcnf : CNF (F0 ∪ F1) (pairInput u v) :=
        (cnf_union F0 F1 _).mpr ⟨(hjNF _).mp hjfires, (hkNF _).mp hkfires⟩
      obtain ⟨w, hw, hx⟩ := hcnf S hS
      rcases pairInput_true u v w |>.mp hx with rfl | rfl
      · exact Or.inl hw
      · exact Or.inr hw
    · intro x hx
      have hcnf : CNF (F0 ∪ F1) x := hx
      have hboth := (cnf_union F0 F1 x).mp hcnf
      have hFx := hjoint x ((hjNF x).mpr hboth.1) ((hkNF x).mpr hboth.2)
      simpa [graphFun] using hFx
  have hcover : Ustar G C ⊆ E0 ∪ E1 ∪ D := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rcases SharedSourceCount.visible_edge_positive_charged_or_joint hleast hT hempty j k hpair he with
        ⟨m, hm, d, hd, hdk, hdx, hp, hr⟩ | ⟨hjoint, hboth⟩
      · have hmeq : m = m1 := by
          have hmem : m = m0 ∨ m = m1 := by
            simpa only [hextra, Finset.mem_insert, Finset.mem_singleton] using hm
          rcases hmem with h | h
          · have hn := hr.1
            rw [h, hm0empty] at hn
            exact (Finset.not_nonempty_empty hn).elim
          · exact h
        subst m
        rcases hdk with rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨he, hr, (edgeCNF_pair_iff F0 u v).mpr ((hjNF _).mp hdx)⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨he, hr, (edgeCNF_pair_iff F1 u v).mpr ((hkNF _).mp hdx)⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨he, (Finset.mem_inter.mp hboth).1⟩,
              (Finset.mem_inter.mp hboth).2⟩, hjoint⟩)
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le (E0 ∪ E1) D
  have hu' := Finset.card_union_le E0 E1
  omega
end EmptyCount
namespace EmptyActual
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget ChainMixed
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma finite_pair_cover (V : Finset ℕ) (hne : V.Nonempty) (hcard : V.card ≤ 2) :
    ∃ j ∈ V, ∃ k ∈ V, ∀ d ∈ V, d = j ∨ d = k := by
  classical
  by_cases htwo : V.card = 2
  · obtain ⟨j, k, _, he⟩ := Finset.card_eq_two.mp htwo
    refine ⟨j, by simp [he], k, by simp [he], ?_⟩
    intro d hd
    simpa only [he, Finset.mem_insert, Finset.mem_singleton] using hd
  · obtain ⟨j, hj⟩ := hne
    have hsmall : V.card ≤ 1 := by omega
    exact ⟨j, hj, j, hj, fun d hd => Or.inl (Finset.card_le_one.mp hsmall d hd j hj)⟩
lemma empty_first_two_extra_or_card_le_three
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅) (m0 m1 : ℕ) (hm01 : m0 < m1)
    (hextra : orN G C \ lam G C = {m0, m1})
    (hm0empty : orIn n C (n + m0) = ∅) : (Ustar G C).card ≤ 3 := by
  classical
  have hm0 : m0 ∈ orN G C \ lam G C := by simp [hextra]
  have hm1 : m1 ∈ orN G C \ lam G C := by simp [hextra]
  have memR : ∀ r ∈ orN G C \ lam G C, r = m0 ∨ r = m1 := by
    intro r hr
    simpa only [hextra, Finset.mem_insert, Finset.mem_singleton] using hr
  have first : ∀ r ∈ orN G C \ lam G C, m0 ≤ r := by
    intro r hr
    rcases memR r hr with rfl | rfl <;> omega
  have only : ∀ r ∈ orN G C \ lam G C, r < m1 → r = m0 := by
    intro r hr hlt
    rcases memR r hr with h | h
    · exact h
    · omega
  have hmax : ∀ r ∈ orN G C \ lam G C, r ≤ m1 := by
    intro r hr
    rcases memR r hr with rfl | rfl <;> omega
  have hm1raw := LastExtra.last_extra_raw_nonempty hleast hempty hm1 hmax
  let V := (junk G C).filter (fun j => ∃ a ∈ tops G C, ∃ b : Fin 2,
    OrReaches n C (opnd C a b) j)
  by_cases hU : (Ustar G C).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hU]
    simp
  have hV : V.Nonempty := by
    obtain ⟨e, he⟩ := hU
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨a, ha, b, j, hj, _, hr, _⟩ := residualTrace hleast hT he
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, a, ha, b, hr⟩⟩
  have reader : ∀ d ∈ V, ∃ r ∈ orN G C \ lam G C,
      n + d ∈ (gateAt C r).inputs ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
        Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + r) := by
    intro d hdV
    obtain ⟨hd, a, ha, b, hp⟩ := Finset.mem_filter.mp hdV
    obtain ⟨r, hr, hin, hpath⟩ := residualPath hleast.1 hempty ha hd hp
    exact ⟨r, hr, hin, a, ha, b, hpath⟩
  by_cases hvisible : ∃ a ∈ tops G C, ∃ b : Fin 2,
      Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m0)
  · obtain ⟨a, ha, b, hpath⟩ := hvisible
    obtain ⟨r, hr, hlt, hmin, _⟩ :=
      VisibleRoots.visible_empty_extra_has_reader hleast.1 hempty hm0 hm0empty ha hpath
    have hr1 : r = m1 := by
      rcases memR r hr with h | h
      · omega
      · exact h
    subst r
    have source : ∀ d ∈ V, n + d ∈ (gateAt C m0).inputs := by
      intro d hdV
      have hd := (Finset.mem_filter.mp hdV).1
      obtain ⟨r, hr, hdin, _⟩ := reader d hdV
      rcases memR r hr with rfl | rfl
      · exact hdin
      · have he := VisibleRoots.empty_input_unique hleast.1 (orData hm1).1 hm1raw
          hmin hdin hm0empty (andRawEmpty (junkData hd).2.1)
        have he' : m0 = d := by omega
        have hop := (orData hm0).2.1
        rw [he', (junkData hd).2.1] at hop
        contradiction
    have hVcard : V.card ≤ 2 := by
      have hv := VisibleForestGeneral.visible_junk_card_le_extra_add_twice_centreless hleast.1 V
        (by intro d hd; exact Finset.mem_filter.mp hd)
      have hr : (orN G C \ lam G C).card ≤ 2 := by rw [hextra]; exact Finset.card_le_two
      simp only [hempty, Finset.card_empty, Nat.mul_zero, Nat.add_zero] at hv
      omega
    obtain ⟨j, hjV, k, hkV, hpairs⟩ := finite_pair_cover V hV hVcard
    have hj := (Finset.mem_filter.mp hjV).1
    have hk := (Finset.mem_filter.mp hkV).1
    have before : ∀ d ∈ V, d < m0 := by
      intro d hd
      have := hleast.1.2.1 _ (orData hm0).1 _ (source d hd)
      omega
    obtain ⟨F0, hF0, hjNF⟩ := PrefixCNF.prefix_junk_basic_cnf hleast.1 hT
      (orData hm0).1.le first j (before j hjV) hj
    obtain ⟨F1, hF1, hkNF⟩ := PrefixCNF.prefix_junk_basic_cnf hleast.1 hT
      (orData hm0).1.le first k (before k hkV) hk
    have path (d : ℕ) (hdV : d ∈ V) :
        Relation.ReflTransGen (OrStep n C) (n + m1) (n + d) :=
      .head ⟨m1, (orData hm1).1, rfl, (orData hm1).2.1, hmin, by omega⟩
        (.head ⟨m0, (orData hm0).1, rfl, (orData hm0).2.1, source d hdV,
          hleast.1.2.1 _ (orData hm0).1 _ (source d hdV)⟩ .refl)
    exact EmptyCount.two_visible_pure_cnf_card_le_three hleast hT hfour color hbip hempty
      m0 m1 j k hextra hm0empty
      (fun a ha b d hd hp => hpairs d (Finset.mem_filter.mpr ⟨hd, a, ha, b, hp⟩))
      (path j hjV) (path k hkV) F0 F1 hF0 hF1 hjNF hkNF
  · have source : ∀ d ∈ V, n + d ∈ (gateAt C m1).inputs := by
      intro d hdV
      obtain ⟨r, hr, hdin, a, ha, b, hp⟩ := reader d hdV
      rcases memR r hr with rfl | rfl
      · exact (hvisible ⟨a, ha, b, hp⟩).elim
      · exact hdin
    obtain ⟨k, hkV⟩ := hV
    have hk := (Finset.mem_filter.mp hkV).1
    have hpair : ∀ a ∈ tops G C, ∀ b : Fin 2, ∀ d ∈ junk G C,
        OrReaches n C (opnd C a b) d → d = k := by
      intro a ha b d hd hp
      exact singleJunkInput hleast.1 hm1 hm1raw hd hk
        (source d (Finset.mem_filter.mpr ⟨hd, a, ha, b, hp⟩)) (source k hkV)
    have hkbefore : k < m1 := by
      have := hleast.1.2.1 _ (orData hm1).1 _ (source k hkV)
      omega
    obtain ⟨F0, F1, hF0, hF1, hNF⟩ := EmptyExtra.junk_before_second_two_cnf hleast.1 hT
      hm0 first hm0empty only (orData hm1).1.le k hkbefore hk
    have hpath : Relation.ReflTransGen (OrStep n C) (n + m1) (n + k) :=
      .head ⟨m1, (orData hm1).1, rfl, (orData hm1).2.1, source k hkV,
        hleast.1.2.1 _ (orData hm1).1 _ (source k hkV)⟩ .refl
    have hcount := EmptyCount.single_visible_two_cnf_card_le_two hleast hT hfour color hbip
      hempty m0 m1 k hextra hm0empty hk hpair hpath F0 F1 hF0 hF1 hNF
    omega
end EmptyActual
namespace GeneralTwoExtra
open Budget PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
lemma two_extra_or_ustar_card_le_four
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅) (hcard : (orN G C \ lam G C).card ≤ 2) :
    (Ustar G C).card ≤ 4 := by
  classical
  by_cases hzero : (orN G C \ lam G C).card = 0
  · have hRzero := Finset.card_eq_zero.mp hzero
    have hUempty : Ustar G C = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      induction e using Sym2.ind with
      | h u v =>
        obtain ⟨a, ha, b, j, hj, _, hr, _⟩ := residualTrace hleast hT he
        obtain ⟨r, hrR, _⟩ := residualPath hleast.1 hempty ha hj hr
        rw [hRzero] at hrR
        exact Finset.notMem_empty _ hrR
    simp [hUempty]
  by_cases hone : (orN G C \ lam G C).card = 1
  · have h := MixingOne.bipartite_one_extra_or_ustar_card_le_one
      color hbip hfour hleast hT hempty hone
    omega
  have htwo : (orN G C \ lam G C).card = 2 := by omega
  obtain ⟨m, l, hne, he⟩ := Finset.card_eq_two.mp htwo
  have hsorted : ∃ m0 m1 : ℕ, m0 < m1 ∧ orN G C \ lam G C = {m0,m1} := by
    by_cases hml : m < l
    · exact ⟨m, l, hml, he⟩
    · exact ⟨l, m, by omega, by simpa only [Finset.pair_comm] using he⟩
  obtain ⟨m0, m1, h01, hextra⟩ := hsorted
  by_cases hblocked : ∃ r ∈ orN G C \ lam G C, ∀ j ∈ junk G C,
      ¬ Relation.ReflTransGen (OrStep n C) (n+r) (n+j)
  · obtain ⟨r, hr, hb⟩ := hblocked
    have h := PureExceptional.two_extra_or_one_pure_card_le_two
      hleast hT hfour color hbip hempty hcard r hr hb
    omega
  have hactive : ∀ r ∈ orN G C \ lam G C, ∃ j ∈ junk G C,
      Relation.ReflTransGen (OrStep n C) (n+r) (n+j) := by
    intro r hr
    by_contra hn
    exact hblocked ⟨r, hr, fun j hj hp => hn ⟨j, hj, hp⟩⟩
  by_cases hraw : ∀ r ∈ orN G C \ lam G C, (orIn n C (n+r)).Nonempty
  · exact SharedSourceCount.two_nonempty_active_extra_ustar_card_le_four
      hleast hT hfour color hbip hempty m0 m1 h01 hextra hraw hactive
  push Not at hraw
  obtain ⟨r, hr, hrempty⟩ := hraw
  have hm1 : m1 ∈ orN G C \ lam G C := by simp [hextra]
  have hmax : ∀ r ∈ orN G C \ lam G C, r ≤ m1 := by
    intro r hr
    have hmem : r = m0 ∨ r = m1 := by
      simpa only [hextra, Finset.mem_insert, Finset.mem_singleton] using hr
    rcases hmem with h | h <;> omega
  have hm1raw := LastExtra.last_extra_raw_nonempty hleast hempty hm1 hmax
  have hr0 : r = m0 := by
    have hmem : r = m0 ∨ r = m1 := by
      simpa only [hextra, Finset.mem_insert, Finset.mem_singleton] using hr
    rcases hmem with h | h
    · exact h
    · exfalso
      have he0 : orIn n C (n+m1) = ∅ := by simpa only [h] using hrempty
      rw [he0] at hm1raw
      exact Finset.not_nonempty_empty hm1raw
  subst r
  have h := EmptyActual.empty_first_two_extra_or_card_le_three
    hleast hT hfour color hbip hempty m0 m1 h01 hextra
    hrempty
  omega
end GeneralTwoExtra
lemma bipartite_penalty_five_large_residual_shape
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfour : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hleast : IsLeastAO G C) (hT : TopForm G C)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hjunk : 2 ≤ (junk G C).card) (hU : 5 ≤ (Ustar G C).card)
    (hP : 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card = 5) :
    (junk G C).card = 2 ∧ centreless G C = ∅ ∧ (orN G C \ lam G C).card = 3 := by
  have hz : centreless G C = ∅ := by
    apply Finset.card_eq_zero.mp
    by_contra hn
    have hp : 0 < (centreless G C).card := by omega
    have h := bipartite_penalty_five_positive_centreless_ustar_card_le_three
      n G C hfour hE hleast hT color hbip hjunk hp hP
    omega
  have hr : 3 ≤ (orN G C \ lam G C).card := by
    by_contra hn
    have h := GeneralTwoExtra.two_extra_or_ustar_card_le_four
      hleast hT hfour color hbip hz (by omega)
    omega
  have hzcard : (centreless G C).card = 0 := by rw [hz]; simp
  exact ⟨by omega, hz, by omega⟩



namespace EarlySources

open Budget OrdinaryCharge PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma rooted_ordinary_card_le_extra_of_all_raw
    (ao : IsAO2 n C) (top : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (order : ∀ j ∈ junk G C, ∀ r ∈ orN G C \ lam G C, j<r)
    (hempty : centreless G C = ∅)
    (hall : ∀ m ∈ orN G C \ lam G C, (orIn n C (n+m)).Nonempty)
    (O : Finset (Sym2 (Fin n))) (hOU : O ⊆ Ustar G C)
    (hroute : ∀ e ∈ O, RootedOrdinary G C e) : O.card ≤ (orN G C \ lam G C).card := by
  classical
  have witness : ∀ e : Sym2 (Fin n), ∃ j m : ℕ, e ∈ O →
      j ∈ junk G C ∧ m ∈ orN G C \ lam G C ∧
      (orIn n C (n+m)).Nonempty ∧ Served G C j m e ∧
      ∃ c ∈ (gateAt C m).inputs, orIn n C c=∅ ∧
        Relation.ReflTransGen (OrStep n C) c (n+j) := by
    intro e
    by_cases he : e∈O
    · obtain ⟨j,hj,m,hm,hn,hs,hb⟩ := rooted_ordinary_boundary ao hempty (hroute e he)
      exact ⟨j,m,fun _ => ⟨hj,hm,hn,hs,hb⟩⟩
    · exact ⟨0,0,fun h => (he h).elim⟩
  choose J M hJM using witness
  apply Finset.card_le_card_of_injOn M (fun e he => (hJM e he).2.1)
  intro e he d hd heq
  change e∈O at he
  change d∈O at hd
  obtain ⟨hj,hm,hn,hs,c,hc,hz,hp⟩ := hJM e he
  obtain ⟨hjd,hmd,hnd,hsd,cd,hcd,hzd,hpd⟩ := hJM d hd
  have hcj := empty_raw_path_direct ao hall hj hz hp
  have hcdj := empty_raw_path_direct ao hall hjd hzd hpd
  rw [hcj] at hc
  rw [hcdj,← heq] at hcd
  have hjjd := singleJunkInput ao hm hn hj hjd hc hcd
  rw [← heq,← hjjd] at hsd
  exact early_served_edges_equal ao top hfour color hbip order (J e) (M e) hj hn
    (hOU he) (hOU hd) hs hsd

lemma two_early_junk_all_raw_residual_bound
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (order : ∀ j ∈ junk G C, ∀ r ∈ orN G C \ lam G C, j < r)
    (hempty : centreless G C = ∅) (hall : ∀ m ∈ orN G C \ lam G C, (orIn n C (n+m)).Nonempty)
    (j k : ℕ) (hpair : junk G C = {j, k}) :
    (Ustar G C).card ≤ (orN G C \ lam G C).card + 1 := by
  classical
  have hj : j ∈ junk G C := by simp [hpair]
  have hk : k ∈ junk G C := by simp [hpair]
  let O := (Ustar G C).filter (RootedOrdinary G C)
  have hOU : O ⊆ Ustar G C := Finset.filter_subset _ _
  have hroute : ∀ e ∈ O, RootedOrdinary G C e := fun e he => (Finset.mem_filter.mp he).2
  have hordinary := rooted_ordinary_card_le_extra_of_all_raw hleast.1 hT hfour color hbip order hempty hall O hOU hroute
  by_cases hJoint : ∀ x, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true
  · let D := Ustar G C ∩ gammaE G C j ∩ gammaE G C k
    have hDU : D ⊆ Ustar G C := by
      intro e he
      exact (Finset.mem_inter.mp (Finset.mem_inter.mp he).1).1
    have hDj : ∀ e ∈ D, e ∈ gammaE G C j := by
      intro e he
      exact (Finset.mem_inter.mp (Finset.mem_inter.mp he).1).2
    have hDk : ∀ e ∈ D, e ∈ gammaE G C k := by
      intro e he
      exact (Finset.mem_inter.mp he).2
    have hD := early_joint_card_le_one hleast.1 hT hfour color hbip order D hDU j k hj hk hDj hDk hJoint
    have hcover : Ustar G C ⊆ O ∪ D := by
      intro e he
      rcases residual_rooted_ordinary_or_joint hleast hT j k hpair he with hraw | ⟨_, hboth⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hraw⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
          ⟨Finset.mem_inter.mpr ⟨he, (Finset.mem_inter.mp hboth).1⟩, (Finset.mem_inter.mp hboth).2⟩)
    have hcount := Finset.card_le_card hcover
    have hsum := Finset.card_union_le O D
    omega
  · have hUO : Ustar G C ⊆ O := by
      intro e he
      rcases residual_rooted_ordinary_or_joint hleast hT j k hpair he with hraw | ⟨hjoint, _⟩
      · exact Finset.mem_filter.mpr ⟨he, hraw⟩
      · exact (hJoint hjoint).elim
    have hcount := Finset.card_le_card hUO
    omega


end EarlySources

namespace EarlyPairs

open Budget EarlySources PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

noncomputable def rawExtra (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Finset ℕ := by
  classical
  exact (orN G C \ lam G C).filter (fun m => (orIn n C (n+m)).Nonempty)

noncomputable def sourcePairs (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Finset (ℕ × ℕ) := by
  classical
  exact (rawExtra G C ×ˢ junk G C).filter (fun p =>
    Relation.ReflTransGen (OrStep n C) (n+p.1) (n+p.2))

lemma ordinary_card_le_source_pairs
    (ao : IsAO2 n C) (top : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (order : ∀ j ∈ junk G C, ∀ r ∈ orN G C \ lam G C, j<r)
    (hempty : centreless G C = ∅)
    (O : Finset (Sym2 (Fin n))) (hOU : O ⊆ Ustar G C)
    (hroute : ∀ e∈O, RootedOrdinary G C e) : O.card ≤ (sourcePairs G C).card := by
  classical
  have witness : ∀ e : Sym2 (Fin n), ∃ j m : ℕ, e∈O →
      j ∈ junk G C ∧ m ∈ orN G C \ lam G C ∧
      (orIn n C (n+m)).Nonempty ∧ Served G C j m e ∧
      Relation.ReflTransGen (OrStep n C) (n+m) (n+j) := by
    intro e
    by_cases he : e∈O
    · obtain ⟨j,hj,m,hm,hn,hs,c,hcin,hcz,hcj⟩ := rooted_ordinary_boundary ao hempty (hroute e he)
      have hp : Relation.ReflTransGen (OrStep n C) (n+m) (n+j) :=
        .head ⟨m,(orData hm).1,rfl,(orData hm).2.1,hcin,ao.2.1 m (orData hm).1 c hcin⟩ hcj
      exact ⟨j,m,fun _ => ⟨hj,hm,hn,hs,hp⟩⟩
    · exact ⟨0,0,fun h => (he h).elim⟩
  choose J M hJM using witness
  apply Finset.card_le_card_of_injOn (fun e => (M e,J e))
  · intro e he
    obtain ⟨hj,hm,hn,hs,hp⟩ := hJM e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hm,hn⟩,hj⟩,hp⟩
  · intro e he d hd heq
    change e∈O at he
    change d∈O at hd
    obtain ⟨hj,hm,hn,hs,hp⟩ := hJM e he
    obtain ⟨hjd,hmd,hnd,hsd,hpd⟩ := hJM d hd
    have heqM : M e=M d := congrArg Prod.fst heq
    have heqJ : J e=J d := congrArg Prod.snd heq
    rw [← heqM,← heqJ] at hsd
    exact early_served_edges_equal ao top hfour color hbip order (J e) (M e) hj hn
      (hOU he) (hOU hd) hs hsd

lemma nonordinary_has_forbidden_pair
    (hleast : IsLeastAO G C) (top : TopForm G C) (hempty : centreless G C = ∅)
    {e : Sym2 (Fin n)} (he : e∈Ustar G C) (hnot : ¬ RootedOrdinary G C e) :
    ∃ p∈rawExtra G C ×ˢ junk G C, p∉sourcePairs G C := by
  classical
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨a,ha,b,j,hj,hav,hr,hjv⟩ := residualTrace hleast top he
    obtain ⟨al,ao,ab⟩ := topData ha
    have hv := (andValOperands hleast.1 al ao _).mp hav (1-b)
    rcases operandSupport hleast.1 top al ao hv with ⟨w,hw,hwe⟩ | ⟨d,hd,hdr,hdv⟩
    · exact (hnot ⟨a,ha,b,j,hj,hr,
        Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1,u,v,rfl,hjv⟩,
        w,hw,Sym2.mem_iff.mpr hwe⟩).elim
    · obtain ⟨m,hm,hn,hp,c,hcin,hcz,hcj⟩ := raw_boundary_on_dirty_path hleast.1 hj
        (orReaches_reach j _ hr).1 (topSides hempty ha b)
      refine ⟨(m,d),Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hm,hn⟩,hd⟩,?_⟩
      intro hmem
      have hmd : Relation.ReflTransGen (OrStep n C) (n+m) (n+d) := (Finset.mem_filter.mp hmem).2
      obtain ⟨_,_,x,hdx,hFx⟩ := junkData hd
      have htopval : gateVal n C a x=true := by
        apply (andValOperands hleast.1 al ao x).mpr
        intro t
        rcases opposite b t with rfl | rfl
        · exact orStep_up (n := n) (by simp) (hp.trans hmd) hdx
        · exact orStep_up (n := n) (by simp) (orReaches_reach d _ hdr).1 hdx
      exact Bool.false_ne_true (hFx.symm.trans (ab x htopval))

end EarlyPairs

namespace EarlyPairs

open Budget EarlySources PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma two_early_junk_card_le_twice_raw
    (hleast : IsLeastAO G C) (top : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (order : ∀ j ∈ junk G C, ∀ r ∈ orN G C \ lam G C, j<r)
    (hempty : centreless G C = ∅) (j k : ℕ) (hpair : junk G C = {j,k}) :
    (Ustar G C).card ≤ 2*(rawExtra G C).card := by
  classical
  have hj : j∈junk G C := by simp [hpair]
  have hk : k∈junk G C := by simp [hpair]
  have hJcard : (junk G C).card ≤ 2 := by
    rw [hpair]
    exact Finset.card_le_two
  let O := (Ustar G C).filter (RootedOrdinary G C)
  have hOU : O ⊆ Ustar G C := Finset.filter_subset _ _
  have hroute : ∀ e∈O, RootedOrdinary G C e := fun e he => (Finset.mem_filter.mp he).2
  have hO := ordinary_card_le_source_pairs hleast.1 top hfour color hbip order hempty O hOU hroute
  have hAsub : sourcePairs G C ⊆ rawExtra G C ×ˢ junk G C := Finset.filter_subset _ _
  have hAcard := Finset.card_le_card hAsub
  have hprod : (rawExtra G C ×ˢ junk G C).card ≤ 2*(rawExtra G C).card := by
    rw [Finset.card_product]
    have h := Nat.mul_le_mul_left (rawExtra G C).card hJcard
    simpa only [Nat.mul_comm] using h
  by_cases hUO : Ustar G C ⊆ O
  · have h := Finset.card_le_card hUO
    omega
  · change ¬ ∀ e, e∈Ustar G C → e∈O at hUO
    push Not at hUO
    obtain ⟨e,he,hnO⟩ := hUO
    have hnot : ¬ RootedOrdinary G C e := fun h => hnO (Finset.mem_filter.mpr ⟨he,h⟩)
    obtain ⟨p,hp,hpnot⟩ := nonordinary_has_forbidden_pair hleast top hempty he hnot
    have hstrict : sourcePairs G C ⊂ rawExtra G C ×ˢ junk G C := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hAsub,?_⟩
      intro heq
      rw [heq] at hpnot
      exact hpnot hp
    have hgap := Finset.card_lt_card hstrict
    have hJoint : ∀ x, gateVal n C j x=true → gateVal n C k x=true → graphFun G ∅ x=true := by
      rcases residual_rooted_ordinary_or_joint hleast top j k hpair he with hraw | ⟨hJ,_⟩
      · exact (hnot hraw).elim
      · exact hJ
    let D := Ustar G C ∩ gammaE G C j ∩ gammaE G C k
    have hDU : D ⊆ Ustar G C := by
      intro e he
      exact (Finset.mem_inter.mp (Finset.mem_inter.mp he).1).1
    have hDj : ∀ e∈D, e∈gammaE G C j := by
      intro e he
      exact (Finset.mem_inter.mp (Finset.mem_inter.mp he).1).2
    have hDk : ∀ e∈D, e∈gammaE G C k := fun e he => (Finset.mem_inter.mp he).2
    have hD := early_joint_card_le_one hleast.1 top hfour color hbip order D hDU j k hj hk hDj hDk hJoint
    have hcover : Ustar G C ⊆ O∪D := by
      intro d hd
      rcases residual_rooted_ordinary_or_joint hleast top j k hpair hd with hraw | ⟨_,hboth⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd,hraw⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
          ⟨Finset.mem_inter.mpr ⟨hd,(Finset.mem_inter.mp hboth).1⟩,(Finset.mem_inter.mp hboth).2⟩)
    have hcount := Finset.card_le_card hcover
    have hsum := Finset.card_union_le O D
    omega

lemma two_early_junk_three_extra_card_le_four
    (hleast : IsLeastAO G C) (top : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (order : ∀ j ∈ junk G C, ∀ r ∈ orN G C \ lam G C, j<r)
    (hempty : centreless G C = ∅) (j k : ℕ) (hpair : junk G C = {j,k})
    (hR : (orN G C \ lam G C).card ≤ 3) : (Ustar G C).card ≤ 4 := by
  classical
  by_cases hall : ∀ m ∈ orN G C \ lam G C, (orIn n C (n+m)).Nonempty
  · have h := two_early_junk_all_raw_residual_bound hleast top hfour color hbip order hempty hall j k hpair
    omega
  · push Not at hall
    obtain ⟨m,hm,hmzero⟩ := hall
    have hmnot : m∉rawExtra G C := by
      intro hmem
      have hne : (orIn n C (n+m)).Nonempty := (Finset.mem_filter.mp hmem).2
      rw [hmzero] at hne
      exact Finset.not_nonempty_empty hne
    have hstrict : rawExtra G C ⊂ orN G C \ lam G C := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.filter_subset _ _,?_⟩
      intro heq
      rw [heq] at hmnot
      exact hmnot hm
    have hlt := Finset.card_lt_card hstrict
    have h := two_early_junk_card_le_twice_raw hleast top hfour color hbip order hempty j k hpair
    omega

end EarlyPairs

namespace ThreeExtraHelpers

open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma top_visible_wire_raw_basic (ao : IsAO2 n C) (hempty : centreless G C = ∅)
    {a w : ℕ} {b : Fin 2} (ha : a ∈ tops G C)
    (hp : Relation.ReflTransGen (OrStep n C) (opnd C a b) w) :
    Basic G C (orIn n C w) := by
  obtain ⟨v, hv⟩ := topSides hempty ha (1-b)
  refine Or.inr ⟨v, ?_⟩
  intro u hu
  exact SimpleGraph.deleteEdges_adj.mp (cleanAdj ao ha b
    (reach_mem_orIn u (hp.trans (mem_orIn_reach u hu))) hv)

lemma raw_basic_before_of_extra_basic (ao : IsAO2 n C) {B : ℕ}
    (hB : B ≤ C.gates.length)
    (hextra : ∀ r ∈ orN G C \ lam G C, r < B → Basic G C (orIn n C (n+r))) :
    ∀ w < n+B, Basic G C (orIn n C w) := by
  intro w hw
  by_cases hsmall : (orIn n C w).card ≤ 1
  · exact Or.inl hsmall
  have hne : (orIn n C w).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hne
  by_cases hi : w < n
  · exfalso
    apply hsmall
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have eq (u : Fin n) (hu : u ∈ orIn n C w) : (u : ℕ) = w := by
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with he | ⟨_, hs, _⟩
      · exact he.symm
      · obtain ⟨k, _, he, _, _, _⟩ := hs
        omega
    exact Fin.ext ((eq a ha).trans (eq b hb).symm)
  obtain ⟨r, rfl⟩ : ∃ r, w = n+r := ⟨w-n, by omega⟩
  have hrB : r < B := by omega
  have hrl : r < C.gates.length := hrB.trans_le hB
  have hro : (gateAt C r).op = GateOp.or := by
    rcases ao.1 _ (gateAt_mem hrl) with h | h
    · rw [andRawEmpty h] at hv
      exact (Finset.notMem_empty _ hv).elim
    · exact h
  have hdirty : ¬ BelowF G C r := by
    intro h
    have ht := reach_var_val (pairInput v v) _ v (mem_orIn_reach v hv) (pairInput_left v v)
    exact G.irrefl ((graphFun_pair G v v).mp (h _ ht))
  have hrN : r ∈ orN G C := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hrl (And.intro hro hdirty)
  by_cases hrL : r ∈ lam G C
  · obtain ⟨z, hz⟩ := ZeroExtra.lambda_clean_pencil ao hrL
    exact Or.inr ⟨z, fun u hu => SimpleGraph.deleteEdges_adj.mp (hz u hu).symm⟩
  · exact hextra r (Finset.mem_sdiff.mpr ⟨hrN, hrL⟩) hrB

lemma term_edges_one_exception_card_le_two
    (ao : IsAO2 n C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (m : ℕ) (F : Finset (Finset (Fin n))) (A B : Finset (Fin n))
    (hA : Basic G C A) (hB : Basic G C B)
    (hclauses : ∀ S ∈ F, Basic G C S ∨ S = A ∪ B)
    (himp : ∀ x, CNF F x → gateVal n C m x = true) :
    (termEdges G C m F).card ≤ 2 := by
  classical
  let E := termEdges G C m F
  by_cases hE : E.Nonempty
  · obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht⟩ := (termEdges_mem.mp he).2.1.1
    have sub : E ⊆ Ustar G C := fun e he => (termEdges_mem.mp he).1
    have basic_mono (S : Finset (Fin n)) (hS : Basic G C S) : ExceptionalCover.Basic G E S := by
      rcases hS with hs | ⟨z, hz⟩
      · exact Or.inl hs
      · exact Or.inr ⟨z, fun v hv => ⟨(hz v hv).1, fun he => (hz v hv).2 (sub he)⟩⟩
    apply PureExceptional.exceptional_local_cover_card_le_two G E color hbip
      (common_neighbors_unique_of_card_le_one G hfour)
      (fun u v huv => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (sub huv)).1)
      t A B (basic_mono A hA) (basic_mono B hB)
    intro u v huv
    obtain ⟨_, ⟨_, a, ha, b, hp, w, hw, hwe⟩, hedge⟩ := termEdges_mem.mp huv
    have hta : t ∈ side C a b := reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
    have clean := cleanAdj ao ha b hta hw
    refine ⟨w, Sym2.mem_iff.mp hwe, (SimpleGraph.deleteEdges_adj.mp clean).1,
      fun h => (SimpleGraph.deleteEdges_adj.mp clean).2 (sub h), ?_⟩
    intro x hx hind
    have hfalse : graphFun G ∅ x = false := by
      have hnone : ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
        rintro ⟨a, b, hab, ha, hb⟩
        exact Bool.false_ne_true ((hind a b hab ha).symm.trans hb)
      simp [graphFun, hnone]
    have hnot : ¬ CNF F x := by
      intro hc
      exact Bool.false_ne_true (hfalse.symm.trans (firingTop ao ha hp hw x (himp x hc) hx))
    have missing : ∃ S ∈ F, ∀ w ∈ S, x w = false := by
      by_contra hn
      apply hnot
      intro S hS
      by_contra hmiss
      exact hn ⟨S, hS, fun w hw => Bool.eq_false_iff.mpr (fun h => hmiss ⟨w, hw, h⟩)⟩
    obtain ⟨S, hS, hmiss⟩ := missing
    refine ⟨S, ?_, ?_, hmiss⟩
    · rcases hclauses S hS with hbasic | heq
      · exact Or.inl (basic_mono S hbasic)
      · exact Or.inr heq
    · intro a b hab
      obtain ⟨w, hw, hwe⟩ := (termEdges_mem.mp hab).2.2 S hS
      rcases Sym2.mem_iff.mp hwe with rfl | rfl
      · exact Or.inl hw
      · exact Or.inr hw
  · change E.card ≤ 2
    simp [Finset.not_nonempty_iff_eq_empty.mp hE]

end ThreeExtraHelpers

namespace ThreeExtraHelpers

open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma second_extra_raw_union_two_basic (ao : IsAO2 n C) {m0 m1 j : ℕ}
    (hm0 : m0 ∈ orN G C \ lam G C) (hm1 : m1 ∈ orN G C \ lam G C)
    (first : ∀ r ∈ orN G C \ lam G C, m0 ≤ r)
    (only : ∀ r ∈ orN G C \ lam G C, r < m1 → r = m0)
    (hj : j ∈ junk G C)
    (path : Relation.ReflTransGen (OrStep n C) (n+m0) (n+j)) :
    ∃ A B : Finset (Fin n), Basic G C A ∧ Basic G C B ∧ orIn n C (n+m1) = A ∪ B := by
  have hbasic (b : Fin 2) : Basic G C (side C m1 b) :=
    raw_before_upper_basic ao hm0 first only (orData hm1).1.le hj path
      (opndBound ao (orData hm1).1 b)
  exact ⟨side C m1 0, side C m1 1, hbasic 0, hbasic 1,
    raw_or_union ao (orData hm1).1 (orData hm1).2.1⟩

lemma raw_before_two_extras_basic_or_second_wire (ao : IsAO2 n C) {m0 m1 B : ℕ}
    (hB : B ≤ C.gates.length)
    (hfirstbasic : Basic G C (orIn n C (n+m0)))
    (only : ∀ r ∈ orN G C \ lam G C, r < B → r = m0 ∨ r = m1)
    {w : ℕ} (hw : w < n+B) : Basic G C (orIn n C w) ∨ w = n+m1 := by
  rcases PureExceptional.raw_shape_or_extra (G := G) (w := w) ao (by omega) with h | ⟨r, hr, he⟩
  · exact Or.inl h
  · have hrB : r < B := by omega
    rcases only r hr hrB with h | h
    · left
      simpa only [he, h] using hfirstbasic
    · exact Or.inr (by omega)

lemma unmixed_operand_before_two_extras_basic (ao : IsAO2 n C) {m0 m1 j k : ℕ}
    (hk : k ∈ junk G C) (hj : j ∈ junk G C)
    (hfirstbasic : Basic G C (orIn n C (n+m0)))
    (only : ∀ r ∈ orN G C \ lam G C, r < k → r = m0 ∨ r = m1)
    (h1j : Relation.ReflTransGen (OrStep n C) (n+m1) (n+j))
    (b : Fin 2) (hnot : ¬ OrReaches n C (opnd C k b) j) :
    Basic G C (side C k b) := by
  rcases raw_before_two_extras_basic_or_second_wire ao (junkData hk).1.le hfirstbasic only
    (opndBound ao (junkData hk).1 b) with h | he
  · exact h
  · exfalso
    apply hnot
    rw [he]
    exact reach_orReaches h1j j rfl (junkData hj).1

end ThreeExtraHelpers

namespace ThreeExtraHelpers

open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma or_path_from_junk_eq {j k : ℕ} (hk : k ∈ junk G C)
    (path : Relation.ReflTransGen (OrStep n C) (n+k) (n+j)) : k = j := by
  rcases Relation.ReflTransGen.cases_head path with he | ⟨w, hs, _⟩
  · omega
  · obtain ⟨r, _, he, ho, _, _⟩ := hs
    have hrk : r = k := by omega
    rw [hrk, (junkData hk).2.1] at ho
    contradiction

lemma raw_boundary_direct_junk_unique (ao : IsAO2 n C) {m c j k : ℕ}
    (hm : m < C.gates.length) (hmraw : (orIn n C (n+m)).Nonempty)
    (hcin : c ∈ (gateAt C m).inputs) (hcempty : orIn n C c = ∅)
    (hcj : Relation.ReflTransGen (OrStep n C) c (n+j))
    (hk : k ∈ junk G C) (hkin : n+k ∈ (gateAt C m).inputs) : j = k := by
  have hceq := VisibleRoots.empty_input_unique ao hm hmraw hcin hkin
    hcempty (andRawEmpty (junkData hk).2.1)
  rw [hceq] at hcj
  exact (or_path_from_junk_eq hk hcj).symm

end ThreeExtraHelpers

namespace ThreeExtraHelpers
open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma edge_positive_raw_boundary_or_joint
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hempty : centreless G C = ∅)
    (j k : ℕ) (hpair : junk G C = {j,k})
    {u v : Fin n} (he : s(u,v) ∈ Ustar G C) :
    (∃ m ∈ orN G C \ lam G C, ∃ d ∈ junk G C,
      gateVal n C d (pairInput u v) = true ∧
      Relation.ReflTransGen (OrStep n C) (n+m) (n+d) ∧ RoutedThrough G C m s(u,v) ∧
      ∃ c ∈ (gateAt C m).inputs, orIn n C c = ∅ ∧
        Relation.ReflTransGen (OrStep n C) c (n+d)) ∨
    (∀ x, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true) ∧
      s(u,v) ∈ gammaE G C j ∩ gammaE G C k := by
  obtain ⟨a,ha,b,d,hd,hav,hr,hdv⟩ := residualTrace hleast hT he
  obtain ⟨al,ao,ab⟩ := topData ha
  have hv := (andValOperands hleast.1 al ao _).mp hav (1-b)
  rcases operandSupport hleast.1 hT al ao hv with ⟨w,hw,hwe⟩ | ⟨l,hl,hlr,hlv⟩
  · obtain ⟨m,hm,hraw,hp,c,hcin,hcz,hcj⟩ := EarlySources.raw_boundary_on_dirty_path hleast.1 hd
      (orReaches_reach d _ hr).1 (topSides hempty ha b)
    have hmd : Relation.ReflTransGen (OrStep n C) (n+m) (n+d) :=
      .head ⟨m, (orData hm).1, rfl, (orData hm).2.1, hcin,
        hleast.1.2.1 m (orData hm).1 c hcin⟩ hcj
    refine Or.inl ⟨m,hm,d,hd,hdv,hmd,?_,c,hcin,hcz,hcj⟩
    exact ⟨hraw,a,ha,b,hp,w,hw,Sym2.mem_iff.mpr hwe⟩
  · have hJ : ∀ x, gateVal n C d x = true → gateVal n C l x = true → graphFun G ∅ x = true := by
      intro x hdx hlx
      apply ab x ((andValOperands hleast.1 al ao x).mpr ?_)
      intro c
      rcases opposite b c with rfl | rfl
      · exact orStep_up (n := n) (by simp) (orReaches_reach d _ hr).1 hdx
      · exact orStep_up (n := n) (by simp) (orReaches_reach l _ hlr).1 hlx
    have hdl : d ≠ l := by
      intro eq
      obtain ⟨_,_,x,hx,hFx⟩ := junkData hl
      exact Bool.false_ne_true (hFx.symm.trans (hJ x (eq ▸ hx) hx))
    have hdE : s(u,v) ∈ gammaE G C d :=
      Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1,u,v,rfl,hdv⟩
    have hlE : s(u,v) ∈ gammaE G C l :=
      Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1,u,v,rfl,hlv⟩
    have member : ∀ d ∈ junk G C, d = j ∨ d = k := by
      intro d hd
      simpa only [hpair, Finset.mem_insert, Finset.mem_singleton] using hd
    rcases member d hd with rfl | rfl <;> rcases member l hl with rfl | rfl
    · exact (hdl rfl).elim
    · exact Or.inr ⟨hJ, Finset.mem_inter.mpr ⟨hdE,hlE⟩⟩
    · exact Or.inr ⟨fun x hx hy => hJ x hy hx, Finset.mem_inter.mpr ⟨hlE,hdE⟩⟩
    · exact (hdl rfl).elim


end ThreeExtraHelpers

namespace ThreeExtraHelpers

open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma upper_junk_shared_cnf_of_operand_shape
    (ao : IsAO2 n C) (top : TopForm G C) {j k : ℕ}
    (hpair : junk G C = {j,k}) (Shape : Finset (Fin n) → Prop)
    (hshape : ∀ b : Fin 2, Shape (side C k b))
    (hunmixed : ∀ b : Fin 2, ¬ OrReaches n C (opnd C k b) j → Basic G C (side C k b)) :
    ∃ S T : Finset (Finset (Fin n)),
      (∀ A ∈ S, Basic G C A) ∧ (∀ A ∈ T, Shape A) ∧
      ∀ x : Fin n → Bool, gateVal n C k x = true ↔
        CNF S x ∧ (gateVal n C j x = true ∨ CNF T x) := by
  classical
  have hk : k ∈ junk G C := by simp [hpair]
  have opNF : ∀ b : Fin 2, ∃ S T : Finset (Finset (Fin n)),
      (∀ A ∈ S, Basic G C A) ∧ (∀ A ∈ T, Shape A) ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C k b) = true ↔
        CNF S x ∧ (gateVal n C j x = true ∨ CNF T x) := by
    intro b
    by_cases hreach : OrReaches n C (opnd C k b) j
    · refine ⟨∅, {side C k b}, by simp, ?_, ?_⟩
      · intro A hA
        exact Finset.mem_singleton.mp hA ▸ hshape b
      · intro x
        simpa only [CNF, Finset.notMem_empty, false_implies, forall_const,
          Finset.mem_singleton, forall_eq, true_and, hreach, or_comm] using
          upper_junk_operand_normal_form ao top hpair b x
    · refine ⟨{side C k b}, ∅, ?_, by simp, ?_⟩
      · intro A hA
        exact Finset.mem_singleton.mp hA ▸ hunmixed b hreach
      · intro x
        simpa [CNF, hreach] using upper_junk_operand_normal_form ao top hpair b x
  obtain ⟨S0,T0,hS0,hT0,hNF0⟩ := opNF 0
  obtain ⟨S1,T1,hS1,hT1,hNF1⟩ := opNF 1
  refine ⟨S0 ∪ S1,T0 ∪ T1,?_,?_,?_⟩
  · intro A hA
    exact (Finset.mem_union.mp hA).elim (hS0 A) (hS1 A)
  · intro A hA
    exact (Finset.mem_union.mp hA).elim (hT0 A) (hT1 A)
  · intro x
    have hand : gateVal n C k x = true ↔
        val C (List.ofFn x) (opnd C k 0) = true ∧
        val C (List.ofFn x) (opnd C k 1) = true := by
      rw [andValOperands ao (junkData hk).1 (junkData hk).2.1 x]
      constructor
      · intro h
        exact ⟨h 0,h 1⟩
      · intro h b
        fin_cases b
        · exact h.1
        · exact h.2
    rw [hand,hNF0 x,hNF1 x,SharedSource.cnf_union,SharedSource.cnf_union]
    tauto

end ThreeExtraHelpers

namespace ThreeExtraHelpers

open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma two_before_upper_class_bound
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (j k m0 m1 m2 : ℕ) (hpair : junk G C = {j,k}) (hjk : j ≠ k)
    (hextra : orN G C \ lam G C = {m0,m1,m2}) (h0k : m0 < k) (h1k : m1 < k)
    (h2in : n+k ∈ (gateAt C m2).inputs)
    (F S T : Finset (Finset (Fin n)))
    (hF : ∀ A ∈ F, Basic G C A) (hS : ∀ A ∈ S, Basic G C A)
    (hlo : ∀ x, gateVal n C j x = true ↔ CNF F x)
    (hhi : ∀ x, gateVal n C k x = true ↔ CNF S x ∧ (gateVal n C j x = true ∨ CNF T x)) :
    (Ustar G C).card ≤ (termEdges G C m0 F ∪ termEdges G C m1 F).card +
      (termEdges G C m2 (S ∪ T)).card + 1 := by
  classical
  have hk : k ∈ junk G C := by simp [hpair]
  have hm2 : m2 ∈ orN G C \ lam G C := by simp [hextra]
  have h2path := EffectiveExtra.extra_or_direct_path hleast.1 hm2 h2in
  have hFS : ∀ A ∈ F ∪ S, Basic G C A := fun A hA =>
    (Finset.mem_union.mp hA).elim (hF A) (hS A)
  have jointNF (x : Fin n → Bool) :
      (gateVal n C j x = true ∧ gateVal n C k x = true) ↔ CNF (F ∪ S) x := by
    rw [hhi x, SharedSource.cnf_union, ← hlo x]
    tauto
  let Joint := ∀ x, gateVal n C j x = true → gateVal n C k x = true → graphFun G ∅ x = true
  let D := if Joint then (Ustar G C).filter (EdgeCNF (F ∪ S)) else termEdges G C m2 (F ∪ S)
  let E01 := termEdges G C m0 F ∪ termEdges G C m1 F
  let E2 := termEdges G C m2 (S ∪ T)
  have hD : D.card ≤ 1 := by
    by_cases hJ : Joint
    · simp only [D, if_pos hJ]
      apply OneCentreless.safe_cnf_subset_card_le_one hfour color hbip
        ((Ustar G C).filter (EdgeCNF (F ∪ S))) (Finset.filter_subset _ _) (F ∪ S) hFS
      · intro u v he
        exact (edgeCNF_pair_iff (F ∪ S) u v).mp (Finset.mem_filter.mp he).2
      · intro x hx
        have h := (jointNF x).mpr hx
        exact hJ x h.1 h.2
    · simp only [D, if_neg hJ]
      apply termEdges_card_le_one hleast.1 hfour color hbip m2 (F ∪ S) hFS
      intro x hx
      exact orStep_up (n := n) (by simp) h2path ((jointNF x).mpr hx).2
  have intoD {u v : Fin n} (he : s(u,v) ∈ Ustar G C)
      (hr : RoutedThrough G C m2 s(u,v)) (hcnf : CNF (F ∪ S) (pairInput u v)) : s(u,v) ∈ D := by
    by_cases hJ : Joint
    · simp only [D, if_pos hJ]
      exact Finset.mem_filter.mpr ⟨he, (edgeCNF_pair_iff (F ∪ S) u v).mpr hcnf⟩
    · simp only [D, if_neg hJ]
      exact termEdges_mem.mpr ⟨he, hr, (edgeCNF_pair_iff (F ∪ S) u v).mpr hcnf⟩
  have cover : Ustar G C ⊆ E01 ∪ E2 ∪ D := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rcases edge_positive_raw_boundary_or_joint hleast hT hempty j k hpair he with
        ⟨m,hm,d,hd,hval,hpath,hroute,c,hcin,hcz,hcj⟩ | ⟨hJoint,hboth⟩
      · have hdd : d = j ∨ d = k := by
          simpa only [hpair, Finset.mem_insert, Finset.mem_singleton] using hd
        have hmm : m = m0 ∨ m = m1 ∨ m = m2 := by
          simpa only [hextra, Finset.mem_insert, Finset.mem_singleton] using hm
        rcases hdd with hdj | hdk
        · subst d
          have hmem : s(u,v) ∈ E01 := by
            rcases hmm with h | h | h
            · subst m
              exact Finset.mem_union_left _ (termEdges_mem.mpr
                ⟨he, hroute, (edgeCNF_pair_iff F u v).mpr ((hlo _).mp hval)⟩)
            · subst m
              exact Finset.mem_union_right _ (termEdges_mem.mpr
                ⟨he, hroute, (edgeCNF_pair_iff F u v).mpr ((hlo _).mp hval)⟩)
            · subst m
              exact (hjk (raw_boundary_direct_junk_unique hleast.1 (orData hm2).1 hroute.1
                hcin hcz hcj hk h2in)).elim
          exact Finset.mem_union_left _ (Finset.mem_union_left _ hmem)
        · subst d
          have hmEq : m = m2 := by
            have hle := orStep_le hpath
            rcases hmm with h | h | h <;> omega
          subst m
          obtain ⟨hSx, hjx | hTx⟩ := (hhi _).mp hval
          · have hcnf := (SharedSource.cnf_union F S (pairInput u v)).mpr ⟨(hlo _).mp hjx, hSx⟩
            exact Finset.mem_union_right _ (intoD he hroute hcnf)
          · have hcnf := (SharedSource.cnf_union S T (pairInput u v)).mpr ⟨hSx, hTx⟩
            exact Finset.mem_union_left _ (Finset.mem_union_right _
              (termEdges_mem.mpr ⟨he, hroute, (edgeCNF_pair_iff (S ∪ T) u v).mpr hcnf⟩))
      · have hJ : Joint := hJoint
        apply Finset.mem_union_right
        simp only [D, if_pos hJ]
        apply Finset.mem_filter.mpr
        refine ⟨he, (edgeCNF_pair_iff (F ∪ S) u v).mpr ((jointNF _).mp ?_)⟩
        exact ⟨gate_accepts_pair_of_gammaE (Finset.mem_inter.mp hboth).1,
          gate_accepts_pair_of_gammaE (Finset.mem_inter.mp hboth).2⟩
  have hc := Finset.card_le_card cover
  have h01 := Finset.card_union_le E01 E2
  have h012 := Finset.card_union_le (E01 ∪ E2) D
  change (Ustar G C).card ≤ E01.card + E2.card + 1
  omega

end ThreeExtraHelpers

namespace ThreeExtraHelpers

open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma three_active_two_before_upper_direct_card_le_four
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (j k m0 m1 m2 : ℕ) (hpair : junk G C = {j,k}) (hjk : j < k)
    (h01 : m0 < m1) (h12 : m1 < m2) (h1k : m1 < k)
    (hextra : orN G C \ lam G C = {m0,m1,m2})
    (hactive : ∀ m ∈ orN G C \ lam G C, ∃ d ∈ junk G C,
      Relation.ReflTransGen (OrStep n C) (n+m) (n+d))
    (h2in : n+k ∈ (gateAt C m2).inputs) :
    (Ustar G C).card ≤ 4 := by
  classical
  have hj : j ∈ junk G C := by simp [hpair]
  have hk : k ∈ junk G C := by simp [hpair]
  have hm0 : m0 ∈ orN G C \ lam G C := by simp [hextra]
  have hm1 : m1 ∈ orN G C \ lam G C := by simp [hextra]
  have hm2 : m2 ∈ orN G C \ lam G C := by simp [hextra]
  have memR : ∀ m ∈ orN G C \ lam G C, m=m0 ∨ m=m1 ∨ m=m2 := by
    intro m hm
    simpa only [hextra,Finset.mem_insert,Finset.mem_singleton] using hm
  have first : ∀ m ∈ orN G C \ lam G C, m0 ≤ m := by
    intro m hm
    rcases memR m hm with h | h | h <;> omega
  have only1 : ∀ m ∈ orN G C \ lam G C, m<m1 → m=m0 := by
    intro m hm hlt
    rcases memR m hm with h | h | h <;> omega
  have hk2 : k < m2 := by
    have h := hleast.1.2.1 m2 (orData hm2).1 (n+k) h2in
    omega
  have onlyK : ∀ m ∈ orN G C \ lam G C, m<k → m=m0 ∨ m=m1 := by
    intro m hm hlt
    rcases memR m hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · omega
  have early_path : ∀ m ∈ orN G C \ lam G C, m<k →
      Relation.ReflTransGen (OrStep n C) (n+m) (n+j) := by
    intro m hm hmk
    obtain ⟨d,hd,hp⟩ := hactive m hm
    have hmem : d=j ∨ d=k := by simpa only [hpair,Finset.mem_insert,Finset.mem_singleton] using hd
    rcases hmem with h | h
    · simpa only [h] using hp
    · have hle := orStep_le hp
      omega
  have h0j := early_path m0 hm0 (by omega)
  have h1j := early_path m1 hm1 h1k
  have h2path := EffectiveExtra.extra_or_direct_path hleast.1 hm2 h2in
  have hj0 : j < m0 := by
    have hin := SharedSource.first_extra_direct_junk hleast.1 hm0 first hj h0j
    have hb := hleast.1.2.1 m0 (orData hm0).1 (n+j) hin
    omega
  obtain ⟨F,hF,hlo⟩ := PrefixCNF.prefix_junk_basic_cnf hleast.1 hT (orData hm0).1.le first j hj0 hj
  have hraw0 := first_mixed_raw_basic hleast.1 hm0 first hj h0j
  have hE0 : (termEdges G C m0 F).card ≤ 1 :=
    termEdges_card_le_one hleast.1 hfour color hbip m0 F hF
      (fun x hx => orStep_up (n := n) (by simp) h0j ((hlo x).mpr hx))
  have hE1 : (termEdges G C m1 F).card ≤ 1 :=
    termEdges_card_le_one hleast.1 hfour color hbip m1 F hF
      (fun x hx => orStep_up (n := n) (by simp) h1j ((hlo x).mpr hx))
  by_cases hvisible : ∃ a ∈ tops G C, ∃ b : Fin 2,
      Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+m1)
  · obtain ⟨a,ha,b,hp⟩ := hvisible
    have hraw1 := top_visible_wire_raw_basic hleast.1 hempty ha hp
    have hraw : ∀ w<n+k, Basic G C (orIn n C w) := by
      apply raw_basic_before_of_extra_basic hleast.1 (junkData hk).1.le
      intro m hm hmk
      rcases onlyK m hm hmk with h | h
      · simpa only [h] using hraw0
      · simpa only [h] using hraw1
    have hside (b : Fin 2) : Basic G C (side C k b) :=
      hraw _ (opndBound hleast.1 (junkData hk).1 b)
    obtain ⟨S,T,hS,hTT,hhi⟩ := upper_junk_shared_cnf_of_operand_shape hleast.1 hT hpair
      (Basic G C) hside (fun b _ => hside b)
    have hST : ∀ A∈S∪T, Basic G C A := fun A hA =>
      (Finset.mem_union.mp hA).elim (hS A) (hTT A)
    have hE2 : (termEdges G C m2 (S∪T)).card ≤ 1 := by
      apply termEdges_card_le_one hleast.1 hfour color hbip m2 (S∪T) hST
      intro x hx
      have h := (SharedSource.cnf_union S T x).mp hx
      exact orStep_up (n := n) (by simp) h2path ((hhi x).mpr ⟨h.1,Or.inr h.2⟩)
    have hc := two_before_upper_class_bound hleast hT hfour color hbip hempty
      j k m0 m1 m2 hpair (by omega) hextra (by omega) h1k h2in F S T hF hS hlo hhi
    have hu := Finset.card_union_le (termEdges G C m0 F) (termEdges G C m1 F)
    omega
  · have hE1empty : termEdges G C m1 F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨_,a,ha,b,hp,_⟩ := (termEdges_mem.mp he).2.1
      exact hvisible ⟨a,ha,b,hp⟩
    obtain ⟨A,B,hA,hB,hraw1⟩ := second_extra_raw_union_two_basic hleast.1 hm0 hm1 first only1 hj h0j
    have hshape (b : Fin 2) : Basic G C (side C k b) ∨ side C k b = A∪B := by
      rcases raw_before_two_extras_basic_or_second_wire hleast.1 (junkData hk).1.le hraw0 onlyK
        (opndBound hleast.1 (junkData hk).1 b) with h | h
      · exact Or.inl h
      · right
        change orIn n C (opnd C k b) = A∪B
        rw [h,hraw1]
    have hunmixed (b : Fin 2) (hnot : ¬ OrReaches n C (opnd C k b) j) : Basic G C (side C k b) :=
      unmixed_operand_before_two_extras_basic hleast.1 hk hj hraw0 onlyK h1j b hnot
    obtain ⟨S,T,hS,hTT,hhi⟩ := upper_junk_shared_cnf_of_operand_shape hleast.1 hT hpair
      (fun D => Basic G C D ∨ D=A∪B) hshape hunmixed
    have hST : ∀ D∈S∪T, Basic G C D ∨ D=A∪B := by
      intro D hD
      exact (Finset.mem_union.mp hD).elim (fun h => Or.inl (hS D h)) (hTT D)
    have hE2 : (termEdges G C m2 (S∪T)).card ≤ 2 := by
      apply term_edges_one_exception_card_le_two hleast.1 hfour color hbip m2 (S∪T) A B hA hB hST
      intro x hx
      have h := (SharedSource.cnf_union S T x).mp hx
      exact orStep_up (n := n) (by simp) h2path ((hhi x).mpr ⟨h.1,Or.inr h.2⟩)
    have hc := two_before_upper_class_bound hleast hT hfour color hbip hempty
      j k m0 m1 m2 hpair (by omega) hextra (by omega) h1k h2in F S T hF hS hlo hhi
    rw [hE1empty,Finset.union_empty] at hc
    omega

end ThreeExtraHelpers

namespace ThreeExtraHelpers

open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma three_active_two_before_upper_card_le_four
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (j k m0 m1 m2 : ℕ) (hpair : junk G C = {j,k}) (hjk : j<k)
    (h01 : m0<m1) (h12 : m1<m2) (h1k : m1<k)
    (hextra : orN G C \ lam G C = {m0,m1,m2})
    (hactive : ∀ m ∈ orN G C \ lam G C, ∃ d ∈ junk G C,
      Relation.ReflTransGen (OrStep n C) (n+m) (n+d)) : (Ustar G C).card ≤ 4 := by
  have hk : k ∈ junk G C := by simp [hpair]
  have hlast : ∀ d ∈ junk G C, d≤k := by
    intro d hd
    have hmem : d=j ∨ d=k := by simpa only [hpair,Finset.mem_insert,Finset.mem_singleton] using hd
    rcases hmem with h | h <;> omega
  obtain ⟨m,hm,hkm,hin⟩ := RemainingOrder.last_junk_has_extra_reader hleast hempty hk hlast
  have hm2 : m=m2 := by
    have hmem : m=m0 ∨ m=m1 ∨ m=m2 := by
      simpa only [hextra,Finset.mem_insert,Finset.mem_singleton] using hm
    rcases hmem with h | h | h <;> omega
  have h2in : n+k ∈ (gateAt C m2).inputs := by simpa only [hm2] using hin
  exact three_active_two_before_upper_direct_card_le_four hleast hT hfour color hbip hempty
    j k m0 m1 m2 hpair hjk h01 h12 h1k hextra hactive h2in

end ThreeExtraHelpers

namespace SourceCNFCount

open Budget ChainMixed PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma source_cnf_family_card_le {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (U : Finset (Sym2 (Fin n))) (hUsub : U ⊆ Ustar G C)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m)
    (t : Fin n) (P : (Fin n → Bool) → Prop)
    (Ts : Finset (Finset (Finset (Fin n))))
    (hshape : ∀ F ∈ Ts, ∀ S ∈ F, ChainMixed.Basic G C S)
    (hcover : ∀ u v, s(u,v) ∈ U → ∃ F ∈ Ts, CNF F (pairInput u v))
    (himplies : ∀ F ∈ Ts, ∀ x : Fin n → Bool, CNF F x → P x)
    (hsource : ∀ u v, s(u,v) ∈ U → ∃ w,
      (w = u ∨ w = v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj t w ∧
      ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false → ¬ P x) :
    U.card ≤ Ts.card := by
  classical
  let part (F : Finset (Finset (Fin n))) := U.filter (EdgeCNF F)
  have hpartU (F : Finset (Finset (Fin n))) : part F ⊆ U := Finset.filter_subset _ _
  have hpartStar (F : Finset (Finset (Fin n))) : part F ⊆ Ustar G C :=
    fun e he => hUsub (hpartU F he)
  have hpartFire (F : Finset (Finset (Fin n))) (u v : Fin n)
      (huv : s(u,v) ∈ part F) : CNF F (pairInput u v) :=
    (edgeCNF_pair_iff F u v).mp (Finset.mem_filter.mp huv).2
  have hbound (F : Finset (Finset (Fin n))) (hF : F ∈ Ts) : (part F).card ≤ 1 := by
    apply cover_property_card_le_one G (part F) color hbip hfour
      (fun u v h => SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hpartStar F h)).1) t
    intro u v huv
    obtain ⟨w,hw,hclean,hsafe⟩ := hsource u v (hpartU F huv)
    have hcl := SimpleGraph.deleteEdges_adj.mp hclean
    refine ⟨w,hw,hcl.1,fun h => hcl.2 (hpartStar F h),?_⟩
    intro x hx hind
    have hnone : ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
      rintro ⟨a,b,hab,ha,hb⟩
      exact Bool.false_ne_true ((hind a b hab ha).symm.trans hb)
    have hfalse : graphFun G ∅ x = false := by simp [graphFun,hnone]
    have hn : ¬ CNF F x := fun h => hsafe x hx hfalse (himplies F hF x h)
    have missing : ∃ S ∈ F, ∀ w ∈ S, x w = false := by
      by_contra hm
      apply hn
      intro S hS
      by_contra hh
      exact hm ⟨S,hS,fun w hw => Bool.eq_false_iff.mpr (fun hwx => hh ⟨w,hw,hwx⟩)⟩
    obtain ⟨S,hS,hSfalse⟩ := missing
    refine ⟨S,?_,?_,hSfalse⟩
    · rcases hshape F hF S hS with hsmall | ⟨z,hz⟩
      · exact Or.inl hsmall
      · exact Or.inr ⟨z,fun w hw => ⟨(hz w hw).1,fun h => (hz w hw).2 (hpartStar F h)⟩⟩
    · intro a b hab
      obtain ⟨w,hw,hx⟩ := hpartFire F a b hab S hS
      rcases (pairInput_true a b w).mp hx with rfl | rfl
      · exact Or.inl hw
      · exact Or.inr hw
  have hcoverUnion : U ⊆ Ts.biUnion part := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨F,hF,hterm⟩ := hcover u v he
      exact Finset.mem_biUnion.mpr ⟨F,hF,Finset.mem_filter.mpr ⟨he,(edgeCNF_pair_iff F u v).mpr hterm⟩⟩
  calc
    U.card ≤ (Ts.biUnion part).card := Finset.card_le_card hcoverUnion
    _ ≤ ∑ F ∈ Ts, (part F).card := Finset.card_biUnion_le
    _ ≤ ∑ F ∈ Ts, 1 := Finset.sum_le_sum (fun F hF => hbound F hF)
    _ = Ts.card := by simp

end SourceCNFCount

namespace BlockedPrefix

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge Budget ChainMixed

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma prefix_junk_shape_cnf (ao : IsAO2 n C) (top : TopForm G C) {m : ℕ}
    (Shape : Finset (Fin n) → Prop)
    (hraw : ∀ w < n+m, Shape (orIn n C w))
    (hactive : ∀ r ∈ orN G C \ lam G C, ∀ d ∈ junk G C,
      Relation.ReflTransGen (OrStep n C) (n+r) (n+d) → m ≤ r) :
    ∀ j < m, j ∈ junk G C → ∃ F : Finset (Finset (Fin n)),
      (∀ S ∈ F, Shape S) ∧
      ∀ x : Fin n → Bool, gateVal n C j x = true ↔ CNF F x := by
  classical
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjm hj
    obtain ⟨jl, jo, _⟩ := junkData hj
    have operand (b : Fin 2) : ∃ F : Finset (Finset (Fin n)),
        (∀ S ∈ F, Shape S) ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C j b) = true ↔ CNF F x := by
      have direct (k : ℕ) (hk : k ∈ junk G C) (hr : OrReaches n C (opnd C j b) k) :
          opnd C j b = n + k := by
        rcases lastOrBefore (orReaches_reach k _ hr).1 with h | ⟨r, rl, ro, ri, rb, rp⟩
        · exact h
        · have hr' := lastOrOutside ao hk rl ro ri rb
          have hmr := hactive r hr' k hk (EffectiveExtra.extra_or_direct_path ao hr' ri)
          have hle := orStep_le rp
          have hlt := opndBound ao jl b
          omega
      by_cases hd : ∃ k, k ∈ junk G C ∧ opnd C j b = n + k
      · obtain ⟨k, hk, he⟩ := hd
        have hbnd := opndBound ao jl b
        have hkj : k < j := by omega
        obtain ⟨F, hF, hsem⟩ := ih k hkj (hkj.trans hjm) hk
        refine ⟨F, hF, ?_⟩
        intro x
        rw [he]
        exact hsem x
      · refine ⟨{side C j b}, ?_, ?_⟩
        · intro S hS
          have hS' : S = side C j b := Finset.mem_singleton.mp hS
          subst S
          exact hraw _ (by have := opndBound ao jl b; omega)
        · intro x
          have hpure : val C (List.ofFn x) (opnd C j b) = true ↔ Hit (side C j b) x := by
            constructor
            · intro hx
              rcases operand_support_general ao top jl jo b x hx with hraw | ⟨k, hk, hr, _⟩
              · exact hraw
              · exact (hd ⟨k, hk, direct k hk hr⟩).elim
            · rintro ⟨w, hw, hx⟩
              exact sideVal hw hx
          simpa only [CNF, Finset.mem_singleton, forall_eq] using hpure
    obtain ⟨F0, hF0, h0⟩ := operand 0
    obtain ⟨F1, hF1, h1⟩ := operand 1
    refine ⟨F0 ∪ F1, ?_, ?_⟩
    · intro S hS
      rcases Finset.mem_union.mp hS with h | h
      · exact hF0 S h
      · exact hF1 S h
    · intro x
      constructor
      · intro hx
        have hboth := (andValOperands ao jl jo x).mp hx
        intro S hS
        rcases Finset.mem_union.mp hS with h | h
        · exact (h0 x).mp (hboth 0) S h
        · exact (h1 x).mp (hboth 1) S h
      · intro hx
        apply (andValOperands ao jl jo x).mpr
        intro b
        fin_cases b
        · exact (h0 x).mpr (fun S hS => hx S (Finset.mem_union_left _ hS))
        · exact (h1 x).mpr (fun S hS => hx S (Finset.mem_union_right _ hS))

end BlockedPrefix

namespace BlockedPrefix
open Budget ChainMixed
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma cnf_erase_split (F : Finset (Finset (Fin n))) (A B : Finset (Fin n))
    (h : A∪B ∈ F) (x : Fin n → Bool) :
    CNF F x ↔ CNF (insert A (F.erase (A∪B))) x ∨ CNF (insert B (F.erase (A∪B))) x := by
  classical
  have hi (T : Finset (Fin n)) : CNF (insert T (F.erase (A∪B))) x ↔
      Hit T x ∧ CNF (F.erase (A∪B)) x := by simp [CNF]
  rw [hi,hi]
  constructor
  · intro hx
    have hrest : CNF (F.erase (A∪B)) x := fun S hS => hx S (Finset.mem_of_mem_erase hS)
    obtain ⟨v,hv,hxv⟩ := hx (A∪B) h
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Or.inl ⟨⟨v,hv,hxv⟩,hrest⟩
    · exact Or.inr ⟨⟨v,hv,hxv⟩,hrest⟩
  · rintro (⟨hA,hrest⟩ | ⟨hB,hrest⟩) S hS
    · by_cases he : S=A∪B
      · subst S
        obtain ⟨v,hv,hxv⟩ := hA
        exact ⟨v,Finset.mem_union_left _ hv,hxv⟩
      · exact hrest S (Finset.mem_erase.mpr ⟨he,hS⟩)
    · by_cases he : S=A∪B
      · subst S
        obtain ⟨v,hv,hxv⟩ := hB
        exact ⟨v,Finset.mem_union_right _ hv,hxv⟩
      · exact hrest S (Finset.mem_erase.mpr ⟨he,hS⟩)

lemma cnf_one_exception_terms (F : Finset (Finset (Fin n))) (A B : Finset (Fin n))
    (hA : Basic G C A) (hB : Basic G C B)
    (hshape : ∀ S∈F, Basic G C S ∨ S=A∪B) :
    ∃ Ts : Finset (Finset (Finset (Fin n))), Ts.card≤2 ∧
      (∀ T∈Ts, ∀ S∈T, Basic G C S) ∧
      ∀ x, CNF F x ↔ ∃ T∈Ts, CNF T x := by
  classical
  by_cases he : A∪B∈F
  · refine ⟨{insert A (F.erase (A∪B)),insert B (F.erase (A∪B))},?_,?_,?_⟩
    · have hc := Finset.card_insert_le (insert A (F.erase (A∪B))) ({insert B (F.erase (A∪B))} : Finset (Finset (Finset (Fin n))))
      simpa using hc
    · intro T hT S hS
      simp only [Finset.mem_insert,Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · rcases Finset.mem_insert.mp hS with rfl | hS
        · exact hA
        · exact (hshape S (Finset.mem_of_mem_erase hS)).resolve_right (Finset.mem_erase.mp hS).1
      · rcases Finset.mem_insert.mp hS with rfl | hS
        · exact hB
        · exact (hshape S (Finset.mem_of_mem_erase hS)).resolve_right (Finset.mem_erase.mp hS).1
    · intro x
      simpa only [Finset.mem_insert,Finset.mem_singleton,exists_eq_or_imp,exists_eq_left] using cnf_erase_split F A B he x
  · refine ⟨{F},by simp,?_,?_⟩
    · intro T hT S hS
      have ht := Finset.mem_singleton.mp hT
      subst T
      rcases hshape S hS with h | rfl
      · exact h
      · exact (he hS).elim
    · intro x
      simp only [Finset.mem_singleton,exists_eq_left]

lemma cnf_two_exception_terms (F : Finset (Finset (Fin n))) (A B D E : Finset (Fin n))
    (hA : Basic G C A) (hB : Basic G C B) (hD : Basic G C D) (hE : Basic G C E)
    (hshape : ∀ S∈F, Basic G C S ∨ S=A∪B ∨ S=D∪E) :
    ∃ Ts : Finset (Finset (Finset (Fin n))), Ts.card≤4 ∧
      (∀ T∈Ts, ∀ S∈T, Basic G C S) ∧
      ∀ x, CNF F x ↔ ∃ T∈Ts, CNF T x := by
  classical
  by_cases he : A∪B∈F
  · have shape (V : Finset (Fin n)) (hV : Basic G C V) :
        ∀ S∈insert V (F.erase (A∪B)), Basic G C S ∨ S=D∪E := by
      intro S hS
      rcases Finset.mem_insert.mp hS with rfl | hS
      · exact Or.inl hV
      · rcases hshape S (Finset.mem_of_mem_erase hS) with h | h | h
        · exact Or.inl h
        · exact ((Finset.mem_erase.mp hS).1 h).elim
        · exact Or.inr h
    obtain ⟨Ts,hTs,hBs,hFs⟩ := cnf_one_exception_terms (insert A (F.erase (A∪B))) D E hD hE (shape A hA)
    obtain ⟨Us,hUs,hBu,hFu⟩ := cnf_one_exception_terms (insert B (F.erase (A∪B))) D E hD hE (shape B hB)
    refine ⟨Ts∪Us,?_,?_,?_⟩
    · have := Finset.card_union_le Ts Us
      omega
    · intro T hT
      exact (Finset.mem_union.mp hT).elim (hBs T) (hBu T)
    · intro x
      rw [cnf_erase_split F A B he x,hFs x,hFu x]
      simp only [Finset.mem_union]
      aesop
  · obtain ⟨Ts,hTs,hBs,hFs⟩ := cnf_one_exception_terms F D E hD hE (by
      intro S hS
      rcases hshape S hS with h | h | h
      · exact Or.inl h
      · exact (he (h ▸ hS)).elim
      · exact Or.inr h)
    exact ⟨Ts,by omega,hBs,hFs⟩

lemma cnf_nested_exception_terms (F : Finset (Finset (Fin n))) (A B D : Finset (Fin n))
    (hA : Basic G C A) (hB : Basic G C B) (hD : Basic G C D)
    (hshape : ∀ S∈F, Basic G C S ∨ S=A∪B ∨ S=(A∪B)∪D) :
    ∃ Ts : Finset (Finset (Finset (Fin n))), Ts.card≤4 ∧
      (∀ T∈Ts, ∀ S∈T, Basic G C S) ∧
      ∀ x, CNF F x ↔ ∃ T∈Ts, CNF T x := by
  classical
  by_cases heq : (A∪B)∪D=A∪B
  · obtain ⟨Ts,hTs,hBs,hFs⟩ := cnf_one_exception_terms F A B hA hB (by
      intro S hS
      rcases hshape S hS with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr (h.trans heq))
    exact ⟨Ts,by omega,hBs,hFs⟩
  by_cases h0 : A∪B∈F
  · have hshape' : ∀ S∈F.erase ((A∪B)∪D), Basic G C S ∨ S=A∪B := by
      intro S hS
      rcases hshape S (Finset.mem_of_mem_erase hS) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact ((Finset.mem_erase.mp hS).1 h).elim
    obtain ⟨Ts,hTs,hBs,hFs⟩ := cnf_one_exception_terms (F.erase ((A∪B)∪D)) A B hA hB hshape'
    refine ⟨Ts,by omega,hBs,?_⟩
    intro x
    rw [←hFs x]
    constructor
    · intro h S hS
      exact h S (Finset.mem_of_mem_erase hS)
    · intro h S hS
      by_cases he : S=(A∪B)∪D
      · subst S
        obtain ⟨v,hv,hx⟩ := h (A∪B) (Finset.mem_erase.mpr ⟨Ne.symm heq,h0⟩)
        exact ⟨v,Finset.mem_union_left _ hv,hx⟩
      · exact h S (Finset.mem_erase.mpr ⟨he,hS⟩)
  · by_cases h1 : (A∪B)∪D∈F
    · have hrest : ∀ S∈F.erase ((A∪B)∪D), Basic G C S := by
        intro S hS
        rcases hshape S (Finset.mem_of_mem_erase hS) with h | h | h
        · exact h
        · exact (h0 (h ▸ Finset.mem_of_mem_erase hS)).elim
        · exact ((Finset.mem_erase.mp hS).1 h).elim
      obtain ⟨Ts,hTs,hBs,hFs⟩ := cnf_one_exception_terms (insert (A∪B) (F.erase ((A∪B)∪D))) A B hA hB (by
        intro S hS
        rcases Finset.mem_insert.mp hS with h | h
        · exact Or.inr h
        · exact Or.inl (hrest S h))
      let T := insert D (F.erase ((A∪B)∪D))
      refine ⟨insert T Ts,?_,?_,?_⟩
      · have hc := Finset.card_insert_le T Ts
        omega
      · intro V hV S hS
        rcases Finset.mem_insert.mp hV with rfl | hV
        · rcases Finset.mem_insert.mp hS with rfl | hS
          · exact hD
          · exact hrest S hS
        · exact hBs V hV S hS
      · intro x
        rw [cnf_erase_split F (A∪B) D h1 x,hFs x]
        change ((∃ V∈Ts, CNF V x) ∨ CNF T x) ↔ ∃ V∈insert T Ts, CNF V x
        simp only [Finset.mem_insert]
        aesop
    · refine ⟨{F},by simp,?_,?_⟩
      · intro T hT S hS
        have ht := Finset.mem_singleton.mp hT
        subst T
        rcases hshape S hS with h | h | h
        · exact h
        · exact (h0 (h ▸ hS)).elim
        · exact (h1 (h ▸ hS)).elim
      · intro x
        simp only [Finset.mem_singleton,exists_eq_left]

end BlockedPrefix

namespace BlockedPrefix
open Budget ChainMixed PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma two_blocked_raw_shapes
    (ao : IsAO2 n C) (p0 p1 m : ℕ) (h01 : p0<p1)
    (hextra : orN G C \ lam G C = {p0,p1,m})
    (hblocked : ∀ p ∈ ({p0,p1} : Finset ℕ), ∀ d∈junk G C,
      ¬ Relation.ReflTransGen (OrStep n C) (n+p) (n+d))
    (hactive : ∃ d∈junk G C, Relation.ReflTransGen (OrStep n C) (n+m) (n+d)) :
    ∃ A B : Finset (Fin n), Basic G C A ∧ Basic G C B ∧
      orIn n C (n+p0)=A∪B ∧
      ((∃ D E : Finset (Fin n), Basic G C D ∧ Basic G C E ∧ orIn n C (n+p1)=D∪E) ∨
       ∃ D : Finset (Fin n), Basic G C D ∧ orIn n C (n+p1)=(A∪B)∪D) := by
  classical
  have hp0 : p0∈orN G C \ lam G C := by simp [hextra]
  have hp1 : p1∈orN G C \ lam G C := by simp [hextra]
  have opShape (p : ℕ) (hp : p∈({p0,p1} : Finset ℕ)) (hR : p∈orN G C \ lam G C) (b : Fin 2) :
      Basic G C (side C p b) ∨ opnd C p b = n+p0 ∧ p0<p := by
    have hl := (orData hR).1
    have hb := opndBound ao hl b
    rcases PureExceptional.raw_shape_or_extra (G := G) ao (by omega : opnd C p b<n+C.gates.length) with hs | ⟨r,hr,he⟩
    · exact Or.inl hs
    · have hm : r=p0 ∨ r=p1 ∨ r=m := by
        simpa only [hextra,Finset.mem_insert,Finset.mem_singleton] using hr
      rcases hm with hr0 | hr1 | hrm
      · exact Or.inr ⟨by omega,by omega⟩
      · have hp' : p=p0 ∨ p=p1 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hp
        rcases hp' with h | h <;> omega
      · obtain ⟨d,hd,hpath⟩ := hactive
        have he' : opnd C p b = n+m := by omega
        have hin : n+m∈(gateAt C p).inputs := he' ▸ opndMem ao (orData hR).1 b
        exact (hblocked p hp d hd ((EffectiveExtra.extra_or_direct_path ao hR hin).trans hpath)).elim
  have shape0 (b : Fin 2) : Basic G C (side C p0 b) := by
    rcases opShape p0 (by simp) hp0 b with h | ⟨_,h⟩
    · exact h
    · omega
  refine ⟨side C p0 0,side C p0 1,shape0 0,shape0 1,?_,?_⟩
  · exact PureExceptional.raw_union_operands ao (orData hp0).1 (orData hp0).2.1
  have hraw0 := PureExceptional.raw_union_operands ao (orData hp0).1 (orData hp0).2.1
  have hraw1 := PureExceptional.raw_union_operands ao (orData hp1).1 (orData hp1).2.1
  rcases opShape p1 (by simp) hp1 0 with h0 | ⟨h0,_⟩ <;>
    rcases opShape p1 (by simp) hp1 1 with h1 | ⟨h1,_⟩
  · exact Or.inl ⟨side C p1 0,side C p1 1,h0,h1,hraw1⟩
  · refine Or.inr ⟨side C p1 0,h0,?_⟩
    change orIn n C (n+p1)=(side C p0 0∪side C p0 1)∪orIn n C (opnd C p1 0)
    rw [hraw1,h1,hraw0,Finset.union_comm]
    rfl
  · refine Or.inr ⟨side C p1 1,h1,?_⟩
    change orIn n C (n+p1)=(side C p0 0∪side C p0 1)∪orIn n C (opnd C p1 1)
    rw [hraw1,h0,hraw0]
    rfl
  · refine Or.inr ⟨∅,Or.inl (by simp),?_⟩
    rw [hraw1,h0,h1,hraw0]
    simp only [Finset.union_self,Finset.union_empty]
    rfl

lemma one_active_prefix_raw_shape (ao : IsAO2 n C) (p0 p1 m : ℕ)
    (hextra : orN G C \ lam G C = {p0,p1,m}) :
    ∀ w<n+m, w<n+C.gates.length → Basic G C (orIn n C w) ∨
      orIn n C w=orIn n C (n+p0) ∨ orIn n C w=orIn n C (n+p1) := by
  intro w hwm hwl
  rcases PureExceptional.raw_shape_or_extra (G := G) ao hwl with h | ⟨r,hr,he⟩
  · exact Or.inl h
  · have hm : r=p0 ∨ r=p1 ∨ r=m := by
      simpa only [hextra,Finset.mem_insert,Finset.mem_singleton] using hr
    rcases hm with rfl | rfl | rfl
    · exact Or.inr (Or.inl (by rw [he]))
    · exact Or.inr (Or.inr (by rw [he]))
    · omega

end BlockedPrefix

namespace BlockedPrefix
open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma two_blocked_extra_or_card_le_four
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (p0 p1 m : ℕ) (h01 : p0<p1)
    (hextra : orN G C \ lam G C = {p0,p1,m})
    (hblocked : ∀ p∈({p0,p1} : Finset ℕ), ∀ d∈junk G C,
      ¬ Relation.ReflTransGen (OrStep n C) (n+p) (n+d)) :
    (Ustar G C).card ≤ 4 := by
  classical
  by_cases hU : (Ustar G C).Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp hU]
  have hm : m∈orN G C \ lam G C := by simp [hextra]
  have unique : ∀ r∈orN G C \ lam G C, ∀ d∈junk G C,
      Relation.ReflTransGen (OrStep n C) (n+r) (n+d) → r=m := by
    intro r hr d hd hp
    have hmem : r=p0 ∨ r=p1 ∨ r=m := by
      simpa only [hextra,Finset.mem_insert,Finset.mem_singleton] using hr
    rcases hmem with h | h | h
    · subst r
      exact (hblocked p0 (by simp) d hd hp).elim
    · subst r
      exact (hblocked p1 (by simp) d hd hp).elim
    · exact h
  have hactive : ∃ d∈junk G C, Relation.ReflTransGen (OrStep n C) (n+m) (n+d) := by
    obtain ⟨e,he⟩ := hU
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨a,ha,b,d,hd,_,hr,_⟩ := residualTrace hleast hT he
      obtain ⟨r,hrR,hin,_⟩ := residualPath hleast.1 hempty ha hd hr
      have hp := EffectiveExtra.extra_or_direct_path hleast.1 hrR hin
      have heq := unique r hrR d hd hp
      exact ⟨d,hd,by simpa only [heq] using hp⟩
  obtain ⟨j,hj,hjm,t,hpos,hsource⟩ := EffectiveExtra.one_effective_extra_or_source hleast hT hempty m unique hU
  obtain ⟨A,B,hA,hB,hraw0,hraw1⟩ := two_blocked_raw_shapes hleast.1 p0 p1 m h01 hextra hblocked hactive
  have hml := (orData hm).1
  obtain ⟨F,hF,hNF⟩ := prefix_junk_shape_cnf hleast.1 hT
    (m := m) (fun S => Basic G C S ∨ S=orIn n C (n+p0) ∨ S=orIn n C (n+p1))
    (fun w hw => one_active_prefix_raw_shape hleast.1 p0 p1 m hextra w hw (by omega))
    (fun r hr d hd hp => (unique r hr d hd hp).ge) j hjm hj
  have hterms : ∃ Ts : Finset (Finset (Finset (Fin n))), Ts.card≤4 ∧
      (∀ T∈Ts, ∀ S∈T, Basic G C S) ∧
      ∀ x, CNF F x ↔ ∃ T∈Ts, CNF T x := by
    rcases hraw1 with ⟨D,E,hD,hE,hraw1⟩ | ⟨D,hD,hraw1⟩
    · apply cnf_two_exception_terms F A B D E hA hB hD hE
      intro S hS
      simpa only [hraw0,hraw1] using hF S hS
    · apply cnf_nested_exception_terms F A B D hA hB hD
      intro S hS
      simpa only [hraw0,hraw1] using hF S hS
  obtain ⟨Ts,hTs,hBasic,hTerms⟩ := hterms
  have hcount := SourceCNFCount.source_cnf_family_card_le G C (Ustar G C) (by intro e he; exact he)
    color hbip (common_neighbors_unique_of_card_le_one G hfour) t
    (fun x => gateVal n C j x=true) Ts hBasic
    (fun u v huv => (hTerms _).mp ((hNF _).mp (hpos u v huv)))
    (fun T hT x hx => (hNF x).mpr ((hTerms x).mpr ⟨T,hT,hx⟩))
    (by
      intro u v huv
      obtain ⟨w,z,he,hclean,hsafe⟩ := hsource s(u,v) huv
      have hw : w=u ∨ w=v := by
        rcases Sym2.eq_iff.mp he with ⟨h,_⟩ | ⟨_,h⟩
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      refine ⟨w,hw,hclean.symm,?_⟩
      intro x hx hfalse htrue
      exact Bool.false_ne_true ((hsafe x hx hfalse).symm.trans htrue))
  omega

end BlockedPrefix

namespace ThreeExtraHelpers
open Budget
variable {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
lemma all_active_three_extra_large_residual_order
  (hl:IsLeastAO G C) (hT:TopForm G C) (h4:NoFourCycle G)
  (f:Fin n → Bool) (hb:∀ a b,G.Adj a b → f a ≠ f b)
  (hz:centreless G C = ∅)
  (j k a b c:ℕ) (hs:junk G C = {j,k}) (h:j<k)
  (h01:a<b) (h12:b<c)
  (he:orN G C \ lam G C = {a,b,c})
  (ha:∀ m∈orN G C \ lam G C,∃ d∈junk G C,
   Relation.ReflTransGen (OrStep n C) (n+m) (n+d))
  (hU:5≤(Ustar G C).card):
  j<a∧a<k∧k<b∧
   Relation.ReflTransGen (OrStep n C) (n+a) (n+j)∧
   (n+k∈(gateAt C b).inputs ∨ n+k∈(gateAt C c).inputs):= by
 have hj:j∈junk G C:= by simp [hs]
 have hk:k∈junk G C:= by simp [hs]
 have hm0:a∈orN G C \ lam G C:= by simp [he]
 have hm1:b∈orN G C \ lam G C:= by simp [he]
 have hn0:= RemainingOrder.junk_ne_extra hk hm0
 have hn1:= RemainingOrder.junk_ne_extra hk hm1
 have mj:∀ d∈junk G C,d=j ∨ d=k:= by simp [hs]
 have mr:∀ m∈orN G C \ lam G C,m=a ∨ m=b ∨ m=c:= by simp [he]
 have h0k:a<k:= by
  by_contra hn
  have hko:k<a:= by omega
  have order:∀ d∈junk G C,∀ m∈orN G C \ lam G C,d<m:= by
   intro d hd m hm
   rcases mj d hd with h | h<;> rcases mr m hm with h' | h' | h'<;> omega
  have hR:(orN G C \ lam G C).card≤3:= by rw [he]; exact Finset.card_le_three
  have h:= EarlyPairs.two_early_junk_three_extra_card_le_four hl hT h4 f hb order hz j k hs hR
  omega
 have hk1:k<b:= by
  by_contra hn
  have h1k:b<k:= by omega
  have h:= three_active_two_before_upper_card_le_four hl hT h4 f hb hz
   j k a b c hs h h01 h12 h1k he ha
  omega
 obtain ⟨d,hd,hp⟩:= ha a hm0
 have hdj:d=j:= by
  rcases mj d hd with h | h
  · exact h
  · have hle:= orStep_le hp; omega
 subst d
 have hj0:j<a:= by
  have hle:= orStep_le hp
  have hne:= RemainingOrder.junk_ne_extra hj hm0
  omega
 have hmax:∀ d∈junk G C,d≤k:= by
  intro d hd
  rcases mj d hd with h | h<;> omega
 obtain ⟨m,hm,hkm,hin⟩:= RemainingOrder.last_junk_has_extra_reader hl hz hk hmax
 have hr:n+k∈(gateAt C b).inputs ∨ n+k∈(gateAt C c).inputs:= by
  rcases mr m hm with h | h | h
  · omega
  · exact Or.inl (h ▸ hin)
  · exact Or.inr (h ▸ hin)
 exact ⟨hj0,h0k,hk1,hp,hr⟩
end ThreeExtraHelpers

namespace ThreeExtraHelpers

open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma three_extra_all_raw_shared_source_card_le_five
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (j k m0 m1 m2 : ℕ) (hpair : junk G C = {j,k}) (hjk : j ≠ k)
    (hextra : orN G C \ lam G C = {m0,m1,m2}) (h0k : m0<k)
    (hall : ∀ m∈orN G C \ lam G C, (orIn n C (n+m)).Nonempty)
    (F S T : Finset (Finset (Fin n)))
    (hF : ∀ A∈F, Basic G C A) (hS : ∀ A∈S, Basic G C A) (hTT : ∀ A∈T, Basic G C A)
    (hlo : ∀ x, gateVal n C j x=true ↔ CNF F x)
    (hhi : ∀ x, gateVal n C k x=true ↔ CNF S x ∧ (gateVal n C j x=true ∨ CNF T x)) :
    (Ustar G C).card ≤ 5 := by
  classical
  have hj : j∈junk G C := by simp [hpair]
  have hk : k∈junk G C := by simp [hpair]
  have hFS : ∀ A∈F∪S, Basic G C A := fun A hA => (Finset.mem_union.mp hA).elim (hF A) (hS A)
  have hST : ∀ A∈S∪T, Basic G C A := fun A hA => (Finset.mem_union.mp hA).elim (hS A) (hTT A)
  have jointNF (x : Fin n → Bool) :
      (gateVal n C j x=true ∧ gateVal n C k x=true) ↔ CNF (F∪S) x := by
    rw [hhi x, SharedSource.cnf_union, ← hlo x]
    tauto
  let Joint := ∀ x, gateVal n C j x=true → gateVal n C k x=true → graphFun G ∅ x=true
  let D := if Joint then (Ustar G C).filter (EdgeCNF (F∪S)) else ∅
  let E (m : ℕ) := if n+j∈(gateAt C m).inputs then termEdges G C m F else
    if n+k∈(gateAt C m).inputs then
      if Joint then termEdges G C m (S∪T) else termEdges G C m (F∪S) ∪ termEdges G C m (S∪T)
    else ∅
  have hD : D.card ≤ if Joint then 1 else 0 := by
    by_cases hJ : Joint
    · simp only [D, if_pos hJ]
      apply OneCentreless.safe_cnf_subset_card_le_one hfour color hbip
        ((Ustar G C).filter (EdgeCNF (F∪S))) (Finset.filter_subset _ _) (F∪S) hFS
      · intro u v he
        exact (edgeCNF_pair_iff (F∪S) u v).mp (Finset.mem_filter.mp he).2
      · intro x hx
        have h := (jointNF x).mpr hx
        exact hJ x h.1 h.2
    · simp [D,hJ]
  have hE (m : ℕ) (hm : m∈orN G C \ lam G C) : (E m).card ≤ if Joint then 1 else 2 := by
    by_cases hji : n+j∈(gateAt C m).inputs
    · have hp := EffectiveExtra.extra_or_direct_path hleast.1 hm hji
      have hc := termEdges_card_le_one hleast.1 hfour color hbip m F hF
        (fun x hx => orStep_up (n := n) (by simp) hp ((hlo x).mpr hx))
      simp only [E,if_pos hji]
      split_ifs <;> omega
    · by_cases hki : n+k∈(gateAt C m).inputs
      · have hp := EffectiveExtra.extra_or_direct_path hleast.1 hm hki
        have hcST := termEdges_card_le_one hleast.1 hfour color hbip m (S∪T) hST
          (fun x hx => orStep_up (n := n) (by simp) hp ((hhi x).mpr
            ⟨((SharedSource.cnf_union S T x).mp hx).1,Or.inr ((SharedSource.cnf_union S T x).mp hx).2⟩))
        have hcFS := termEdges_card_le_one hleast.1 hfour color hbip m (F∪S) hFS
          (fun x hx => orStep_up (n := n) (by simp) hp ((jointNF x).mpr hx).2)
        have hu := Finset.card_union_le (termEdges G C m (F∪S)) (termEdges G C m (S∪T))
        simp only [E,if_neg hji,if_pos hki]
        split_ifs <;> omega
      · simp only [E,if_neg hji,if_neg hki,Finset.card_empty]
        split_ifs <;> omega
  have hE0 : (E m0).card ≤ 1 := by
    have hm : m0∈orN G C \ lam G C := by simp [hextra]
    have hnot : n+k∉(gateAt C m0).inputs := by
      intro h
      have hb := hleast.1.2.1 m0 (orData hm).1 (n+k) h
      omega
    by_cases hji : n+j∈(gateAt C m0).inputs
    · simp only [E,if_pos hji]
      have hp := EffectiveExtra.extra_or_direct_path hleast.1 hm hji
      exact termEdges_card_le_one hleast.1 hfour color hbip m0 F hF
        (fun x hx => orStep_up (n := n) (by simp) hp ((hlo x).mpr hx))
    · simp [E,hji,hnot]
  have cover : Ustar G C ⊆ E m0 ∪ E m1 ∪ E m2 ∪ D := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rcases edge_positive_raw_boundary_or_joint hleast hT hempty j k hpair he with
        ⟨m,hm,d,hd,hval,hpath,hroute,c,hcin,hcz,hcj⟩ | ⟨hJoint,hboth⟩
      · have hcd := EarlySources.empty_raw_path_direct hleast.1 hall hd hcz hcj
        have hdi : n+d∈(gateAt C m).inputs := hcd ▸ hcin
        have hdd : d=j ∨ d=k := by
          simpa only [hpair,Finset.mem_insert,Finset.mem_singleton] using hd
        have hmem : s(u,v)∈E m ∪ D := by
          rcases hdd with hdj | hdk
          · subst d
            apply Finset.mem_union_left
            simp only [E,if_pos hdi]
            exact termEdges_mem.mpr ⟨he,hroute,(edgeCNF_pair_iff F u v).mpr ((hlo _).mp hval)⟩
          · subst d
            have hnot : n+j∉(gateAt C m).inputs := by
              intro hji
              exact hjk (singleJunkInput hleast.1 hm (hall m hm) hj hk hji hdi)
            obtain ⟨hSx,hjx | hTx⟩ := (hhi _).mp hval
            · have hx := (SharedSource.cnf_union F S (pairInput u v)).mpr ⟨(hlo _).mp hjx,hSx⟩
              by_cases hJ : Joint
              · apply Finset.mem_union_right
                simp only [D,if_pos hJ]
                exact Finset.mem_filter.mpr ⟨he,(edgeCNF_pair_iff (F∪S) u v).mpr hx⟩
              · apply Finset.mem_union_left
                simp only [E,if_neg hnot,if_pos hdi,if_neg hJ]
                exact Finset.mem_union_left _ (termEdges_mem.mpr
                  ⟨he,hroute,(edgeCNF_pair_iff (F∪S) u v).mpr hx⟩)
            · have hx := (SharedSource.cnf_union S T (pairInput u v)).mpr ⟨hSx,hTx⟩
              have hterm := termEdges_mem.mpr ⟨he,hroute,(edgeCNF_pair_iff (S∪T) u v).mpr hx⟩
              apply Finset.mem_union_left
              simp only [E,if_neg hnot,if_pos hdi]
              split_ifs
              · exact hterm
              · exact Finset.mem_union_right _ hterm
        have hmm : m=m0 ∨ m=m1 ∨ m=m2 := by
          simpa only [hextra,Finset.mem_insert,Finset.mem_singleton] using hm
        rcases Finset.mem_union.mp hmem with h | h
        · apply Finset.mem_union_left
          rcases hmm with rfl | rfl | rfl
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
          · exact Finset.mem_union_right _ h
        · exact Finset.mem_union_right _ h
      · apply Finset.mem_union_right
        have hJ : Joint := hJoint
        simp only [D,if_pos hJ]
        refine Finset.mem_filter.mpr ⟨he,(edgeCNF_pair_iff (F∪S) u v).mpr ((jointNF _).mp ?_)⟩
        exact ⟨gate_accepts_pair_of_gammaE (Finset.mem_inter.mp hboth).1,
          gate_accepts_pair_of_gammaE (Finset.mem_inter.mp hboth).2⟩
  have hE1 := hE m1 (by simp [hextra])
  have hE2 := hE m2 (by simp [hextra])
  have hc := Finset.card_le_card cover
  have hu1 := Finset.card_union_le (E m0) (E m1)
  have hu2 := Finset.card_union_le (E m0∪E m1) (E m2)
  have hu3 := Finset.card_union_le (E m0∪E m1∪E m2) D
  by_cases hJ : Joint <;> simp only [hJ,ite_true,ite_false] at hD hE1 hE2 <;> omega

end ThreeExtraHelpers

namespace ThreeExtraHelpers
open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma three_active_one_before_upper_all_raw_card_le_five
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (j k m0 m1 m2 : ℕ) (hpair : junk G C = {j,k}) (hjk : j<k)
    (h01 : m0<m1) (h12 : m1<m2) (h0k : m0<k) (hk1 : k<m1)
    (hextra : orN G C \ lam G C = {m0,m1,m2})
    (hactive : ∀ m∈orN G C \ lam G C, ∃ d∈junk G C,
      Relation.ReflTransGen (OrStep n C) (n+m) (n+d))
    (hall : ∀ m∈orN G C \ lam G C, (orIn n C (n+m)).Nonempty) :
    (Ustar G C).card ≤ 5 := by
  classical
  have hj : j∈junk G C := by simp [hpair]
  have hk : k∈junk G C := by simp [hpair]
  have hm0 : m0∈orN G C \ lam G C := by simp [hextra]
  have memR : ∀ m∈orN G C \ lam G C, m=m0 ∨ m=m1 ∨ m=m2 := by
    intro m hm
    simpa only [hextra,Finset.mem_insert,Finset.mem_singleton] using hm
  have first : ∀ m∈orN G C \ lam G C, m0≤m := by
    intro m hm
    rcases memR m hm with h | h | h <;> omega
  have onlyK : ∀ m∈orN G C \ lam G C, m<k → m=m0 := by
    intro m hm hmk
    rcases memR m hm with h | h | h <;> omega
  obtain ⟨d,hd,hp⟩ := hactive m0 hm0
  have hdj : d=j := by
    have hd' : d=j ∨ d=k := by simpa only [hpair,Finset.mem_insert,Finset.mem_singleton] using hd
    rcases hd' with h | h
    · exact h
    · have hle := orStep_le hp
      omega
  subst d
  have hj0 : j<m0 := by
    have hle := orStep_le hp
    have hne := RemainingOrder.junk_ne_extra hj hm0
    omega
  obtain ⟨F,hF,hlo⟩ := PrefixCNF.prefix_junk_basic_cnf hleast.1 hT (orData hm0).1.le first j hj0 hj
  have hraw : ∀ w<n+k, Basic G C (orIn n C w) :=
    fun w hw => raw_before_upper_basic hleast.1 hm0 first onlyK (junkData hk).1.le hj hp hw
  have hside (b : Fin 2) : Basic G C (side C k b) :=
    hraw _ (opndBound hleast.1 (junkData hk).1 b)
  obtain ⟨S,T,hS,hTT,hhi⟩ := upper_junk_shared_cnf_of_operand_shape hleast.1 hT hpair
    (Basic G C) hside (fun b _ => hside b)
  exact three_extra_all_raw_shared_source_card_le_five hleast hT hfour color hbip hempty
    j k m0 m1 m2 hpair (by omega) hextra h0k hall F S T hF hS hTT hlo hhi

end ThreeExtraHelpers

namespace LeastWire
open Budget PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma gate_ne_earlier_wire (hleast : IsLeastAO G C) {j i : ℕ}
    (hj : j<C.gates.length) (hi : i<n+j) :
    ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) i = gateVal n C j x := by
  intro hsem
  have hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x)=graphFun G ∅ x :=
    fun x => congrFun hleast.2.1 x
  have hAO : Ledger.S98.AO n C := Ledger.S98.AO_of_IsAO2 n C hleast.1
  have hLeast : Ledger.S98.Least n C := ⟨hAO,fun D hD hDf =>
    hleast.2.2 D (Ledger.S98.IsAO2_of_AO n D hD) (funext fun x => (hDf x).trans (hfun x))⟩
  have hsame : ∀ x : Fin n → Bool,
      (Ledger.S98.eraseC n C j i).eval (List.ofFn x)=C.eval (List.ofFn x) := by
    intro x
    have hw : Ledger.S98.W n C x i=Ledger.S98.W n C x (n+j) := hsem x
    exact Ledger.S98.erase_wires n C j i hj hi x (Or.inl hw) C.output (fun _ => hw)
  have hsize := hLeast.2 _ (Ledger.S98.erase_AO n C j i hLeast.1 hj hi) hsame
  have hlength := Ledger.S98.erase_length n C j i hj
  omega

end LeastWire

namespace LeastWire
open Budget ChainMixed PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma nonbelow_has_and_above (hleast : IsLeastAO G C) :
    ∀ m<C.gates.length, ¬ BelowF G C m →
    ∃ a<C.gates.length, (gateAt C a).op=GateOp.and ∧ ∃ b : Fin 2,
      Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+m) := by
  have descend : ∀ d m, C.gates.length-m=d → m<C.gates.length → ¬ BelowF G C m →
      ∃ a<C.gates.length, (gateAt C a).op=GateOp.and ∧ ∃ b : Fin 2,
        Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+m) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro m hd hm hdirty
      obtain ⟨k,hmk,hk,hin⟩ := LastExtra.least_nonbelow_has_reader hleast hm hdirty
      rcases hleast.1.1 _ (gateAt_mem hk) with hka | hko
      · obtain ⟨b,hb⟩ := inputsAsOpnd hleast.1 hk hin
        exact ⟨k,hk,hka,b,by rw [←hb]⟩
      · have hp : Relation.ReflTransGen (OrStep n C) (n+k) (n+m) :=
          .single ⟨k,hk,rfl,hko,hin,by omega⟩
        have hkdirty : ¬ BelowF G C k := by
          intro hbelow
          apply hdirty
          intro x hx
          exact hbelow x (orStep_up (n := n) (by simp) hp hx)
        obtain ⟨a,ha,ho,b,hb⟩ := ih (C.gates.length-k) (by omega) k rfl hk hkdirty
        exact ⟨a,ha,ho,b,hb.trans hp⟩
  intro m hm hd
  exact descend (C.gates.length-m) m rfl hm hd

lemma wire_support_below_and (ao : IsAO2 n C) (top : TopForm G C)
    {a w : ℕ} (ha : a<C.gates.length) (ho : (gateAt C a).op=GateOp.and)
    (b : Fin 2) (hp : Relation.ReflTransGen (OrStep n C) (opnd C a b) w)
    (x : Fin n → Bool) (hv : val C (List.ofFn x) w=true) :
    Hit (orIn n C w) x ∨ ∃ d∈junk G C,
      Relation.ReflTransGen (OrStep n C) w (n+d) ∧ gateVal n C d x=true := by
  obtain ⟨v,hr,hw,hkind⟩ := or_trace (n := n) (by simp) w hv
  rcases hkind with hinput | ⟨d,hd,rfl,hnot⟩
  · let t : Fin n := ⟨v,hinput⟩
    exact Or.inl ⟨t,reach_mem_orIn t hr,(val_ofFn C x t).symm.trans hw⟩
  · have hreach := reach_orReaches (hp.trans hr) d rfl hd
    have hand := (ao.1 _ (gateAt_mem hd)).resolve_right hnot
    exact Or.inr ⟨d,operandOrAndJunk ao top ha ho hreach hand,hr,hw⟩

lemma unique_earlier_junk_extra_raw_nonempty
    (hleast : IsLeastAO G C) (top : TopForm G C) {j m : ℕ}
    (hm : m∈orN G C \ lam G C) (hj : j<m)
    (hp : Relation.ReflTransGen (OrStep n C) (n+m) (n+j))
    (hunique : ∀ d∈junk G C, d<m → d=j) :
    (orIn n C (n+m)).Nonempty := by
  by_contra hn
  have hzero := Finset.not_nonempty_iff_eq_empty.mp hn
  obtain ⟨a,ha,ho,b,hpath⟩ := nonbelow_has_and_above hleast m (orData hm).1 (orData hm).2.2
  apply gate_ne_earlier_wire hleast (orData hm).1 (by omega : n+j<n+m)
  intro x
  have iffval : gateVal n C m x=true ↔ gateVal n C j x=true := by
    constructor
    · intro hx
      rcases wire_support_below_and hleast.1 top ha ho b hpath x hx with hraw | ⟨d,hd,hr,hdv⟩
      · obtain ⟨t,ht,_⟩ := hraw
        rw [hzero] at ht
        exact (Finset.notMem_empty _ ht).elim
      · have hle := orStep_le hr
        have hne : d≠m := by
          intro he
          have hAND := (junkData hd).2.1
          rw [he,(orData hm).2.1] at hAND
          contradiction
        have heq := hunique d hd (by omega)
        simpa only [heq] using hdv
    · intro hx
      exact orStep_up (n := n) (by simp) hp hx
  change gateVal n C j x=gateVal n C m x
  cases hmval : gateVal n C m x <;> cases hjval : gateVal n C j x <;> simp_all

end LeastWire

namespace ThreeExtraHelpers
open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma three_extra_middle_empty_shared_source_card_le_five
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (j k m0 m1 m2 : ℕ) (hpair : junk G C = {j,k})
    (hextra : orN G C \ lam G C = {m0,m1,m2}) (h0k : m0<k)
    (h0j : Relation.ReflTransGen (OrStep n C) (n+m0) (n+j))
    (hz1 : orIn n C (n+m1)=∅)
    (F S T : Finset (Finset (Fin n)))
    (hF : ∀ A∈F, Basic G C A) (hS : ∀ A∈S, Basic G C A) (hTT : ∀ A∈T, Basic G C A)
    (hlo : ∀ x, gateVal n C j x=true ↔ CNF F x)
    (hhi : ∀ x, gateVal n C k x=true ↔ CNF S x ∧ (gateVal n C j x=true ∨ CNF T x)) :
    (Ustar G C).card ≤ 5 := by
  classical
  have hFS : ∀ A∈F∪S, Basic G C A := fun A hA => (Finset.mem_union.mp hA).elim (hF A) (hS A)
  have hST : ∀ A∈S∪T, Basic G C A := fun A hA => (Finset.mem_union.mp hA).elim (hS A) (hTT A)
  have jointNF (x : Fin n → Bool) :
      (gateVal n C j x=true ∧ gateVal n C k x=true) ↔ CNF (F∪S) x := by
    rw [hhi x, SharedSource.cnf_union, ← hlo x]
    tauto
  let Joint := ∀ x, gateVal n C j x=true → gateVal n C k x=true → graphFun G ∅ x=true
  let D := if Joint then (Ustar G C).filter (EdgeCNF (F∪S)) else ∅
  let A := if Relation.ReflTransGen (OrStep n C) (n+m2) (n+j) then termEdges G C m2 F else ∅
  let B := if Relation.ReflTransGen (OrStep n C) (n+m2) (n+k) then
    termEdges G C m2 (F∪S) ∪ termEdges G C m2 (S∪T) else ∅
  have hD : D.card ≤ 1 := by
    by_cases hJ : Joint
    · simp only [D,if_pos hJ]
      apply OneCentreless.safe_cnf_subset_card_le_one hfour color hbip
        ((Ustar G C).filter (EdgeCNF (F∪S))) (Finset.filter_subset _ _) (F∪S) hFS
      · intro u v he
        exact (edgeCNF_pair_iff (F∪S) u v).mp (Finset.mem_filter.mp he).2
      · intro x hx
        have h := (jointNF x).mpr hx
        exact hJ x h.1 h.2
    · simp [D,hJ]
  have hA : A.card ≤ 1 := by
    by_cases hp : Relation.ReflTransGen (OrStep n C) (n+m2) (n+j)
    · simp only [A,if_pos hp]
      exact termEdges_card_le_one hleast.1 hfour color hbip m2 F hF
        (fun x hx => orStep_up (n := n) (by simp) hp ((hlo x).mpr hx))
    · simp [A,hp]
  have hB : B.card ≤ 2 := by
    by_cases hp : Relation.ReflTransGen (OrStep n C) (n+m2) (n+k)
    · simp only [B,if_pos hp]
      have hcST := termEdges_card_le_one hleast.1 hfour color hbip m2 (S∪T) hST
        (fun x hx => orStep_up (n := n) (by simp) hp ((hhi x).mpr
          ⟨((SharedSource.cnf_union S T x).mp hx).1,Or.inr ((SharedSource.cnf_union S T x).mp hx).2⟩))
      have hcFS := termEdges_card_le_one hleast.1 hfour color hbip m2 (F∪S) hFS
        (fun x hx => orStep_up (n := n) (by simp) hp ((jointNF x).mpr hx).2)
      have hu := Finset.card_union_le (termEdges G C m2 (F∪S)) (termEdges G C m2 (S∪T))
      omega
    · simp [B,hp]
  have hE0 : (termEdges G C m0 F).card ≤ 1 :=
    termEdges_card_le_one hleast.1 hfour color hbip m0 F hF
      (fun x hx => orStep_up (n := n) (by simp) h0j ((hlo x).mpr hx))
  have cover : Ustar G C ⊆ termEdges G C m0 F ∪ A ∪ B ∪ D := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rcases edge_positive_raw_boundary_or_joint hleast hT hempty j k hpair he with
        ⟨m,hm,d,hd,hval,hpath,hroute,c,hcin,hcz,hcj⟩ | ⟨hJoint,hboth⟩
      · have hdd : d=j ∨ d=k := by
          simpa only [hpair,Finset.mem_insert,Finset.mem_singleton] using hd
        have hmm : m=m0 ∨ m=m1 ∨ m=m2 := by
          simpa only [hextra,Finset.mem_insert,Finset.mem_singleton] using hm
        have hmne : m≠m1 := by
          intro heq
          have hn := hroute.1
          rw [heq,hz1] at hn
          exact Finset.not_nonempty_empty hn
        rcases hmm with heq | heq | heq
        · subst m
          have hdj : d=j := by
            rcases hdd with h | h
            · exact h
            · have hle := orStep_le hpath
              omega
          subst d
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (termEdges_mem.mpr ⟨he,hroute,(edgeCNF_pair_iff F u v).mpr ((hlo _).mp hval)⟩)))
        · exact (hmne heq).elim
        · subst m
          apply Finset.mem_union_left
          rcases hdd with hdj | hdk
          · subst d
            apply Finset.mem_union_left
            apply Finset.mem_union_right
            simp only [A,if_pos hpath]
            exact termEdges_mem.mpr ⟨he,hroute,(edgeCNF_pair_iff F u v).mpr ((hlo _).mp hval)⟩
          · subst d
            apply Finset.mem_union_right
            simp only [B,if_pos hpath]
            obtain ⟨hSx,hjx | hTx⟩ := (hhi _).mp hval
            · have hx := (SharedSource.cnf_union F S (pairInput u v)).mpr ⟨(hlo _).mp hjx,hSx⟩
              exact Finset.mem_union_left _ (termEdges_mem.mpr
                ⟨he,hroute,(edgeCNF_pair_iff (F∪S) u v).mpr hx⟩)
            · have hx := (SharedSource.cnf_union S T (pairInput u v)).mpr ⟨hSx,hTx⟩
              exact Finset.mem_union_right _ (termEdges_mem.mpr
                ⟨he,hroute,(edgeCNF_pair_iff (S∪T) u v).mpr hx⟩)
      · apply Finset.mem_union_right
        have hJ : Joint := hJoint
        simp only [D,if_pos hJ]
        refine Finset.mem_filter.mpr ⟨he,(edgeCNF_pair_iff (F∪S) u v).mpr ((jointNF _).mp ?_)⟩
        exact ⟨gate_accepts_pair_of_gammaE (Finset.mem_inter.mp hboth).1,
          gate_accepts_pair_of_gammaE (Finset.mem_inter.mp hboth).2⟩
  have hc := Finset.card_le_card cover
  have hu1 := Finset.card_union_le (termEdges G C m0 F) A
  have hu2 := Finset.card_union_le (termEdges G C m0 F∪A) B
  have hu3 := Finset.card_union_le (termEdges G C m0 F∪A∪B) D
  omega

end ThreeExtraHelpers

namespace ThreeExtraHelpers
open Budget ChainMixed PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma three_active_one_before_upper_middle_empty_card_le_five
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (j k m0 m1 m2 : ℕ) (hpair : junk G C = {j,k}) (hjk : j<k)
    (h01 : m0<m1) (h12 : m1<m2) (h0k : m0<k) (hk1 : k<m1)
    (hextra : orN G C \ lam G C = {m0,m1,m2})
    (hactive : ∀ m∈orN G C \ lam G C, ∃ d∈junk G C,
      Relation.ReflTransGen (OrStep n C) (n+m) (n+d))
    (hz1 : orIn n C (n+m1)=∅) :
    (Ustar G C).card ≤ 5 := by
  classical
  have hj : j∈junk G C := by simp [hpair]
  have hk : k∈junk G C := by simp [hpair]
  have hm0 : m0∈orN G C \ lam G C := by simp [hextra]
  have memR : ∀ m∈orN G C \ lam G C, m=m0 ∨ m=m1 ∨ m=m2 := by
    intro m hm
    simpa only [hextra,Finset.mem_insert,Finset.mem_singleton] using hm
  have first : ∀ m∈orN G C \ lam G C, m0≤m := by
    intro m hm
    rcases memR m hm with h | h | h <;> omega
  have onlyK : ∀ m∈orN G C \ lam G C, m<k → m=m0 := by
    intro m hm hmk
    rcases memR m hm with h | h | h <;> omega
  obtain ⟨d,hd,hp⟩ := hactive m0 hm0
  have hdj : d=j := by
    have hd' : d=j ∨ d=k := by simpa only [hpair,Finset.mem_insert,Finset.mem_singleton] using hd
    rcases hd' with h | h
    · exact h
    · have hle := orStep_le hp
      omega
  subst d
  have hj0 : j<m0 := by
    have hle := orStep_le hp
    have hne := RemainingOrder.junk_ne_extra hj hm0
    omega
  obtain ⟨F,hF,hlo⟩ := PrefixCNF.prefix_junk_basic_cnf hleast.1 hT (orData hm0).1.le first j hj0 hj
  have hraw : ∀ w<n+k, Basic G C (orIn n C w) :=
    fun w hw => raw_before_upper_basic hleast.1 hm0 first onlyK (junkData hk).1.le hj hp hw
  have hside (b : Fin 2) : Basic G C (side C k b) :=
    hraw _ (opndBound hleast.1 (junkData hk).1 b)
  obtain ⟨S,T,hS,hTT,hhi⟩ := upper_junk_shared_cnf_of_operand_shape hleast.1 hT hpair
    (Basic G C) hside (fun b _ => hside b)
  exact three_extra_middle_empty_shared_source_card_le_five hleast hT hfour color hbip hempty
    j k m0 m1 m2 hpair hextra h0k hp hz1 F S T hF hS hTT hlo hhi

end ThreeExtraHelpers

namespace ThreeExtraHelpers
open Budget PEqualNP.CleanedNonEdge
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma three_active_one_before_upper_card_le_five
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (j k m0 m1 m2 : ℕ) (hpair : junk G C = {j,k}) (hjk : j<k)
    (h01 : m0<m1) (h12 : m1<m2) (h0k : m0<k) (hk1 : k<m1)
    (hextra : orN G C \ lam G C = {m0,m1,m2})
    (hactive : ∀ m∈orN G C \ lam G C, ∃ d∈junk G C,
      Relation.ReflTransGen (OrStep n C) (n+m) (n+d)) :
    (Ustar G C).card ≤ 5 := by
  have hj : j∈junk G C := by simp [hpair]
  have hm0 : m0∈orN G C \ lam G C := by simp [hextra]
  have hm2 : m2∈orN G C \ lam G C := by simp [hextra]
  have memR : ∀ m∈orN G C \ lam G C, m=m0 ∨ m=m1 ∨ m=m2 := by
    intro m hm
    simpa only [hextra,Finset.mem_insert,Finset.mem_singleton] using hm
  have memJ : ∀ d∈junk G C, d=j ∨ d=k := by
    intro d hd
    simpa only [hpair,Finset.mem_insert,Finset.mem_singleton] using hd
  obtain ⟨d,hd,hp⟩ := hactive m0 hm0
  have hdj : d=j := by
    rcases memJ d hd with h | h
    · exact h
    · have hle := orStep_le hp
      omega
  subst d
  have hj0 : j<m0 := by
    have hle := orStep_le hp
    have hne := RemainingOrder.junk_ne_extra hj hm0
    omega
  have hraw0 := LeastWire.unique_earlier_junk_extra_raw_nonempty hleast hT hm0 hj0 hp (by
    intro d hd hdm
    rcases memJ d hd with h | h
    · exact h
    · omega)
  have hraw2 := LastExtra.last_extra_raw_nonempty hleast hempty hm2 (by
    intro r hr
    rcases memR r hr with h | h | h <;> omega)
  by_cases hraw1 : (orIn n C (n+m1)).Nonempty
  · have hall : ∀ m∈orN G C \ lam G C, (orIn n C (n+m)).Nonempty := by
      intro m hm
      rcases memR m hm with rfl | rfl | rfl
      · exact hraw0
      · exact hraw1
      · exact hraw2
    exact three_active_one_before_upper_all_raw_card_le_five hleast hT hfour color hbip hempty
      j k m0 m1 m2 hpair hjk h01 h12 h0k hk1 hextra hactive hall
  · exact three_active_one_before_upper_middle_empty_card_le_five hleast hT hfour color hbip hempty
      j k m0 m1 m2 hpair hjk h01 h12 h0k hk1 hextra hactive
      (Finset.not_nonempty_iff_eq_empty.mp hraw1)

lemma three_active_two_junk_card_le_five
    (hleast : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hempty : centreless G C = ∅)
    (j k m0 m1 m2 : ℕ) (hpair : junk G C = {j,k}) (hjk : j<k)
    (h01 : m0<m1) (h12 : m1<m2)
    (hextra : orN G C \ lam G C = {m0,m1,m2})
    (hactive : ∀ m∈orN G C \ lam G C, ∃ d∈junk G C,
      Relation.ReflTransGen (OrStep n C) (n+m) (n+d)) :
    (Ustar G C).card ≤ 5 := by
  by_contra hn
  have hU : 5≤(Ustar G C).card := by omega
  obtain ⟨hj0,h0k,hk1,hp,hreader⟩ := all_active_three_extra_large_residual_order
    hleast hT hfour color hbip hempty j k m0 m1 m2 hpair hjk h01 h12 hextra hactive hU
  have hc := three_active_one_before_upper_card_le_five hleast hT hfour color hbip hempty
    j k m0 m1 m2 hpair hjk h01 h12 h0k hk1 hextra hactive
  omega

end ThreeExtraHelpers

end PEqualNP.Outside.L_meta_2583_aux

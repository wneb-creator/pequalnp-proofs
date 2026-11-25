import PEqualNP.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace PEqualNP.Outside.L_meta_6240

namespace Local1490
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
lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
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
end Local1490

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Local1490
local instance : DecidableEq GateOp := gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
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
theorem orInOr (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.or) :
    orIn n C (n + m) = side C m 0 ∪ side C m 1 := by
  ext x
  constructor
  · intro hx
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach x hx) with he | ⟨z, hst, hrem⟩
    · have := x.isLt
      omega
    · obtain ⟨k, hk, he, _, hz, _⟩ := hst
      have e : k = m := by omega
      subst k
      obtain ⟨b, rfl⟩ := inputsAsOpnd hAO hm hz
      have hx' := reach_mem_orIn x hrem
      apply Finset.mem_union.mpr
      fin_cases b
      · exact Or.inl hx'
      · exact Or.inr hx'
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact orInTrans (Relation.ReflTransGen.single (orStepOpnd hAO hm hop 0)) hx
    · exact orInTrans (Relation.ReflTransGen.single (orStepOpnd hAO hm hop 1)) hx
theorem orInAnd {j : ℕ} (hop : (gateAt C j).op = GateOp.and) :
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
theorem reachTrans {w m j : ℕ}
    (hwm : OrReaches n C w m) (hmj : OrReaches n C (n + m) j) :
    OrReaches n C w j :=
  reach_orReaches ((orReaches_reach m _ hwm).1.trans (orReaches_reach j _ hmj).1) j rfl
    (orReaches_reach j _ hmj).2
theorem orNOfRaw {m : ℕ} (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hn : (orIn n C (n + m)).Nonempty) : m ∈ orN G C := by
  obtain ⟨t, ht⟩ := hn
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm, hop, ?_⟩
  intro hb
  have hv : gateVal n C m (pairInput t t) = true :=
    reach_var_val (pairInput t t) _ t (mem_orIn_reach t ht) (pairInput_left t t)
  exact G.irrefl ((graphFun_pair G t t).mp (hb _ hv))
theorem mixingNotLam {m : ℕ} (hm : m ∈ mixing G C) : m ∈ orN G C \ lam G C := by
  rcases Finset.mem_filter.mp hm with ⟨hm, hmix⟩
  refine Finset.mem_sdiff.mpr ⟨hm, ?_⟩
  intro hl
  rcases Finset.mem_filter.mp hl with ⟨_, h0, h1, _⟩
  apply hmix
  simp only [← Finset.not_nonempty_iff_eq_empty, h0, h1]
theorem mixingAlong (hAO : IsAO2 n C) {w j : ℕ} (hr : OrReaches n C w j)
    (hj : (gateAt C j).op = GateOp.and) (hw : (orIn n C w).Nonempty) :
    ∃ m ∈ mixing G C, OrReaches n C w m ∧ OrReaches n C (n + m) j ∧
      (orIn n C (n + m)).Nonempty := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    have hn : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    rcases (orReaches_iff n C k j).mp hr with ⟨hk, rfl | ⟨hop, z, hz, hzb, hr'⟩⟩
    · rw [orInAnd hj] at hw
      exact (Finset.not_nonempty_empty hw).elim
    · obtain ⟨b, rfl⟩ := inputsAsOpnd hAO hk hz
      by_cases hzb' : (side (n := n) C k b).Nonempty
      · obtain ⟨m, hm, hrm, hjm, hnon⟩ := ih _ hzb hr' hzb'
        exact ⟨m, hm, (orReaches_iff n C k m).mpr ⟨hk, Or.inr ⟨hop, _, hz, hzb, hrm⟩⟩,
          hjm, hnon⟩
      · have hempty : side (n := n) C k b = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hzb'
        have hboth : (side (n := n) C k 0 ∪ side (n := n) C k 1).Nonempty :=
          orInOr hAO hk hop ▸ hw
        have hm : k ∈ mixing G C := by
          refine Finset.mem_filter.mpr ⟨orNOfRaw hk hop hw, ?_⟩
          change (side (n := n) C k 0 = ∅) ≠ (side (n := n) C k 1 = ∅)
          fin_cases b
          · change side (n := n) C k 0 = ∅ at hempty
            have h1 : side (n := n) C k 1 ≠ ∅ := by
              rwa [hempty, Finset.empty_union, Finset.nonempty_iff_ne_empty] at hboth
            simp [hempty, h1]
          · change side (n := n) C k 1 = ∅ at hempty
            have h0 : side (n := n) C k 0 ≠ ∅ := by
              rwa [hempty, Finset.union_empty, Finset.nonempty_iff_ne_empty] at hboth
            simp [hempty, h0]
        exact ⟨k, hm, (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hr, hw⟩

theorem pairHitsTop (hL : IsLeastAO G C) {u v : Fin n} (he : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
    fun x => congrFun hL.2.1 x
  obtain ⟨a, ha, hano, path, hon⟩ :=
    edge_trace G (graphFun G ∅) (fun u v hx => (graphFun_pair G u v).mp hx)
      hout u v ((graphFun_pair G u v).mpr he)
  have hop := (hL.1.1 _ (gateAt_mem ha)).resolve_right hano
  refine ⟨a, ?_, hon⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha,hop,
    fun x hx => below_of_reach _ hout a path x hx⟩

theorem routedTopCross {a : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    {x y : Fin n} (hx : x ∈ side (n := n) C a b)
    (hy : y ∈ side (n := n) C a (1 - b)) :
    s(x, y) ∈ starEdges G C := by
  unfold starEdges
  refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ?_⟩
  fin_cases b
  · exact ⟨(x,y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  · exact ⟨(y,x), Finset.mem_product.mpr ⟨hy, hx⟩, Sym2.eq_swap⟩

theorem ustarReachesJunkVal {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n} (he : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true ∧
      ∃ (b : Fin 2), ∃ g ∈ junk G C, OrReaches n C (opnd C a b) g ∧
        gateVal n C g (pairInput u v) = true := by
  obtain ⟨hed, hns⟩ := Finset.mem_sdiff.mp he
  have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp hed
  obtain ⟨a, ha, hv⟩ := pairHitsTop hL hadj
  obtain ⟨hal, hao, hab⟩ := topData ha
  obtain ⟨hv0, hv1⟩ := (andValBoth hL.1 hal hao (pairInput u v)).mp hv
  rcases operand_trace u v (opnd C a 0) hv0 with ⟨t0, ht0, hr0⟩ | ⟨g, hgl, hgno, hr0, hvg0⟩
  · rcases operand_trace u v (opnd C a 1) hv1 with ⟨t1, ht1, hr1⟩ | ⟨g, hgl, hgno, hr1, hvg1⟩
    · exfalso
      have hs0 : t0 ∈ side (n := n) C a 0 := reach_mem_orIn t0 hr0
      have hs1 : t1 ∈ side (n := n) C a 1 := reach_mem_orIn t1 hr1
      have hcr : ∀ x ∈ side (n := n) C a 0, ∀ y ∈ side (n := n) C a 1, G.Adj x y := by
        intro x hx y hy
        apply (graphFun_pair G x y).mp
        apply hab
        apply (andValBoth hL.1 hal hao (pairInput x y)).mpr
        exact ⟨reach_var_val _ _ _ (mem_orIn_reach x hx) (pairInput_left x y),
          reach_var_val _ _ _ (mem_orIn_reach y hy) ((pairInput_true x y y).mpr (Or.inr rfl))⟩
      rcases ht0 with rfl | rfl <;> rcases ht1 with rfl | rfl
      · exact G.irrefl (hcr _ hs0 _ hs1)
      · exact hns (routedTopCross (b := 0) ha hs0 hs1)
      · have hst := routedTopCross (b := 0) ha hs0 hs1
        rw [Sym2.eq_swap] at hst
        exact hns hst
      · exact G.irrefl (hcr _ hs0 _ hs1)
    · have hgop : (gateAt C g).op = GateOp.and := (hL.1.1 _ (gateAt_mem hgl)).resolve_right hgno
      have hr : OrReaches n C (opnd C a 1) g := reach_orReaches hr1 g rfl hgl
      exact ⟨a, ha, hv, 1, g, operandOrAndJunk hL.1 hT hal hao hr hgop, hr, hvg1⟩
  · have hgop : (gateAt C g).op = GateOp.and := (hL.1.1 _ (gateAt_mem hgl)).resolve_right hgno
    have hr : OrReaches n C (opnd C a 0) g := reach_orReaches hr0 g rfl hgl
    exact ⟨a, ha, hv, 0, g, operandOrAndJunk hL.1 hT hal hao hr hgop, hr, hvg0⟩

theorem memGammaInterUstar {u v : Fin n} {g : ℕ} (he : s(u, v) ∈ Ustar G C)
    (hv : gateVal n C g (pairInput u v) = true) :
    s(u, v) ∈ gammaE G C g ∩ Ustar G C :=
  Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1, u, v, rfl, hv⟩, he⟩

theorem ustarCover {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C) {e : Sym2 (Fin n)} (he : e ∈ Ustar G C) :
    e ∈ (centreless G C).biUnion (fun h => gammaE G C h ∩ Ustar G C) ∨
      (e ∈ (junk G C).biUnion (fun h => gammaE G C h ∩ Ustar G C) ∧
       e ∈ (mixing G C).biUnion (fun h => gammaE G C h ∩ Ustar G C)) := by
  revert he
  refine Sym2.ind (fun u v he => ?_) e
  obtain ⟨a, ha, hva, b, g, hg, hr, hvg⟩ := ustarReachesJunkVal hL hT he
  by_cases hc : a ∈ centreless G C
  · exact Or.inl (Finset.mem_biUnion.mpr ⟨a, hc, memGammaInterUstar he hva⟩)
  · right
    have hb : (side (n := n) C a b).Nonempty := by
      by_contra h
      have h' := Finset.not_nonempty_iff_eq_empty.mp h
      apply hc
      apply Finset.mem_filter.mpr
      refine ⟨ha, ?_⟩
      fin_cases b
      · exact Or.inl h'
      · exact Or.inr h'
    obtain ⟨m, hm, _, hmg, _⟩ := mixingAlong (G := G) hL.1 hr (junkData hg).2.1 hb
    have hvm : gateVal n C m (pairInput u v) = true := reachVal hmg hvg
    exact ⟨Finset.mem_biUnion.mpr ⟨g, hg, memGammaInterUstar he hvg⟩,
           Finset.mem_biUnion.mpr ⟨m, hm, memGammaInterUstar he hvm⟩⟩

theorem cardBiUnionLeOne {α β : Type*} [DecidableEq α] (S : Finset β) (f : β → Finset α)
    (h1 : ∀ x ∈ S, (f x).card ≤ 1) :
    (S.biUnion f).card ≤ S.card := by
  calc (S.biUnion f).card ≤ ∑ x ∈ S, (f x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, 1 := Finset.sum_le_sum h1
    _ = S.card := by simp

theorem main : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∀ x7 ∈ PEqualNP.TopForm.centreless x2 x4 ∪ PEqualNP.TopForm.junk x2 x4 ∪ PEqualNP.TopForm.mixing x2 x4, (PEqualNP.TopForm.gammaE x2 x4 x7 ∩ PEqualNP.TopForm.Ustar x2 x4).card ≤ (1 : ℕ)) → (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x4).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  intro n G _ C hL hT hcap
  let Uc := (centreless G C).biUnion (fun h => gammaE G C h ∩ Ustar G C)
  let Uj := (junk G C).biUnion (fun h => gammaE G C h ∩ Ustar G C)
  let Um := (mixing G C).biUnion (fun h => gammaE G C h ∩ Ustar G C)
  have hsub_j : Ustar G C ⊆ Uc ∪ Uj := by
    intro e he
    rcases ustarCover hL hT he with hc | ⟨hj, _⟩
    · exact Finset.mem_union_left _ hc
    · exact Finset.mem_union_right _ hj
  have hsub_m : Ustar G C ⊆ Uc ∪ Um := by
    intro e he
    rcases ustarCover hL hT he with hc | ⟨_, hm⟩
    · exact Finset.mem_union_left _ hc
    · exact Finset.mem_union_right _ hm
  have h1 : (Ustar G C).card ≤ Uc.card + Uj.card :=
    (Finset.card_le_card hsub_j).trans (Finset.card_union_le Uc Uj)
  have h2 : (Ustar G C).card ≤ Uc.card + Um.card :=
    (Finset.card_le_card hsub_m).trans (Finset.card_union_le Uc Um)
  have hUc : Uc.card ≤ (centreless G C).card :=
    cardBiUnionLeOne _ _ (fun x hx => hcap x (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))
  have hUj : Uj.card ≤ (junk G C).card :=
    cardBiUnionLeOne _ _ (fun x hx => hcap x (Finset.mem_union_left _ (Finset.mem_union_right _ hx)))
  have hUm : Um.card ≤ (mixing G C).card :=
    cardBiUnionLeOne _ _ (fun x hx => hcap x (Finset.mem_union_right _ hx))
  have hmix : (mixing G C).card ≤ (orN G C \ lam G C).card :=
    Finset.card_le_card (fun _ hm => mixingNotLam hm)
  omega

end PEqualNP.Outside.L_meta_6240

theorem PEqualNP.Outside.L_meta_6240 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∀ x7 ∈ PEqualNP.TopForm.centreless x2 x4 ∪ PEqualNP.TopForm.junk x2 x4 ∪ PEqualNP.TopForm.mixing x2 x4, (PEqualNP.TopForm.gammaE x2 x4 x7 ∩ PEqualNP.TopForm.Ustar x2 x4).card ≤ (1 : ℕ)) → (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x4).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card :=
  PEqualNP.Outside.L_meta_6240.main

namespace PEqualNP.Outside.L_meta_650_aux.SingletonMixingMarker
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_6240 PEqualNP.Outside.L_meta_6240.Local1490
set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem singleton_marker {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (w j : ℕ) (q : Fin n)
    (raw : orIn n C w = {q}) (reach : OrReaches n C w j)
    (hop : (gateAt C j).op = GateOp.and) :
    ∃ m ∈ orN G C \ lam G C, OrReaches n C w m ∧ orIn n C (n + m) = {q} := by
  classical
  obtain ⟨m, hm, hwm, hmj, hnon⟩ := mixingAlong (G := G) hAO reach hop
    (by rw [raw]; exact Finset.singleton_nonempty q)
  have sub := orInTrans (orReaches_reach m w hwm).1
  have sub' : orIn n C (n + m) ⊆ {q} := by simpa [raw] using sub
  have equal : orIn n C (n + m) = {q} := by
    apply Finset.Subset.antisymm sub'
    obtain ⟨x, hx⟩ := hnon
    have hxq : x = q := Finset.mem_singleton.mp (sub' hx)
    intro y hy
    have hyq : y = q := Finset.mem_singleton.mp hy
    simpa [hxq, hyq] using hx
  exact ⟨m, mixingNotLam hm, hwm, equal⟩

theorem disjoint_wings_no_common_nonempty_marker {n : ℕ} {C : Circuit}
    (w z m : ℕ) (disjoint : Disjoint (orIn n C w) (orIn n C z))
    (wm : OrReaches n C w m) (zm : OrReaches n C z m)
    (nonempty : (orIn n C (n + m)).Nonempty) : False := by
  obtain ⟨q, hq⟩ := nonempty
  have hw := orInTrans (orReaches_reach m w wm).1 hq
  have hz := orInTrans (orReaches_reach m z zm).1 hq
  exact Finset.disjoint_left.mp disjoint hw hz

theorem singleton_wing_count {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (A : Finset (Fin n)) (wing : Fin n → ℕ)
    (raw : ∀ q ∈ A, orIn n C (wing q) = {q})
    (polluted : ∀ q ∈ A, ∃ j, OrReaches n C (wing q) j ∧ (gateAt C j).op = GateOp.and) :
    A.card ≤ (orN G C \ lam G C).card := by
  classical
  have markers : ∀ q ∈ A, ∃ m ∈ orN G C \ lam G C, orIn n C (n + m) = {q} := by
    intro q hq
    obtain ⟨j, hj, hop⟩ := polluted q hq
    obtain ⟨m, hm, hr, he⟩ := singleton_marker (G := G) hAO (wing q) j q (raw q hq) hj hop
    exact ⟨m, hm, he⟩
  let f : Fin n → ℕ := fun q => if hq : q ∈ A then Classical.choose (markers q hq) else 0
  have hf (q : Fin n) (hq : q ∈ A) :
      f q ∈ orN G C \ lam G C ∧ orIn n C (n + f q) = {q} := by
    simp only [f, dif_pos hq]
    exact Classical.choose_spec (markers q hq)
  apply Finset.card_le_card_of_injOn f (fun q hq => (hf q hq).1)
  intro a ha b hb heq
  have hh : ({a} : Finset (Fin n)) = {b} := by
    rw [← (hf a ha).2, ← (hf b hb).2, heq]
  simpa using hh

end PEqualNP.Outside.L_meta_650_aux.SingletonMixingMarker

namespace PEqualNP.Outside.L_meta_650_aux.SharedLineMarker
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_6240 PEqualNP.Outside.L_meta_6240.Local1490

 theorem shared_marker_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (noFour : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter (G.Adj a)) ∩ (Finset.univ.filter (G.Adj b))).card ≤ 1)
    (C : Circuit) (a b : Fin n) (different : a ≠ b) (w z m : ℕ)
    (left : orIn n C w ⊆ Finset.univ.filter (G.Adj a))
    (right : orIn n C z ⊆ Finset.univ.filter (G.Adj b))
    (wm : OrReaches n C w m) (zm : OrReaches n C z m) :
    (orIn n C (n + m)).card ≤ 1 := by
  have hw := orInTrans (orReaches_reach m w wm).1
  have hz := orInTrans (orReaches_reach m z zm).1
  have sub : orIn n C (n + m) ⊆
      (Finset.univ.filter (G.Adj a)) ∩ (Finset.univ.filter (G.Adj b)) := by
    intro q hq
    exact Finset.mem_inter.mpr ⟨left (hw hq), right (hz hq)⟩
  exact (Finset.card_le_card sub).trans (noFour a b different)

 theorem shared_nonempty_marker_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (noFour : ∀ a b : Fin n, a ≠ b →
      ((Finset.univ.filter (G.Adj a)) ∩ (Finset.univ.filter (G.Adj b))).card ≤ 1)
    (C : Circuit) (a b : Fin n) (different : a ≠ b) (w z m : ℕ)
    (left : orIn n C w ⊆ Finset.univ.filter (G.Adj a))
    (right : orIn n C z ⊆ Finset.univ.filter (G.Adj b))
    (wm : OrReaches n C w m) (zm : OrReaches n C z m)
    (nonempty : (orIn n C (n + m)).Nonempty) :
    ∃ q : Fin n, orIn n C (n + m) = {q} := by
  have upper := shared_marker_card G noFour C a b different w z m left right wm zm
  have lower := Finset.card_pos.mpr nonempty
  exact Finset.card_eq_one.mp (by omega)

end PEqualNP.Outside.L_meta_650_aux.SharedLineMarker

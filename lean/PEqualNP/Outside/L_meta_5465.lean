import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5465

-- FRAGMENT fold    DEPENDS: (none)
-- Wire list as a fold over the gate list. C.wires x = W C.gates x (rfl), C.eval x = (W C.gates x).getD C.output false.
-- Exports:
--   def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
--   def W (gs : List Gate) (w : List Bool) := gs.foldl step w
--   wires_W C x : C.wires x = W C.gates x
--   eval_W C x : C.eval x = (W C.gates x).getD C.output false
--   circuitFun_W n C x : circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false
--   W_nil, W_cons : W (g :: gs) w = W gs (step w g), W_single : W [g] w = step w g
--   W_append : W (a ++ b) w = W b (W a w),  W_snoc : W (gs ++ [g]) w = step (W gs w) g
--   W_split j : W gs w = W (gs.drop j) (W (gs.take j) w)
--   step_len : (step w g).length = w.length + 1,  W_length : (W gs w).length = w.length + gs.length
--   getD_app_lt (i < l.length) : (l ++ l2).getD i false = l.getD i false
--   getD_app_len : (l ++ [v]).getD l.length false = v
--   getD_ge (l.length <= i) : l.getD i false = false
--   step_lt (i < w.length) : (step w g).getD i false = w.getD i false
--   step_last (k = w.length) : (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false)
--   W_prefix (i < w.length) : (W gs w).getD i false = w.getD i false
--   W_ge (w.length + gs.length <= i) : (W gs w).getD i false = false
--   W_snoc_getD : (W (gs ++ [g]) w).getD t false = if t = w.length + gs.length then (eval of g on W gs w) else (W gs w).getD t false
--   W_gate (j < gs.length) : (W gs w).getD (w.length + j) false
--        = gs[j].op.eval (gs[j].inputs.map fun i => if i < w.length + j then (W gs w).getD i false else false)
--   W_gate_pre (gs = pre ++ g :: post) : (W gs w).getD (w.length + pre.length) false = g.op.eval (g.inputs.map fun i => (W pre w).getD i false)
--   ofFn_getD (u < n) : (List.ofFn x).getD u false = x u
--   ofFn_getD_ge (n <= u) : (List.ofFn x).getD u false = false
--   split_gates (j < gs.length) : exists pre post, gs = pre ++ gs[j] :: post and pre.length = j
--   split2 (gs[j]? = some g) : exists pre post, pre.length = j, gs = pre ++ g :: post, and for all g2, gs.set j g2 = pre ++ g2 :: post
--   step_congr : same gate value on P gives same step
--   gateAt_eq (j < C.gates.length) : gateAt C j = C.gates[j],  gateAt_mem : gateAt C j in C.gates
--   gateAt_ge (C.gates.length <= j) : gateAt C j = (OR of nothing)
--   getElem?_gateAt : C.gates[j]? = some g -> gateAt C j = g and j < C.gates.length
--   eval_and_iff : GateOp.and.eval (l.map f) = true iff all i in l, f i = true
--   eval_or_iff : GateOp.or.eval (l.map f) = true iff exists i in l, f i = true
--   eval_and2 / eval_or2 : GateOp.and.eval [a, b] = (a and b) / GateOp.or.eval [a, b] = (a or b);  eval_or1 / eval_and1 : one operand copies it
-- Use: rewrite C.wires/eval/circuitFun into W, split the gate list at the changed gate with split2,
-- then compare W post (step P g1) with W post (step P g2) (W_prefix for wires below, W_gate for gate wires).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl

-- FRAGMENT mono    DEPENDS: fold
-- Wire values val, gate-by-gate value equations, monotonicity of AND/OR circuits, Monotone2 / IsAO2 facts,
-- minimal true points.
-- Exports:
--   def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false     (val C x u = (W C.gates x).getD u false by rfl)
--   eval_eq_val : C.eval x = val C x C.output ;  circuitFun_val : circuitFun n C x = val C (List.ofFn x) C.output
--   val_input (hx : x.length = n) (hu : u < n) : val C x u = x.getD u false
--   val_ofFn (u : Fin n) : val C (List.ofFn x) u.val = x u ;  val_ofFn_lt (hu : u < n) : val C (List.ofFn x) u = x (u, hu)
--   val_ge (hx : x.length = n) (hu : n + C.gates.length <= u) : val C x u = false
--   val_gate (hx : x.length = n) (hj : j < C.gates.length) :
--       val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => if i < n + j then val C x i else false)
--   val_gate_rb : same, without the if, when every input i of gate j has i < n + j (ReadsBack)
--   val_or  (op = or)  : val C x (n + r) = true iff exists i in inputs, i < n + r and val C x i = true
--   val_and (op = and) : val C x (n + r) = true iff all i in inputs, i < n + r and val C x i = true
--   and_val (IsAO2, op = and) : val C x (n + j) = (val of input 0 && val of input 1)  (inputs.getD 0 0 / getD 1 0)
--   or_val  (IsAO2, op = or)  : val C x (n + j) = (val of input 0 || val of input 1)
--   def OpMono R : AND and OR are monotone for relation R on Bool ;  opMono_eq : OpMono Eq ;  opMono_imp : OpMono (a = true -> b = true)
--   andOrOnly_of_monotone2 : Monotone2 C -> AndOrOnly C ;  andOrOnly_of_isAO2 : IsAO2 n C -> AndOrOnly C
--   mono (AndOrOnly C) (x <= y pointwise) : for all w, val C (ofFn x) w = true -> val C (ofFn y) w = true
--   circuitFun_mono (AndOrOnly C) (x <= y) : circuitFun n C x = true -> circuitFun n C y = true
--   monotone2_len : Monotone2 C -> g in C.gates -> g.inputs.length <= 2 ;  isAO2_len : IsAO2 n C -> g in C.gates -> g.inputs.length = 2
--   isAO2_rb : IsAO2 n C -> j < C.gates.length -> i in (gateAt C j).inputs -> i < n + j
--   def tr y : Finset of true coordinates ;  tr_lt : z < y strictly -> (tr z).card < (tr y).card
--   exists_min F x (F x = true) : exists y <= x, F y = true and every z < y (z <= y, z ne y) has F z = false
-- Use: induction on the wire index w (Nat.strong_induction_on) with val_input / val_ge / val_gate to compare two runs.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

theorem opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

theorem opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

theorem val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
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

theorem val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
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

theorem andOrOnly_of_monotone2 {C : Circuit} (h : Monotone2 C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := by
  intro g hg
  have h1 := (h g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem andOrOnly_of_isAO2 {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := h.1

theorem monotone2_len {C : Circuit} (h : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length ≤ 2 := (h g hg).2

theorem isAO2_len {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length = 2 := h.2.2 g hg

theorem isAO2_rb {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) {i : ℕ} (hi : i ∈ (gateAt C j).inputs) : i < n + j :=
  h.2.1 j hj i hi

theorem mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

theorem circuitFun_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
    (h : circuitFun n C x = true) : circuitFun n C y = true :=
  mono n C hAO x y hxy C.output h

theorem and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) &&
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem or_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) ||
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

def tr {n : ℕ} (y : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => y i = true)

theorem tr_lt {n : ℕ} (z y : Fin n → Bool) (hzy : ∀ i, z i = true → y i = true) (hne : z ≠ y) :
    (tr z).card < (tr y).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hzy i hi
  · intro heq
    apply hne
    funext i
    have h : i ∈ tr z ↔ i ∈ tr y := by rw [heq]
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact Bool.eq_iff_iff.mpr h

theorem exists_min {n : ℕ} (F : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : F x = true) :
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ F y = true ∧
      ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y → F z = false := by
  let S : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun y => F y = true ∧ ∀ i, y i = true → x i = true)
  have hS : S.Nonempty := ⟨x, by simp [S, hx]⟩
  obtain ⟨y, hyS, hmin⟩ := Finset.exists_min_image S (fun y => (tr y).card) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hyS
  refine ⟨y, hyS.2, hyS.1, ?_⟩
  intro z hzy hne
  cases hz : F z
  · rfl
  · exfalso
    have hzS : z ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz, fun i hi => hyS.2 i (hzy i hi)⟩
    have h1 := hmin z hzS
    have h2 := tr_lt z y hzy hne
    omega

-- FRAGMENT table1a    DEPENDS: fold mono
-- Table 1a rows: RepSizeAtMost (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) s, upper and lower bounds.
-- Profiles: the profile of a wire is the 16-bit Nat whose bit k is its value at input t1_inp k = oneEach (k / 4) (k % 4).
-- Every gate of a Monotone2 circuit has profile a AND b or a OR b of earlier profiles or the constants 0 and 65535,
-- so a circuit of at most s gates gives a chain of s such steps from t1_base reaching the target T; t1_reach
-- (a Bool search, evaluated by decide +kernel) checks that no such chain exists.
-- Exports:
--   def t1_bits (f : Nat -> Bool) (m) : Nat  (bit k is f k for k < m) ;  t1_bits_testBit : testBit (t1_bits f m) i = (decide (i < m) and f i)
--   t1_bits_ext (agree below m) ;  t1_bits_and / t1_bits_or : t1_bits of pointwise and / or = land / lor ;  t1_bits_false : t1_bits (fun _ => false) m = 0
--   def t1_inp k : List Bool := oneEach (k / 4 % 4) (k % 4) ;  t1_inp_len : (t1_inp k).length = 8
--   def t1_prof C w := t1_bits (fun k => val C (t1_inp k) w) 16 ;  def t1_base : the 10 base profiles (0, 65535, 4 rows, 4 columns)
--   def t1_St C j : t1_base with the profiles of gate wires 8 .. 8 + j - 1 pushed in front ;  def t1_Step S p : exists a b in S, p = a land b or p = a lor b
--   t1_St_prof : i < 8 + j -> t1_prof C i in t1_St C j ;  t1_gate_step : one AND / OR gate of fan-in at most 2 is a t1_Step
--   def t1_mem, t1_pany (pairs a b with a before or equal b), t1_one T S (T is one step from S), t1_reach T S r (T within r steps)
--   t1_reach_step : a, b in S, p = a op b, t1_reach T (p :: S) r -> t1_reach T S (r + 1) ;  t1_chain : chains of steps are found by t1_reach
--   t1_lower M s T (hT : t1_bits (fun k => M.testBit k) 16 = T) (hc : t1_reach T t1_base s = false) : not RepSizeAtMost (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) s
--   def t1_okop ;  t1_mono2 (h : C.gates.all (fun g => t1_okop g.op and decide (g.inputs.length <= 2)) = true) : Monotone2 C
-- Use: exact t1_lower 1023 3 1023 (by decide +kernel) (by decide +kernel)   (SP/tools/table1a.py writes whole files).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def t1_bits (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => Nat.bit (f 0) (t1_bits (fun i => f (i + 1)) m)

theorem t1_bits_testBit (m : ℕ) : ∀ (f : ℕ → Bool) (i : ℕ),
    (t1_bits f m).testBit i = (decide (i < m) && f i) := by
  induction m with
  | zero => intro f i; simp [t1_bits]
  | succ m ih =>
    intro f i
    cases i with
    | zero => simp [t1_bits, Nat.testBit_bit_zero]
    | succ i =>
      have e : (t1_bits f (m + 1)).testBit (i + 1) = (t1_bits (fun i => f (i + 1)) m).testBit i :=
        Nat.testBit_bit_succ i _ _
      rw [e, ih]
      simp

theorem t1_bits_ext {f g : ℕ → Bool} {m : ℕ} (h : ∀ k, k < m → f k = g k) :
    t1_bits f m = t1_bits g m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [t1_bits_testBit, t1_bits_testBit]
  by_cases hi : i < m
  · rw [h i hi]
  · simp [hi]

theorem t1_bits_and (f g : ℕ → Bool) (m : ℕ) :
    t1_bits (fun i => f i && g i) m = t1_bits f m &&& t1_bits g m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_land, t1_bits_testBit]
  cases (decide (i < m)) <;> cases (f i) <;> cases (g i) <;> rfl

theorem t1_bits_or (f g : ℕ → Bool) (m : ℕ) :
    t1_bits (fun i => f i || g i) m = t1_bits f m ||| t1_bits g m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_lor, t1_bits_testBit]
  cases (decide (i < m)) <;> cases (f i) <;> cases (g i) <;> rfl

theorem t1_bits_false (m : ℕ) : t1_bits (fun _ => false) m = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [t1_bits_testBit]

theorem t1_bits_true16 : t1_bits (fun _ => true) 16 = 65535 := by decide

theorem t1_land_comm (a b : ℕ) : a &&& b = b &&& a := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_lor_comm (a b : ℕ) : a ||| b = b ||| a := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_land_absl (a b : ℕ) : a &&& (a &&& b) = a &&& b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_land_absr (a b : ℕ) : b &&& (a &&& b) = a &&& b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_lor_absl (a b : ℕ) : a ||| (a ||| b) = a ||| b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

theorem t1_lor_absr (a b : ℕ) : b ||| (a ||| b) = a ||| b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> rfl

def t1_inp (k : ℕ) : List Bool :=
  PEqualNP.Represents.oneEach (n := 4) (m := 4) ⟨k / 4 % 4, by omega⟩ ⟨k % 4, by omega⟩

theorem t1_inp_len (k : ℕ) : (t1_inp k).length = 8 := by
  simp [t1_inp, PEqualNP.Represents.oneEach]

def t1_prof (C : Circuit) (w : ℕ) : ℕ := t1_bits (fun k => val C (t1_inp k) w) 16

def t1_base : List ℕ := [0, 65535, 15, 240, 3840, 61440, 4369, 8738, 17476, 34952]

theorem t1_base_ok : ∀ u, u < 8 → t1_bits (fun k => (t1_inp k).getD u false) 16 ∈ t1_base := by
  decide +kernel

def t1_St (C : Circuit) : ℕ → List ℕ
  | 0 => t1_base
  | j + 1 => t1_prof C (8 + j) :: t1_St C j

def t1_Step (S : List ℕ) (p : ℕ) : Prop := ∃ a ∈ S, ∃ b ∈ S, p = a &&& b ∨ p = a ||| b

theorem t1_St_base (C : Circuit) {x : ℕ} (hx : x ∈ t1_base) (j : ℕ) : x ∈ t1_St C j := by
  induction j with
  | zero => exact hx
  | succ j ih => exact List.mem_cons_of_mem _ ih

theorem t1_St_prof (C : Circuit) (j : ℕ) : ∀ i, i < 8 + j → t1_prof C i ∈ t1_St C j := by
  induction j with
  | zero =>
    intro i hi
    have e : t1_prof C i = t1_bits (fun k => (t1_inp k).getD i false) 16 := by
      unfold t1_prof
      congr 1
      funext k
      exact val_input (t1_inp_len k) (by omega)
    rw [e]
    exact t1_base_ok i (by omega)
  | succ j ih =>
    intro i hi
    by_cases h : i < 8 + j
    · exact List.mem_cons_of_mem _ (ih i h)
    · have e : i = 8 + j := by omega
      subst e
      simp [t1_St]

theorem t1_gate_step (S : List ℕ) (R : ℕ → ℕ → Bool) (op : GateOp) (l : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : l.length ≤ 2)
    (hR : ∀ i ∈ l, t1_bits (fun k => R k i) 16 ∈ S) (h0 : 0 ∈ S) (h1 : 65535 ∈ S) :
    t1_Step S (t1_bits (fun k => op.eval (l.map (R k))) 16) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval (([] : List ℕ).map (R k))) = fun _ => true := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_true16]
      exact ⟨65535, h1, 65535, h1, Or.inl (by decide)⟩
    · have e : (fun k => GateOp.or.eval (([] : List ℕ).map (R k))) = fun _ => false := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_false]
      exact ⟨0, h0, 0, h0, Or.inr (by decide)⟩
  · have ha := hR a (by simp)
    rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval ([a].map (R k))) = fun k => R k a && true := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_and, t1_bits_true16]
      exact ⟨_, ha, 65535, h1, Or.inl rfl⟩
    · have e : (fun k => GateOp.or.eval ([a].map (R k))) = fun k => R k a || false := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_or, t1_bits_false]
      exact ⟨_, ha, 0, h0, Or.inr rfl⟩
  · have ha := hR a (by simp)
    have hb := hR b (by simp)
    rcases hop with rfl | rfl
    · have e : (fun k => GateOp.and.eval ([a, b].map (R k))) = fun k => R k a && R k b := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_and]
      exact ⟨_, ha, _, hb, Or.inl rfl⟩
    · have e : (fun k => GateOp.or.eval ([a, b].map (R k))) = fun k => R k a || R k b := by
        funext k; simp [GateOp.eval]
      rw [e, t1_bits_or]
      exact ⟨_, ha, _, hb, Or.inr rfl⟩
  · simp only [List.length_cons] at hl
    omega

def t1_mem (T : ℕ) : List ℕ → Bool
  | [] => false
  | a :: l => (a == T) || t1_mem T l

theorem t1_mem_of (T : ℕ) (l : List ℕ) (h : T ∈ l) : t1_mem T l = true := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.mp h with h | h
    · subst h; simp [t1_mem]
    · simp [t1_mem, ih h]

def t1_pany (f : ℕ → ℕ → Bool) : List ℕ → Bool
  | [] => false
  | a :: l => (a :: l).any (f a) || t1_pany f l

theorem t1_pany_of (f : ℕ → ℕ → Bool) (hsym : ∀ a b, f a b = f b a) (l : List ℕ) (a b : ℕ)
    (ha : a ∈ l) (hb : b ∈ l) (h : f a b = true) : t1_pany f l = true := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [t1_pany, Bool.or_eq_true, List.any_eq_true]
    rcases List.mem_cons.mp ha with ha' | ha'
    · subst ha'
      exact Or.inl ⟨b, hb, h⟩
    · rcases List.mem_cons.mp hb with hb' | hb'
      · subst hb'
        exact Or.inl ⟨a, List.mem_cons_of_mem _ ha', by rw [hsym]; exact h⟩
      · exact Or.inr (ih ha' hb')

def t1_one (T : ℕ) (S : List ℕ) : Bool :=
  t1_pany (fun a b => a ||| b == T) (S.filter (fun a => a ||| T == T)) ||
  t1_pany (fun a b => a &&& b == T) (S.filter (fun a => a &&& T == T))

def t1_reach (T : ℕ) : ℕ → List ℕ → Bool
  | 0, S => t1_mem T S
  | 1, S => t1_mem T S || t1_one T S
  | r + 2, S => t1_mem T S || t1_pany (fun a b =>
      t1_reach T (r + 1) ((a &&& b) :: S) || t1_reach T (r + 1) ((a ||| b) :: S)) S

theorem t1_reach_zero (T : ℕ) (S : List ℕ) : t1_reach T 0 S = t1_mem T S := rfl

theorem t1_reach_one (T : ℕ) (S : List ℕ) : t1_reach T 1 S = (t1_mem T S || t1_one T S) := rfl

theorem t1_reach_two (T r : ℕ) (S : List ℕ) : t1_reach T (r + 2) S = (t1_mem T S || t1_pany
    (fun a b => t1_reach T (r + 1) ((a &&& b) :: S) || t1_reach T (r + 1) ((a ||| b) :: S)) S) := rfl

theorem t1_reach_mem (T r : ℕ) (S : List ℕ) (h : T ∈ S) : t1_reach T r S = true := by
  rcases r with _ | _ | r
  · rw [t1_reach_zero]; exact t1_mem_of T S h
  · rw [t1_reach_one, t1_mem_of T S h]; rfl
  · rw [t1_reach_two, t1_mem_of T S h]; rfl

theorem t1_one_of (T : ℕ) (S : List ℕ) (a b : ℕ) (ha : a ∈ S) (hb : b ∈ S)
    (h : a &&& b = T ∨ a ||| b = T) : t1_one T S = true := by
  unfold t1_one
  rw [Bool.or_eq_true]
  rcases h with h | h
  · right
    have hsym : ∀ x y, (fun a b => a &&& b == T) x y = (fun a b => a &&& b == T) y x := by
      intro x y; show (x &&& y == T) = (y &&& x == T); rw [t1_land_comm]
    exact t1_pany_of _ hsym _ a b
      (List.mem_filter.mpr ⟨ha, by rw [← h, t1_land_absl]; exact beq_self_eq_true _⟩)
      (List.mem_filter.mpr ⟨hb, by rw [← h, t1_land_absr]; exact beq_self_eq_true _⟩)
      (by simp [h])
  · left
    have hsym : ∀ x y, (fun a b => a ||| b == T) x y = (fun a b => a ||| b == T) y x := by
      intro x y; show (x ||| y == T) = (y ||| x == T); rw [t1_lor_comm]
    exact t1_pany_of _ hsym _ a b
      (List.mem_filter.mpr ⟨ha, by rw [← h, t1_lor_absl]; exact beq_self_eq_true _⟩)
      (List.mem_filter.mpr ⟨hb, by rw [← h, t1_lor_absr]; exact beq_self_eq_true _⟩)
      (by simp [h])

theorem t1_reach_step (T r : ℕ) (S : List ℕ) (a b p : ℕ) (ha : a ∈ S) (hb : b ∈ S)
    (hp : p = a &&& b ∨ p = a ||| b) (h : t1_reach T r (p :: S) = true) :
    t1_reach T (r + 1) S = true := by
  rcases r with _ | r
  · rw [t1_reach_zero] at h
    simp only [t1_mem, Bool.or_eq_true, beq_iff_eq] at h
    show (t1_mem T S || t1_one T S) = true
    rw [Bool.or_eq_true]
    rcases h with h | h
    · right
      apply t1_one_of T S a b ha hb
      rcases hp with hp | hp
      · exact Or.inl (hp.symm.trans h)
      · exact Or.inr (hp.symm.trans h)
    · left; exact h
  · rw [t1_reach_two, Bool.or_eq_true]
    right
    have hsym : ∀ x y,
        (fun a b => t1_reach T (r + 1) ((a &&& b) :: S) || t1_reach T (r + 1) ((a ||| b) :: S)) x y =
        (fun a b => t1_reach T (r + 1) ((a &&& b) :: S) || t1_reach T (r + 1) ((a ||| b) :: S)) y x := by
      intro x y
      show (t1_reach T (r + 1) ((x &&& y) :: S) || t1_reach T (r + 1) ((x ||| y) :: S)) =
        (t1_reach T (r + 1) ((y &&& x) :: S) || t1_reach T (r + 1) ((y ||| x) :: S))
      rw [t1_land_comm x y, t1_lor_comm x y]
    refine t1_pany_of _ hsym S a b ha hb ?_
    rcases hp with hp | hp
    · subst hp; simp [h]
    · subst hp; simp [h]

theorem t1_chain (T : ℕ) (St : ℕ → List ℕ) (P : ℕ → ℕ) (len : ℕ)
    (hst : ∀ j, j < len → St (j + 1) = P j :: St j ∧ t1_Step (St j) (P j))
    (hT : T ∈ St len) : ∀ d j r, j + d = len → d ≤ r → t1_reach T r (St j) = true := by
  intro d
  induction d with
  | zero =>
    intro j r hj _
    have e : j = len := by omega
    subst e
    exact t1_reach_mem T r _ hT
  | succ d ih =>
    intro j r hj hr
    obtain ⟨hs, a, ha, b, hb, hp⟩ := hst j (by omega)
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have h := ih (j + 1) r' (by omega) (by omega)
    rw [hs] at h
    exact t1_reach_step T r' (St j) a b (P j) ha hb hp h

theorem t1_lower (M s T : ℕ) (hT : t1_bits (fun k => M.testBit k) 16 = T)
    (hc : t1_reach T s t1_base = false) :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => M.testBit (4 * u.val + v.val)) s := by
  rintro ⟨C, hm, hs, hr⟩
  have hlen : C.gates.length ≤ s := hs
  have h0 : (0 : ℕ) ∈ t1_base := by decide
  have h1 : (65535 : ℕ) ∈ t1_base := by decide
  have hstep : ∀ j, j < C.gates.length → t1_St C (j + 1) = t1_prof C (8 + j) :: t1_St C j ∧
      t1_Step (t1_St C j) (t1_prof C (8 + j)) := by
    intro j hj
    refine ⟨rfl, ?_⟩
    have hg := hm _ (gateAt_mem hj)
    have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by simpa using hg.1
    have e : t1_prof C (8 + j) = t1_bits (fun k => (gateAt C j).op.eval ((gateAt C j).inputs.map
        (fun i => if i < 8 + j then val C (t1_inp k) i else false))) 16 := by
      unfold t1_prof
      congr 1
      funext k
      exact val_gate (t1_inp_len k) hj
    rw [e]
    apply t1_gate_step _ (fun k i => if i < 8 + j then val C (t1_inp k) i else false) _ _ hop hg.2
    · intro i _
      by_cases hi : i < 8 + j
      · simp only [hi, ↓reduceIte]
        exact t1_St_prof C j i hi
      · simp only [hi, ↓reduceIte]
        rw [t1_bits_false]
        exact t1_St_base C h0 j
    · exact t1_St_base C h0 j
    · exact t1_St_base C h1 j
  have hout : t1_prof C C.output ∈ t1_St C C.gates.length := by
    by_cases ho : C.output < 8 + C.gates.length
    · exact t1_St_prof C _ _ ho
    · have e : (fun k => val C (t1_inp k) C.output) = fun _ => false :=
        funext fun k => val_ge (t1_inp_len k) (by omega)
      have e2 : t1_prof C C.output = 0 := by
        unfold t1_prof; rw [e, t1_bits_false]
      rw [e2]
      exact t1_St_base C h0 _
  have htarget : t1_prof C C.output = T := by
    rw [← hT]
    unfold t1_prof
    apply t1_bits_ext
    intro k hk
    have h : C.eval (t1_inp k) = M.testBit (4 * (k / 4 % 4) + k % 4) :=
      hr ⟨k / 4 % 4, by omega⟩ ⟨k % 4, by omega⟩
    have e : 4 * (k / 4 % 4) + k % 4 = k := by omega
    rw [e] at h
    exact h
  rw [htarget] at hout
  have hch := t1_chain T (t1_St C) (fun j => t1_prof C (8 + j)) C.gates.length hstep hout
    C.gates.length 0 s (by omega) hlen
  have h2 : t1_reach T s t1_base = true := hch
  rw [hc] at h2
  exact Bool.false_ne_true h2

def t1_okop : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => false
  | GateOp.mod _ => false
  | GateOp.maj => false

theorem t1_mono2 (C : Circuit)
    (h : C.gates.all (fun g => t1_okop g.op && decide (g.inputs.length ≤ 2)) = true) :
    Monotone2 C := by
  intro g hg
  have h2 := List.all_eq_true.mp h g hg
  rcases g with ⟨op, ins⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  refine ⟨?_, h2.2⟩
  have h3 := h2.1
  cases op <;> simp [t1_okop] at h3 ⊢

def t1w0 : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.or, [9, 10]⟩], 11⟩

theorem t1w0_rep : PEqualNP.Represents.Represents (fun u v : Fin 4 => (19 : ℕ).testBit (4 * u.val + v.val)) t1w0 := by
  decide

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (19 : ℕ).testBit (4 * u.val + v.val)) 4 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (19 : ℕ).testBit (4 * u.val + v.val)) 3 :=
  ⟨⟨t1w0, t1_mono2 t1w0 (by decide), by decide, t1w0_rep⟩, t1_lower 19 3 19 (by decide +kernel) (by decide +kernel)⟩

end PEqualNP.Outside.L_meta_5465

theorem PEqualNP.Outside.L_meta_5465 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (19 : ℕ).testBit (4 * u.val + v.val)) 4 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (19 : ℕ).testBit (4 * u.val + v.val)) 3 :=
  PEqualNP.Outside.L_meta_5465.main_aux

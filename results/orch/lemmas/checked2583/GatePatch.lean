import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.EdgeInvisible

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

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

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

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

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

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

theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

theorem orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
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

theorem orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

theorem orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

theorem orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

theorem reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : val C x (n + j) = true) :
    ∀ b : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C b j → val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩

def erase_rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem erase_redirect_lt (n m p i : ℕ) (h : i < n + m) : eraseRedirect n m p i = i := by
  unfold eraseRedirect
  rw [if_neg (by omega), if_neg (by omega)]

theorem erase_redirect_self (n m p : ℕ) : eraseRedirect n m p (n + m) = p := by
  unfold eraseRedirect
  rw [if_pos rfl]

theorem erase_redirect_gt (n m p i : ℕ) (h : n + m < i) : eraseRedirect n m p i = i - 1 := by
  unfold eraseRedirect
  rw [if_neg (by omega), if_pos h]

theorem erase_redirect_succ (n m p k : ℕ) (h : n + m ≤ k) : eraseRedirect n m p (k + 1) = k := by
  rw [erase_redirect_gt n m p (k + 1) (by omega), Nat.add_sub_cancel]

theorem erase_snoc_eq (a : List Bool) (v : Bool) (i : ℕ) (h : i = a.length) :
    (a ++ [v]).getD i false = v := by
  subst h
  exact getD_app_len a v

theorem erase_snoc_gt (a : List Bool) (v : Bool) (i : ℕ) (h : a.length < i) :
    (a ++ [v]).getD i false = false :=
  getD_ge _ _ (by rw [List.length_append, List.length_singleton]; omega)

theorem erase_step_rel (rel : Bool → Bool → Prop) (h00 : rel false false) (n m p : ℕ)
    (hp : p < n + m) (a b : List Bool) (va vb : Bool) (hl : a.length = b.length + 1)
    (hn : n + m < a.length)
    (h : ∀ i, rel (a.getD i false) (b.getD (eraseRedirect n m p i) false)) (hv : rel va vb) :
    ∀ i, rel ((a ++ [va]).getD i false) ((b ++ [vb]).getD (eraseRedirect n m p i) false) := by
  intro i
  by_cases hi : i < a.length
  · have hri : eraseRedirect n m p i < b.length := by
      unfold eraseRedirect
      split_ifs <;> omega
    rw [getD_app_lt a [va] i hi, getD_app_lt b [vb] _ hri]
    exact h i
  · rw [erase_redirect_gt n m p i (by omega)]
    by_cases hi2 : i = a.length
    · rw [erase_snoc_eq a va i hi2, erase_snoc_eq b vb (i - 1) (by omega)]
      exact hv
    · rw [erase_snoc_gt a va i (by omega), erase_snoc_gt b vb (i - 1) (by omega)]
      exact h00

theorem erase_W_rel (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (h00 : rel false false)
    (n m p : ℕ) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (gs : List Gate) : ∀ (a b : List Bool), (∀ g ∈ gs, Q g.op) →
      a.length = b.length + 1 → n + m < a.length →
      (∀ i, rel (a.getD i false) (b.getD (eraseRedirect n m p i) false)) →
      ∀ i, rel ((W gs a).getD i false)
        ((W (gs.map (erase_rg (eraseRedirect n m p))) b).getD (eraseRedirect n m p i) false) := by
  induction gs with
  | nil => intro a b _ _ _ h i; exact h i
  | cons g gs ih =>
    intro a b hg hl hn h i
    rw [List.map_cons, W_cons, W_cons]
    refine ih (step a g) (step b (erase_rg (eraseRedirect n m p) g)) ?_ ?_ ?_ ?_ i
    · intro g' hg'
      exact hg g' (List.mem_cons_of_mem _ hg')
    · rw [step_len, step_len, hl]
    · rw [step_len]
      omega
    · exact erase_step_rel rel h00 n m p hp a b
        (g.op.eval (g.inputs.map fun i => a.getD i false))
        (g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun i => b.getD i false))
        hl hn h
        (hop g.op g.inputs (fun i => a.getD i false) (fun i => b.getD i false)
          (hg g (by simp)) h)

theorem erase_sem (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (hrefl : ∀ b, rel b b)
    (n m p : ℕ) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (pre post : List Gate) (gm : Gate) (x : List Bool) (hx : x.length = n)
    (hpre : pre.length = m)
    (hpost : ∀ g ∈ post, Q g.op)
    (hbase : rel (gm.op.eval (gm.inputs.map fun i => (W pre x).getD i false))
      ((W pre x).getD p false)) :
    ∀ i, rel ((W (pre ++ gm :: post) x).getD i false)
      ((W (pre ++ post.map (erase_rg (eraseRedirect n m p))) x).getD
        (eraseRedirect n m p i) false) := by
  have hA : (W pre x).length = n + m := by rw [W_length, hx, hpre]
  rw [W_append, W_append, W_cons]
  refine erase_W_rel Q rel (hrefl false) n m p hp hop post (step (W pre x) gm) (W pre x)
    hpost ?_ ?_ ?_
  · exact step_len _ _
  · rw [step_len, hA]
    omega
  · intro i
    show rel ((W pre x ++ [gm.op.eval (gm.inputs.map fun i => (W pre x).getD i false)]).getD i
      false) ((W pre x).getD (eraseRedirect n m p i) false)
    by_cases hi : i < n + m
    · rw [erase_redirect_lt n m p i hi, getD_app_lt (W pre x) _ i (by omega)]
      exact hrefl _
    · by_cases hi2 : i = n + m
      · rw [hi2, erase_redirect_self n m p, erase_snoc_eq (W pre x) _ (n + m) hA.symm]
        exact hbase
      · rw [erase_redirect_gt n m p i (by omega), erase_snoc_gt (W pre x) _ i (by omega),
          getD_ge (W pre x) (i - 1) (by omega)]
        exact hrefl false

theorem erase_eq (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    eraseGate n C m p = Circuit.mk
      (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)))
      (eraseRedirect n m p C.output) := if_pos hm

theorem erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates
      = C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)) :=
  congrArg Circuit.gates (erase_eq n C m p hm)

theorem erase_output (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).output = eraseRedirect n m p C.output :=
  congrArg Circuit.output (erase_eq n C m p hm)

theorem erase_length (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length + 1 = C.gates.length := by
  rw [erase_gates n C m p hm, List.length_append, List.length_take, List.length_map,
    List.length_drop]
  omega

theorem erase_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).size + 1 = C.size := by
  show (eraseGate n C m p).gates.length + 1 = C.gates.length
  exact erase_length n C m p hm

theorem erase_getD (l : List Gate) (f : Gate → Gate) (d : Gate) (m j : ℕ) (hm : m < l.length)
    (hj : j + 1 < l.length) :
    (l.take m ++ (l.drop (m + 1)).map f).getD j d
      = if j < m then l.getD j d else f (l.getD (j + 1) d) := by
  have hlt : (l.take m).length = m := by
    rw [List.length_take]
    omega
  by_cases h : j < m
  · rw [if_pos h, List.getD_append _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem (l.take m) d (by omega), List.getD_eq_getElem l d (by omega),
      List.getElem_take]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega), hlt]
    have e : m + 1 + (j - m) = j + 1 := by omega
    rw [List.getD_eq_getElem (List.map f (l.drop (m + 1))) d
        (by rw [List.length_map, List.length_drop]; omega),
      List.getD_eq_getElem l d hj, List.getElem_map, List.getElem_drop]
    simp only [e]

theorem erase_gateAt (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hj : j + 1 < C.gates.length) :
    gateAt (eraseGate n C m p) j
      = if j < m then gateAt C j else erase_rg (eraseRedirect n m p) (gateAt C (j + 1)) := by
  have h0 : gateAt (eraseGate n C m p) j
      = (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))).getD j
        (Gate.mk GateOp.or []) :=
    congrArg (fun gs : List Gate => gs.getD j (Gate.mk GateOp.or [])) (erase_gates n C m p hm)
  rw [h0]
  exact erase_getD C.gates (erase_rg (eraseRedirect n m p)) (Gate.mk GateOp.or []) m j hm hj

theorem erase_gateAt_ge (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hj : m ≤ j) (hj1 : j + 1 < C.gates.length) :
    gateAt (eraseGate n C m p) j = erase_rg (eraseRedirect n m p) (gateAt C (j + 1)) := by
  rw [erase_gateAt n C m p j hm hj1, if_neg (Nat.not_lt.mpr hj)]

theorem erase_andOrOnly (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hA : PEqualNP.EdgeOwnership.AndOrOnly C) :
    PEqualNP.EdgeOwnership.AndOrOnly (eraseGate n C m p) := by
  intro g hg
  rw [erase_gates n C m p hm] at hg
  rcases List.mem_append.1 hg with h | h
  · exact hA g (List.mem_of_mem_take h)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
    exact hA g0 (List.mem_of_mem_drop hg0)

theorem erase_readsBack (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hp : p < n + m) (hR : ReadsBack n C) : ReadsBack n (eraseGate n C m p) := by
  have hElen := erase_length n C m p hm
  intro j hj i hi
  rw [erase_gateAt n C m p j hm (by omega)] at hi
  by_cases hjm : j < m
  · rw [if_pos hjm] at hi
    exact hR j (by omega) i hi
  · rw [if_neg hjm] at hi
    have hi' : i ∈ (gateAt C (j + 1)).inputs.map (eraseRedirect n m p) := hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi'
    have h2 := hR (j + 1) (by omega) i0 hi0
    unfold eraseRedirect
    split_ifs <;> omega

theorem erase_val_lt {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length)
    {x : List Bool} (hx : x.length = n) {i : ℕ} (hi : i < n + m) :
    val (eraseGate n C m p) x i = val C x i := by
  have hpre : (C.gates.take m).length = m := by
    rw [List.length_take]
    omega
  have hA : (W (C.gates.take m) x).length = n + m := by rw [W_length, hx, hpre]
  have e1 : val (eraseGate n C m p) x i
      = (W (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))) x).getD
        i false :=
    congrArg (fun gs : List Gate => (W gs x).getD i false) (erase_gates n C m p hm)
  have e2 : val C x i = (W (C.gates.take m ++ C.gates.drop m) x).getD i false :=
    congrArg (fun gs : List Gate => (W gs x).getD i false) (List.take_append_drop m C.gates).symm
  rw [e1, e2, W_append, W_append,
    W_prefix ((C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)))
      (W (C.gates.take m) x) i (by omega),
    W_prefix (C.gates.drop m) (W (C.gates.take m) x) i (by omega)]

theorem erase_val_rel (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (hrefl : ∀ b, rel b b)
    {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (hQ : ∀ g ∈ C.gates.drop (m + 1), Q g.op)
    {x : List Bool} (hx : x.length = n) (hv : rel (val C x (n + m)) (val C x p)) :
    ∀ i, rel (val C x i) (val (eraseGate n C m p) x (eraseRedirect n m p i)) := by
  have hsplit : C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1) = C.gates := by
    rw [gateAt_eq hm, ← List.drop_eq_getElem_cons hm, List.take_append_drop]
  have hpre : (C.gates.take m).length = m := by
    rw [List.length_take]
    omega
  have hA : (W (C.gates.take m) x).length = n + m := by rw [W_length, hx, hpre]
  have e1 : val C x (n + m) = (gateAt C m).op.eval
      ((gateAt C m).inputs.map fun i => (W (C.gates.take m) x).getD i false) := by
    have h1 := W_gate_pre C.gates (C.gates.take m) (C.gates.drop (m + 1)) (gateAt C m) x
      hsplit.symm
    rw [hx, hpre] at h1
    exact h1
  have e2 : val C x p = (W (C.gates.take m) x).getD p false := by
    show (W C.gates x).getD p false = _
    rw [W_split C.gates x m]
    exact W_prefix _ _ _ (by omega)
  rw [e1, e2] at hv
  have key := erase_sem Q rel hrefl n m p hp hop (C.gates.take m) (C.gates.drop (m + 1))
    (gateAt C m) x hx hpre hQ hv
  have hW : ∀ i, val C x i
      = (W (C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1)) x).getD i false :=
    fun i => congrArg (fun gs : List Gate => (W gs x).getD i false) hsplit.symm
  have hWD : ∀ i, val (eraseGate n C m p) x i
      = (W (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))) x).getD
        i false :=
    fun i => congrArg (fun gs : List Gate => (W gs x).getD i false) (erase_gates n C m p hm)
  intro i
  rw [hW i, hWD (eraseRedirect n m p i)]
  exact key i

theorem cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega

theorem cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
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
      have e2 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (PEqualNP.EdgeOwnership.coneStep n
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    PEqualNP.EdgeOwnership.InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ PEqualNP.EdgeOwnership.InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold PEqualNP.EdgeOwnership.InCone PEqualNP.EdgeOwnership.cones gateAt
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

theorem inCone_of_read (n : ℕ) (C : Circuit) (k j : ℕ) (hj : j < C.gates.length) (hk : k < j)
    (hin : n + k ∈ (gateAt C j).inputs) : PEqualNP.EdgeOwnership.InCone n C k j :=
  (inCone_iff n C k j).mpr ⟨hj, k, hk, hin, Or.inl rfl⟩

theorem inCone_trans (n : ℕ) (C : Circuit) (i k : ℕ) (hik : PEqualNP.EdgeOwnership.InCone n C i k) :
    ∀ j, PEqualNP.EdgeOwnership.InCone n C k j → PEqualNP.EdgeOwnership.InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k', hk', hin, h3⟩ := h
    rw [inCone_iff]
    refine ⟨h0, k', hk', hin, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hik
    · exact ih k' hk' h3

theorem p47_mem2 (l : List ℕ) (h : l.length = 2) (t : ℕ) (ht : t < 2) : l.getD t 0 ∈ l := by
  rw [List.getD_eq_getElem l 0 (by omega : t < l.length)]
  apply List.getElem_mem

theorem p47_map_getD (l : List ℕ) (r : ℕ → ℕ) (t : ℕ) (ht : t < l.length) :
    (l.map r).getD t 0 = r (l.getD t 0) := by
  have h2 : t < (l.map r).length := by rw [List.length_map]; exact ht
  rw [List.getD_eq_getElem (l.map r) 0 h2, List.getD_eq_getElem l 0 ht, List.getElem_map]

theorem p47_pair_val {n : ℕ} (C : Circuit) (u z : Fin n) (w : ℕ) (hw : w < n) :
    val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) w = decide (w = u.val ∨ w = z.val) := by
  rw [val_ofFn_lt C _ w hw]
  simp [PEqualNP.EdgeOwnership.pairInput, Fin.ext_iff]

theorem p47_unit_val {n : ℕ} (C : Circuit) (u : Fin n) (w : ℕ) (hw : w < n) :
    val C (List.ofFn (PEqualNP.SplitCount.unitInput u)) w = decide (w = u.val) := by
  rw [val_ofFn_lt C _ w hw]
  simp [PEqualNP.SplitCount.unitInput, Fin.ext_iff]

theorem p47_isAO2_erase (n : ℕ) (C : Circuit) (g v : ℕ) (hg : g < C.gates.length) (hv : v < n + g)
    (hAO : PEqualNP.TopForm.IsAO2 n C) : PEqualNP.TopForm.IsAO2 n (eraseGate n C g v) := by
  refine ⟨erase_andOrOnly n C g v hg hAO.1, erase_readsBack n C g v hg hv hAO.2.1, ?_⟩
  intro gt hgt
  rw [erase_gates n C g v hg] at hgt
  rcases List.mem_append.1 hgt with h | h
  · exact hAO.2.2 _ (List.mem_of_mem_take h)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
    show (g0.inputs.map _).length = 2
    rw [List.length_map]
    exact hAO.2.2 g0 (List.mem_of_mem_drop hg0)

theorem p47_rec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (u z : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hLF : PEqualNP.Core.IsLiftFixedPoint G C)
    (hcone : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k) :
    ∀ w : ℕ, (¬ ∀ x : Fin n → Bool, val C (List.ofFn x) w = true → graphFun G ∅ x = true) →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) w = true →
      val C (List.ofFn (PEqualNP.SplitCount.unitInput u)) w = true ∨
      val C (List.ofFn (PEqualNP.SplitCount.unitInput z)) w = true ∨
      PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  unfold PEqualNP.Core.IsLiftFixedPoint PEqualNP.Core.LiftApplies PEqualNP.Core.LiftAt
    PEqualNP.Core.IsImpWire at hLF
  unfold PEqualNP.TopForm.BelowF at hbelow
  have hx : ∀ y : Fin n → Bool, (List.ofFn y).length = n := fun y => by simp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hnb hv
    by_cases hwn : w < n
    · rw [p47_pair_val C u z w hwn, decide_eq_true_eq] at hv
      rcases hv with h | h
      · left
        rw [p47_unit_val C u w hwn, decide_eq_true_eq]
        exact h
      · right; left
        rw [p47_unit_val C z w hwn, decide_eq_true_eq]
        exact h
    · by_cases hwl : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
        rcases hAO.1 _ (gateAt_mem hj) with hop | hop
        · by_cases hjg : j = g
          · subst hjg
            exact Or.inr (Or.inr (orReaches_self n C j hj))
          · exact absurd (fun x hx' => hbelow j hj hop hjg x hx') hnb
        · have key : ∀ t : ℕ, t < 2 →
              val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z))
                ((gateAt C j).inputs.getD t 0) = true →
              val C (List.ofFn (PEqualNP.SplitCount.unitInput u)) (n + j) = true ∨
              val C (List.ofFn (PEqualNP.SplitCount.unitInput z)) (n + j) = true ∨
              PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g := by
            intro t ht hvt
            have hmem := p47_mem2 _ hlen t ht
            have hlt := isAO2_rb hAO hj hmem
            have hnbt : ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) ((gateAt C j).inputs.getD t 0) = true →
                graphFun G ∅ x = true := by
              intro hb
              apply hLF
              exact ⟨j, hj, ⟨t, ht⟩, hcone j hj, hop, fun hb2 => hnb (fun x hx' => hb2 x hx'), hb,
                PEqualNP.EdgeOwnership.pairInput u z, hvt⟩
            have hup : ∀ y : Fin n → Bool, val C (List.ofFn y) ((gateAt C j).inputs.getD t 0) = true →
                val C (List.ofFn y) (n + j) = true := by
              intro y hy
              rw [or_val n C hAO _ (hx y) j hj hop]
              rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
              · rw [hy, Bool.true_or]
              · rw [hy, Bool.or_true]
            rcases ih _ hlt hnbt hvt with h | h | h
            · exact Or.inl (hup _ h)
            · exact Or.inr (Or.inl (hup _ h))
            · exact Or.inr (Or.inr (orReaches_step n C j _ g hj hop hmem hlt h))
          rw [or_val n C hAO _ (hx _) j hj hop, Bool.or_eq_true] at hv
          rcases hv with h | h
          · exact key 0 (by omega) h
          · exact key 1 (by omega) h
      · rw [val_ge (C := C) (hx _) (by omega)] at hv
        exact absurd hv (by simp)

theorem p47_both {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g j : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k)
    (hgnb : ¬ PEqualNP.TopForm.BelowF G C g)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (h0 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 0 0) g)
    (h1 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 1 0) g) : False := by
  unfold PEqualNP.TopForm.BelowF at hbelow hgnb
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  have hjg : j ≠ g := by
    intro hjg
    subst hjg
    have b1 := (orReaches_bound n C j _ h0).1
    have b2 := isAO2_rb hAO hj (p47_mem2 _ hlen 0 (by omega))
    omega
  apply hgnb
  intro x hx
  apply hbelow j hj hop hjg x
  show val C (List.ofFn x) (n + j) = true
  have hx' : val C (List.ofFn x) (n + g) = true := hx
  rw [and_val n C hAO _ (by simp) j hj hop, reach_up n C _ (by simp) g hx' _ h0,
    reach_up n C _ (by simp) g hx' _ h1]
  rfl

def p40cf (C : Circuit) (g : ℕ) : Circuit := ⟨C.gates.set g ⟨GateOp.or, []⟩, C.output⟩

theorem p40_len (C : Circuit) (g : ℕ) : (p40cf C g).gates.length = C.gates.length := by
  simp [p40cf]

theorem p40_gateAt (C : Circuit) (g j : ℕ) (h : g ≠ j) : gateAt (p40cf C g) j = gateAt C j := by
  simp [p40cf, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set, h]

theorem p40_gateAt_self (C : Circuit) (g : ℕ) (hg : g < C.gates.length) :
    gateAt (p40cf C g) g = ⟨GateOp.or, []⟩ := by
  simp [p40cf, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set, hg]

theorem p40_aoo (C : Circuit) (g : ℕ) (hA : PEqualNP.EdgeOwnership.AndOrOnly C) :
    PEqualNP.EdgeOwnership.AndOrOnly (p40cf C g) := by
  intro gt hgt
  rcases List.mem_or_eq_of_mem_set hgt with h | h
  · exact hA gt h
  · rw [h]; exact Or.inr rfl

theorem p40_self {n : ℕ} (C : Circuit) (g : ℕ) (hg : g < C.gates.length) (x : List Bool)
    (hx : x.length = n) : val (p40cf C g) x (n + g) = false := by
  rw [val_gate (C := p40cf C g) hx (by rw [p40_len]; exact hg), p40_gateAt_self C g hg]
  rfl

theorem p40_and {n : ℕ} (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) (hjg : j ≠ g)
    (hop : (gateAt C j).op = GateOp.and) :
    val (p40cf C g) x (n + j) = (val (p40cf C g) x ((gateAt C j).inputs.getD 0 0) &&
      val (p40cf C g) x ((gateAt C j).inputs.getD 1 0)) := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hAO.2.1 j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate (C := p40cf C g) hx (by rw [p40_len]; exact hj), p40_gateAt C g j (Ne.symm hjg), hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem p40_or {n : ℕ} (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) (hjg : j ≠ g)
    (hop : (gateAt C j).op = GateOp.or) :
    val (p40cf C g) x (n + j) = (val (p40cf C g) x ((gateAt C j).inputs.getD 0 0) ||
      val (p40cf C g) x ((gateAt C j).inputs.getD 1 0)) := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hAO.2.1 j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate (C := p40cf C g) hx (by rw [p40_len]; exact hj), p40_gateAt C g j (Ne.symm hjg), hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem p40_le {n : ℕ} (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hg : g < C.gates.length) (x : List Bool) (hx : x.length = n) :
    ∀ i, val (p40cf C g) x i = true → val C x i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    by_cases h1 : i < n
    · rw [val_input (C := p40cf C g) hx h1] at h
      rw [val_input (C := C) hx h1]
      exact h
    by_cases h2 : i < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases hjg : j = g
      · subst hjg
        rw [p40_self C j hg x hx] at h
        exact absurd h (by simp)
      have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
      have l0 := isAO2_rb hAO hj (p47_mem2 _ hlen 0 (by omega))
      have l1 := isAO2_rb hAO hj (p47_mem2 _ hlen 1 (by omega))
      rcases hAO.1 _ (gateAt_mem hj) with hop | hop
      · rw [p40_and C g hAO x hx j hj hjg hop, Bool.and_eq_true] at h
        rw [and_val n C hAO x hx j hj hop, Bool.and_eq_true]
        exact ⟨ih _ l0 h.1, ih _ l1 h.2⟩
      · rw [p40_or C g hAO x hx j hj hjg hop, Bool.or_eq_true] at h
        rw [or_val n C hAO x hx j hj hop, Bool.or_eq_true]
        rcases h with h | h
        · exact Or.inl (ih _ l0 h)
        · exact Or.inr (ih _ l1 h)
    · rw [val_ge (C := p40cf C g) hx (by rw [p40_len]; omega)] at h
      exact absurd h (by simp)

theorem p40_eq_all {n : ℕ} (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hg : g < C.gates.length) (x : List Bool) (hx : x.length = n)
    (hge : val C x (n + g) = false) :
    ∀ i, val (p40cf C g) x i = val C x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n
    · rw [val_input (C := p40cf C g) hx h1, val_input (C := C) hx h1]
    by_cases h2 : i < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases hjg : j = g
      · subst hjg
        rw [p40_self C j hg x hx, hge]
      have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
      have l0 := isAO2_rb hAO hj (p47_mem2 _ hlen 0 (by omega))
      have l1 := isAO2_rb hAO hj (p47_mem2 _ hlen 1 (by omega))
      rcases hAO.1 _ (gateAt_mem hj) with hop | hop
      · rw [p40_and C g hAO x hx j hj hjg hop, and_val n C hAO x hx j hj hop, ih _ l0, ih _ l1]
      · rw [p40_or C g hAO x hx j hj hjg hop, or_val n C hAO x hx j hj hop, ih _ l0, ih _ l1]
    · rw [val_ge (C := p40cf C g) hx (by rw [p40_len]; omega), val_ge (C := C) hx (by omega)]

theorem p40_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (u z : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hLF : PEqualNP.Core.IsLiftFixedPoint G C)
    (hcone : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k)
    (hadj : G.Adj u z)
    (hge : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = true)
    (d : ℕ) (hdnb : ¬ ∀ x : Fin n → Bool, val C (List.ofFn x) d = true → graphFun G ∅ x = true)
    (hdg : ¬ PEqualNP.CleanedNonEdge.OrReaches n C d g)
    (hk : ∀ a b : Fin n, G.Adj a b → val C (List.ofFn (PEqualNP.SplitCount.unitInput b)) d = true →
      PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput a b) = false) :
    val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) d = false := by
  have hsw : PEqualNP.EdgeOwnership.pairInput z u = PEqualNP.EdgeOwnership.pairInput u z := by
    funext w
    simp [PEqualNP.EdgeOwnership.pairInput, or_comm]
  cases hd : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) d
  · rfl
  exfalso
  rcases p47_rec G C g u z hAO hLF hcone hbelow d hdnb hd with h | h | h
  · have h2 := hk z u hadj.symm h
    rw [hsw] at h2
    have h3 : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = false := h2
    rw [hge] at h3
    exact absurd h3 (by simp)
  · have h2 := hk u z hadj h
    have h3 : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = false := h2
    rw [hge] at h3
    exact absurd h3 (by simp)
  · exact hdg h

theorem p40_eq_reach {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (u z : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hLF : PEqualNP.Core.IsLiftFixedPoint G C)
    (hcone : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k)
    (hbelow : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g →
      PEqualNP.TopForm.BelowF G C k)
    (hg : g < C.gates.length)
    (hNB : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ t ∈ (gateAt C k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → graphFun G ∅ x = true))
    (hgnb : ¬ PEqualNP.TopForm.BelowF G C g)
    (hkey : ∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u z : Fin n, G.Adj u z → (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u z) = false)
    (hadj : G.Adj u z)
    (hge : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = true) :
    ∀ i, ¬ PEqualNP.CleanedNonEdge.OrReaches n C i g →
      val (p40cf C g) (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) i =
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) i := by
  have hx : (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)).length = n := by simp
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · rw [val_input (C := p40cf C g) hx h1, val_input (C := C) hx h1]
    by_cases h2 : i < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases hjg : j = g
      · subst hjg
        exact absurd (orReaches_self n C j hj) hi
      have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
      have m0 := p47_mem2 _ hlen 0 (by omega)
      have m1 := p47_mem2 _ hlen 1 (by omega)
      have l0 := isAO2_rb hAO hj m0
      have l1 := isAO2_rb hAO hj m1
      rcases hAO.1 _ (gateAt_mem hj) with hop | hop
      · rw [p40_and C g hAO _ hx j hj hjg hop, and_val n C hAO _ hx j hj hop]
        by_cases r0 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 0 0) g
        · by_cases r1 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 1 0) g
          · exact (p47_both G C g j hAO hbelow hgnb hj hop r0 r1).elim
          · have hf := p40_other G C g u z hAO hLF hcone hbelow hadj hge
              ((gateAt C j).inputs.getD 1 0) (hNB j hj hop _ m1) r1
              (fun a b hab hb => hkey j hj hop a b hab (Or.inl ⟨r0, hb⟩))
            rw [ih _ l1 r1, hf]
            simp
        · by_cases r1 : PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 1 0) g
          · have hf := p40_other G C g u z hAO hLF hcone hbelow hadj hge
              ((gateAt C j).inputs.getD 0 0) (hNB j hj hop _ m0) r0
              (fun a b hab hb => hkey j hj hop a b hab (Or.inr ⟨r1, hb⟩))
            rw [ih _ l0 r0, hf]
            simp
          · rw [ih _ l0 r0, ih _ l1 r1]
      · rw [p40_or C g hAO _ hx j hj hjg hop, or_val n C hAO _ hx j hj hop]
        have r0 : ¬ PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 0 0) g :=
          fun h => hi (orReaches_step n C j _ g hj hop m0 l0 h)
        have r1 : ¬ PEqualNP.CleanedNonEdge.OrReaches n C ((gateAt C j).inputs.getD 1 0) g :=
          fun h => hi (orReaches_step n C j _ g hj hop m1 l1 h)
        rw [ih _ l0 r0, ih _ l1 r1]
    · rw [val_ge (C := p40cf C g) hx (by rw [p40_len]; omega), val_ge (C := C) hx (by omega)]

theorem p40_reader (n : ℕ) (C : Circuit) (h : ℕ) :
    ∀ o, PEqualNP.EdgeOwnership.InCone n C h o → ∃ k, n + h ∈ (gateAt C k).inputs ∧
      k < C.gates.length ∧ (k = o ∨ PEqualNP.EdgeOwnership.InCone n C k o) := by
  intro o
  induction o using Nat.strong_induction_on with
  | _ o ih =>
    intro hc
    obtain ⟨hj, k, hko, hmem, h1 | h1⟩ := (inCone_iff n C h o).1 hc
    · subst h1
      exact ⟨o, hmem, hj, Or.inl rfl⟩
    · obtain ⟨k', hm', hk', h2 | h2⟩ := ih k hko h1
      · subst h2
        exact ⟨k', hm', hk', Or.inr (inCone_of_read n C k' o hj hko hmem)⟩
      · exact ⟨k', hm', hk', Or.inr (inCone_trans n C k' k h2 o (inCone_of_read n C k o hj hko hmem))⟩

theorem p40_pos (l : List ℕ) (hl : l.length = 2) (w : ℕ) (hw : w ∈ l) : ∃ t, t < 2 ∧ l.getD t 0 = w := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ⟨0, by omega, rfl⟩
  · exact ⟨1, by omega, rfl⟩

theorem p40_find {n : ℕ} (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C) :
    ∀ m h, C.gates.length - h = m → PEqualNP.Core.InOutputCone n C h → g ≤ h →
      (∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) (n + h) = false) →
      (∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) C.output = false) ∨
      ∃ r, r < C.gates.length ∧ g < r ∧ (gateAt C r).op = GateOp.or ∧ ∃ t, t < 2 ∧
        ∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) ((gateAt C r).inputs.getD t 0) = false := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h hm hoc hgh hz
    obtain ⟨hh, ho | ⟨hno, hc⟩⟩ := hoc
    · left
      intro x
      rw [ho]
      exact hz x
    · obtain ⟨k, hmem, hk, hko⟩ := p40_reader n C h _ hc
      have hlt := isAO2_rb hAO hk hmem
      have hlen : (gateAt C k).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hk)
      obtain ⟨t, ht, hpos⟩ := p40_pos _ hlen _ hmem
      have hkoc : PEqualNP.Core.InOutputCone n C k := by
        show k < C.gates.length ∧ (C.output = n + k ∨
          (n ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone n C k (C.output - n)))
        refine ⟨hk, ?_⟩
        rcases hko with e | e
        · left; omega
        · right; exact ⟨hno, e⟩
      rcases hAO.1 _ (gateAt_mem hk) with hop | hop
      · have hkg : k ≠ g := by omega
        have hzk : ∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) (n + k) = false := by
          intro x
          rw [p40_and C g hAO _ (by simp) k hk hkg hop]
          rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
          · rw [hpos, hz x]; rfl
          · rw [hpos, hz x]; simp
        exact ih (C.gates.length - k) (by omega) k rfl hkoc (by omega) hzk
      · right
        refine ⟨k, hk, by omega, hop, t, ht, ?_⟩
        intro x
        rw [hpos]
        exact hz x

theorem p40_ge {n : ℕ} (C : Circuit) (g r y : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hg : g < C.gates.length) (hr : r < C.gates.length) (hgr : g < r) (hy : y < n + r)
    (x : List Bool) (hx : x.length = n)
    (hry : val (p40cf C g) x (n + r) = val (p40cf C g) x y) :
    ∀ i, val (p40cf C g) x i = true →
      val (eraseGate n C r y) x (eraseRedirect n r y i) = true := by
  have hAOE : PEqualNP.TopForm.IsAO2 n (eraseGate n C r y) := p47_isAO2_erase n C r y hr hy hAO
  have hElen := erase_length n C r y hr
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    by_cases h1 : i < n + r
    · rw [erase_redirect_lt n r y i h1, erase_val_lt hr hx h1]
      exact p40_le C g hAO hg x hx i h
    by_cases h2 : i = n + r
    · subst h2
      rw [erase_redirect_self, erase_val_lt hr hx hy]
      rw [hry] at h
      exact p40_le C g hAO hg x hx y h
    by_cases h3 : i < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j + 1 := ⟨i - n - 1, by omega⟩
      have hj1 : j + 1 < C.gates.length := by omega
      have hrj : r ≤ j := by omega
      rw [erase_redirect_succ n r y (n + j) (by omega)]
      have hjE : j < (eraseGate n C r y).gates.length := by omega
      have hgE : gateAt (eraseGate n C r y) j = erase_rg (eraseRedirect n r y) (gateAt C (j + 1)) :=
        erase_gateAt_ge n C r y j hr hrj hj1
      have hlen : (gateAt C (j + 1)).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj1)
      have e0 : (gateAt (eraseGate n C r y) j).inputs.getD 0 0 =
          eraseRedirect n r y ((gateAt C (j + 1)).inputs.getD 0 0) := by
        rw [hgE]; exact p47_map_getD _ _ 0 (by omega)
      have e1 : (gateAt (eraseGate n C r y) j).inputs.getD 1 0 =
          eraseRedirect n r y ((gateAt C (j + 1)).inputs.getD 1 0) := by
        rw [hgE]; exact p47_map_getD _ _ 1 (by omega)
      have eop : (gateAt (eraseGate n C r y) j).op = (gateAt C (j + 1)).op := by rw [hgE]; rfl
      have l0 := isAO2_rb hAO hj1 (p47_mem2 _ hlen 0 (by omega))
      have l1 := isAO2_rb hAO hj1 (p47_mem2 _ hlen 1 (by omega))
      have hjg : j + 1 ≠ g := by omega
      have hCi : n + j + 1 = n + (j + 1) := by omega
      rw [hCi] at h
      rcases hAO.1 _ (gateAt_mem hj1) with hop | hop
      · rw [p40_and C g hAO x hx (j + 1) hj1 hjg hop, Bool.and_eq_true] at h
        rw [and_val n _ hAOE x hx j hjE (by rw [eop]; exact hop), e0, e1, Bool.and_eq_true]
        exact ⟨ih _ (by omega) h.1, ih _ (by omega) h.2⟩
      · rw [p40_or C g hAO x hx (j + 1) hj1 hjg hop, Bool.or_eq_true] at h
        rw [or_val n _ hAOE x hx j hjE (by rw [eop]; exact hop), e0, e1, Bool.or_eq_true]
        rcases h with h | h
        · exact Or.inl (ih _ (by omega) h)
        · exact Or.inr (ih _ (by omega) h)
    · rw [val_ge (C := p40cf C g) hx (by rw [p40_len]; omega)] at h
      exact absurd h (by simp)

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ w : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput w) = false) → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u z : Fin n, G.Adj u z → (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u z) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C s g hbip h4c hAO hF hLF hNB hcone hg hgop hgnb hbelow hunit0 hkey
  have hxl : ∀ y : Fin n → Bool, (List.ofFn y).length = n := fun y => by simp
  have hout : ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output g := by
    intro hr
    apply hgnb
    unfold PEqualNP.TopForm.BelowF
    intro y hy
    rw [← hF]
    exact reach_up n C _ (by simp) g hy _ hr
  have hCf : ∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      rw [← hF]
      exact p40_le C g hAO hg _ (hxl x) _ h
    · intro h
      have h' : ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true := by
        unfold graphFun at h
        simpa using h
      obtain ⟨u, z, hadj, hxu, hxz⟩ := h'
      have hle : ∀ i : Fin n, PEqualNP.EdgeOwnership.pairInput u z i = true → x i = true := by
        intro i hi
        simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
        rcases hi with hi | hi
        · rw [hi]; exact hxu
        · rw [hi]; exact hxz
      refine mono n (p40cf C g) (p40_aoo C g hAO.1) (PEqualNP.EdgeOwnership.pairInput u z) x hle
        C.output ?_
      have hCe : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) C.output = true := by
        show circuitFun n C (PEqualNP.EdgeOwnership.pairInput u z) = true
        rw [hF]
        unfold graphFun
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        right
        exact ⟨u, z, hadj, by simp [PEqualNP.EdgeOwnership.pairInput],
          by simp [PEqualNP.EdgeOwnership.pairInput]⟩
      cases hge : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g)
      · rw [p40_eq_all C g hAO hg _ (hxl _) hge]
        exact hCe
      · rw [p40_eq_reach G C g u z hAO hLF hcone hbelow hg hNB hgnb hkey hadj hge C.output hout]
        exact hCe
  rcases p40_find C g hAO _ g rfl (hcone g hg) (le_refl g)
      (fun x => p40_self C g hg _ (hxl x)) with hz | ⟨r, hr, hgr, hrop, t, ht, hw⟩
  · refine ⟨⟨[], n⟩, ⟨fun gt h => by simp at h, fun j hj => by simp at hj, fun gt h => by simp at h⟩,
      by show 0 < C.gates.length; omega, ?_⟩
    funext x
    rw [← hCf x, hz x]
    show val (⟨[], n⟩ : Circuit) (List.ofFn x) n = false
    exact val_ge (hxl x) (by simp)
  · have hlen : (gateAt C r).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hr)
    have hgr' : r ≠ g := by omega
    obtain ⟨y, hy, hry, hyC⟩ : ∃ y, y < n + r ∧
        (∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) (n + r) = val (p40cf C g) (List.ofFn x) y) ∧
        (∀ x : Fin n → Bool, val C (List.ofFn x) y = true → val C (List.ofFn x) (n + r) = true) := by
      rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
      · refine ⟨(gateAt C r).inputs.getD 1 0, isAO2_rb hAO hr (p47_mem2 _ hlen 1 (by omega)), ?_, ?_⟩
        · intro x
          rw [p40_or C g hAO _ (hxl x) r hr hgr' hrop, hw x]
          rfl
        · intro x hx
          rw [or_val n C hAO _ (hxl x) r hr hrop, hx]
          simp
      · refine ⟨(gateAt C r).inputs.getD 0 0, isAO2_rb hAO hr (p47_mem2 _ hlen 0 (by omega)), ?_, ?_⟩
        · intro x
          rw [p40_or C g hAO _ (hxl x) r hr hgr' hrop, hw x]
          simp
        · intro x hx
          rw [or_val n C hAO _ (hxl x) r hr hrop, hx]
          rfl
    refine ⟨eraseGate n C r y, p47_isAO2_erase n C r y hr hy hAO,
      by have := erase_size n C r y hr; omega, ?_⟩
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      have hrel := erase_val_rel (fun op => op = GateOp.and ∨ op = GateOp.or)
        (fun a b => b = true → a = true) (fun b hb => hb) hr hy
        (fun op l f f' hq h => by
          show op.eval ((l.map (eraseRedirect n r y)).map f') = true → op.eval (l.map f) = true
          rw [List.map_map]
          exact opMono_imp op hq l (f' ∘ eraseRedirect n r y) f (fun i _ => h i))
        (fun gt hgt => hAO.1 gt (List.mem_of_mem_drop hgt)) (hxl x)
        (hyC x) C.output
      rw [← hF]
      apply hrel
      show val (eraseGate n C r y) (List.ofFn x) (eraseRedirect n r y C.output) = true
      rw [← erase_output n C r y hr]
      exact h
    · intro h
      rw [← hCf x] at h
      have h2 := p40_ge C g r y hAO hg hr hgr hy _ (hxl x) (hry x) C.output h
      show val (eraseGate n C r y) (List.ofFn x) (eraseGate n C r y).output = true
      rw [erase_output n C r y hr]
      exact h2


theorem edge_invisible_gate_removable (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅)
    (hcone : PEqualNP.Core.InOutputCone n C g) (hg : g < C.gates.length)
    (hzero : ∀ u z : Fin n, G.Adj u z →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = false) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
      circuitFun n D = graphFun G ∅ := by
  have hxl : ∀ y : Fin n → Bool, (List.ofFn y).length = n := fun y => by simp
  have hCf : ∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      rw [← hF]
      exact p40_le C g hAO hg _ (hxl x) _ h
    · intro h
      have h' : ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true := by
        unfold graphFun at h
        simpa using h
      obtain ⟨u, z, hadj, hxu, hxz⟩ := h'
      have hle : ∀ i : Fin n, PEqualNP.EdgeOwnership.pairInput u z i = true → x i = true := by
        intro i hi
        simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
        rcases hi with hi | hi
        · rw [hi]; exact hxu
        · rw [hi]; exact hxz
      refine mono n (p40cf C g) (p40_aoo C g hAO.1) (PEqualNP.EdgeOwnership.pairInput u z) x hle
        C.output ?_
      rw [p40_eq_all C g hAO hg _ (hxl _) (hzero u z hadj)]
      show circuitFun n C (PEqualNP.EdgeOwnership.pairInput u z) = true
      rw [hF]
      unfold graphFun
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      right
      exact ⟨u, z, hadj, by simp [PEqualNP.EdgeOwnership.pairInput],
        by simp [PEqualNP.EdgeOwnership.pairInput]⟩
  rcases p40_find C g hAO _ g rfl hcone (le_refl g)
      (fun x => p40_self C g hg _ (hxl x)) with hz | ⟨r, hr, hgr, hrop, t, ht, hw⟩
  · refine ⟨⟨[], n⟩, ⟨fun gt h => by simp at h, fun j hj => by simp at hj, fun gt h => by simp at h⟩,
      by show 0 < C.gates.length; omega, ?_⟩
    funext x
    rw [← hCf x, hz x]
    show val (⟨[], n⟩ : Circuit) (List.ofFn x) n = false
    exact val_ge (hxl x) (by simp)
  · have hlen : (gateAt C r).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hr)
    have hgr' : r ≠ g := by omega
    obtain ⟨y, hy, hry, hyC⟩ : ∃ y, y < n + r ∧
        (∀ x : Fin n → Bool, val (p40cf C g) (List.ofFn x) (n + r) = val (p40cf C g) (List.ofFn x) y) ∧
        (∀ x : Fin n → Bool, val C (List.ofFn x) y = true → val C (List.ofFn x) (n + r) = true) := by
      rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl
      · refine ⟨(gateAt C r).inputs.getD 1 0, isAO2_rb hAO hr (p47_mem2 _ hlen 1 (by omega)), ?_, ?_⟩
        · intro x
          rw [p40_or C g hAO _ (hxl x) r hr hgr' hrop, hw x]
          rfl
        · intro x hx
          rw [or_val n C hAO _ (hxl x) r hr hrop, hx]
          simp
      · refine ⟨(gateAt C r).inputs.getD 0 0, isAO2_rb hAO hr (p47_mem2 _ hlen 0 (by omega)), ?_, ?_⟩
        · intro x
          rw [p40_or C g hAO _ (hxl x) r hr hgr' hrop, hw x]
          simp
        · intro x hx
          rw [or_val n C hAO _ (hxl x) r hr hrop, hx]
          rfl
    refine ⟨eraseGate n C r y, p47_isAO2_erase n C r y hr hy hAO,
      by have := erase_size n C r y hr; omega, ?_⟩
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      have hrel := erase_val_rel (fun op => op = GateOp.and ∨ op = GateOp.or)
        (fun a b => b = true → a = true) (fun b hb => hb) hr hy
        (fun op l f f' hq h => by
          show op.eval ((l.map (eraseRedirect n r y)).map f') = true → op.eval (l.map f) = true
          rw [List.map_map]
          exact opMono_imp op hq l (f' ∘ eraseRedirect n r y) f (fun i _ => h i))
        (fun gt hgt => hAO.1 gt (List.mem_of_mem_drop hgt)) (hxl x)
        (hyC x) C.output
      rw [← hF]
      apply hrel
      show val (eraseGate n C r y) (List.ofFn x) (eraseRedirect n r y C.output) = true
      rw [← erase_output n C r y hr]
      exact h
    · intro h
      rw [← hCf x] at h
      have h2 := p40_ge C g r y hAO hg hr hgr hy _ (hxl x) (hry x) C.output h
      show val (eraseGate n C r y) (List.ofFn x) (eraseGate n C r y).output = true
      rw [erase_output n C r y hr]
      exact h2

theorem least_gate_has_edge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅)
    (hcone : PEqualNP.Core.InOutputCone n C g) (hg : g < C.gates.length)
    (hmin : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D → circuitFun n D = graphFun G ∅ →
      C.size ≤ D.size) :
    ∃ u z : Fin n, G.Adj u z ∧
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = true := by
  by_contra h
  push_neg at h
  have hzero : ∀ u z : Fin n, G.Adj u z →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = false := by
    intro u z hadj
    exact Bool.eq_false_iff.mpr (h u z hadj)
  obtain ⟨D, hD, hsize, hfun⟩ := edge_invisible_gate_removable n G C g hAO hF hcone hg hzero
  have := hmin D hD hfun
  omega


theorem edge_equiv_smaller_replacement (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g y : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hg : g < C.gates.length) (hy : y < n + g)
    (hbelow : ∀ x : Fin n → Bool, val C (List.ofFn x) y = true →
      val C (List.ofFn x) (n + g) = true)
    (hedge : ∀ u z : Fin n, G.Adj u z →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) y =
        val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
      circuitFun n D = graphFun G ∅ := by
  let D := eraseGate n C g y
  have hD : PEqualNP.TopForm.IsAO2 n D := p47_isAO2_erase n C g y hg hy hAO
  have hxl : ∀ x : Fin n → Bool, (List.ofFn x).length = n := fun x => by simp
  refine ⟨D, hD, by have := erase_size n C g y hg; dsimp [D]; omega, ?_⟩
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    have hrel := erase_val_rel (fun op => op = GateOp.and ∨ op = GateOp.or)
      (fun a b => b = true → a = true) (fun b hb => hb) hg hy
      (fun op l f f' hq h => by
        show op.eval ((l.map (eraseRedirect n g y)).map f') = true → op.eval (l.map f) = true
        rw [List.map_map]
        exact opMono_imp op hq l (f' ∘ eraseRedirect n g y) f (fun i _ => h i))
      (fun gt hgt => hAO.1 gt (List.mem_of_mem_drop hgt)) (hxl x)
      (hbelow x) C.output
    rw [← hF]
    apply hrel
    show val D (List.ofFn x) (eraseRedirect n g y C.output) = true
    rw [← erase_output n C g y hg]
    exact hx
  · intro hx
    have he : ∃ u z : Fin n, G.Adj u z ∧ x u = true ∧ x z = true := by
      unfold graphFun at hx
      simpa using hx
    obtain ⟨u, z, hadj, hxu, hxz⟩ := he
    have hle : ∀ i : Fin n, PEqualNP.EdgeOwnership.pairInput u z i = true → x i = true := by
      intro i hi
      simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hxu
      · exact hxz
    apply mono n D hD.1 (PEqualNP.EdgeOwnership.pairInput u z) x hle D.output
    have hCe : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) C.output = true := by
      show circuitFun n C (PEqualNP.EdgeOwnership.pairInput u z) = true
      rw [hF]
      unfold graphFun
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      right
      exact ⟨u, z, hadj, by simp [PEqualNP.EdgeOwnership.pairInput],
        by simp [PEqualNP.EdgeOwnership.pairInput]⟩
    have hrel := erase_val_rel (fun _ => True) (fun a b => a = b) (fun b => rfl) hg hy
      (fun op l f f' _ h => by
        rw [List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => h i))
      (fun _ _ => True.intro) (hxl (PEqualNP.EdgeOwnership.pairInput u z))
      (hedge u z hadj).symm C.output
    change val D (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z))
      (eraseGate n C g y).output = true
    rw [erase_output n C g y hg, ← hrel]
    exact hCe

theorem least_gate_separates_earlier (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g y : ℕ) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hg : g < C.gates.length) (hy : y < n + g)
    (hmin : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D → circuitFun n D = graphFun G ∅ →
      C.size ≤ D.size)
    (hbelow : ∀ x : Fin n → Bool, val C (List.ofFn x) y = true →
      val C (List.ofFn x) (n + g) = true) :
    ∃ u z : Fin n, G.Adj u z ∧
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = true ∧
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) y = false := by
  by_contra h
  push_neg at h
  have hedge : ∀ u z : Fin n, G.Adj u z →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) y =
        val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) := by
    intro u z hadj
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hbelow (PEqualNP.EdgeOwnership.pairInput u z)
    · intro hg'
      exact Bool.eq_true_of_ne_false (h u z hadj hg')
  obtain ⟨D, hD, hsize, hfun⟩ := edge_equiv_smaller_replacement n G C g y hAO hF hg hy hbelow hedge
  have := hmin D hD hfun
  omega

lemma singleton_overlap_on_edge {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (u : Fin n) (huA : u ∈ A) (huB : u ∈ B)
    (hinter : ∀ v, v ∈ A → v ∈ B → v = u)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → a = u ∨ b = u)
    (a b : Fin n) (hab : G.Adj a b) :
    ((a ∈ A ∨ b ∈ A) ∧ (a ∈ B ∨ b ∈ B)) ↔ a = u ∨ b = u := by
  constructor
  · rintro ⟨ha | hb, ha' | hb'⟩
    · exact Or.inl (hinter a ha ha')
    · exact hcross a ha b hb' hab
    · exact (hcross b hb a ha' hab.symm).symm
    · exact Or.inr (hinter b hb hb')
  · rintro (rfl | rfl) <;> simp [huA, huB]


def patchGate (C : Circuit) (g : ℕ) (fresh : Gate) : Circuit :=
  ⟨C.gates.set g fresh, C.output⟩

lemma patch_length (C : Circuit) (g : ℕ) (fresh : Gate) :
    (patchGate C g fresh).gates.length = C.gates.length := by simp [patchGate]

lemma patch_gate_other (C : Circuit) (g j : ℕ) (fresh : Gate) (h : g ≠ j) :
    gateAt (patchGate C g fresh) j = gateAt C j := by
  simp [patchGate, gateAt, List.getD_eq_getElem?_getD, h]

lemma patch_gate_self (C : Circuit) (g : ℕ) (fresh : Gate) (hg : g < C.gates.length) :
    gateAt (patchGate C g fresh) g = fresh := by
  simp [patchGate, gateAt, List.getD_eq_getElem?_getD, hg]

lemma patch_isAO2 (n : ℕ) (C : Circuit) (g : ℕ) (fresh : Gate)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hg : g < C.gates.length)
    (hop : fresh.op = GateOp.and ∨ fresh.op = GateOp.or)
    (hlen : fresh.inputs.length = 2) (hback : ∀ i ∈ fresh.inputs, i < n + g) :
    PEqualNP.TopForm.IsAO2 n (patchGate C g fresh) := by
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    rcases List.mem_or_eq_of_mem_set hgt with h | rfl
    · exact hAO.1 gt h
    · exact hop
  · intro j hj
    have hjC : j < C.gates.length := by simpa [patchGate] using hj
    change ∀ i ∈ (gateAt (patchGate C g fresh) j).inputs, i < n + j
    by_cases h : j = g
    · subst j
      rw [patch_gate_self C g fresh hg]
      exact hback
    · rw [patch_gate_other C g j fresh (Ne.symm h)]
      exact hAO.2.1 j hjC
  · intro gt hgt
    rcases List.mem_or_eq_of_mem_set hgt with h | rfl
    · exact hAO.2.2 gt h
    · exact hlen

lemma patch_eq_before (n : ℕ) (C : Circuit) (g : ℕ) (fresh : Gate)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hg : g < C.gates.length)
    (x : List Bool) (hx : x.length = n) :
    ∀ i, i < n + g → val (patchGate C g fresh) x i = val C x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hinput : i < n
    · rw [val_input hx hinput, val_input hx hinput]
    obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have hjp : j < (patchGate C g fresh).gates.length := by rw [patch_length]; exact hj
    rw [val_gate hx hjp, patch_gate_other C g j fresh (by omega), val_gate hx hj]
    congr 1
    apply List.map_congr_left
    intro k hk
    have hb := hAO.2.1 j hj k hk
    simp only [if_pos hb]
    exact ih k hb (by omega)

lemma patch_val_self (n : ℕ) (C : Circuit) (g : ℕ) (fresh : Gate)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hg : g < C.gates.length)
    (hback : ∀ i ∈ fresh.inputs, i < n + g) (x : List Bool) (hx : x.length = n) :
    val (patchGate C g fresh) x (n + g) = fresh.op.eval (fresh.inputs.map (val C x)) := by
  rw [val_gate hx (by rw [patch_length]; exact hg), patch_gate_self C g fresh hg]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hb := hback i hi
  simp only [if_pos hb]
  exact patch_eq_before n C g fresh hAO hg x hx i hb

lemma patch_val_rel (n : ℕ) (C : Circuit) (g : ℕ) (fresh : Gate)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hg : g < C.gates.length)
    (hback : ∀ i ∈ fresh.inputs, i < n + g) (x : List Bool) (hx : x.length = n)
    (R : Bool → Bool → Prop) (hrefl : ∀ b, R b b) (hmono : OpMono R)
    (hgate : R (val C x (n + g)) (fresh.op.eval (fresh.inputs.map (val C x)))) :
    ∀ i, R (val C x i) (val (patchGate C g fresh) x i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hinput : i < n
    · rw [val_input hx hinput, val_input hx hinput]
      exact hrefl _
    by_cases hin : i < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases hjg : j = g
      · subst j
        rw [patch_val_self n C g fresh hAO hg hback x hx]
        exact hgate
      have hjp : j < (patchGate C g fresh).gates.length := by rw [patch_length]; exact hj
      rw [val_gate hx hj, val_gate hx hjp, patch_gate_other C g j fresh (Ne.symm hjg)]
      apply hmono _ (hAO.1 _ (gateAt_mem hj))
      intro k hk
      have hb := hAO.2.1 j hj k hk
      simp only [if_pos hb]
      exact ih k hb
    · rw [val_ge hx (by omega), val_ge (C := patchGate C g fresh) hx
        (by rw [patch_length]; omega)]
      exact hrefl _

lemma patch_opMono_eq : OpMono (fun a b => a = b) := by
  intro op _ l f f' h
  congr 1
  exact List.map_congr_left h

theorem patch_below_target (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (fresh : Gate) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hg : g < C.gates.length)
    (hop : fresh.op = GateOp.and ∨ fresh.op = GateOp.or)
    (hlen : fresh.inputs.length = 2) (hback : ∀ i ∈ fresh.inputs, i < n + g)
    (hold : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + g) = true → graphFun G ∅ x = true)
    (hnew : ∀ x : Fin n → Bool,
      fresh.op.eval (fresh.inputs.map (val C (List.ofFn x))) = true → graphFun G ∅ x = true)
    (hedge : ∀ u z : Fin n, G.Adj u z →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (n + g) = true →
      fresh.op.eval (fresh.inputs.map (val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)))) = true) :
    PEqualNP.TopForm.IsAO2 n (patchGate C g fresh) ∧ (patchGate C g fresh).size = C.size ∧
      circuitFun n (patchGate C g fresh) = graphFun G ∅ := by
  have hD := patch_isAO2 n C g fresh hAO hg hop hlen hback
  refine ⟨hD, by simp [patchGate, Circuit.size], ?_⟩
  funext x
  cases hFx : graphFun G ∅ x with
  | false =>
    have hgo : val C (List.ofFn x) (n + g) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have := hold x h
      simp [hFx] at this
    have hgn : fresh.op.eval (fresh.inputs.map (val C (List.ofFn x))) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have := hnew x h
      simp [hFx] at this
    have heq := patch_val_rel n C g fresh hAO hg hback (List.ofFn x) (by simp)
      (fun a b => a = b) (fun b => rfl) patch_opMono_eq (by rw [hgo, hgn]) C.output
    change val (patchGate C g fresh) (List.ofFn x) C.output = false
    rw [← heq]
    change circuitFun n C x = false
    rw [hF, hFx]
  | true =>
    have he : ∃ u z : Fin n, G.Adj u z ∧ x u = true ∧ x z = true := by
      unfold graphFun at hFx
      simpa using hFx
    obtain ⟨u, z, hadj, hxu, hxz⟩ := he
    have hle : ∀ i : Fin n, PEqualNP.EdgeOwnership.pairInput u z i = true → x i = true := by
      intro i hi
      simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hxu
      · exact hxz
    apply mono n (patchGate C g fresh) hD.1 (PEqualNP.EdgeOwnership.pairInput u z) x hle C.output
    apply patch_val_rel n C g fresh hAO hg hback
      (List.ofFn (PEqualNP.EdgeOwnership.pairInput u z)) (by simp)
      (fun a b => a = true → b = true) (fun b hb => hb) opMono_imp (hedge u z hadj) C.output
    change circuitFun n C (PEqualNP.EdgeOwnership.pairInput u z) = true
    rw [hF]
    unfold graphFun
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    right
    exact ⟨u, z, hadj, by simp [PEqualNP.EdgeOwnership.pairInput],
      by simp [PEqualNP.EdgeOwnership.pairInput]⟩

end PEqualNP.Outside.L_meta_2583_aux.EdgeInvisible

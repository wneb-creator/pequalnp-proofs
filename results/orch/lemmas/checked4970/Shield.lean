import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.Shield


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


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem wireVal_eq_val (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.wireVal n C w x = val C (List.ofFn x) w := rfl

theorem gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

theorem readVal_eq (n : ℕ) (C : Circuit) (a w : ℕ) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.readVal n C a w x =
      if w < n + a then val C (List.ofFn x) w else false := rfl

theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

theorem orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

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

theorem orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

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

theorem orReaches_trans (n : ℕ) (C : Circuit) (k g : ℕ) (hkg : PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w k → PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
    obtain ⟨hm, h3⟩ := (orReaches_iff n C m k).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]; exact hkg
    · exact orReaches_step n C m i g hm hop hi hlt (ih i hlt hri)

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

theorem reach_up_wire (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j b : ℕ)
    (hv : PEqualNP.CleanedNonEdge.wireVal n C (n + j) x = true)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C b j) :
    PEqualNP.CleanedNonEdge.wireVal n C b x = true :=
  reach_up n C (List.ofFn x) (by simp) j hv b hr

theorem orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

theorem mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

theorem orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

theorem orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

theorem orIn_reach (n : ℕ) (C : Circuit) (b k : ℕ) (a : Fin n)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C b k)
    (h : a ∈ PEqualNP.TopForm.orIn n C (n + k)) : a ∈ PEqualNP.TopForm.orIn n C b := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨m, hm, hrm, hopm, hin⟩
  · exfalso; have := a.isLt; omega
  · exact ⟨m, hm, orReaches_trans n C k m hrm b hr, hopm, hin⟩

theorem orIn_val (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (a : Fin n) (b : ℕ)
    (h : a ∈ PEqualNP.TopForm.orIn n C b) (hv : val C x a = true) : val C x b = true := by
  rw [mem_orIn] at h
  rcases h with hw | ⟨k, hk, hr, hop, hin⟩
  · rw [← hw]; exact hv
  · refine reach_up n C x hx k ?_ b hr
    refine (val_or hx hk hop).mpr ⟨a.val, hin, ?_, hv⟩
    have := a.isLt
    omega

def q91_d : Gate × Bool := (⟨GateOp.or, []⟩, false)

def q91_k (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (t : ℕ) : Bool :=
  if t < n then lin t else (S.getD (t - n) q91_d).2

def q91_v (S : List (Gate × Bool)) (x : List Bool) (t : ℕ) : Bool :=
  (W (S.map Prod.fst) x).getD t false

def q91_ov (S : List (Gate × Bool)) (x : List Bool) : Option ℕ → Bool
  | none => false
  | some t => q91_v S x t

def q91_Gd (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (c : Bool) (o : Option ℕ) : Prop :=
  ∀ t, o = some t → t < n + S.length ∧ q91_k n lin S t = c

def q91_GOK (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) : Prop :=
  ∀ k < S.length, ((S.getD k q91_d).1.op = GateOp.and ∨ (S.getD k q91_d).1.op = GateOp.or) ∧
    (S.getD k q91_d).1.inputs.length = 2 ∧ (∀ i ∈ (S.getD k q91_d).1.inputs, i < n + k) ∧
    ((S.getD k q91_d).1.op = GateOp.or → ∀ i ∈ (S.getD k q91_d).1.inputs,
      q91_k n lin S i = (S.getD k q91_d).2)

theorem q91_getD_pre {α : Type} (L T : List α) (d : α) (k : ℕ) (hk : k < L.length) :
    (L ++ T).getD k d = L.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem q91_getD_snoc {α : Type} (L : List α) (g d : α) (k : ℕ) (hk : k = L.length) :
    (L ++ [g]).getD k d = g := by
  subst hk; simp [List.getD_eq_getElem?_getD]

theorem q91_k_app (n : ℕ) (lin : ℕ → Bool) (S T : List (Gate × Bool)) (t : ℕ)
    (ht : t < n + S.length) : q91_k n lin (S ++ T) t = q91_k n lin S t := by
  unfold q91_k
  by_cases h : t < n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, q91_getD_pre S T q91_d (t - n) (by omega)]

theorem q91_k_gate (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (k : ℕ) :
    q91_k n lin S (n + k) = (S.getD k q91_d).2 := by
  unfold q91_k
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem q91_v_app (n : ℕ) (S T : List (Gate × Bool)) (x : List Bool) (t : ℕ) (hx : x.length = n)
    (ht : t < n + S.length) : q91_v (S ++ T) x t = q91_v S x t := by
  unfold q91_v
  rw [List.map_append, W_append, W_prefix]
  rw [W_length, hx, List.length_map]; exact ht

theorem q91_v_new (n : ℕ) (S : List (Gate × Bool)) (g : Gate) (c : Bool) (x : List Bool)
    (hx : x.length = n) :
    q91_v (S ++ [(g, c)]) x (n + S.length) = g.op.eval (g.inputs.map fun i => q91_v S x i) := by
  unfold q91_v
  rw [List.map_append, List.map_singleton, W_snoc_getD, if_pos (by rw [hx, List.length_map])]

theorem q91_Gd_mono (n : ℕ) (lin : ℕ → Bool) (S S' : List (Gate × Bool)) (c : Bool)
    (o : Option ℕ) (h : q91_Gd n lin S c o) (hp : S <+: S') : q91_Gd n lin S' c o := by
  obtain ⟨T, rfl⟩ := hp
  intro t ht
  obtain ⟨h1, h2⟩ := h t ht
  refine ⟨by rw [List.length_append]; omega, ?_⟩
  rw [q91_k_app n lin S T t h1]; exact h2

theorem q91_ov_mono (n : ℕ) (lin : ℕ → Bool) (S S' : List (Gate × Bool)) (x : List Bool)
    (c : Bool) (o : Option ℕ) (hx : x.length = n) (h : q91_Gd n lin S c o) (hp : S <+: S') :
    q91_ov S' x o = q91_ov S x o := by
  obtain ⟨T, rfl⟩ := hp
  cases o with
  | none => rfl
  | some t => exact q91_v_app n S T x t hx (h t rfl).1

theorem q91_GOK_snoc (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (g : Gate) (c : Bool)
    (hS : q91_GOK n lin S)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hrb : ∀ i ∈ g.inputs, i < n + S.length)
    (hc : g.op = GateOp.or → ∀ i ∈ g.inputs, q91_k n lin S i = c) :
    q91_GOK n lin (S ++ [(g, c)]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_or_ge k S.length with h | h
  · rw [q91_getD_pre S _ q91_d k h]
    obtain ⟨a1, a2, a3, a4⟩ := hS k h
    refine ⟨a1, a2, a3, fun ho i hi => ?_⟩
    rw [q91_k_app n lin S _ i (by have := a3 i hi; omega)]
    exact a4 ho i hi
  · have hk2 : k = S.length := by omega
    rw [q91_getD_snoc S (g, c) q91_d k hk2]
    refine ⟨hop, hlen, fun i hi => by have := hrb i hi; omega, fun ho i hi => ?_⟩
    rw [q91_k_app n lin S _ i (hrb i hi)]
    exact hc ho i hi

def q91_and (n : ℕ) (S : List (Gate × Bool)) (c : Bool) :
    Option ℕ → Option ℕ → List (Gate × Bool) × Option ℕ
  | some i, some j => (S ++ [(⟨GateOp.and, [i, j]⟩, c)], some (n + S.length))
  | some _, none => (S, none)
  | none, _ => (S, none)

def q91_or (n : ℕ) (S : List (Gate × Bool)) (c : Bool) :
    Option ℕ → Option ℕ → List (Gate × Bool) × Option ℕ
  | some i, some j => (S ++ [(⟨GateOp.or, [i, j]⟩, c)], some (n + S.length))
  | some i, none => (S, some i)
  | none, b => (S, b)

theorem q91_new_Gd (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (g : Gate) (c : Bool) :
    q91_Gd n lin (S ++ [(g, c)]) c (some (n + S.length)) := by
  intro t ht
  cases ht
  refine ⟨by simp, ?_⟩
  rw [q91_k_gate, q91_getD_snoc S (g, c) q91_d S.length rfl]

theorem q91_and_spec (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (c ca cb : Bool)
    (a b : Option ℕ) (S' : List (Gate × Bool)) (r : Option ℕ) (h : q91_and n S c a b = (S', r))
    (hS : q91_GOK n lin S) (ha : q91_Gd n lin S ca a) (hb : q91_Gd n lin S cb b) :
    S <+: S' ∧ S'.length ≤ S.length + 1 ∧ q91_GOK n lin S' ∧ q91_Gd n lin S' c r ∧
      ∀ x : List Bool, x.length = n → q91_ov S' x r = (q91_ov S x a && q91_ov S x b) := by
  rcases a with _ | i <;> rcases b with _ | j
  · simp only [q91_and, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
    exact ⟨List.prefix_refl _, by omega, hS, (fun t ht => by cases ht), (fun x _ => by simp [q91_ov])⟩
  · simp only [q91_and, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
    exact ⟨List.prefix_refl _, by omega, hS, (fun t ht => by cases ht), (fun x _ => by simp [q91_ov])⟩
  · simp only [q91_and, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
    exact ⟨List.prefix_refl _, by omega, hS, (fun t ht => by cases ht), (fun x _ => by simp [q91_ov])⟩
  · simp only [q91_and, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
    have hi := ha i rfl
    have hj := hb j rfl
    refine ⟨List.prefix_append S _, by simp, ?_, q91_new_Gd n lin S _ c, ?_⟩
    · apply q91_GOK_snoc n lin S _ c hS (Or.inl rfl) rfl
      · intro t ht
        simp at ht
        rcases ht with rfl | rfl
        · exact hi.1
        · exact hj.1
      · intro ho; cases ho
    · intro x hx
      show q91_v _ x _ = (q91_v S x i && q91_v S x j)
      rw [q91_v_new n S _ c x hx]
      simp only [List.map_cons, List.map_nil, eval_and2]

theorem q91_or_spec (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (c : Bool)
    (a b : Option ℕ) (S' : List (Gate × Bool)) (r : Option ℕ) (h : q91_or n S c a b = (S', r))
    (hS : q91_GOK n lin S) (ha : q91_Gd n lin S c a) (hb : q91_Gd n lin S c b) :
    S <+: S' ∧ S'.length ≤ S.length + 1 ∧ q91_GOK n lin S' ∧ q91_Gd n lin S' c r ∧
      ∀ x : List Bool, x.length = n → q91_ov S' x r = (q91_ov S x a || q91_ov S x b) := by
  rcases a with _ | i <;> rcases b with _ | j
  · simp only [q91_or, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
    exact ⟨List.prefix_refl _, by omega, hS, (fun t ht => by cases ht), (fun x _ => by simp [q91_ov])⟩
  · simp only [q91_or, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
    exact ⟨List.prefix_refl _, by omega, hS, hb, (fun x _ => by simp [q91_ov])⟩
  · simp only [q91_or, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
    exact ⟨List.prefix_refl _, by omega, hS, ha, (fun x _ => by simp [q91_ov])⟩
  · simp only [q91_or, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
    have hi := ha i rfl
    have hj := hb j rfl
    refine ⟨List.prefix_append S _, by simp, ?_, q91_new_Gd n lin S _ c, ?_⟩
    · apply q91_GOK_snoc n lin S _ c hS (Or.inr rfl) rfl
      · intro t ht
        simp at ht
        rcases ht with rfl | rfl
        · exact hi.1
        · exact hj.1
      · intro _ t ht
        simp at ht
        rcases ht with rfl | rfl
        · exact hi.2
        · exact hj.2
    · intro x hx
      show q91_v _ x _ = (q91_v S x i || q91_v S x j)
      rw [q91_v_new n S _ c x hx]
      simp only [List.map_cons, List.map_nil, eval_or2]

def q91_ba (n : ℕ) (S : List (Gate × Bool)) (pu lu pv lv : Option ℕ) :
    List (Gate × Bool) × Option ℕ × Option ℕ :=
  let r1 := q91_and n S false pu pv
  let r2 := q91_and n r1.1 true lu lv
  let r3 := q91_and n r2.1 false pu lv
  let r4 := q91_and n r3.1 false lu pv
  let r5 := q91_or n r4.1 false r3.2 r4.2
  let r6 := q91_or n r5.1 false r1.2 r5.2
  (r6.1, r6.2, r2.2)

def q91_bo (n : ℕ) (S : List (Gate × Bool)) (pu lu pv lv : Option ℕ) :
    List (Gate × Bool) × Option ℕ × Option ℕ :=
  let r1 := q91_or n S false pu pv
  let r2 := q91_or n r1.1 true lu lv
  (r2.1, r1.2, r2.2)

def q91_blk (n : ℕ) (S : List (Gate × Bool)) (op : GateOp) (pu lu pv lv : Option ℕ) :
    List (Gate × Bool) × Option ℕ × Option ℕ :=
  match op with
  | GateOp.and => q91_ba n S pu lu pv lv
  | _ => q91_bo n S pu lu pv lv

theorem q91_ba_spec (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (pu lu pv lv : Option ℕ)
    (S' : List (Gate × Bool)) (P L : Option ℕ) (h : q91_ba n S pu lu pv lv = (S', P, L))
    (hS : q91_GOK n lin S) (hpu : q91_Gd n lin S false pu) (hlu : q91_Gd n lin S true lu)
    (hpv : q91_Gd n lin S false pv) (hlv : q91_Gd n lin S true lv) :
    S <+: S' ∧ S'.length ≤ S.length + 6 ∧ q91_GOK n lin S' ∧ q91_Gd n lin S' false P ∧
      q91_Gd n lin S' true L ∧ ∀ x : List Bool, x.length = n →
        (q91_ov S' x P || q91_ov S' x L) =
          ((q91_ov S x pu || q91_ov S x lu) && (q91_ov S x pv || q91_ov S x lv)) := by
  obtain ⟨S1, o1, e1⟩ : ∃ S1 o1, q91_and n S false pu pv = (S1, o1) := ⟨_, _, rfl⟩
  obtain ⟨p1, n1, g1, d1, v1⟩ := q91_and_spec n lin S false false false pu pv S1 o1 e1 hS hpu hpv
  obtain ⟨S2, o2, e2⟩ : ∃ S2 o2, q91_and n S1 true lu lv = (S2, o2) := ⟨_, _, rfl⟩
  obtain ⟨p2, n2, g2, d2, v2⟩ := q91_and_spec n lin S1 true true true lu lv S2 o2 e2 g1
    (q91_Gd_mono n lin S S1 true lu hlu p1) (q91_Gd_mono n lin S S1 true lv hlv p1)
  have p12 := p1.trans p2
  obtain ⟨S3, o3, e3⟩ : ∃ S3 o3, q91_and n S2 false pu lv = (S3, o3) := ⟨_, _, rfl⟩
  obtain ⟨p3, n3, g3, d3, v3⟩ := q91_and_spec n lin S2 false false true pu lv S3 o3 e3 g2
    (q91_Gd_mono n lin S S2 false pu hpu p12) (q91_Gd_mono n lin S S2 true lv hlv p12)
  have p13 := p12.trans p3
  obtain ⟨S4, o4, e4⟩ : ∃ S4 o4, q91_and n S3 false lu pv = (S4, o4) := ⟨_, _, rfl⟩
  obtain ⟨p4, n4, g4, d4, v4⟩ := q91_and_spec n lin S3 false true false lu pv S4 o4 e4 g3
    (q91_Gd_mono n lin S S3 true lu hlu p13) (q91_Gd_mono n lin S S3 false pv hpv p13)
  obtain ⟨S5, o5, e5⟩ : ∃ S5 o5, q91_or n S4 false o3 o4 = (S5, o5) := ⟨_, _, rfl⟩
  obtain ⟨p5, n5, g5, d5, v5⟩ := q91_or_spec n lin S4 false o3 o4 S5 o5 e5 g4
    (q91_Gd_mono n lin S3 S4 false o3 d3 p4) d4
  have p25 : S1 <+: S5 := ((p2.trans p3).trans p4).trans p5
  obtain ⟨S6, o6, e6⟩ : ∃ S6 o6, q91_or n S5 false o1 o5 = (S6, o6) := ⟨_, _, rfl⟩
  obtain ⟨p6, n6, g6, d6, v6⟩ := q91_or_spec n lin S5 false o1 o5 S6 o6 e6 g5
    (q91_Gd_mono n lin S1 S5 false o1 d1 p25) d5
  have p36 : S2 <+: S6 := ((p3.trans p4).trans p5).trans p6
  have eb : q91_ba n S pu lu pv lv = (S6, o6, o2) := by
    simp only [q91_ba, e1, e2, e3, e4, e5, e6]
  rw [eb] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [← h1, ← h2, ← h3]
  refine ⟨(p1.trans p25).trans p6, by omega, g6, d6, q91_Gd_mono n lin S2 S6 true o2 d2 p36, ?_⟩
  intro x hx
  rw [v6 x hx, v5 x hx, v4 x hx, q91_ov_mono n lin S1 S5 x false o1 hx d1 p25, v1 x hx,
    q91_ov_mono n lin S3 S4 x false o3 hx d3 p4, v3 x hx,
    q91_ov_mono n lin S2 S6 x true o2 hx d2 p36, v2 x hx,
    q91_ov_mono n lin S S3 x true lu hx hlu p13, q91_ov_mono n lin S S3 x false pv hx hpv p13,
    q91_ov_mono n lin S S2 x false pu hx hpu p12, q91_ov_mono n lin S S2 x true lv hx hlv p12,
    q91_ov_mono n lin S S1 x true lu hx hlu p1, q91_ov_mono n lin S S1 x true lv hx hlv p1]
  generalize q91_ov S x pu = A1
  generalize q91_ov S x lu = A2
  generalize q91_ov S x pv = A3
  generalize q91_ov S x lv = A4
  cases A1 <;> cases A2 <;> cases A3 <;> cases A4 <;> rfl

theorem q91_bo_spec (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (pu lu pv lv : Option ℕ)
    (S' : List (Gate × Bool)) (P L : Option ℕ) (h : q91_bo n S pu lu pv lv = (S', P, L))
    (hS : q91_GOK n lin S) (hpu : q91_Gd n lin S false pu) (hlu : q91_Gd n lin S true lu)
    (hpv : q91_Gd n lin S false pv) (hlv : q91_Gd n lin S true lv) :
    S <+: S' ∧ S'.length ≤ S.length + 6 ∧ q91_GOK n lin S' ∧ q91_Gd n lin S' false P ∧
      q91_Gd n lin S' true L ∧ ∀ x : List Bool, x.length = n →
        (q91_ov S' x P || q91_ov S' x L) =
          ((q91_ov S x pu || q91_ov S x lu) || (q91_ov S x pv || q91_ov S x lv)) := by
  obtain ⟨S1, o1, e1⟩ : ∃ S1 o1, q91_or n S false pu pv = (S1, o1) := ⟨_, _, rfl⟩
  obtain ⟨p1, n1, g1, d1, v1⟩ := q91_or_spec n lin S false pu pv S1 o1 e1 hS hpu hpv
  obtain ⟨S2, o2, e2⟩ : ∃ S2 o2, q91_or n S1 true lu lv = (S2, o2) := ⟨_, _, rfl⟩
  obtain ⟨p2, n2, g2, d2, v2⟩ := q91_or_spec n lin S1 true lu lv S2 o2 e2 g1
    (q91_Gd_mono n lin S S1 true lu hlu p1) (q91_Gd_mono n lin S S1 true lv hlv p1)
  have eb : q91_bo n S pu lu pv lv = (S2, o1, o2) := by
    simp only [q91_bo, e1, e2]
  rw [eb] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [← h1, ← h2, ← h3]
  refine ⟨p1.trans p2, by omega, g2, q91_Gd_mono n lin S1 S2 false o1 d1 p2, d2, ?_⟩
  intro x hx
  rw [q91_ov_mono n lin S1 S2 x false o1 hx d1 p2, v1 x hx, v2 x hx,
    q91_ov_mono n lin S S1 x true lu hx hlu p1, q91_ov_mono n lin S S1 x true lv hx hlv p1]
  generalize q91_ov S x pu = A1
  generalize q91_ov S x lu = A2
  generalize q91_ov S x pv = A3
  generalize q91_ov S x lv = A4
  cases A1 <;> cases A2 <;> cases A3 <;> cases A4 <;> rfl

theorem q91_blk_spec (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (op : GateOp)
    (pu lu pv lv : Option ℕ)
    (S' : List (Gate × Bool)) (P L : Option ℕ) (h : q91_blk n S op pu lu pv lv = (S', P, L))
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (hS : q91_GOK n lin S) (hpu : q91_Gd n lin S false pu) (hlu : q91_Gd n lin S true lu)
    (hpv : q91_Gd n lin S false pv) (hlv : q91_Gd n lin S true lv) :
    S <+: S' ∧ S'.length ≤ S.length + 6 ∧ q91_GOK n lin S' ∧ q91_Gd n lin S' false P ∧
      q91_Gd n lin S' true L ∧ ∀ x : List Bool, x.length = n →
        (q91_ov S' x P || q91_ov S' x L) =
          op.eval [q91_ov S x pu || q91_ov S x lu, q91_ov S x pv || q91_ov S x lv] := by
  rcases hop with rfl | rfl
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := q91_ba_spec n lin S pu lu pv lv S' P L h hS hpu hlu hpv hlv
    exact ⟨a1, a2, a3, a4, a5, fun x hx => by rw [a6 x hx, eval_and2]⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := q91_bo_spec n lin S pu lu pv lv S' P L h hS hpu hlu hpv hlv
    exact ⟨a1, a2, a3, a4, a5, fun x hx => by rw [a6 x hx, eval_or2]⟩

def q91_rp (n : ℕ) (lin : ℕ → Bool) (R : List (Option ℕ × Option ℕ)) (w : ℕ) :
    Option ℕ × Option ℕ :=
  if w < n then (if lin w = true then (none, some w) else (some w, none))
  else R.getD (w - n) (none, none)

theorem q91_rp_app (n : ℕ) (lin : ℕ → Bool) (R T : List (Option ℕ × Option ℕ)) (w : ℕ)
    (hw : w < n + R.length) : q91_rp n lin (R ++ T) w = q91_rp n lin R w := by
  unfold q91_rp
  by_cases h : w < n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, q91_getD_pre R T _ (w - n) (by omega)]

theorem q91_rp_last (n : ℕ) (lin : ℕ → Bool) (R : List (Option ℕ × Option ℕ))
    (e : Option ℕ × Option ℕ) (w : ℕ) (hw : w = n + R.length) : q91_rp n lin (R ++ [e]) w = e := by
  unfold q91_rp
  rw [if_neg (by omega)]
  exact q91_getD_snoc R e _ (w - n) (by omega)

theorem q91_rp_ge (n : ℕ) (lin : ℕ → Bool) (R : List (Option ℕ × Option ℕ)) (w : ℕ)
    (hw : n + R.length ≤ w) : q91_rp n lin R w = (none, none) := by
  unfold q91_rp
  rw [if_neg (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show R.length ≤ w - n by omega)]

theorem q91_rp_in (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (R : List (Option ℕ × Option ℕ))
    (w : ℕ) (hw : w < n) :
    q91_Gd n lin S false (q91_rp n lin R w).1 ∧ q91_Gd n lin S true (q91_rp n lin R w).2 := by
  cases hl : lin w
  · have e : q91_rp n lin R w = (some w, none) := by simp [q91_rp, hw, hl]
    rw [e]
    refine ⟨fun t ht => ?_, (fun t ht => by cases ht)⟩
    simp at ht
    subst ht
    exact ⟨by omega, by simp [q91_k, hw, hl]⟩
  · have e : q91_rp n lin R w = (none, some w) := by simp [q91_rp, hw, hl]
    rw [e]
    refine ⟨(fun t ht => by cases ht), fun t ht => ?_⟩
    simp at ht
    subst ht
    exact ⟨by omega, by simp [q91_k, hw, hl]⟩

theorem q91_rp_val (n : ℕ) (lin : ℕ → Bool) (R : List (Option ℕ × Option ℕ)) (w : ℕ) (hw : w < n)
    (x : List Bool) :
    (q91_ov [] x (q91_rp n lin R w).1 || q91_ov [] x (q91_rp n lin R w).2) = x.getD w false := by
  cases hl : lin w
  · have e : q91_rp n lin R w = (some w, none) := by simp [q91_rp, hw, hl]
    rw [e]
    simp [q91_ov, q91_v, W_nil]
  · have e : q91_rp n lin R w = (none, some w) := by simp [q91_rp, hw, hl]
    rw [e]
    simp [q91_ov, q91_v, W_nil]

theorem q91_first (n : ℕ) (lin : ℕ → Bool) (R : List (Option ℕ × Option ℕ)) (op : GateOp)
    (u v : ℕ) (hu : u < n) (hv : v < n) (hop : op = GateOp.and ∨ op = GateOp.or) :
    (q91_blk n [] op (q91_rp n lin R u).1 (q91_rp n lin R u).2 (q91_rp n lin R v).1
      (q91_rp n lin R v).2).1.length ≤ 1 := by
  have eu : q91_rp n lin R u = if lin u = true then (none, some u) else (some u, none) := by
    unfold q91_rp; rw [if_pos hu]
  have ev : q91_rp n lin R v = if lin v = true then (none, some v) else (some v, none) := by
    unfold q91_rp; rw [if_pos hv]
  rw [eu, ev]
  rcases hop with rfl | rfl <;> cases lin u <;> cases lin v <;>
    simp [q91_blk, q91_ba, q91_bo, q91_and, q91_or]

def q91_bs (n : ℕ) (lin : ℕ → Bool) (st : List (Gate × Bool) × List (Option ℕ × Option ℕ))
    (g : Gate) : List (Gate × Bool) × List (Option ℕ × Option ℕ) :=
  let u := q91_rp n lin st.2 (g.inputs.getD 0 0)
  let v := q91_rp n lin st.2 (g.inputs.getD 1 0)
  let r := q91_blk n st.1 g.op u.1 u.2 v.1 v.2
  (r.1, st.2 ++ [r.2])

def q91_B (n : ℕ) (lin : ℕ → Bool) (gs : List Gate) :
    List (Gate × Bool) × List (Option ℕ × Option ℕ) :=
  gs.foldl (q91_bs n lin) ([], [])

def q91_Inv (n : ℕ) (lin : ℕ → Bool) (gs : List Gate) (S : List (Gate × Bool))
    (R : List (Option ℕ × Option ℕ)) : Prop :=
  R.length = gs.length ∧ q91_GOK n lin S ∧ (S.length + 5 ≤ 6 * gs.length ∨ (gs = [] ∧ S = [])) ∧
  (∀ w < n + gs.length, q91_Gd n lin S false (q91_rp n lin R w).1 ∧
    q91_Gd n lin S true (q91_rp n lin R w).2) ∧
  (∀ x : List Bool, x.length = n → ∀ w < n + gs.length,
    (W gs x).getD w false = (q91_ov S x (q91_rp n lin R w).1 || q91_ov S x (q91_rp n lin R w).2))

def q91_Hg (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∨
    (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or) ∧
    (gs.getD j ⟨GateOp.or, []⟩).inputs.length = 2 ∧ ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

theorem q91_inv (n : ℕ) (lin : ℕ → Bool) (gs : List Gate) (hg : q91_Hg n gs) :
    q91_Inv n lin gs (q91_B n lin gs).1 (q91_B n lin gs).2 := by
  induction gs using List.reverseRecOn with
  | nil =>
    show q91_Inv n lin [] [] []
    refine ⟨rfl, fun k hk => absurd hk (by simp), Or.inr ⟨rfl, rfl⟩, ?_, ?_⟩
    · intro w hw
      exact q91_rp_in n lin [] [] w (by simpa using hw)
    · intro x hx w hw
      rw [q91_rp_val n lin [] w (by simpa using hw) x, W_nil]
  | append_singleton l a ih =>
    have hl : q91_Hg n l := by
      intro j hj
      have h := hg j (by simp; omega)
      rw [q91_getD_pre l [a] _ j hj] at h
      exact h
    have ha := hg l.length (by simp)
    rw [q91_getD_snoc l a _ l.length rfl] at ha
    obtain ⟨haop, halen, harb⟩ := ha
    obtain ⟨u, v, huv⟩ := List.length_eq_two.mp halen
    have hu : u < n + l.length := harb u (by rw [huv]; simp)
    have hv : v < n + l.length := harb v (by rw [huv]; simp)
    have ih' := ih hl
    have eB : q91_B n lin (l ++ [a]) = q91_bs n lin (q91_B n lin l) a := by
      simp [q91_B, List.foldl_append]
    generalize q91_B n lin l = st at ih' eB
    obtain ⟨S, R⟩ := st
    dsimp only at ih'
    obtain ⟨hR, hGOK, hcost, hGd, hval⟩ := ih'
    obtain ⟨S', P, L, eK⟩ : ∃ S' P L, q91_blk n S a.op (q91_rp n lin R u).1 (q91_rp n lin R u).2
        (q91_rp n lin R v).1 (q91_rp n lin R v).2 = (S', P, L) := ⟨_, _, _, rfl⟩
    have hu0 : a.inputs.getD 0 0 = u := by rw [huv]; rfl
    have hv0 : a.inputs.getD 1 0 = v := by rw [huv]; rfl
    have est : q91_bs n lin (S, R) a = (S', R ++ [(P, L)]) := by
      simp only [q91_bs, hu0, hv0, eK]
    rw [eB, est]
    obtain ⟨hpre, hlen', hGOK', hP, hL, hvalB⟩ := q91_blk_spec n lin S a.op _ _ _ _ S' P L eK haop
      hGOK (hGd u hu).1 (hGd u hu).2 (hGd v hv).1 (hGd v hv).2
    refine ⟨by simp [hR], hGOK', ?_, ?_, ?_⟩
    · rcases hcost with h | ⟨h1, h2⟩
      · left; simp only [List.length_append, List.length_singleton]; omega
      · subst h1; subst h2
        have h3 := q91_first n lin R a.op u v (by simpa using hu) (by simpa using hv) haop
        rw [eK] at h3
        left; simp only [List.length_append, List.length_singleton, List.length_nil]
        simp only at h3
        omega
    · intro w hw
      simp only [List.length_append, List.length_singleton] at hw
      rcases Nat.lt_or_ge w (n + l.length) with hw' | hw'
      · rw [q91_rp_app n lin R _ w (by omega)]
        exact ⟨q91_Gd_mono n lin S S' false _ (hGd w hw').1 hpre,
          q91_Gd_mono n lin S S' true _ (hGd w hw').2 hpre⟩
      · rw [q91_rp_last n lin R (P, L) w (by omega)]
        exact ⟨hP, hL⟩
    · intro x hx w hw
      simp only [List.length_append, List.length_singleton] at hw
      rw [W_snoc_getD]
      by_cases hwe : w = x.length + l.length
      · rw [if_pos hwe, q91_rp_last n lin R (P, L) w (by omega), huv]
        simp only [List.map_cons, List.map_nil]
        rw [hval x hx u hu, hval x hx v hv]
        exact (hvalB x hx).symm
      · rw [if_neg hwe]
        have hw' : w < n + l.length := by omega
        rw [q91_rp_app n lin R _ w (by omega), hval x hx w hw',
          q91_ov_mono n lin S S' x false _ hx (hGd w hw').1 hpre,
          q91_ov_mono n lin S S' x true _ hx (hGd w hw').2 hpre]

def q91_ex : Option ℕ → Option ℕ → List Gate
  | some a, some b => [⟨GateOp.or, [a, b]⟩]
  | some _, none => []
  | none, _ => []

def q91_fin (n : ℕ) (S : List (Gate × Bool)) : Option ℕ → Option ℕ → Circuit
  | some a, some b => ⟨S.map Prod.fst ++ [⟨GateOp.or, [a, b]⟩], n + S.length⟩
  | some a, none => ⟨S.map Prod.fst, a⟩
  | none, some b => ⟨S.map Prod.fst, b⟩
  | none, none => ⟨S.map Prod.fst, n + S.length⟩

theorem q91_fin_gates (n : ℕ) (S : List (Gate × Bool)) (po lo : Option ℕ) :
    (q91_fin n S po lo).gates = S.map Prod.fst ++ q91_ex po lo := by
  rcases po with _ | a <;> rcases lo with _ | b <;> simp [q91_fin, q91_ex]

theorem q91_ex_len (po lo : Option ℕ) : (q91_ex po lo).length ≤ 1 := by
  rcases po with _ | a <;> rcases lo with _ | b <;> simp [q91_ex]

theorem q91_ex_mem (po lo : Option ℕ) (g : Gate) (h : g ∈ q91_ex po lo) :
    ∃ a b, po = some a ∧ lo = some b ∧ g = ⟨GateOp.or, [a, b]⟩ := by
  rcases po with _ | a <;> rcases lo with _ | b <;> simp [q91_ex] at h
  exact ⟨a, b, rfl, rfl, h⟩

theorem q91_mem (S : List (Gate × Bool)) (g : Gate) (hg : g ∈ S.map Prod.fst) :
    ∃ k < S.length, (S.getD k q91_d).1 = g := by
  rw [List.mem_map] at hg
  obtain ⟨e, he, rfl⟩ := hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  exact ⟨k, hk, by simp [List.getD_eq_getElem?_getD, hk]⟩

theorem q91_gateAt (n : ℕ) (S : List (Gate × Bool)) (po lo : Option ℕ) (k : ℕ) (hk : k < S.length) :
    gateAt (q91_fin n S po lo) k = (S.getD k q91_d).1 := by
  unfold gateAt
  rw [q91_fin_gates, q91_getD_pre _ _ _ k (by simpa using hk)]
  simp [List.getD_eq_getElem?_getD, hk]

theorem q91_gateAt_last (n : ℕ) (S : List (Gate × Bool)) (a b : ℕ) :
    gateAt (q91_fin n S (some a) (some b)) S.length = ⟨GateOp.or, [a, b]⟩ := by
  show (S.map Prod.fst ++ [Gate.mk GateOp.or [a, b]]).getD S.length (Gate.mk GateOp.or []) = _
  exact q91_getD_snoc _ _ _ _ (by simp)

theorem q91_fin_val (n : ℕ) (S : List (Gate × Bool)) (po lo : Option ℕ) (x : List Bool)
    (hx : x.length = n) :
    (W (q91_fin n S po lo).gates x).getD (q91_fin n S po lo).output false =
      (q91_ov S x po || q91_ov S x lo) := by
  rcases po with _ | a <;> rcases lo with _ | b
  · show (W (S.map Prod.fst) x).getD (n + S.length) false = (false || false)
    rw [W_ge _ _ _ (by rw [hx, List.length_map])]; rfl
  · show (W (S.map Prod.fst) x).getD b false = (false || q91_v S x b)
    simp [q91_v]
  · show (W (S.map Prod.fst) x).getD a false = (q91_v S x a || false)
    simp [q91_v]
  · show (W (S.map Prod.fst ++ [Gate.mk GateOp.or [a, b]]) x).getD (n + S.length) false =
      (q91_v S x a || q91_v S x b)
    rw [W_snoc_getD, if_pos (by rw [hx, List.length_map])]
    simp [eval_or2, q91_v]

theorem q91_fin_ao2 (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (po lo : Option ℕ)
    (hS : q91_GOK n lin S) (hpo : ∀ t, po = some t → t < n + S.length)
    (hlo : ∀ t, lo = some t → t < n + S.length) :
    PEqualNP.TopForm.IsAO2 n (q91_fin n S po lo) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rw [q91_fin_gates, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨k, hk, rfl⟩ := q91_mem S g hg
      exact (hS k hk).1
    · obtain ⟨a, b, _, _, rfl⟩ := q91_ex_mem po lo g hg
      exact Or.inr rfl
  · intro j hj i hi
    rw [q91_fin_gates, List.length_append, List.length_map] at hj
    rcases Nat.lt_or_ge j S.length with hlt | hge
    · rw [q91_gateAt n S po lo j hlt] at hi
      exact (hS j hlt).2.2.1 i hi
    · have hex := q91_ex_len po lo
      have hj' : j = S.length := by omega
      subst hj'
      rcases po with _ | a <;> rcases lo with _ | b
      · simp [q91_ex] at hj
      · simp [q91_ex] at hj
      · simp [q91_ex] at hj
      · rw [q91_gateAt_last] at hi
        simp at hi
        rcases hi with rfl | rfl
        · exact hpo _ rfl
        · exact hlo _ rfl
  · intro g hg
    rw [q91_fin_gates, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨k, hk, rfl⟩ := q91_mem S g hg
      exact (hS k hk).2.1
    · obtain ⟨a, b, _, _, rfl⟩ := q91_ex_mem po lo g hg
      rfl

theorem q91_reach (n : ℕ) (D : Circuit) (κ : ℕ → Bool) (m : ℕ)
    (hor : ∀ k < m, (gateAt D k).op = GateOp.or → ∀ i ∈ (gateAt D k).inputs, κ i = κ (n + k)) :
    ∀ w, w < n + m → ∀ g, PEqualNP.CleanedNonEdge.OrReaches n D w g → κ w = κ (n + g) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw g hr
    have hb := orReaches_bound n D g w hr
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    rw [orReaches_iff] at hr
    rcases hr with ⟨_, rfl | ⟨hop, i, hi, hil, hri⟩⟩
    · rfl
    · rw [← hor j (by omega) hop i hi]
      exact ih i hil (by omega) g hri

theorem q91_col (n : ℕ) (lin : ℕ → Bool) (D : Circuit) (κ : ℕ → Bool) (m : ℕ)
    (hin : ∀ i < n, κ i = lin i)
    (hor : ∀ k < m, (gateAt D k).op = GateOp.or → ∀ i ∈ (gateAt D k).inputs, κ i = κ (n + k)) :
    ∀ w < n + m, ∀ a ∈ PEqualNP.TopForm.orIn n D w, lin (a : ℕ) = κ w := by
  intro w hw a ha
  rw [mem_orIn] at ha
  rcases ha with h | ⟨k, hk, hr, hop, hin2⟩
  · rw [← h, hin a a.isLt]
  · have hb := orReaches_bound n D k w hr
    rw [q91_reach n D κ m hor w hw k hr, ← hor k (by omega) hop a hin2, hin a a.isLt]

theorem q91_fin_tc (n : ℕ) (lin : ℕ → Bool) (S : List (Gate × Bool)) (po lo : Option ℕ)
    (hS : q91_GOK n lin S)
    (hone : ∀ a : Fin n, val (q91_fin n S po lo) (List.ofFn (fun k => decide (k = a)))
      (q91_fin n S po lo).output = false) :
    PEqualNP.TwoColour.tCount n (q91_fin n S po lo) lin = 0 := by
  unfold PEqualNP.TwoColour.tCount PEqualNP.TwoColour.twoColour
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _ htc
  unfold PEqualNP.TwoColour.IsTwoColour at htc
  obtain ⟨hgl, _, ⟨i1, hi1, hl1⟩, ⟨i2, hi2, hl2⟩⟩ := htc
  rw [q91_fin_gates, List.length_append, List.length_map] at hgl
  rcases Nat.lt_or_ge g S.length with hlt | hge
  · have hin : ∀ i < n, q91_k n lin S i = lin i := by
      intro i hi; unfold q91_k; rw [if_pos hi]
    have hor : ∀ k < S.length, (gateAt (q91_fin n S po lo) k).op = GateOp.or →
        ∀ i ∈ (gateAt (q91_fin n S po lo) k).inputs, q91_k n lin S i = q91_k n lin S (n + k) := by
      intro k hk hop i hi
      rw [q91_gateAt n S po lo k hk] at hop hi
      rw [q91_k_gate]
      exact (hS k hk).2.2.2 hop i hi
    have hc := q91_col n lin (q91_fin n S po lo) (q91_k n lin S) S.length hin hor
    have e1 := hc (n + g) (by omega) i1 hi1
    have e2 := hc (n + g) (by omega) i2 hi2
    rw [hl1] at e1
    rw [hl2, ← e1] at e2
    cases e2
  · have hex := q91_ex_len po lo
    have hex1 : (q91_ex po lo).length = 1 := by omega
    have hout : (q91_fin n S po lo).output = n + S.length := by
      rcases po with _ | a <;> rcases lo with _ | b <;> simp [q91_ex, q91_fin] at hex1 ⊢
    have hg' : g = S.length := by omega
    have hv := orIn_val n (q91_fin n S po lo) (List.ofFn fun k => decide (k = i1)) (by simp) i1
      (n + g) hi1 (by rw [val_ofFn]; simp)
    rw [hg', ← hout, hone i1] at hv
    cases hv

theorem main_aux : ∀ (p l : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (p + l) C → 1 ≤ C.size → (∀ i : Fin (p + l), PEqualNP.MetaComplexity.circuitFun (p + l) C (fun k => decide (k = i)) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (p + l) D ∧ D.size + 4 ≤ 6 * C.size ∧ PEqualNP.MetaComplexity.circuitFun (p + l) D = PEqualNP.MetaComplexity.circuitFun (p + l) C ∧ PEqualNP.TwoColour.tCount (p + l) D (fun i => decide (p ≤ i)) = 0 := by
  intro p l C hC hs hone
  have hg : q91_Hg (p + l) C.gates := by
    intro j hj
    have hmem : C.gates.getD j ⟨GateOp.or, []⟩ ∈ C.gates := gateAt_mem hj
    exact ⟨hC.1 _ hmem, hC.2.2 _ hmem, hC.2.1 j hj⟩
  have hI := q91_inv (p + l) (fun i => decide (p ≤ i)) C.gates hg
  generalize q91_B (p + l) (fun i => decide (p ≤ i)) C.gates = st at hI
  obtain ⟨S, R⟩ := st
  dsimp only at hI
  obtain ⟨hR, hGOK, hcost, hGd, hval⟩ := hI
  have hGo : q91_Gd (p + l) (fun i => decide (p ≤ i)) S false
        (q91_rp (p + l) (fun i => decide (p ≤ i)) R C.output).1 ∧
      q91_Gd (p + l) (fun i => decide (p ≤ i)) S true
        (q91_rp (p + l) (fun i => decide (p ≤ i)) R C.output).2 := by
    by_cases ho : C.output < p + l + C.gates.length
    · exact hGd _ ho
    · rw [q91_rp_ge (p + l) _ R C.output (by omega)]
      exact ⟨(fun t ht => by cases ht), (fun t ht => by cases ht)⟩
  have hvo : ∀ x : List Bool, x.length = p + l → (W C.gates x).getD C.output false =
      (q91_ov S x (q91_rp (p + l) (fun i => decide (p ≤ i)) R C.output).1 ||
        q91_ov S x (q91_rp (p + l) (fun i => decide (p ≤ i)) R C.output).2) := by
    intro x hx
    by_cases ho : C.output < p + l + C.gates.length
    · exact hval x hx _ ho
    · rw [q91_rp_ge (p + l) _ R C.output (by omega), W_ge _ _ _ (by omega)]
      rfl
  obtain ⟨po, lo, hpl⟩ : ∃ po lo, q91_rp (p + l) (fun i => decide (p ≤ i)) R C.output = (po, lo) :=
    ⟨_, _, rfl⟩
  rw [hpl] at hGo hvo
  obtain ⟨hGp, hGl⟩ := hGo
  have hfun : circuitFun (p + l) (q91_fin (p + l) S po lo) = circuitFun (p + l) C := by
    funext x
    rw [circuitFun_W, circuitFun_W, q91_fin_val (p + l) S po lo (List.ofFn x) (by simp),
      hvo (List.ofFn x) (by simp)]
  have hone' : ∀ a : Fin (p + l), val (q91_fin (p + l) S po lo)
      (List.ofFn (fun k => decide (k = a))) (q91_fin (p + l) S po lo).output = false := by
    intro a
    rw [← circuitFun_val, hfun]
    exact hone a
  refine ⟨q91_fin (p + l) S po lo,
    q91_fin_ao2 (p + l) (fun i => decide (p ≤ i)) S po lo hGOK (fun t ht => (hGp t ht).1)
      (fun t ht => (hGl t ht).1), ?_, hfun, q91_fin_tc (p + l) _ S po lo hGOK hone'⟩
  have hsz : C.size = C.gates.length := rfl
  show (q91_fin (p + l) S po lo).gates.length + 4 ≤ 6 * C.size
  rw [q91_fin_gates, List.length_append, List.length_map, hsz]
  have hex := q91_ex_len po lo
  rcases hcost with h | ⟨h1, _⟩
  · omega
  · rw [hsz, h1] at hs; simp at hs

end PEqualNP.Outside.L_meta_4970_aux.Shield

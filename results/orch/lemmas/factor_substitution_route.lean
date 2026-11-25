import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.factorSubstitution

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

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

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

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

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


open PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.FactorSubst

lemma reach_le {n : ℕ} {C : Circuit} {g : ℕ} :
    ∀ w, OrReaches n C w g → n + g ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    rw [orReaches_iff] at h
    rcases h.2 with h | ⟨_, i, _, hlt, hr⟩
    · omega
    · have := ih i hlt hr
      omega

lemma reach_self {n : ℕ} {C : Circuit} {g : ℕ} (hg : g < C.gates.length) :
    OrReaches n C (n + g) g := by
  rw [orReaches_iff]; exact ⟨hg, Or.inl rfl⟩

lemma reach_up {n : ℕ} {C : Circuit} {k i g : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hi : i ∈ (gateAt C k).inputs) (hlt : i < n + k)
    (h : OrReaches n C i g) : OrReaches n C (n + k) g := by
  rw [orReaches_iff]; exact ⟨hk, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

lemma reach_mono {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {g : ℕ} :
    ∀ w, OrReaches n C w g → val C x (n + g) = true → val C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h hv
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    rw [orReaches_iff] at h
    obtain ⟨hk, h⟩ := h
    rcases h with h | ⟨hop, i, hi, hlt, hr⟩
    · subst h; exact hv
    · exact (val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hr hv⟩

lemma exists_reader {n : ℕ} {C : Circuit} {c : ℕ} :
    ∀ w, OrReaches n C w c → w ≠ n + c → ∃ r ∈ readers n C c, OrReaches n C w r := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h hne
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    rw [orReaches_iff] at h
    obtain ⟨hk, h⟩ := h
    rcases h with h | ⟨hop, i, hi, hlt, hr⟩
    · subst h; exact (hne rfl).elim
    · by_cases hic : i = n + c
      · subst hic
        exact ⟨k, by simp [readers, hk, hi], reach_self hk⟩
      · obtain ⟨r, hr1, hr2⟩ := ih i hlt hr hic
        exact ⟨r, hr1, reach_up hk hop hi hlt hr2⟩

def ren (n c : ℕ) (sigma : ℕ → ℕ) (k i : ℕ) : ℕ := if i = n + c then sigma k else i

lemma sub_len (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n c sigma).gates.length = C.gates.length := by simp [substReads]

lemma sub_gate {C : Circuit} {n c : ℕ} {sigma : ℕ → ℕ} {k : ℕ} (hk : k < C.gates.length) :
    gateAt (substReads C n c sigma) k =
      ⟨(gateAt C k).op, (gateAt C k).inputs.map (ren n c sigma k)⟩ := by
  rw [gateAt_eq hk, gateAt_eq (by rw [sub_len]; exact hk)]
  simp [substReads, ren]

lemma sub_inputs {C : Circuit} {n c : ℕ} {sigma : ℕ → ℕ} {k i : ℕ} (hk : k < C.gates.length) :
    i ∈ (gateAt (substReads C n c sigma) k).inputs ↔
      ∃ p ∈ (gateAt C k).inputs, ren n c sigma k p = i := by
  rw [sub_gate hk]; simp

lemma main (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ) (hao : IsAO2 n C)
    (hc : c < C.gates.length) (hcop : (gateAt C c).op = GateOp.and)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b)
    (H2 : ∀ g ∈ frontier n C c, (gateAt C g).op = GateOp.and → ∀ u y : ℕ,
      ((gateAt C g).inputs = [u, y] ∨ (gateAt C g).inputs = [y, u]) →
      (∃ w ∈ insert c (orClosure n C c), u = n + w) →
      (∀ w' ∈ insert c (orClosure n C c), y ≠ n + w') ∧
      ∀ r ∈ readers n C c, (r = g ∨ OrReaches n C u r) →
        (sigma r = b → ∀ x : Fin n → Bool, wireVal n C y x = true → wireVal n C a x = true) ∧
        (sigma r = a → ∀ x' : Fin n → Bool, wireVal n C y x' = true → wireVal n C b x' = true))
    (H3 : ∀ g2 ∈ frontier n C c, ∀ u2 ∈ (gateAt C g2).inputs, ∀ r1 ∈ readers n C c,
      ∀ r2 ∈ readers n C c, OrReaches n C u2 r1 → OrReaches n C u2 r2 → sigma r1 = sigma r2)
    (z : Fin n → Bool) :
    ∀ w, (¬ OrReaches n C w c →
        val (substReads C n c sigma) (List.ofFn z) w = val C (List.ofFn z) w) ∧
      (OrReaches n C w c → w ≠ n + c →
        (val C (List.ofFn z) w = true → val (substReads C n c sigma) (List.ofFn z) w = true) ∧
        ∀ s, (∀ r ∈ readers n C c, OrReaches n C w r → sigma r = s) →
          val (substReads C n c sigma) (List.ofFn z) w = true →
          val C (List.ofFn z) w = true ∨ val C (List.ofFn z) s = true) := by
  have hx : (List.ofFn z).length = n := by simp
  obtain ⟨hAO, hRB, h2⟩ := hao
  have ha : a < n + c := hRB c hc a (by rw [hcin]; simp)
  have hb : b < n + c := hRB c hc b (by rw [hcin]; simp)
  have hread : ∀ k, k < C.gates.length → n + c ∈ (gateAt C k).inputs → k ∈ readers n C c := by
    intro k hk h; simp [readers, hk, h]
  have hvc : val C (List.ofFn z) (n + c) = true ↔
      val C (List.ofFn z) a = true ∧ val C (List.ofFn z) b = true := by
    rw [val_and hx hc hcop, hcin]; simp [ha, hb]
  have hclos : ∀ u, OrReaches n C u c → ∃ w ∈ insert c (orClosure n C c), u = n + w := by
    intro u hu
    have h1 := hu.1
    obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
    refine ⟨k, ?_, rfl⟩
    by_cases hkc : k = c
    · simp [hkc]
    · have := ((orReaches_iff n C k c).mp hu).1
      simp [orClosure, hkc, this, hu]
  have hclos' : ∀ u, (∀ w' ∈ insert c (orClosure n C c), u ≠ n + w') → ¬ OrReaches n C u c := by
    intro u hu hr
    obtain ⟨w, hw, e⟩ := hclos u hr
    exact hu w hw e
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  by_cases hwn : w < n
  · refine ⟨fun _ => ?_, fun h => ?_⟩
    · rw [val_input hx hwn, val_input hx hwn]
    · have := h.1; omega
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  by_cases hk : k < C.gates.length
  swap
  · refine ⟨fun _ => ?_, fun h => ?_⟩
    · rw [val_ge (n := n) (C := C) hx (by omega),
        val_ge (n := n) (C := substReads C n c sigma) hx (by rw [sub_len]; omega)]
    · exact (hk ((orReaches_iff n C k c).mp h).1).elim
  have hk' : k < (substReads C n c sigma).gates.length := by rw [sub_len]; exact hk
  have hopk : (gateAt (substReads C n c sigma) k).op = (gateAt C k).op := by rw [sub_gate hk]
  have hck : n + c ∈ (gateAt C k).inputs → c < k := by
    intro h; have := hRB k hk _ h; omega
  have hrenlt : ∀ i ∈ (gateAt C k).inputs, ren n c sigma k i < n + k := by
    intro i hi
    unfold ren
    split_ifs with h
    · subst h
      have := hck hi
      rcases hsig k (hread k hk hi) with e | e <;> omega
    · exact hRB k hk i hi
  have hor : (gateAt C k).op = GateOp.or → (val C (List.ofFn z) (n + k) = true ↔
      ∃ i ∈ (gateAt C k).inputs, val C (List.ofFn z) i = true) := by
    intro h
    rw [val_or hx hk h]
    exact ⟨fun ⟨i, hi, _, hv⟩ => ⟨i, hi, hv⟩, fun ⟨i, hi, hv⟩ => ⟨i, hi, hRB k hk i hi, hv⟩⟩
  have hor' : (gateAt C k).op = GateOp.or →
      (val (substReads C n c sigma) (List.ofFn z) (n + k) = true ↔
      ∃ i ∈ (gateAt C k).inputs,
        val (substReads C n c sigma) (List.ofFn z) (ren n c sigma k i) = true) := by
    intro h
    rw [val_or hx hk' (by rw [hopk]; exact h)]
    constructor
    · rintro ⟨i, hi, _, hv⟩
      obtain ⟨p, hp, rfl⟩ := (sub_inputs hk).mp hi
      exact ⟨p, hp, hv⟩
    · rintro ⟨i, hi, hv⟩
      exact ⟨_, (sub_inputs hk).mpr ⟨i, hi, rfl⟩, hrenlt i hi, hv⟩
  have hand : (gateAt C k).op = GateOp.and → (val C (List.ofFn z) (n + k) = true ↔
      ∀ i ∈ (gateAt C k).inputs, val C (List.ofFn z) i = true) := by
    intro h
    rw [val_and hx hk h]
    exact ⟨fun f i hi => (f i hi).2, fun f i hi => ⟨hRB k hk i hi, f i hi⟩⟩
  have hand' : (gateAt C k).op = GateOp.and →
      (val (substReads C n c sigma) (List.ofFn z) (n + k) = true ↔
      ∀ i ∈ (gateAt C k).inputs,
        val (substReads C n c sigma) (List.ofFn z) (ren n c sigma k i) = true) := by
    intro h
    rw [val_and hx hk' (by rw [hopk]; exact h)]
    constructor
    · intro f i hi
      exact (f _ ((sub_inputs hk).mpr ⟨i, hi, rfl⟩)).2
    · intro f i hi
      obtain ⟨p, hp, rfl⟩ := (sub_inputs hk).mp hi
      exact ⟨hrenlt p hp, f p hp⟩
  have hfac : n + c ∈ (gateAt C k).inputs →
      val (substReads C n c sigma) (List.ofFn z) (sigma k) = val C (List.ofFn z) (sigma k) := by
    intro h
    have h1 := hck h
    have h3 : sigma k < n + c := by
      rcases hsig k (hread k hk h) with e | e <;> omega
    exact (ih (sigma k) (by omega)).1 (fun hr => by have := reach_le _ hr; omega)
  have hrenc : ren n c sigma k (n + c) = sigma k := by simp [ren]
  have hrenn : ∀ i, i ≠ n + c → ren n c sigma k i = i := by intro i h; simp [ren, h]
  have hRc : OrReaches n C (n + c) c := reach_self hc
  have hrenR : ∀ i, ¬ OrReaches n C i c → ren n c sigma k i = i := by
    intro i h; exact hrenn i (fun e => h (e ▸ hRc))
  refine ⟨fun hnr => ?_, fun hr hne => ?_⟩
  · rcases hAO _ (gateAt_mem hk) with hop | hop
    · -- an AND gate
      obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
      have front : ∀ u y, ((gateAt C k).inputs = [u, y] ∨ (gateAt C k).inputs = [y, u]) →
          OrReaches n C u c →
          val (substReads C n c sigma) (List.ofFn z) (n + k) = val C (List.ofFn z) (n + k) := by
        intro u y huy hu
        have hu_in : u ∈ (gateAt C k).inputs := by rcases huy with e | e <;> simp [e]
        have hy_in : y ∈ (gateAt C k).inputs := by rcases huy with e | e <;> simp [e]
        have hall : ∀ P : ℕ → Prop, (∀ i ∈ (gateAt C k).inputs, P i) ↔ (P u ∧ P y) := by
          intro P
          rcases huy with e | e <;> simp [e, and_comm]
        have hfr : k ∈ frontier n C c := by
          have hkc : k ≠ c := fun e => hnr (e ▸ hRc)
          obtain ⟨w, hw, e⟩ := hclos u hu
          simp only [FactorSubst.frontier, Finset.mem_filter, Finset.mem_range]
          refine ⟨hk, hkc, ?_, w, hw, e ▸ hu_in⟩
          simp only [orClosure, Finset.mem_filter, not_and]
          exact fun _ _ => hnr
        obtain ⟨hy1, hy2⟩ := H2 k hfr hop u y huy (hclos u hu)
        have hyR := hclos' y hy1
        rw [Bool.eq_iff_iff, hand hop, hand' hop, hall, hall, hrenR y hyR,
          (ih y (hRB k hk y hy_in)).1 hyR]
        by_cases huc : u = n + c
        · subst huc
          rw [hrenc, hfac hu_in, hvc]
          obtain ⟨h3, h4⟩ := hy2 k (hread k hk hu_in) (Or.inl rfl)
          rcases hsig k (hread k hk hu_in) with e | e
          · have h5 := h4 e z
            rw [e]
            exact ⟨fun ⟨h6, h7⟩ => ⟨⟨h6, h5 h7⟩, h7⟩, fun ⟨h6, h7⟩ => ⟨h6.1, h7⟩⟩
          · have h5 := h3 e z
            rw [e]
            exact ⟨fun ⟨h6, h7⟩ => ⟨⟨h5 h7, h6⟩, h7⟩, fun ⟨h6, h7⟩ => ⟨h6.2, h7⟩⟩
        · rw [hrenn u huc]
          obtain ⟨r, hr1, hr2⟩ := exists_reader u hu huc
          obtain ⟨h3, h4⟩ := hy2 r hr1 (Or.inr hr2)
          obtain ⟨h5, h6⟩ := (ih u (hRB k hk u hu_in)).2 hu huc
          constructor
          · rintro ⟨h7, h8⟩
            refine ⟨?_, h8⟩
            rcases h6 (sigma r) (fun r2 hr3 hr4 => H3 k hfr u hu_in r2 hr3 r hr1 hr4 hr2) h7
              with h9 | h9
            · exact h9
            · refine reach_mono hx u hu (hvc.mpr ?_)
              rcases hsig r hr1 with e | e
              · rw [e] at h9; exact ⟨h9, h4 e z h8⟩
              · rw [e] at h9; exact ⟨h3 e z h8, h9⟩
          · rintro ⟨h7, h8⟩
            exact ⟨h5 h7, h8⟩
      by_cases hp : OrReaches n C p c
      · exact front p q (Or.inl hpq) hp
      by_cases hq : OrReaches n C q c
      · exact front q p (Or.inr hpq) hq
      have hall : ∀ P : ℕ → Prop, (∀ i ∈ (gateAt C k).inputs, P i) ↔ (P p ∧ P q) := by
        intro P; simp [hpq]
      rw [Bool.eq_iff_iff, hand hop, hand' hop, hall, hall, hrenR p hp, hrenR q hq,
        (ih p (hRB k hk p (by simp [hpq]))).1 hp, (ih q (hRB k hk q (by simp [hpq]))).1 hq]
    · -- an OR gate outside the closure reads nothing of it
      have hno : ∀ i ∈ (gateAt C k).inputs, ¬ OrReaches n C i c := fun i hi hr =>
        hnr (reach_up hk hop hi (hRB k hk i hi) hr)
      rw [Bool.eq_iff_iff, hor hop, hor' hop]
      constructor
      · rintro ⟨i, hi, hv⟩
        rw [hrenR i (hno i hi), (ih i (hRB k hk i hi)).1 (hno i hi)] at hv
        exact ⟨i, hi, hv⟩
      · rintro ⟨i, hi, hv⟩
        refine ⟨i, hi, ?_⟩
        rw [hrenR i (hno i hi), (ih i (hRB k hk i hi)).1 (hno i hi)]
        exact hv
  · have hop : (gateAt C k).op = GateOp.or := by
      rcases ((orReaches_iff n C k c).mp hr).2 with e | ⟨e, _⟩
      · exact (hne (by rw [e])).elim
      · exact e
    refine ⟨fun hv => ?_, fun s hs hv => ?_⟩
    · obtain ⟨i, hi, hv⟩ := (hor hop).mp hv
      refine (hor' hop).mpr ⟨i, hi, ?_⟩
      by_cases hic : i = n + c
      · subst hic
        rw [hrenc, hfac hi]
        rcases hsig k (hread k hk hi) with e | e
        · rw [e]; exact (hvc.mp hv).1
        · rw [e]; exact (hvc.mp hv).2
      · rw [hrenn i hic]
        by_cases hR : OrReaches n C i c
        · exact ((ih i (hRB k hk i hi)).2 hR hic).1 hv
        · rw [(ih i (hRB k hk i hi)).1 hR]; exact hv
    · obtain ⟨i, hi, hv⟩ := (hor' hop).mp hv
      by_cases hic : i = n + c
      · subst hic
        rw [hrenc, hfac hi, hs k (hread k hk hi) (reach_self hk)] at hv
        exact Or.inr hv
      · rw [hrenn i hic] at hv
        by_cases hR : OrReaches n C i c
        · rcases ((ih i (hRB k hk i hi)).2 hR hic).2 s
            (fun r hr1 hr2 => hs r hr1 (reach_up hk hop hi (hRB k hk i hi) hr2)) hv with h | h
          · exact Or.inl ((hor hop).mpr ⟨i, hi, h⟩)
          · exact Or.inr h
        · rw [(ih i (hRB k hk i hi)).1 hR] at hv
          exact Or.inl ((hor hop).mpr ⟨i, hi, hv⟩)

lemma cone_sub {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ} (hRB : ReadsBack n C)
    (hc : c < C.gates.length) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ j i, InCone n (substReads C n c sigma) i j → InCone n C i j ∧ i ≠ c := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    rw [inCone_iff, sub_len] at h
    obtain ⟨hj, k, hk, hin, h⟩ := h
    obtain ⟨p, hp, e⟩ := (sub_inputs hj).mp hin
    have h' : (i = k ∨ InCone n C i k) ∧ (i = c → k = c ∧ i = k) := by
      rcases h with h | h
      · exact ⟨Or.inl h, fun hi => ⟨h ▸ hi, h⟩⟩
      · exact ⟨Or.inr (ih k hk i h).1, fun hi => ((ih k hk i h).2 hi).elim⟩
    have ha : a < n + c := hRB c hc a (by rw [hcin]; simp)
    have hb : b < n + c := hRB c hc b (by rw [hcin]; simp)
    unfold ren at e
    split_ifs at e with hpc
    · subst hpc
      have hrd : j ∈ readers n C c := by simp [readers, hj, hp]
      have hcj : c < j := by have := hRB j hj _ hp; omega
      have hs := hsig j hrd
      have hkc : k < c := by rcases hs with h | h <;> omega
      refine ⟨?_, fun hi => ?_⟩
      · rw [inCone_iff]
        refine ⟨hj, c, hcj, hp, Or.inr ?_⟩
        rw [inCone_iff]
        refine ⟨hc, k, hkc, ?_, h'.1⟩
        rw [hcin, ← e]
        rcases hs with h | h <;> simp [h]
      · have := (h'.2 hi).1; omega
    · subst e
      refine ⟨?_, fun hi => ?_⟩
      · rw [inCone_iff]
        exact ⟨hj, k, hk, hp, h'.1⟩
      · have := (h'.2 hi).1
        exact hpc (by rw [this])

lemma exchange : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C := by
  intro n C c a b sigma hao hc hcop hcin hsig H2 H3 H4 hlive
  refine ⟨?_, ?_⟩
  · intro k hk hkc hkO z
    have hm := main n C c a b sigma hao hc hcop hcin hsig H2 H3 z (n + k)
    rw [gateVal_eq_val, gateVal_eq_val]
    refine hm.1 (fun hr => hkO ?_)
    simp only [PEqualNP.FactorSubst.orClosure, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk, hkc, hr⟩
  · have hcone := cone_sub (sigma := sigma) hao.2.1 hc hcin hsig
    have hsub : PEqualNP.FactorSubst.liveGates n (PEqualNP.FactorSubst.substReads C n c sigma) ⊆
        (PEqualNP.FactorSubst.liveGates n C).erase c := by
      intro j hj
      simp only [PEqualNP.FactorSubst.liveGates, Finset.mem_filter, Finset.mem_range,
        sub_len] at hj
      obtain ⟨hj, hn, h⟩ := hj
      have ho : (PEqualNP.FactorSubst.substReads C n c sigma).output = C.output := rfl
      rw [ho] at hn h
      rw [Finset.mem_erase]
      simp only [PEqualNP.FactorSubst.liveGates, Finset.mem_filter, Finset.mem_range]
      rcases h with h | h
      · refine ⟨fun hjc => ?_, hj, hn, Or.inl h⟩
        exact H4 c (Finset.mem_insert_self _ _) (by omega)
      · obtain ⟨h1, h2⟩ := hcone _ _ h
        exact ⟨h2, hj, hn, Or.inr h1⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_erase_lt_of_mem hlive
    unfold PEqualNP.FactorSubst.liveSize
    omega

end PEqualNP.Outside.L_meta_1772_aux.factorSubstitution

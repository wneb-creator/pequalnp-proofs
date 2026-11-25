import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux.OneJunkActive

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

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

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

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

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


def TraceCondition {n : ℕ} (C : Circuit) (source : Fin n) (base d : ℕ → Bool) : Prop :=
  (∀ t : Fin n, d t.val = decide (t = source)) ∧
  ∀ j, j < C.gates.length → ∀ a b, (gateAt C j).inputs = [a,b] →
    ((gateAt C j).op = .and → d (n+j) = (base a && d b || d a && base b)) ∧
    ((gateAt C j).op = .or → d (n+j) = (d a || d b))

lemma trace_or_up {n : ℕ} {C : Circuit} {source : Fin n} {base d : ℕ → Bool}
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hd : TraceCondition C source base d) {a b : ℕ}
    (path : Relation.ReflTransGen (OrStep n C) a b) (hb : d b = true) : d a = true := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact hb
  | @head a c step rest ih =>
    obtain ⟨j,hj,rfl,ho,hm,_⟩ := step
    obtain ⟨u,v,hi⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hj))
    rw [(hd.2 j hj u v hi).2 ho]
    rw [hi] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl <;> simp [ih]

lemma trace_and_up {n : ℕ} {C : Circuit} {source : Fin n} {base d : ℕ → Bool}
    (hd : TraceCondition C source base d) {j a b : ℕ} (hj : j < C.gates.length)
    (ho : (gateAt C j).op = .and)
    (hi : (gateAt C j).inputs = [a,b] ∨ (gateAt C j).inputs = [b,a])
    (ha : d a = true) (hb : base b = true) : d (n+j) = true := by
  rcases hi with hi | hi
  · rw [(hd.2 j hj a b hi).1 ho]
    simp [ha,hb]
  · rw [(hd.2 j hj b a hi).1 ho]
    simp [ha,hb]

lemma value_and_up {n : ℕ} {C : Circuit} (x : Fin n → Bool)
    {j a b : ℕ} (hj : j < C.gates.length) (ho : (gateAt C j).op = .and)
    (hi : (gateAt C j).inputs = [a,b] ∨ (gateAt C j).inputs = [b,a])
    (ha : a < n+j) (hb : b < n+j)
    (va : val C (List.ofFn x) a = true) (vb : val C (List.ofFn x) b = true) :
    val C (List.ofFn x) (n+j) = true := by
  rw [val_and (n := n) (by simp) hj ho]
  intro i hm
  rcases hi with hi | hi
  · rw [hi] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨ha,va⟩
    · exact ⟨hb,vb⟩
  · rw [hi] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨hb,vb⟩
    · exact ⟨ha,va⟩

open PEqualNP.TopForm PEqualNP.CleanedNonEdge

set_option maxHeartbeats 2000000 in
lemma topform_one_active_junk_trace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (model : IsAO2 n C) (top : PEqualNP.TopForm.TopForm G C)
    (spec : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (p q : Fin n) (edge : G.Adj p q) (dl dp : ℕ → Bool)
    (small : ((junk G C).filter fun h =>
      val C (List.ofFn (pairInput p q)) (n+h) = true).card ≤ 1)
    (hl : TraceCondition C q (val C (List.ofFn (pairInput p p))) dl)
    (hp : TraceCondition C p (val C (List.ofFn (pairInput q q))) dp) :
    dl C.output = true ∨ dp C.output = true := by
  classical
  obtain ⟨ops,reads,two⟩ := model
  have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x := spec
  have hF : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
    fun u v h => (graphFun_pair G u v).mp h
  obtain ⟨a,ha,hnot,ra,va⟩ := edge_trace G (graphFun G ∅) hF hout p q
    ((graphFun_pair G p q).mpr edge)
  have ao : (gateAt C a).op = .and := by
    rcases ops _ (gateAt_mem ha) with h | h
    · exact h
    · exact (hnot h).elim
  have below : BelowF G C a := fun x hx => below_of_reach (graphFun G ∅) hout a ra x hx
  have badP : val C (List.ofFn (pairInput p p)) (n+a) = true → False :=
    fun h => G.irrefl (hF p p (below _ h))
  have badQ : val C (List.ofFn (pairInput q q)) (n+a) = true → False :=
    fun h => G.irrefl (hF q q (below _ h))
  have pval (w : ℕ) (r : Relation.ReflTransGen (OrStep n C) w p.val) :
      val C (List.ofFn (pairInput p p)) w = true :=
    reach_var_val _ _ p r (pairInput_left p p)
  have qval (w : ℕ) (r : Relation.ReflTransGen (OrStep n C) w q.val) :
      val C (List.ofFn (pairInput q q)) w = true :=
    reach_var_val _ _ q r (pairInput_left q q)
  have pdiff (w : ℕ) (r : Relation.ReflTransGen (OrStep n C) w p.val) : dp w = true :=
    trace_or_up two hp r (by rw [hp.1 p]; simp)
  have qdiff (w : ℕ) (r : Relation.ReflTransGen (OrStep n C) w q.val) : dl w = true :=
    trace_or_up two hl r (by rw [hl.1 q]; simp)
  have uniq : ∀ i ∈ junk G C, val C (List.ofFn (pairInput p q)) (n+i) = true →
      ∀ j ∈ junk G C, val C (List.ofFn (pairInput p q)) (n+j) = true → i = j := by
    intro i hi vi j hj vj
    exact Finset.card_le_one.mp small i (Finset.mem_filter.mpr ⟨hi,vi⟩)
      j (Finset.mem_filter.mpr ⟨hj,vj⟩)
  have dirty_of (j : ℕ) (hj : j < C.gates.length) (jo : (gateAt C j).op = .and)
      (w : ℕ) (hm : w ∈ (gateAt C j).inputs) (hw : w < n+j)
      (h : ℕ) (hh : h < C.gates.length) (hnot : (gateAt C h).op ≠ .or)
      (r : Relation.ReflTransGen (OrStep n C) w (n+h)) :
      h ∈ junk G C ∧ (gateAt C h).op = .and ∧ ¬ BelowF G C h := by
    have ho : (gateAt C h).op = .and := by
      rcases ops _ (gateAt_mem hh) with ho | ho
      · exact ho
      · exact (hnot ho).elim
    have nc : ¬ BelowF G C h := fun bh => top h hh j hj ho bh jo (operand_cone hj hm hw r)
    have dirt : IsDirtyAnd n G C h := by
      refine ⟨ho,hh,?_⟩
      by_contra no
      apply nc
      intro x hx
      by_contra hf
      exact no ⟨x,hx,Bool.eq_false_iff.mpr hf⟩
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh,dirt⟩,ho,nc⟩
  have no_ands_below (h : ℕ) (hh : h < C.gates.length) (ho : (gateAt C h).op = .and)
      (hjunk : h ∈ junk G C) (vh : val C (List.ofFn (pairInput p q)) (n+h) = true)
      (w : ℕ) (hm : w ∈ (gateAt C h).inputs)
      (hw : w < n+h) (vw : val C (List.ofFn (pairInput p q)) w = true) :
      ∃ t : Fin n, (t = p ∨ t = q) ∧ Relation.ReflTransGen (OrStep n C) w t.val := by
    rcases operand_trace (C := C) p q w vw with hit | ⟨k,hk,kn,rk,vk⟩
    · exact hit
    · obtain ⟨kj,_,_⟩ := dirty_of h hh ho w hm hw k hk kn rk
      have eq := uniq k kj vk h hjunk vh
      subst k
      have le := orStep_le rk
      omega
  obtain ⟨u,v,uv⟩ := List.length_eq_two.mp (two _ (gateAt_mem ha))
  have um : u ∈ (gateAt C a).inputs := by simp [uv]
  have vm : v ∈ (gateAt C a).inputs := by simp [uv]
  have uval := (val_and (n := n) (by simp) ha ao).mp va u um
  have vval := (val_and (n := n) (by simp) ha ao).mp va v vm
  have finish : dl (n+a) = true ∨ dp (n+a) = true →
      dl C.output = true ∨ dp C.output = true := by
    rintro (h | h)
    · exact Or.inl (trace_or_up two hl ra h)
    · exact Or.inr (trace_or_up two hp ra h)
  have chain (w z h : ℕ) (wz : (gateAt C a).inputs = [w,z] ∨ (gateAt C a).inputs = [z,w])
      (hw : w < n+a) (hz : z < n+a) (hh : h < C.gates.length)
      (ho : (gateAt C h).op = .and) (hjunk : h ∈ junk G C)
      (rw : Relation.ReflTransGen (OrStep n C) w (n+h))
      (vh : val C (List.ofFn (pairInput p q)) (n+h) = true)
      (t : Fin n) (ht : t = p ∨ t = q) (rz : Relation.ReflTransGen (OrStep n C) z t.val) :
      dl (n+a) = true ∨ dp (n+a) = true := by
    obtain ⟨b,c,bc⟩ := List.length_eq_two.mp (two _ (gateAt_mem hh))
    have bm : b ∈ (gateAt C h).inputs := by simp [bc]
    have cm : c ∈ (gateAt C h).inputs := by simp [bc]
    have vb := (val_and (n := n) (by simp) hh ho).mp vh b bm
    have vc := (val_and (n := n) (by simp) hh ho).mp vh c cm
    obtain ⟨r,hr,rb⟩ := no_ands_below h hh ho hjunk vh b bm vb.1 vb.2
    obtain ⟨s,hs,rc⟩ := no_ands_below h hh ho hjunk vh c cm vc.1 vc.2
    have swap : (gateAt C a).inputs = [z,w] ∨ (gateAt C a).inputs = [w,z] := wz.symm
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact (badP (value_and_up _ ha ao wz hw hz
        (orStep_up (n := n) (by simp) rw (value_and_up _ hh ho (Or.inl bc) vb.1 vc.1 (pval _ rb) (pval _ rc))) (pval _ rz))).elim
    · exact Or.inl (trace_and_up hl ha ao swap (qdiff _ rz)
        (orStep_up (n := n) (by simp) rw (value_and_up _ hh ho (Or.inl bc) vb.1 vc.1 (pval _ rb) (pval _ rc))))
    · exact Or.inl (trace_and_up hl ha ao wz
        (trace_or_up two hl rw (trace_and_up hl hh ho (Or.inr bc) (qdiff _ rc) (pval _ rb))) (pval _ rz))
    · exact Or.inr (trace_and_up hp ha ao wz
        (trace_or_up two hp rw (trace_and_up hp hh ho (Or.inl bc) (pdiff _ rb) (qval _ rc))) (qval _ rz))
    · exact Or.inl (trace_and_up hl ha ao wz
        (trace_or_up two hl rw (trace_and_up hl hh ho (Or.inl bc) (qdiff _ rb) (pval _ rc))) (pval _ rz))
    · exact Or.inr (trace_and_up hp ha ao wz
        (trace_or_up two hp rw (trace_and_up hp hh ho (Or.inr bc) (pdiff _ rc) (qval _ rb))) (qval _ rz))
    · exact Or.inr (trace_and_up hp ha ao swap (pdiff _ rz)
        (orStep_up (n := n) (by simp) rw (value_and_up _ hh ho (Or.inl bc) vb.1 vc.1 (qval _ rb) (qval _ rc))))
    · exact (badQ (value_and_up _ ha ao wz hw hz
        (orStep_up (n := n) (by simp) rw (value_and_up _ hh ho (Or.inl bc) vb.1 vc.1 (qval _ rb) (qval _ rc))) (qval _ rz))).elim
  rcases operand_trace (C := C) p q u uval.2 with ⟨t,ht,rt⟩ | ⟨h,hh,hn,rh,vh⟩
  · rcases operand_trace (C := C) p q v vval.2 with ⟨s,hs,rs⟩ | ⟨h,hh,hn,rh,vh⟩
    · apply finish
      rcases ht with rfl | rfl <;> rcases hs with rfl | rfl
      · exact (badP (value_and_up _ ha ao (Or.inl uv) uval.1 vval.1 (pval _ rt) (pval _ rs))).elim
      · exact Or.inl (trace_and_up hl ha ao (Or.inr uv) (qdiff _ rs) (pval _ rt))
      · exact Or.inl (trace_and_up hl ha ao (Or.inl uv) (qdiff _ rt) (pval _ rs))
      · exact (badQ (value_and_up _ ha ao (Or.inl uv) uval.1 vval.1 (qval _ rt) (qval _ rs))).elim
    · obtain ⟨hj,ho,_⟩ := dirty_of a ha ao v vm vval.1 h hh hn rh
      exact finish (chain v u h (Or.inr uv) vval.1 uval.1 hh ho hj rh vh t ht rt)
  · obtain ⟨hj,ho,hnotbelow⟩ := dirty_of a ha ao u um uval.1 h hh hn rh
    rcases operand_trace (C := C) p q v vval.2 with ⟨s,hs,rs⟩ | ⟨k,hk,kn,rk,vk⟩
    · exact finish (chain u v h (Or.inl uv) uval.1 vval.1 hh ho hj rh vh s hs rs)
    · obtain ⟨kj,_,_⟩ := dirty_of a ha ao v vm vval.1 k hk kn rk
      have eq := uniq k kj vk h hj vh
      subst k
      exfalso
      apply hnotbelow
      intro x hx
      apply below x
      exact value_and_up x ha ao (Or.inl uv) uval.1 vval.1
        (orStep_up (n := n) (by simp) rh hx) (orStep_up (n := n) (by simp) rk hx)

end PEqualNP.Outside.L_meta_2602_aux.OneJunkActive

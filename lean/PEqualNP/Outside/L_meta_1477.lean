import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.OneJunk

namespace P1

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

open PEqualNP.TopForm in
lemma off_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C) (u v : Fin n)
    (huv : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
      gateVal n C a (pairInput u v) = true ∧
      OrReaches n C (opnd C a b) h ∧
      gateVal n C h (pairInput u v) = true := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [Ustar, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv
  obtain ⟨hadj, hns⟩ := huv
  have hF : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
    fun u v h => (graphFun_pair G u v).mp h
  have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
    fun x => congrFun hfun x
  obtain ⟨a, halen, hnor, hreach, hval⟩ :=
    edge_trace G (graphFun G ∅) hF hout u v ((graphFun_pair G u v).mpr hadj)
  have hop : (gateAt C a).op = GateOp.and := by
    rcases hAO _ (gateAt_mem halen) with h | h
    · exact h
    · exact (hnor h).elim
  have hbel : BelowF G C a := fun x hx => below_of_reach (graphFun G ∅) hout a hreach x hx
  have hatop : a ∈ tops G C := by
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨halen, hop, hbel⟩
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hpq := (val_and (n := n) (by simp) halen hop).mp hval
  have hp := hpq p (by rw [hin]; simp)
  have hq := hpq q (by rw [hin]; simp)
  have junk_of : ∀ (w : ℕ) (b : Fin 2), opnd C a b = w → w ∈ (gateAt C a).inputs → w < n + a →
      ∀ h, h < C.gates.length → (gateAt C h).op ≠ GateOp.or →
      Relation.ReflTransGen (OrStep n C) w (n + h) →
      val C (List.ofFn (pairInput u v)) (n + h) = true →
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
        gateVal n C a (pairInput u v) = true ∧
        OrReaches n C (opnd C a b) h ∧
        gateVal n C h (pairInput u v) = true := by
    intro w b hb hwin hwlt h hh hhor hr hv
    have hhand : (gateAt C h).op = GateOp.and := by
      rcases hAO _ (gateAt_mem hh) with h3 | h3
      · exact h3
      · exact (hhor h3).elim
    have hcone : InCone n C h a := operand_cone halen hwin hwlt hr
    have hnb : ¬ BelowF G C h := fun hb2 => hT h hh a halen hhand hb2 hop hcone
    have hdirty : IsDirtyAnd n G C h := by
      unfold IsDirtyAnd IsDirty
      refine ⟨hhand, hh, ?_⟩
      by_contra hne
      apply hnb
      intro x hx
      by_contra hfx
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
    have hjunk : h ∈ junk G C := by
      unfold junk gatesWhere
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
    refine ⟨a, hatop, b, h, hjunk, hval, ?_, hv⟩
    rw [hb]
    exact reach_orReaches hr h rfl hh
  rcases operand_trace (C := C) u v p hp.2 with ⟨t1, ht1, hr1⟩ | ⟨h, hh, hhor, hr, hv⟩
  · rcases operand_trace (C := C) u v q hq.2 with ⟨t2, ht2, hr2⟩ | ⟨h, hh, hhor, hr, hv⟩
    · exfalso
      apply hns
      have hadj12 : G.Adj t1 t2 :=
        side_adj G (graphFun G ∅) hF a halen hop hbel p q hin hp.1 hq.1 t1 t2 hr1 hr2
      have hne : t1 ≠ t2 := G.ne_of_adj hadj12
      have hs : s(u, v) = s(t1, t2) := by
        rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
        · exact (hne (h1.trans h2.symm)).elim
        · rw [h1, h2]
        · rw [h1, h2]; exact Sym2.eq_swap
        · exact (hne (h1.trans h2.symm)).elim
      rw [hs]
      simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
      refine ⟨a, hatop, (t1, t2), ⟨?_, ?_⟩, rfl⟩
      · simp only [side, e0]
        exact reach_mem_orIn t1 hr1
      · simp only [side, e1]
        exact reach_mem_orIn t2 hr2
    · exact junk_of q 1 e1 (by rw [hin]; simp) hq.1 h hh hhor hr hv
  · exact junk_of p 0 e0 (by rw [hin]; simp) hp.1 h hh hhor hr hv

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

end P1


lemma prev1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C →
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  intro n G _ C h4 hne hL hTF
  exact PEqualNP.Outside.L_meta_1477.OneJunk.P1.main n G C h4 hne hL hTF



namespace P2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma fin2_sub : ∀ b : Fin 2, (b = 0 ∧ 1 - b = 1) ∨ (b = 1 ∧ 1 - b = 0) := by decide

lemma fin2_ne : ∀ b c : Fin 2, c ≠ b → c = 1 - b := by decide

lemma fin2_ne' : ∀ b c : Fin 2, c ≠ b → 1 - c = b := by decide

lemma fin2_both (p : Fin 2 → Prop) (b : Fin 2) (h1 : p b) (h2 : p (1 - b)) : p 0 ∧ p 1 := by
  rcases fin2_sub b with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [h] at h1; rw [h'] at h2; exact ⟨h1, h2⟩
  · rw [h] at h1; rw [h'] at h2; exact ⟨h2, h1⟩

lemma count_fibres {α β : Type*} [DecidableEq α] [DecidableEq β] (T : Finset α) (c : α → β)
    (P : Finset β)
    (hP : ∀ u ∈ P, ∃ a ∈ T, ∃ a' ∈ T, a ≠ a' ∧ c a = u ∧ c a' = u) :
    (T.image c).card + P.card ≤ T.card := by
  have hsub : P ⊆ T.image c := by
    intro u hu
    obtain ⟨a, ha, _, _, _, rfl, _⟩ := hP u hu
    exact Finset.mem_image_of_mem c ha
  have h1 : T.card = ∑ k ∈ T.image c, (T.filter (fun a => c a = k)).card :=
    Finset.card_eq_sum_card_image c T
  have h2 : (T.image c).card + P.card = ∑ k ∈ T.image c, (1 + if k ∈ P then 1 else 0) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, ← Finset.card_filter]
    congr 2
    ext u
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hsub h, h⟩, fun h => h.2⟩
  rw [h1, h2]
  apply Finset.sum_le_sum
  intro k hk
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
  split_ifs with hkP
  · obtain ⟨a1, ha1, a2, ha2, hne, h1', h2'⟩ := hP _ hkP
    have : 1 < (T.filter (fun a' => c a' = c a)).card :=
      Finset.one_lt_card.mpr ⟨a1, by simp [ha1, h1'], a2, by simp [ha2, h2'], hne⟩
    omega
  · have : 0 < (T.filter (fun a' => c a' = c a)).card :=
      Finset.card_pos.mpr ⟨a, by simp [ha]⟩
    omega

lemma core {n : ℕ} (G : SimpleGraph (Fin n)) (tops centreless : Finset ℕ)
    (side : ℕ → Fin 2 → Finset (Fin n)) (R : ℕ → Fin 2 → Prop) (W : Finset (Fin n))
    (starEdges Ustar : Finset (Sym2 (Fin n)))
    (H1 : ∀ a ∈ tops, a ∈ centreless → (side a 0 = ∅ ∨ side a 1 = ∅))
    (H2 : ∀ a ∈ tops, (side a 0).card ≤ 1 ∨ (side a 1).card ≤ 1)
    (H3 : ∀ a ∈ tops, ¬ (R a 0 ∧ R a 1))
    (H4 : ∀ a ∈ tops, ∀ b : Fin 2, side a b = ∅ → R a b)
    (H5 : ∀ e ∈ starEdges, ∃ a ∈ tops, ∃ u ∈ side a 0, ∃ v ∈ side a 1, e = s(u, v))
    (H6 : ∀ u v, G.Adj u v → s(u, v) ∉ Ustar → s(u, v) ∈ starEdges)
    (H7 : ∀ a ∈ tops, ∀ (b : Fin 2) (u : Fin n), side a b = {u} → R a b →
      side a (1 - b) ⊆ W) :
    ∃ K : Finset (Fin n), (∀ e ∈ starEdges, ∃ v ∈ K, v ∈ e) ∧
      (∀ u, (∃ a ∈ tops, ∃ b : Fin 2, side a b = {u} ∧ R a b) → u ∈ K) ∧
      (∀ w, (∃ a ∈ tops, ∃ b : Fin 2, 2 ≤ (side a b).card ∧ R a b ∧ side a (1 - b) = {w}) →
        w ∈ K) ∧
      ∀ P : Finset (Fin n), (∀ u ∈ P, (∃ a ∈ tops, ∃ b : Fin 2, side a b = {u} ∧ R a b) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ Ustar ∧ v ∉ W ∧ v ∉ K) →
        K.card + P.card ≤ (tops \ centreless).card := by
  classical
  set T : Finset ℕ := tops.filter (fun a => (side a 0).Nonempty ∧ (side a 1).Nonempty) with hT
  have hTsub : T ⊆ tops \ centreless := by
    intro a ha
    obtain ⟨hat, h0, h1⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_sdiff.mpr ⟨hat, fun hac => ?_⟩
    rcases H1 a hat hac with h | h
    · rw [h] at h0; exact Finset.not_nonempty_empty h0
    · rw [h] at h1; exact Finset.not_nonempty_empty h1
  have memT : ∀ a ∈ tops, ∀ b : Fin 2, (side a b).Nonempty → (side a (1 - b)).Nonempty →
      a ∈ T := by
    intro a hat b h1 h2
    exact Finset.mem_filter.mpr ⟨hat, fin2_both (fun b => (side a b).Nonempty) b h1 h2⟩
  have hA : ∀ a ∈ tops, ∀ (b : Fin 2) (u : Fin n), side a b = {u} → R a b → a ∈ T := by
    intro a hat b u hs hr
    refine memT a hat b (by rw [hs]; exact Finset.singleton_nonempty u) ?_
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    exact H3 a hat (fin2_both (fun b => R a b) b hr (H4 a hat _ he))
  have hex : ∀ a : {a // a ∈ T}, ∃ x : Fin n,
      (∃ b : Fin 2, side a.1 b = {x}) ∧
        ∀ (b : Fin 2) (u : Fin n), side a.1 b = {u} → R a.1 b → u = x := by
    rintro ⟨a, ha⟩
    obtain ⟨hat, h0, h1⟩ := Finset.mem_filter.mp ha
    by_cases hf : ∃ (b : Fin 2) (u : Fin n), side a b = {u} ∧ R a b
    · obtain ⟨b, u, hs, hr⟩ := hf
      refine ⟨u, ⟨b, hs⟩, ?_⟩
      intro b' u' hs' hr'
      by_cases hbb : b' = b
      · subst hbb
        rw [hs] at hs'
        exact (Finset.singleton_injective hs').symm
      · exfalso
        have := fin2_ne b b' hbb
        subst this
        exact H3 a hat (fin2_both (fun b => R a b) b hr hr')
    · rcases H2 a hat with h | h
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (le_antisymm h (Finset.card_pos.mpr h0))
        exact ⟨x, ⟨0, hx⟩, fun b u hs hr => absurd ⟨b, u, hs, hr⟩ hf⟩
      · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (le_antisymm h (Finset.card_pos.mpr h1))
        exact ⟨x, ⟨1, hx⟩, fun b u hs hr => absurd ⟨b, u, hs, hr⟩ hf⟩
  choose c hc1 hc2 using hex
  have hcK : ∀ (a : ℕ) (ha : a ∈ T), c ⟨a, ha⟩ ∈ T.attach.image c := fun a ha =>
    Finset.mem_image_of_mem c (Finset.mem_attach T ⟨a, ha⟩)
  refine ⟨T.attach.image c, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, hat, u, hu, v, hv, rfl⟩ := H5 e he
    have haT : a ∈ T := Finset.mem_filter.mpr ⟨hat, ⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨c ⟨a, haT⟩, hcK a haT, ?_⟩
    obtain ⟨b, hb⟩ := hc1 ⟨a, haT⟩
    rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h] at hb
      have hu' : u ∈ ({c ⟨a, haT⟩} : Finset (Fin n)) := hb ▸ hu
      rw [Finset.mem_singleton.mp hu']
      exact Sym2.mem_mk_left _ _
    · rw [h] at hb
      have hv' : v ∈ ({c ⟨a, haT⟩} : Finset (Fin n)) := hb ▸ hv
      rw [Finset.mem_singleton.mp hv']
      exact Sym2.mem_mk_right _ _
  · rintro u ⟨a, hat, b, hs, hr⟩
    have haT := hA a hat b u hs hr
    rw [hc2 ⟨a, haT⟩ b u hs hr]
    exact hcK a haT
  · rintro w ⟨a, hat, b, h2, hr, hs⟩
    have haT : a ∈ T := memT a hat b (Finset.card_pos.mp (by omega))
      (by rw [hs]; exact Finset.singleton_nonempty w)
    obtain ⟨b', hb'⟩ := hc1 ⟨a, haT⟩
    have hbb : b' ≠ b := by
      rintro rfl
      rw [hb', Finset.card_singleton] at h2
      omega
    rw [fin2_ne b b' hbb, hs] at hb'
    rw [Finset.singleton_injective hb']
    exact hcK a haT
  · intro P hP
    have hcount := count_fibres T.attach c P ?_
    · rw [Finset.card_attach] at hcount
      exact le_trans hcount (Finset.card_le_card hTsub)
    intro u hu
    obtain ⟨⟨a, hat, b, hs, hr⟩, v, hadj, hU, hvW, hvK⟩ := hP u hu
    have haT := hA a hat b u hs hr
    obtain ⟨a', hat', u', hu', v', hv', heq⟩ := H5 _ (H6 u v hadj hU)
    have haT' : a' ∈ T := Finset.mem_filter.mpr ⟨hat', ⟨u', hu'⟩, ⟨v', hv'⟩⟩
    have hc0 : ∃ c0 : Fin 2, u ∈ side a' c0 ∧ v ∈ side a' (1 - c0) := by
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, hu', hv'⟩
      · exact ⟨1, hv', hu'⟩
    obtain ⟨c0, hu0, hv0⟩ := hc0
    have hne : a ≠ a' := by
      rintro rfl
      by_cases hcb : c0 = b
      · subst hcb
        exact hvW (H7 a hat c0 u hs hr hv0)
      · rw [fin2_ne' b c0 hcb, hs] at hv0
        rw [Finset.mem_singleton.mp hv0] at hadj
        exact G.irrefl hadj
    refine ⟨⟨a, haT⟩, Finset.mem_attach _ _, ⟨a', haT'⟩, Finset.mem_attach _ _,
      fun h => hne (congrArg Subtype.val h), (hc2 ⟨a, haT⟩ b u hs hr).symm, ?_⟩
    obtain ⟨b'', hb''⟩ := hc1 ⟨a', haT'⟩
    by_cases hcb : b'' = c0
    · subst hcb
      rw [hb''] at hu0
      exact (Finset.mem_singleton.mp hu0).symm
    · exfalso
      rw [fin2_ne c0 b'' hcb] at hb''
      rw [hb''] at hv0
      rw [Finset.mem_singleton.mp hv0] at hvK
      exact hvK (hcK a' haT')

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

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

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

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
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

open PEqualNP.EdgeOwnership in
lemma inCone_c1 (n : ℕ) (C : Circuit) (hA : AO n C) (i k : ℕ) (hk : k < C.gates.length)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩

open PEqualNP.EdgeOwnership in
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

def OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs

def OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)

def Leaf (n : ℕ) (C : Circuit) (v : ℕ) : Prop :=
  v < n ∨ ∃ h, v = n + h ∧ h < C.gates.length ∧ (gateAt C h).op = GateOp.and

lemma orStep_lt (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrStep n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

lemma orR_le (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrR n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt n C hA _ _ h2; omega

lemma orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]

lemma orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih

lemma orR_leaf_true (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) :
    ∀ u, u < n + C.gates.length → W n C x u = true →
      ∃ v, OrR n C u v ∧ Leaf n C v ∧ W n C x v = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hx
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1, hx⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩, hx⟩
      · rw [W_or n C x k hk hop a b hab ha hb] at hx
        simp only [Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih a ha (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih b hb (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩

lemma orR_leaf (n : ℕ) (C : Circuit) (hA : AO n C) :
    ∀ u, u < n + C.gates.length → ∃ v, OrR n C u v ∧ Leaf n C v := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩⟩
      · obtain ⟨v, hv1, hv2⟩ := ih a ha (by omega)
        exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2⟩

open PEqualNP.EdgeOwnership in
lemma orR_cone (n : ℕ) (C : Circuit) (hA : AO n C) (h u : ℕ) (hr : OrR n C u (n + h)) :
    ∀ k, u = n + k → k < C.gates.length → h = k ∨ InCone n C h k := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => intro k hk _; left; omega
  | head h1 h2 ih =>
    rename_i u c
    intro k hk hlen
    have hle := orR_le n C hA _ _ h2
    have hlt := orStep_lt n C hA _ _ h1
    obtain ⟨k', hk', _, _, hin⟩ := h1
    have hkk : k' = k := by omega
    subst hkk
    have hc : c = n + (c - n) := by omega
    rcases ih (c - n) hc (by omega) with h3 | h3
    · right
      refine inCone_c1 n C hA h k' hlen ?_
      rw [h3, ← hc]
      exact hin
    · right
      refine inCone_c2 n C hA h (c - n) k' hlen h3 ?_
      rw [← hc]
      exact hin

lemma orIn_bridge (n : ℕ) (C : Circuit) (hA : AO n C) (f : ℕ → Finset (Fin n))
    (h0 : ∀ w, w < n → ∀ u : Fin n, u ∈ f w ↔ u.val = w)
    (hor : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ u : Fin n, u ∈ f (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, u ∈ f w)
    (hand : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and → f (n + k) = ∅) :
    ∀ w, w < n + C.gates.length → ∀ u : Fin n, u ∈ f w ↔ OrR n C w u.val := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw u
    by_cases h1 : w < n
    · rw [h0 w h1 u]
      constructor
      · intro h; rw [h]; exact Relation.ReflTransGen.refl
      · intro h
        rcases Relation.ReflTransGen.cases_head h with h2 | ⟨c, ⟨k, hk, _⟩, _⟩
        · exact h2.symm
        · omega
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      have hlt : ∀ c ∈ (gateAt C k).inputs, c < n + k := by
        intro c hc
        rw [hab] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        omega
      rcases hop with hop | hop
      · rw [hand k hk hop]
        constructor
        · intro h; simp at h
        · intro h
          rcases Relation.ReflTransGen.cases_head h with h2 | ⟨c, ⟨k', hk', _, hop', _⟩, _⟩
          · have := u.isLt; omega
          · have : k' = k := by omega
            subst this
            rw [hop] at hop'
            exact absurd hop' (by simp)
      · rw [hor k hk hop u]
        constructor
        · rintro ⟨c, hc, hu⟩
          have h3 := (ih c (hlt c hc) (by have := hlt c hc; omega) u).mp hu
          exact Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hc⟩ h3
        · intro h
          rcases Relation.ReflTransGen.cases_head h with h2 | ⟨c, ⟨k', hk', _, _, hc⟩, h3⟩
          · have := u.isLt; omega
          · have : k' = k := by omega
            subst this
            exact ⟨c, hc, (ih c (hlt c hc) (by have := hlt c hc; omega) u).mpr h3⟩


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

lemma opnd_lt (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) : ∀ b : Fin 2, o b < n + a := by
  obtain ⟨_, a1, b1, hab, ha1, hb1⟩ := hA a ha
  rw [hin] at hab
  simp only [List.cons.injEq, and_true] at hab
  intro b
  rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega

lemma top_true (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (x : Fin n → Bool)
    (h : ∀ b : Fin 2, W n C x (o b) = true) : W n C x (n + a) = true := by
  have hlt := opnd_lt n C hA a ha o hin
  rw [W_and n C x a ha hop (o 0) (o 1) hin (hlt 0) (hlt 1), h 0, h 1]
  rfl

lemma sem_both (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (g : ℕ)
    (h0 : OrR n C (o 0) (n + g)) (h1 : OrR n C (o 1) (n + g)) (x : Fin n → Bool)
    (hx : W n C x (n + g) = true) : W n C x (n + a) = true := by
  apply top_true n C hA a ha hop o hin x
  intro b
  rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · exact orR_mono n C hA x _ _ h0 hx
  · exact orR_mono n C hA x _ _ h1 hx

lemma sem_mixed (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (g : ℕ) (b : Fin 2) (w : Fin n)
    (hb : OrR n C (o b) (n + g)) (hw : OrR n C (o (1 - b)) w.val) (x : Fin n → Bool)
    (hx : W n C x (n + g) = true) (hxw : x w = true) : W n C x (n + a) = true := by
  have hww : W n C x w.val = true := by
    rw [W_input n C x w.val w.isLt]; exact hxw
  apply top_true n C hA a ha hop o hin x
  intro b'
  by_cases hbb : b' = b
  · rw [hbb]; exact orR_mono n C hA x _ _ hb hx
  · rw [fin2_ne b b' hbb]; exact orR_mono n C hA x _ _ hw hww

open PEqualNP.EdgeOwnership in
lemma sem_adj (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (u v : Fin n)
    (hu : OrR n C (o 0) u.val) (hv : OrR n C (o 1) v.val) :
    W n C (pairInput u v) (n + a) = true := by
  apply top_true n C hA a ha hop o hin
  intro b
  rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · refine orR_mono n C hA _ _ _ hu ?_
    rw [W_input n C _ u.val u.isLt]; simp [pairInput]
  · refine orR_mono n C hA _ _ _ hv ?_
    rw [W_input n C _ v.val v.isLt]; simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma opnd_leaf (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (b : Fin 2) :
    (∃ w : Fin n, OrR n C (o b) w.val) ∨
      ∃ h, h < C.gates.length ∧ (gateAt C h).op = GateOp.and ∧ OrR n C (o b) (n + h) ∧
        InCone n C h a := by
  have hlt := opnd_lt n C hA a ha o hin b
  obtain ⟨v, hv1, hv2⟩ := orR_leaf n C hA (o b) (by omega)
  rcases hv2 with hv | ⟨h, rfl, hh, hhop⟩
  · exact Or.inl ⟨⟨v, hv⟩, hv1⟩
  · right
    refine ⟨h, hh, hhop, hv1, ?_⟩
    have hle := orR_le n C hA _ _ hv1
    have hu' : o b = n + (o b - n) := by omega
    have hmem : o b ∈ (gateAt C a).inputs := by
      rw [hin]
      rcases fin2_sub b with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] <;> simp
    rcases orR_cone n C hA h (o b) hv1 (o b - n) hu' (by omega) with h3 | h3
    · refine inCone_c1 n C hA h a ha ?_
      rw [h3, ← hu']; exact hmem
    · refine inCone_c2 n C hA h (o b - n) a ha h3 ?_
      rw [← hu']; exact hmem

open PEqualNP.EdgeOwnership in
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

lemma main_abs (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hA : AO n C)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (tops centreless : Finset ℕ) (g : ℕ)
    (htops : ∀ a ∈ tops, a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∀ x : Fin n → Bool, W n C x (n + a) = true → graphFun G ∅ x = true)
    (hg : ¬ ∀ x : Fin n → Bool, W n C x (n + g) = true → graphFun G ∅ x = true)
    (hleaf : ∀ a ∈ tops, ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and →
      PEqualNP.EdgeOwnership.InCone n C h a → h = g)
    (o : ℕ → Fin 2 → ℕ) (hin : ∀ a ∈ tops, (gateAt C a).inputs = [o a 0, o a 1])
    (side : ℕ → Fin 2 → Finset (Fin n))
    (hside : ∀ a ∈ tops, ∀ (b : Fin 2) (u : Fin n), u ∈ side a b ↔ OrR n C (o a b) u.val)
    (R : ℕ → Fin 2 → Prop)
    (hR : ∀ a ∈ tops, ∀ b : Fin 2, R a b ↔ OrR n C (o a b) (n + g))
    (Wm : Finset (Fin n))
    (hW : ∀ w : Fin n, (∀ x : Fin n → Bool, W n C x (n + g) = true → x w = true →
      graphFun G ∅ x = true) → w ∈ Wm)
    (starEdges Ustar : Finset (Sym2 (Fin n)))
    (H1 : ∀ a ∈ tops, a ∈ centreless → (side a 0 = ∅ ∨ side a 1 = ∅))
    (H5 : ∀ e ∈ starEdges, ∃ a ∈ tops, ∃ u ∈ side a 0, ∃ v ∈ side a 1, e = s(u, v))
    (H6 : ∀ u v, G.Adj u v → s(u, v) ∉ Ustar → s(u, v) ∈ starEdges) :
    ∃ K : Finset (Fin n), (∀ e ∈ starEdges, ∃ v ∈ K, v ∈ e) ∧
      (∀ u, (∃ a ∈ tops, ∃ b : Fin 2, side a b = {u} ∧ R a b) → u ∈ K) ∧
      (∀ w, (∃ a ∈ tops, ∃ b : Fin 2, 2 ≤ (side a b).card ∧ R a b ∧ side a (1 - b) = {w}) →
        w ∈ K) ∧
      ∀ P : Finset (Fin n), (∀ u ∈ P, (∃ a ∈ tops, ∃ b : Fin 2, side a b = {u} ∧ R a b) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ Ustar ∧ v ∉ Wm ∧ v ∉ K) →
        K.card + P.card ≤ (tops \ centreless).card := by
  refine core G tops centreless side R Wm starEdges Ustar H1 ?_ ?_ ?_ H5 H6 ?_
  · intro a hat
    obtain ⟨ha, hop, hbel⟩ := htops a hat
    refine biclique_star G h4 (side a 0) (side a 1) ?_
    intro u hu v hv
    rw [← graphFun_pair G u v]
    exact hbel _ (sem_adj n C hA a ha hop (o a) (hin a hat) u v
      ((hside a hat 0 u).mp hu) ((hside a hat 1 v).mp hv))
  · rintro a hat ⟨h0, h1⟩
    obtain ⟨ha, hop, hbel⟩ := htops a hat
    apply hg
    intro x hx
    exact hbel x (sem_both n C hA a ha hop (o a) (hin a hat) g
      ((hR a hat 0).mp h0) ((hR a hat 1).mp h1) x hx)
  · intro a hat b he
    obtain ⟨ha, hop, hbel⟩ := htops a hat
    rcases opnd_leaf n C hA a ha (o a) (hin a hat) b with ⟨w, hw⟩ | ⟨h, hh, hhop, hr, hc⟩
    · have : w ∈ side a b := (hside a hat b w).mpr hw
      rw [he] at this
      exact absurd this (Finset.notMem_empty w)
    · rw [hleaf a hat h hh hhop hc] at hr
      exact (hR a hat b).mpr hr
  · intro a hat b u _ hr w hw
    obtain ⟨ha, hop, hbel⟩ := htops a hat
    apply hW
    intro x hx hxw
    exact hbel x (sem_mixed n C hA a ha hop (o a) (hin a hat) g b w
      ((hR a hat b).mp hr) ((hside a hat (1 - b) w).mp hw) x hx hxw)

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma mem_filter' {α : Type*} (p : α → Prop) (inst : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := Finset.mem_filter

lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w, (w ∈ g.inputs ∧ n ≤ w ∧ w < n + cs.length) ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp [orStep, List.getD_eq_getElem?_getD, hop]
  · simp [orStep, List.getD_eq_getElem?_getD, hop]

lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

lemma orReaches_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ OrReaches n C w g) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : ∀ x, x ∈ (orSets n C).getD k [] ↔ x = k ∨ (gk.op = GateOp.or ∧
      ∃ w, (w ∈ gk.inputs ∧ n ≤ w ∧ w < n + k) ∧
        x ∈ (pre.foldl (orStep n) []).getD (w - n) []) := by
    intro x
    rw [hc, orFold_getD_lt n post _ k (by omega)]
    have h := orStep_mem_last n (pre.foldl (orStep n) []) gk x
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have e : n + k - n = k := by omega
  unfold OrReaches
  rw [e, h1 g]
  constructor
  · rintro ⟨_, h | ⟨hop, w, ⟨hw, hn, hlt⟩, h⟩⟩
    · exact Or.inl h
    · right
      refine ⟨hop, w, hw, hn, hlt, hn, ?_⟩
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro (h | ⟨hop, w, hw, hn, hlt, _, h⟩)
    · exact ⟨by omega, Or.inl h⟩
    · refine ⟨by omega, Or.inr ⟨hop, w, ⟨hw, hn, hlt⟩, ?_⟩⟩
      rw [← h2 (w - n) (by omega)]
      exact h

lemma orReaches_orR (n : ℕ) (C : Circuit) :
    ∀ w, w < n + C.gates.length → ∀ g, OrReaches n C w g → OrR n C w (n + g) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw g hr
    have hn : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (orReaches_iff n C g k hk).mp hr with h | ⟨hop, c, hc, hcn, hclt, hcr⟩
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hc⟩ (ih c hclt (by omega) g hcr)

lemma orR_orReaches (n : ℕ) (C : Circuit) (hA : AO n C) (g : ℕ) (hg : g < C.gates.length) :
    ∀ w, w < n + C.gates.length → OrR n C w (n + g) → OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hr
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, ⟨k, hk1, hk, hop, hc⟩, hcr⟩
    · rw [h]
      exact (orReaches_iff n C g g hg).mpr (Or.inl rfl)
    · subst hk1
      have hle := orR_le n C hA _ _ hcr
      have hclt : c < n + k := by
        obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
        rw [hab] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        omega
      exact (orReaches_iff n C g k hk).mpr
        (Or.inr ⟨hop, c, hc, by omega, hclt, ih c hclt (by omega) hcr⟩)

lemma mem_orIn (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (hw : w < n + C.gates.length)
    (u : Fin n) : u ∈ orIn n C w ↔ OrR n C w u.val := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hu⟩)
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail (orReaches_orR n C w hw k hr) ⟨k, rfl, hk, hop, hu⟩
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, hc, ⟨k, rfl, hk, hop, hu⟩⟩
    · left
      exact h1
    · right
      exact ⟨k, hk, orR_orReaches n C hA k hk w hw hc, hop, hu⟩

lemma ao_of (n : ℕ) (C : Circuit) (h : IsAO2 n C) : AO n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hlen _ hmem)
  exact ⟨hao _ hmem, a, b, hab, hrb k hk a (by rw [hab]; simp), hrb k hk b (by rw [hab]; simp)⟩

lemma opnd_eq (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length) :
    (gateAt C a).inputs = [opnd C a 0, opnd C a 1] := by
  obtain ⟨_, p, q, hpq, _, _⟩ := hA a ha
  simp [opnd, hpq]

lemma nfc (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : NoFourCycle G) :
    ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
  rintro a b c d hac hbd ⟨h1, h2, h3, h4⟩
  have h0 := h a c hac
  have h5 : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj c w).card :=
    Finset.one_lt_card.mpr ⟨b, by simp [h1, h2.symm], d, by simp [h4.symm, h3], hbd⟩
  omega

lemma final : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    ∃ K : Finset (Fin n), (∀ e ∈ PEqualNP.TopForm.starEdges G C, ∃ v ∈ K, v ∈ e) ∧
      (Finset.univ : Finset (Fin n)).filter (fun u => ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ⊆ K ∧
      (Finset.univ : Finset (Fin n)).filter (fun w => ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          2 ≤ (PEqualNP.TopForm.side (n := n) C a b).card ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g ∧
          PEqualNP.TopForm.side (n := n) C a (1 - b) = {w}) ⊆ K ∧
      K.card + ((Finset.univ : Finset (Fin n)).filter (fun u => (∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ PEqualNP.TopForm.Ustar G C ∧ v ∉ PEqualNP.TopForm.wmax G C g ∧ v ∉ K)).card ≤
        (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  intro n G _ C hNF _ hL hTF g hjunk
  have hA : AO n C := ao_of n C hL.1
  have hgj : g ∈ junk G C := by rw [hjunk]; exact Finset.mem_singleton_self g
  obtain ⟨-, hgop, hglen, xg, hxg1, hxg2⟩ := (mem_filter' _ _ _ _).mp hgj
  have htops : ∀ a ∈ tops G C, a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∀ x : Fin n → Bool, W n C x (n + a) = true → graphFun G ∅ x = true := by
    intro a ha
    have ha0 := (mem_filter' _ _ _ _).mp ha
    exact ⟨Finset.mem_range.mp ha0.1, ha0.2.1, ha0.2.2⟩
  have hleaf : ∀ a ∈ tops G C, ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and →
      InCone n C h a → h = g := by
    intro a ha h hh hhop hc
    obtain ⟨ha1, ha2, _⟩ := htops a ha
    by_contra hne
    have hbel : BelowF G C h := by
      intro x hx
      by_contra hf
      have hd : IsDirtyAnd n G C h := by
        unfold IsDirtyAnd IsDirty
        exact ⟨hhop, hh, x, hx, Bool.eq_false_iff.mpr hf⟩
      have hj : h ∈ junk G C := (mem_filter' _ _ _ _).mpr ⟨Finset.mem_range.mpr hh, hd⟩
      rw [hjunk] at hj
      exact hne (Finset.mem_singleton.mp hj)
    exact hTF h hh a ha1 hhop hbel ha2 hc
  have hg : ¬ ∀ x : Fin n → Bool, W n C x (n + g) = true → graphFun G ∅ x = true := by
    intro h
    have h6 := h xg hxg1
    rw [hxg2] at h6
    exact Bool.false_ne_true h6
  have hin : ∀ a ∈ tops G C, (gateAt C a).inputs = [opnd C a 0, opnd C a 1] :=
    fun a ha => opnd_eq n C hA a (htops a ha).1
  have hol : ∀ a ∈ tops G C, ∀ b : Fin 2, opnd C a b < n + C.gates.length := by
    intro a ha b
    have h7 := opnd_lt n C hA a (htops a ha).1 (fun b => opnd C a b) (hin a ha) b
    have h8 := (htops a ha).1
    omega
  have hside : ∀ a ∈ tops G C, ∀ (b : Fin 2) (u : Fin n),
      u ∈ side (n := n) C a b ↔ OrR n C (opnd C a b) u.val :=
    fun a ha b u => mem_orIn n C hA _ (hol a ha b) u
  have hR : ∀ a ∈ tops G C, ∀ b : Fin 2,
      OrReaches n C (opnd C a b) g ↔ OrR n C (opnd C a b) (n + g) :=
    fun a ha b => ⟨orReaches_orR n C _ (hol a ha b) g,
      orR_orReaches n C hA g hglen _ (hol a ha b)⟩
  have hW : ∀ w : Fin n, (∀ x : Fin n → Bool, W n C x (n + g) = true → x w = true →
      graphFun G ∅ x = true) → w ∈ wmax G C g :=
    fun w h => (mem_filter' _ _ _ _).mpr ⟨Finset.mem_univ w, h⟩
  have H1 : ∀ a ∈ tops G C, a ∈ centreless G C →
      (side (n := n) C a 0 = ∅ ∨ side (n := n) C a 1 = ∅) :=
    fun a _ hc => ((mem_filter' _ _ _ _).mp hc).2
  have H5 : ∀ e ∈ starEdges G C, ∃ a ∈ tops G C, ∃ u ∈ side (n := n) C a 0,
      ∃ v ∈ side (n := n) C a 1, e = s(u, v) := by
    intro e he
    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at he
    obtain ⟨a, ha, p, ⟨hp1, hp2⟩, rfl⟩ := he
    exact ⟨a, ha, p.1, hp1, p.2, hp2, rfl⟩
  have H6 : ∀ u v, G.Adj u v → s(u, v) ∉ Ustar G C → s(u, v) ∈ starEdges G C := by
    intro u v hadj hU
    by_contra hns
    exact hU (Finset.mem_sdiff.mpr
      ⟨SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hadj), hns⟩)
  obtain ⟨K, h1, h2, h3, h5⟩ := main_abs n G C hA (nfc n G hNF) (tops G C) (centreless G C) g
    htops hg hleaf (fun a b => opnd C a b) hin (fun a b => side (n := n) C a b) hside
    (fun a b => OrReaches n C (opnd C a b) g) hR (wmax G C g) hW (starEdges G C) (Ustar G C)
    H1 H5 H6
  refine ⟨K, h1, ?_, ?_, ?_⟩
  · intro u hu
    exact h2 u ((mem_filter' _ _ _ _).mp hu).2
  · intro w hw
    exact h3 w ((mem_filter' _ _ _ _).mp hw).2
  · exact h5 _ (fun u hu => ((mem_filter' _ _ _ _).mp hu).2)

end P2


lemma prev2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    ∃ K : Finset (Fin n), (∀ e ∈ PEqualNP.TopForm.starEdges G C, ∃ v ∈ K, v ∈ e) ∧
      (Finset.univ : Finset (Fin n)).filter (fun u => ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ⊆ K ∧
      (Finset.univ : Finset (Fin n)).filter (fun w => ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          2 ≤ (PEqualNP.TopForm.side (n := n) C a b).card ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g ∧
          PEqualNP.TopForm.side (n := n) C a (1 - b) = {w}) ⊆ K ∧
      K.card + ((Finset.univ : Finset (Fin n)).filter (fun u => (∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ PEqualNP.TopForm.Ustar G C ∧ v ∉ PEqualNP.TopForm.wmax G C g ∧ v ∉ K)).card ≤
        (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  exact PEqualNP.Outside.L_meta_1477.OneJunk.P2.final


end PEqualNP.Outside.L_meta_1477.OneJunk

namespace PEqualNP.Outside.L_meta_1477.OneJunk
lemma oneJunkBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    ∃ K : Finset (Fin n), (∀ e ∈ PEqualNP.TopForm.starEdges G C, ∃ v ∈ K, v ∈ e) ∧
      PEqualNP.TopForm.formU G C g ⊆ K ∧ PEqualNP.TopForm.formZ G C g ⊆ K ∧
      G.edgeFinset.card + K.card + (PEqualNP.TopForm.pen G C g K).card + 1 +
        (PEqualNP.TopForm.mixing G C).card + 2 * (PEqualNP.TopForm.centreless G C).card +
        (PEqualNP.TopForm.coneGates G C g).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 := by
  intro n G _ C h4 hE hL hT g hg
  obtain ⟨K, hcov, hU, hZ, hK⟩ := PEqualNP.Outside.L_meta_1477.OneJunk.prev2 n G C h4 hE hL hT g hg
  have h1 := (PEqualNP.Outside.L_meta_1477.OneJunk.prev1 n G C h4 hE hL hT).1
  have hsub1 : PEqualNP.TopForm.mixing G C ⊆ PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C := by
    intro m hm
    simp only [PEqualNP.TopForm.mixing, Finset.mem_filter] at hm
    refine Finset.mem_sdiff.mpr ⟨hm.1, fun hl => ?_⟩
    simp only [PEqualNP.TopForm.lam, Finset.mem_filter] at hl
    apply hm.2
    rw [Finset.nonempty_iff_ne_empty, Finset.nonempty_iff_ne_empty] at hl
    simp only [hl.2.1, hl.2.2.1]
  have hsub2 : PEqualNP.TopForm.coneGates G C g ⊆
      (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C) \ PEqualNP.TopForm.mixing G C :=
    Finset.filter_subset _ _
  have hc2 := Finset.card_le_card hsub2
  have hc3 := Finset.card_sdiff_add_card_eq_card hsub1
  have hj : (PEqualNP.TopForm.junk G C).card = 1 := by rw [hg]; rfl
  have hpen : (PEqualNP.TopForm.pen G C g K).card ≤
      ((Finset.univ : Finset (Fin n)).filter (fun u => (∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ PEqualNP.TopForm.Ustar G C ∧ v ∉ PEqualNP.TopForm.wmax G C g ∧ v ∉ K)).card := by
    apply Finset.card_le_card
    intro u hu
    simp only [PEqualNP.TopForm.pen, PEqualNP.TopForm.formU, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    exact hu
  refine ⟨K, hcov, ?_, ?_, ?_⟩
  · intro u hu
    apply hU
    simpa only [PEqualNP.TopForm.formU] using hu
  · intro w hw
    apply hZ
    simpa only [PEqualNP.TopForm.formZ] using hw
  · omega

end PEqualNP.Outside.L_meta_1477.OneJunk
namespace PEqualNP.Outside.L_meta_1477.OneJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma dirty_ancestor_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (a : ℕ) (ha : a ∈ tops G C) (h : ℕ) (hh : h < C.gates.length)
    (hhop : (gateAt C h).op = GateOp.and) (hc : InCone n C h a) : h = g := by
  have ha0 := (P2.mem_filter' _ _ _ _).mp ha
  have hbel : ¬ BelowF G C h :=
    fun hb => hT h hh a (Finset.mem_range.mp ha0.1) hhop hb ha0.2.1 hc
  have hd : IsDirtyAnd n G C h := by
    unfold IsDirtyAnd IsDirty
    refine ⟨hhop, hh, ?_⟩
    by_contra hn
    apply hbel
    intro x hx
    by_contra hfx
    exact hn ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
  have hm : h ∈ junk G C :=
    (P2.mem_filter' _ _ _ _).mpr ⟨Finset.mem_range.mpr hh, hd⟩
  rw [hg] at hm
  exact Finset.mem_singleton.mp hm

lemma top_not_both_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (g : ℕ) (hg : g ∈ junk G C)
    (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2)
    (hr : P2.OrR n C (opnd C a b) (n + g)) :
    ¬ P2.OrR n C (opnd C a (1 - b)) (n + g) := by
  intro hs
  have ha0 := (P2.mem_filter' _ _ _ _).mp ha
  have halen := Finset.mem_range.mp ha0.1
  obtain ⟨-, _, _, x, hx, hfx⟩ := (P2.mem_filter' _ _ _ _).mp hg
  have hboth : P2.OrR n C (opnd C a 0) (n + g) ∧
      P2.OrR n C (opnd C a 1) (n + g) :=
    P2.fin2_both (fun b => P2.OrR n C (opnd C a b) (n + g)) b hr hs
  have hv := P2.sem_both n C hA a halen ha0.2.1 (opnd C a)
    (P2.opnd_eq n C hA a halen) g hboth.1 hboth.2 x hx
  have ht := ha0.2.2 x hv
  rw [hfx] at ht
  exact Bool.false_ne_true ht

lemma top_pair_mask {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2)
    (hreach : OrReaches n C (opnd C a b) g) (u v : Fin n)
    (hfire : gateVal n C a (pairInput u v) = true)
    (hgf : gateVal n C g (pairInput u v) = true) :
    ∃ c : Fin n, c ∈ wmax G C g ∧ (c = u ∨ c = v) ∧
      gateVal n C g (pairInput u v) = true := by
  have hh : g ∈ junk G C := by rw [hg]; exact Finset.mem_singleton_self g
  have ha0 := (P2.mem_filter' _ _ _ _).mp ha
  have halen := Finset.mem_range.mp ha0.1
  have hin := P2.opnd_eq n C hA a halen
  have hlt := P2.opnd_lt n C hA a halen (opnd C a) hin
  have hbig (b : Fin 2) : opnd C a b < n + C.gates.length := (hlt b).trans (by omega)
  have hr := P2.orReaches_orR n C _ (hbig b) g hreach
  have hfire' : P2.W n C (pairInput u v) (n + a) = true := hfire
  rw [P2.W_and n C (pairInput u v) a halen ha0.2.1 _ _ hin (hlt 0) (hlt 1)] at hfire'
  have hvals : P2.W n C (pairInput u v) (opnd C a 0) = true ∧
      P2.W n C (pairInput u v) (opnd C a 1) = true := by
    simpa only [Bool.and_eq_true] using hfire'
  have hoppt : P2.W n C (pairInput u v) (opnd C a (1 - b)) = true := by
    rcases P2.fin2_sub b with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · simpa only [hc] using hvals.2
    · simpa only [hc] using hvals.1
  obtain ⟨w, hpath, hleaf, hw⟩ :=
    P2.orR_leaf_true n C hA (pairInput u v) _ (hbig (1 - b)) hoppt
  rcases hleaf with hwlt | ⟨h, rfl, hhlen, hhop⟩
  · let c : Fin n := ⟨w, hwlt⟩
    refine ⟨c, ?_, ?_, hgf⟩
    · apply (P2.mem_filter' _ _ _ _).mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro x hx hxc
      exact ha0.2.2 x (P2.sem_mixed n C hA a halen ha0.2.1 (opnd C a)
        hin g b c hr hpath x hx hxc)
    · rw [P2.W_input n C (pairInput u v) w hwlt] at hw
      simpa only [pairInput, decide_eq_true_eq] using hw
  · have hcone : InCone n C h a := by
      have hle := P2.orR_le n C hA _ _ hpath
      have hu' : opnd C a (1 - b) = n + (opnd C a (1 - b) - n) := by omega
      have hmem : opnd C a (1 - b) ∈ (gateAt C a).inputs := by
        rw [hin]
        rcases P2.fin2_sub b with ⟨_, hc⟩ | ⟨_, hc⟩ <;> rw [hc] <;> simp
      rcases P2.orR_cone n C hA h _ hpath _ hu' (by have := hlt (1 - b); omega) with he | he
      · refine P2.inCone_c1 n C hA h a halen ?_
        rw [he, ← hu']
        exact hmem
      · refine P2.inCone_c2 n C hA h _ a halen he ?_
        rw [← hu']
        exact hmem
    have he := dirty_ancestor_eq G C hT g hg a ha h hhlen hhop hcone
    subst h
    exact (top_not_both_junk G C hA g hh a ha b hr hpath).elim

lemma off_star_mask {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (u v : Fin n) (huv : s(u, v) ∈ Ustar G C) :
    ∃ c : Fin n, c ∈ wmax G C g ∧ (c = u ∨ c = v) ∧
      gateVal n C g (pairInput u v) = true := by
  obtain ⟨a, ha, b, h, hh, hfire, hreach, hgf⟩ := P1.S90.off_star G C hL hT u v huv
  have heq : h = g := by rw [hg] at hh; exact Finset.mem_singleton.mp hh
  subst h
  exact top_pair_mask G C (P2.ao_of n C hL.1) hT g hg a ha b hreach u v hfire hgf

lemma operand_orR_inCone {n : ℕ} (C : Circuit) (hA : P2.AO n C)
    (a : ℕ) (ha : a < C.gates.length) (b : Fin 2) (h : ℕ)
    (hr : P2.OrR n C (opnd C a b) (n + h)) : InCone n C h a := by
  have hin := P2.opnd_eq n C hA a ha
  have hlt := P2.opnd_lt n C hA a ha (opnd C a) hin b
  have hle := P2.orR_le n C hA _ _ hr
  have he : opnd C a b = n + (opnd C a b - n) := by omega
  have hm : opnd C a b ∈ (gateAt C a).inputs := by
    rw [hin]
    rcases P2.fin2_sub b with ⟨hb, _⟩ | ⟨hb, _⟩ <;> rw [hb] <;> simp
  rcases P2.orR_cone n C hA h _ hr _ he (by omega) with hh | hh
  · apply P2.inCone_c1 n C hA h a ha
    rw [hh, ← he]
    exact hm
  · apply P2.inCone_c2 n C hA h _ a ha hh
    rw [← he]
    exact hm

lemma junk_operand_no_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C) (g : ℕ)
    (hg : junk G C = {g}) (b : Fin 2) (h : ℕ) (hh : h < C.gates.length)
    (hhop : (gateAt C h).op = GateOp.and) :
    ¬ P2.OrR n C (opnd C g b) (n + h) := by
  intro hr
  have hgj : g ∈ junk G C := by rw [hg]; exact Finset.mem_singleton_self g
  obtain ⟨-, hgop, hglen, _⟩ := (P2.mem_filter' _ _ _ _).mp hgj
  have hc := operand_orR_inCone C hA g hglen b h hr
  have hnot : ¬ BelowF G C h := fun hb => hT h hh g hglen hhop hb hgop hc
  have hdirty : IsDirtyAnd n G C h := by
    unfold IsDirtyAnd IsDirty
    refine ⟨hhop, hh, ?_⟩
    by_contra hn
    apply hnot
    intro x hx
    by_contra hfx
    exact hn ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
  have hj : h ∈ junk G C :=
    (P2.mem_filter' _ _ _ _).mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
  rw [hg] at hj
  have he : h = g := Finset.mem_singleton.mp hj
  subst h
  have hle := P2.orR_le n C hA _ _ hr
  have hlt := P2.opnd_lt n C hA g hglen (opnd C g) (P2.opnd_eq n C hA g hglen) b
  omega

lemma pure_wire_value {n : ℕ} (C : Circuit) (hA : P2.AO n C) (w : ℕ)
    (hw : w < n + C.gates.length)
    (hpure : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and →
      ¬ P2.OrR n C w (n + h)) (x : Fin n → Bool) :
    P2.W n C x w = decide (∃ u ∈ orIn n C w, x u = true) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  constructor
  · intro hx
    obtain ⟨v, hr, hleaf, hv⟩ := P2.orR_leaf_true n C hA x w hw hx
    rcases hleaf with hvn | ⟨h, rfl, hh, hhop⟩
    · refine ⟨⟨v, hvn⟩, (P2.mem_orIn n C hA w hw _).mpr hr, ?_⟩
      simpa only [P2.W_input n C x v hvn] using hv
    · exact (hpure h hh hhop hr).elim
  · rintro ⟨u, hu, hxu⟩
    apply P2.orR_mono n C hA x w u.val ((P2.mem_orIn n C hA w hw u).mp hu)
    rw [P2.W_input n C x u.val u.isLt]
    exact hxu

lemma junk_value_product {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C) (g : ℕ)
    (hg : junk G C = {g}) (x : Fin n → Bool) :
    gateVal n C g x =
      (decide (∃ u ∈ side (n := n) C g 0, x u = true) &&
        decide (∃ u ∈ side (n := n) C g 1, x u = true)) := by
  have hgj : g ∈ junk G C := by rw [hg]; exact Finset.mem_singleton_self g
  obtain ⟨-, hgop, hglen, _⟩ := (P2.mem_filter' _ _ _ _).mp hgj
  have hin := P2.opnd_eq n C hA g hglen
  have hlt := P2.opnd_lt n C hA g hglen (opnd C g) hin
  change P2.W n C x (n + g) = _
  rw [P2.W_and n C x g hglen hgop _ _ hin (hlt 0) (hlt 1)]
  have hp (b : Fin 2) : P2.W n C x (opnd C g b) =
      decide (∃ u ∈ side (n := n) C g b, x u = true) := by
    apply pure_wire_value C hA _ ((hlt b).trans (by omega))
    exact junk_operand_no_and G C hA hT g hg b
  rw [hp 0, hp 1]

lemma junk_sides_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C) (g : ℕ)
    (hg : junk G C = {g}) (b : Fin 2) : (side (n := n) C g b).Nonempty := by
  have hgj : g ∈ junk G C := by rw [hg]; exact Finset.mem_singleton_self g
  obtain ⟨-, _, hglen, _⟩ := (P2.mem_filter' _ _ _ _).mp hgj
  have hlt := P2.opnd_lt n C hA g hglen (opnd C g) (P2.opnd_eq n C hA g hglen) b
  have hbig : opnd C g b < n + C.gates.length := hlt.trans (by omega)
  obtain ⟨v, hr, hleaf⟩ := P2.orR_leaf n C hA _ hbig
  rcases hleaf with hv | ⟨h, rfl, hh, hhop⟩
  · exact ⟨⟨v, hv⟩, (P2.mem_orIn n C hA _ hbig _).mpr hr⟩
  · exact (junk_operand_no_and G C hA hT g hg b h hh hhop hr).elim

lemma orIn_subset_of_orR {n : ℕ} (C : Circuit) (hA : P2.AO n C)
    (w z : ℕ) (hw : w < n + C.gates.length) (hz : z < n + C.gates.length)
    (hr : P2.OrR n C w z) : orIn n C z ⊆ orIn n C w := by
  intro u hu
  apply (P2.mem_orIn n C hA w hw u).mpr
  exact hr.trans ((P2.mem_orIn n C hA z hz u).mp hu)

lemma pure_gate_support_large {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (k : ℕ) (hk : k < C.gates.length)
    (hpure : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and →
      ¬ P2.OrR n C (n + k) (n + h)) : 2 ≤ (orIn n C (n + k)).card := by
  have hA := P2.ao_of n C hL.1
  have hbig : n + k < n + C.gates.length := by omega
  have hne : (orIn n C (n + k)).Nonempty := by
    obtain ⟨v, hr, hleaf⟩ := P2.orR_leaf n C hA _ hbig
    rcases hleaf with hv | ⟨h, rfl, hh, hhop⟩
    · exact ⟨⟨v, hv⟩, (P2.mem_orIn n C hA _ hbig _).mpr hr⟩
    · exact (hpure h hh hhop hr).elim
  by_contra hsmall
  have hcard : (orIn n C (n + k)).card = 1 := by
    have hc := Finset.card_pos.mpr hne
    omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hcard
  have hleast : P1.S98.Least n C :=
    ⟨P1.S98.AO_of_IsAO2 n C hL.1, fun D hD hfun =>
      hL.2.2 D (P1.S98.IsAO2_of_AO n D hD)
        (funext fun x => (hfun x).trans (congrFun hL.2.1 x))⟩
  obtain ⟨x, hneq⟩ := P1.S98.least_nodup n C hleast u.val k (by have := u.isLt; omega) hk
  have hval : P2.W n C x (n + k) = x u := by
    rw [pure_wire_value C hA _ hbig hpure x, hu]
    simp
  change P2.W n C x u.val ≠ P2.W n C x (n + k) at hneq
  rw [P2.W_input n C x u.val u.isLt, hval] at hneq
  exact hneq rfl

lemma lambda_support_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (k : ℕ) (hk : k ∈ lam G C) (a : Fin n)
    (hadj : ∀ v ∈ orIn n C (n + k), G.Adj a v)
    (hlarge : 2 ≤ (orIn n C (n + k)).card) :
    ∀ v ∈ orIn n C (n + k), s(a, v) ∈ starEdges G C := by
  obtain ⟨hkN, _, _, t, ht, b, hb, hr⟩ := (P2.mem_filter' _ _ _ _).mp hk
  have hklen : k < C.gates.length := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp hkN).1
  have htlen : t < C.gates.length := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp ht).1
  have hA := P2.ao_of n C hL.1
  have htl := P2.opnd_lt n C hA t htlen (opnd C t) (P2.opnd_eq n C hA t htlen) b
  have htbig : opnd C t b < n + C.gates.length := htl.trans (by omega)
  have hkr := P2.orReaches_orR n C _ htbig k hr
  have hsub : orIn n C (n + k) ⊆ side (n := n) C t b :=
    orIn_subset_of_orR C hA _ _ htbig (by omega) hkr
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hb
  have hcadj : ∀ v ∈ orIn n C (n + k), G.Adj c v := by
    intro v hv
    have hcside : c ∈ side (n := n) C t (1 - b) := by rw [hc]; simp
    have hvside := hsub hv
    have hf := (P1.S90.top_facts G C hG hL t ht).2.1
    rcases P2.fin2_sub b with ⟨hb0, hb1⟩ | ⟨hb0, hb1⟩
    · rw [hb0] at hvside
      rw [hb1] at hcside
      exact (hf v hvside c hcside).symm
    · rw [hb0] at hvside
      rw [hb1] at hcside
      exact hf c hcside v hvside
  have hac : a = c := by
    by_contra hne
    have hs : orIn n C (n + k) ⊆ Finset.univ.filter (fun v => G.Adj a v ∧ G.Adj c v) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj v hv, hcadj v hv⟩
    have hbound := (Finset.card_le_card hs).trans (hG a c hne)
    omega
  subst c
  intro v hv
  have hav : a ∈ side (n := n) C t (1 - b) := by rw [hc]; simp
  have hvside := hsub hv
  apply Finset.mem_biUnion.mpr
  refine ⟨t, ht, ?_⟩
  rcases P2.fin2_sub b with ⟨hb0, hb1⟩ | ⟨hb0, hb1⟩
  · rw [hb0] at hvside
    rw [hb1] at hav
    exact Finset.mem_image.mpr ⟨(v, a), Finset.mem_product.mpr ⟨hvside, hav⟩, Sym2.eq_swap⟩
  · rw [hb0] at hvside
    rw [hb1] at hav
    exact Finset.mem_image.mpr ⟨(a, v), Finset.mem_product.mpr ⟨hav, hvside⟩, rfl⟩

end PEqualNP.Outside.L_meta_1477.OneJunk

namespace PEqualNP.Outside.L_meta_1477.ResidualCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_1477.OneJunk

lemma residual_side_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (g : ℕ) (hg : g < C.gates.length) (b : Fin 2) (c : Fin n)
    (hadj : ∀ v ∈ side (n := n) C g b, G.Adj c v) :
    ∃ Q : Finset ℕ, Q ⊆ coneGates G C g ∧
      (∀ k ∈ Q, (orIn n C (n + k)).Nonempty ∧
        orIn n C (n + k) ⊆ side (n := n) C g b) ∧
      (((side (n := n) C g b).image (fun v => s(c, v))) \ starEdges G C).card ≤ Q.card + 1 := by
  classical
  have hRB := hL.1.2.1
  have h2 := hL.1.2.2
  have hlen : ∀ k, (gateAt C k).op = GateOp.or → (gateAt C k).inputs.length ≤ 2 := by
    intro k _
    by_cases hk : k < C.gates.length
    · rw [h2 _ (P1.S90.gateAt_mem hk)]
    · rw [P1.gateAt_ge (by omega)]
      simp
  have hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k := by
    intro k i hi
    by_cases hk : k < C.gates.length
    · exact hRB k hk i hi
    · rw [P1.gateAt_ge (by omega)] at hi
      simp at hi
  have hf2 : ∀ k, (gateAt C k).op = GateOp.or → ∀ u,
      u ∈ orIn n C (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, u ∈ orIn n C w := by
    intro k hop u
    rw [P1.orIn_gate]
    constructor
    · rintro ⟨_, _, w, hw, _, hu⟩
      exact ⟨w, hw, hu⟩
    · rintro ⟨w, hw, hu⟩
      have hk : k < C.gates.length := by
        by_contra hk
        rw [P1.gateAt_ge (by omega)] at hw
        simp at hw
      exact ⟨hk, hop, w, hw, hRB k hk w hw, hu⟩
  have hf3 : ∀ k, (gateAt C k).op ≠ GateOp.or → (orIn n C (n + k)).card ≤ 1 := by
    intro k hop
    rw [Finset.card_le_one]
    intro a ha
    exact absurd ((P1.orIn_gate C k a).1 ha).2.1 hop
  have hstop : ∀ k, k ∈ lam G C → orIn n C (n + k) ⊆ orIn n C (opnd C g b) →
      (∀ v ∈ orIn n C (n + k), s(c, v) ∈ starEdges G C) ∨
        (orIn n C (n + k)).card ≤ 1 := by
    intro k hk hsub
    by_cases hsmall : (orIn n C (n + k)).card ≤ 1
    · exact Or.inr hsmall
    · exact Or.inl (lambda_support_star G hG C hL k hk c
        (fun v hv => hadj v (hsub hv)) (by omega))
  obtain ⟨Q, hQlam, hQ, hcount⟩ := P1.top_step2 n (gateAt C) hlen hback
    (orIn n C) (P1.orIn_input C) hf2 hf3 (lam G C) (opnd C g b) c (starEdges G C) hstop
  have hroot : opnd C g b < n + C.gates.length :=
    (P1.opnd_lt h2 hRB hg b).trans (by omega)
  have hdetails (k : ℕ) (hk : k ∈ Q) : k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ P1.TwoNe (gateAt C) (orIn n C) k ∧
      OrReaches n C (opnd C g b) k ∧ orIn n C (n + k) ⊆ side (n := n) C g b := by
    obtain ⟨hop, htwo, hn, hr, hsub⟩ := hQ k hk
    have hrlen : opnd C g b - n < C.gates.length := by omega
    obtain ⟨hpath, hklen⟩ := P1.rtg_conv C hRB _ k hr hrlen
    have he : n + (opnd C g b - n) = opnd C g b := by omega
    rw [he] at hpath
    exact ⟨hklen, hop, htwo, P1.S90.reach_orReaches hpath k rfl hklen, hsub⟩
  refine ⟨Q, ?_, ?_, hcount⟩
  · intro k hk
    obtain ⟨hklen, hop, htwo, hr, hsub⟩ := hdetails k hk
    obtain ⟨hbel, hne0, hne1⟩ := P1.two_facts G C h2 hRB hklen hop htwo
    have hkN : k ∈ orN G C := by
      simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨hklen, hop, hbel⟩
    have hnlam : k ∉ lam G C := fun h => Finset.disjoint_left.mp hQlam h hk
    have hnmix : k ∉ mixing G C := by
      intro hm
      have hm' := (P2.mem_filter' _ _ _ _).mp hm
      exact hm'.2 (propext (iff_of_false hne0.ne_empty hne1.ne_empty))
    apply (P2.mem_filter' _ _ _ _).mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hkN, hnlam⟩, hnmix⟩, ?_⟩
    fin_cases b
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
  · intro k hk
    obtain ⟨hklen, hop, htwo, hr, hsub⟩ := hdetails k hk
    obtain ⟨w, hw, z, hz, hne, hwne, hzne⟩ := htwo
    obtain ⟨v, hv⟩ := hwne
    refine ⟨⟨v, ?_⟩, hsub⟩
    exact (hf2 k hop v).mpr ⟨w, hw, hv⟩

lemma disjoint_sides_residual_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (g : ℕ) (hg : g < C.gates.length) (a b : Fin n)
    (hdis : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (ha : ∀ v ∈ side (n := n) C g 1, G.Adj a v)
    (hb : ∀ v ∈ side (n := n) C g 0, G.Adj b v) :
    (((side (n := n) C g 0).image (fun v => s(b, v))) \ starEdges G C).card +
      (((side (n := n) C g 1).image (fun v => s(a, v))) \ starEdges G C).card ≤
      (coneGates G C g).card + 2 := by
  obtain ⟨Q0, hQ0, hprop0, hc0⟩ := residual_side_cone G hG C hL g hg 0 b hb
  obtain ⟨Q1, hQ1, hprop1, hc1⟩ := residual_side_cone G hG C hL g hg 1 a ha
  have hQQ : Disjoint Q0 Q1 := by
    apply Finset.disjoint_left.mpr
    intro k hk0 hk1
    obtain ⟨v, hv⟩ := (hprop0 k hk0).1
    exact Finset.disjoint_left.mp hdis ((hprop0 k hk0).2 hv) ((hprop1 k hk1).2 hv)
  have hc := Finset.card_le_card (Finset.union_subset hQ0 hQ1)
  rw [Finset.card_union_of_disjoint hQQ] at hc
  omega



lemma double_star_residual_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (A B : Finset (Fin n)) (a b : Fin n)
    (hab : a ≠ b) (ha : a ∈ A) (hb : b ∈ B)
    (hNA : ∀ v ∈ A, G.Adj b v) (hNB : ∀ v ∈ B, G.Adj a v)
    (hcover : Ustar G C ⊆ A.image (fun v => s(b, v)) ∪ B.image (fun v => s(a, v))) :
    ((A.image (fun v => s(b, v))) \ starEdges G C).card +
      ((B.image (fun v => s(a, v))) \ starEdges G C).card =
      (Ustar G C).card + if s(a, b) ∈ Ustar G C then 1 else 0 := by
  classical
  let R0 := (A.image (fun v => s(b, v))) \ starEdges G C
  let R1 := (B.image (fun v => s(a, v))) \ starEdges G C
  have hsub0 : R0 ⊆ Ustar G C := by
    intro e he
    obtain ⟨he, hn⟩ := Finset.mem_sdiff.mp he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr
      ((SimpleGraph.mem_edgeSet G).mpr (hNA v hv)), hn⟩
  have hsub1 : R1 ⊆ Ustar G C := by
    intro e he
    obtain ⟨he, hn⟩ := Finset.mem_sdiff.mp he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr
      ((SimpleGraph.mem_edgeSet G).mpr (hNB v hv)), hn⟩
  have huni : R0 ∪ R1 = Ustar G C := by
    apply Finset.Subset.antisymm (Finset.union_subset hsub0 hsub1)
    intro e he
    have hnot := (Finset.mem_sdiff.mp he).2
    rcases Finset.mem_union.mp (hcover he) with h0 | h1
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h0, hnot⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h1, hnot⟩)
  have hcenter0 : s(a, b) ∈ A.image (fun v => s(b, v)) :=
    Finset.mem_image.mpr ⟨a, ha, Sym2.eq_swap⟩
  have hcenter1 : s(a, b) ∈ B.image (fun v => s(a, v)) :=
    Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hsingle (e : Sym2 (Fin n)) (he : e ∈ R0 ∩ R1) : e = s(a, b) := by
    obtain ⟨h0, h1⟩ := Finset.mem_inter.mp he
    obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp h0).1
    obtain ⟨v, hv, hev⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp h1).1
    have heq : s(b, u) = s(a, v) := heu.trans hev.symm
    rcases Sym2.eq_iff.mp heq with ⟨hba, huv⟩ | ⟨hbv, hua⟩
    · exact (hab hba.symm).elim
    · rw [← heu, hua]
      exact Sym2.eq_swap
  have hinter : (R0 ∩ R1).card = if s(a, b) ∈ Ustar G C then 1 else 0 := by
    by_cases hc : s(a, b) ∈ Ustar G C
    · rw [ite_eq_left hc]
      have heq : R0 ∩ R1 = {s(a, b)} := by
        ext e
        constructor
        · intro he
          exact Finset.mem_singleton.mpr (hsingle e he)
        · intro he
          have heq := Finset.mem_singleton.mp he
          subst e
          have hn := (Finset.mem_sdiff.mp hc).2
          exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hcenter0, hn⟩,
            Finset.mem_sdiff.mpr ⟨hcenter1, hn⟩⟩
      rw [heq]
      simp
    · rw [ite_eq_right hc]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have heu := hsub0 (Finset.mem_inter.mp he).1
      rw [hsingle e he] at heu
      exact hc heu
  have hc := Finset.card_union_add_card_inter R0 R1
  rw [huni, hinter] at hc
  exact hc.symm

lemma disjoint_sides_ustar_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (g : ℕ) (hg : g < C.gates.length) (a b : Fin n)
    (hdis : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (ha : a ∈ side (n := n) C g 0) (hb : b ∈ side (n := n) C g 1)
    (hNA : ∀ v ∈ side (n := n) C g 0, G.Adj b v)
    (hNB : ∀ v ∈ side (n := n) C g 1, G.Adj a v)
    (hcover : Ustar G C ⊆ (side (n := n) C g 0).image (fun v => s(b, v)) ∪
      (side (n := n) C g 1).image (fun v => s(a, v))) :
    (Ustar G C).card + (if s(a, b) ∈ Ustar G C then 1 else 0) ≤
      (coneGates G C g).card + 2 := by
  have hab : a ≠ b := by
    intro h
    subst b
    exact Finset.disjoint_left.mp hdis ha hb
  rw [← double_star_residual_card G C _ _ a b hab ha hb hNA hNB hcover]
  exact disjoint_sides_residual_cone G hG C hL g hg a b hdis hNB hNA



lemma mask_side_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C) (g : ℕ)
    (hg : junk G C = {g}) (b : Fin 2) (c : Fin n) (hc : c ∈ wmax G C g)
    (hcs : c ∈ side (n := n) C g b) :
    ∀ v ∈ side (n := n) C g (1 - b), G.Adj c v := by
  intro v hv
  have hfire : gateVal n C g (pairInput c v) = true := by
    rw [junk_value_product G C hA hT g hg]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    fin_cases b
    · exact ⟨⟨c, hcs, by simp [pairInput]⟩, ⟨v, hv, by simp [pairInput]⟩⟩
    · exact ⟨⟨v, hv, by simp [pairInput]⟩, ⟨c, hcs, by simp [pairInput]⟩⟩
  have hgraph := ((P2.mem_filter' _ _ _ _).mp hc).2 (pairInput c v) hfire (by simp [pairInput])
  exact (P1.S90.graphFun_pair G c v).mp hgraph

lemma two_centers_mask_in_sides {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (a b : Fin n)
    (ha : a ∈ side (n := n) C g 0) (hb : b ∈ side (n := n) C g 1)
    (ham : a ∈ wmax G C g) (hbm : b ∈ wmax G C g)
    (hAcard : 2 ≤ (side (n := n) C g 0).card)
    (hBcard : 2 ≤ (side (n := n) C g 1).card)
    (c : Fin n) (hc : c ∈ wmax G C g)
    (hcs : c ∈ side (n := n) C g 0 ∪ side (n := n) C g 1) : c = a ∨ c = b := by
  rcases Finset.mem_union.mp hcs with hc0 | hc1
  · left
    by_contra hne
    have hca := mask_side_adj G C hA hT g hg 0 c hc hc0
    have haa := mask_side_adj G C hA hT g hg 0 a ham ha
    have hsub : side (n := n) C g 1 ⊆ Finset.univ.filter (fun v => G.Adj c v ∧ G.Adj a v) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca v hv, haa v hv⟩
    have hbnd := (Finset.card_le_card hsub).trans (hG c a hne)
    omega
  · right
    by_contra hne
    have hcb := mask_side_adj G C hA hT g hg 1 c hc hc1
    have hbb := mask_side_adj G C hA hT g hg 1 b hbm hb
    have hsub : side (n := n) C g 0 ⊆ Finset.univ.filter (fun v => G.Adj c v ∧ G.Adj b v) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcb v hv, hbb v hv⟩
    have hbnd := (Finset.card_le_card hsub).trans (hG c b hne)
    omega

lemma disjoint_product_pair_cross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C) (g : ℕ)
    (hg : junk G C = {g})
    (hdis : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (u v : Fin n) (hfire : gateVal n C g (pairInput u v) = true) :
    (u ∈ side (n := n) C g 0 ∧ v ∈ side (n := n) C g 1) ∨
      (v ∈ side (n := n) C g 0 ∧ u ∈ side (n := n) C g 1) := by
  rw [junk_value_product G C hA hT g hg] at hfire
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfire
  obtain ⟨⟨p, hp, hpu⟩, ⟨q, hq, hqv⟩⟩ := hfire
  simp only [pairInput, decide_eq_true_eq] at hpu hqv
  rcases hpu with rfl | rfl <;> rcases hqv with rfl | rfl
  · exact (Finset.disjoint_left.mp hdis hp hq).elim
  · exact Or.inl ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hq⟩
  · exact (Finset.disjoint_left.mp hdis hp hq).elim

lemma disjoint_two_centers_ustar_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (a b : Fin n)
    (hdis : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (ha : a ∈ side (n := n) C g 0) (hb : b ∈ side (n := n) C g 1)
    (ham : a ∈ wmax G C g) (hbm : b ∈ wmax G C g)
    (hAcard : 2 ≤ (side (n := n) C g 0).card)
    (hBcard : 2 ≤ (side (n := n) C g 1).card) :
    Ustar G C ⊆ (side (n := n) C g 0).image (fun v => s(b, v)) ∪
      (side (n := n) C g 1).image (fun v => s(a, v)) := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
    have hA := P2.ao_of n C hL.1
    obtain ⟨c, hc, hcv, hfire⟩ := off_star_mask G C hL hT g hg u v he
    have hcross := disjoint_product_pair_cross G C hA hT g hg hdis u v hfire
    have hcs : c ∈ side (n := n) C g 0 ∪ side (n := n) C g 1 := by
      rcases hcross with ⟨hu, hv⟩ | ⟨hv, hu⟩ <;> rcases hcv with rfl | rfl
      · exact Finset.mem_union_left _ hu
      · exact Finset.mem_union_right _ hv
      · exact Finset.mem_union_right _ hu
      · exact Finset.mem_union_left _ hv
    rcases two_centers_mask_in_sides G hG C hA hT g hg a b ha hb ham hbm
      hAcard hBcard c hc hcs with rfl | rfl
    · rcases hcv with rfl | rfl
      · rcases hcross with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
        · exact (Finset.disjoint_left.mp hdis ha hu).elim
      · rcases hcross with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · exact (Finset.disjoint_left.mp hdis ha hv).elim
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, hu, Sym2.eq_swap⟩)
    · rcases hcv with rfl | rfl
      · rcases hcross with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · exact (Finset.disjoint_left.mp hdis hu hb).elim
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      · rcases hcross with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, Sym2.eq_swap⟩)
        · exact (Finset.disjoint_left.mp hdis hv hb).elim

lemma disjoint_two_centers_cone_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (a b : Fin n)
    (hdis : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (ha : a ∈ side (n := n) C g 0) (hb : b ∈ side (n := n) C g 1)
    (ham : a ∈ wmax G C g) (hbm : b ∈ wmax G C g)
    (hAcard : 2 ≤ (side (n := n) C g 0).card)
    (hBcard : 2 ≤ (side (n := n) C g 1).card) :
    (Ustar G C).card + (if s(a, b) ∈ Ustar G C then 1 else 0) ≤
      (coneGates G C g).card + 2 := by
  have hgj : g ∈ junk G C := by rw [hg]; simp
  have hglen : g < C.gates.length := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp hgj).1
  exact disjoint_sides_ustar_cone G hG C hL g hglen a b hdis ha hb
    (mask_side_adj G C (P2.ao_of n C hL.1) hT g hg 1 b hbm hb)
    (mask_side_adj G C (P2.ao_of n C hL.1) hT g hg 0 a ham ha)
    (disjoint_two_centers_ustar_subset G hG C hL hT g hg a b hdis ha hb ham hbm hAcard hBcard)

end PEqualNP.Outside.L_meta_1477.ResidualCone

namespace PEqualNP.Outside.L_meta_1477.OneJunk
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma mixing_on_junk_path {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (g : ℕ) (hg : g ∈ junk G C)
    (w : ℕ) (hw : w < n + C.gates.length) (hr : P2.OrR n C w (n + g))
    (hne : (orIn n C w).Nonempty) : (mixing G C).Nonempty := by
  classical
  have hg0 := (P1.junk_iff G C g).mp hg
  have hge : orIn n C (n + g) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hu' := (P1.orIn_gate C g u).mp hu
    rw [hg0.2.1] at hu'
    cases hu'.2.1
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => rw [hge] at hne; exact hne.elim (fun u hu => (Finset.notMem_empty u hu).elim)
  | @head w c hs hr ih =>
    have hcw : c < w := P2.orStep_lt n C hA w c hs
    by_cases hc : orIn n C c = ∅
    · obtain ⟨k, rfl, hk, hop, hcin⟩ := hs
      have hin := P2.opnd_eq n C hA k hk
      obtain ⟨u, hu⟩ := hne
      obtain ⟨_, _, d, hdin, _, hud⟩ := (P1.orIn_gate C k u).mp hu
      have hxor : (orIn n C (opnd C k 0) = ∅) ≠ (orIn n C (opnd C k 1) = ∅) := by
        intro heq
        have hc01 : c = opnd C k 0 ∨ c = opnd C k 1 := by
          simpa only [hin, List.mem_cons, List.not_mem_nil, or_false] using hcin
        have hd01 : d = opnd C k 0 ∨ d = opnd C k 1 := by
          simpa only [hin, List.mem_cons, List.not_mem_nil, or_false] using hdin
        have hb : orIn n C (opnd C k 0) = ∅ ∧ orIn n C (opnd C k 1) = ∅ := by
          rcases hc01 with rfl | rfl
          · exact ⟨hc, Eq.mp heq hc⟩
          · exact ⟨Eq.mpr heq hc, hc⟩
        rcases hd01 with rfl | rfl
        · rw [hb.1] at hud
          exact Finset.notMem_empty _ hud
        · rw [hb.2] at hud
          exact Finset.notMem_empty _ hud
      have hkn : ¬ BelowF G C k := by
        intro hb
        apply hg0.2.2
        intro x hx
        apply hb x
        exact P2.orR_mono n C hA x _ _ (Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hcin⟩ hr) hx
      refine ⟨k, Finset.mem_filter.mpr ⟨?_, hxor⟩⟩
      simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨hk, hop, hkn⟩
    · exact ih (hcw.trans hw) (Finset.nonempty_iff_ne_empty.mpr hc)

lemma off_star_reader_overhead {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (u v : Fin n) (huv : s(u, v) ∈ Ustar G C) :
    1 ≤ (mixing G C).card + 2 * (centreless G C).card := by
  obtain ⟨a, ha, b, g, hg, _, hr, _⟩ := P1.S90.off_star G C hL hT u v huv
  by_cases he : side (n := n) C a b = ∅
  · have hac : a ∈ centreless G C := by
      apply Finset.mem_filter.mpr
      refine ⟨ha, ?_⟩
      rcases P2.fin2_sub b with ⟨hb, _⟩ | ⟨hb, _⟩
      · exact Or.inl (by simpa only [hb] using he)
      · exact Or.inr (by simpa only [hb] using he)
    have hpos := Finset.card_pos.mpr (show (centreless G C).Nonempty from ⟨a, hac⟩)
    omega
  · have hA := P2.ao_of n C hL.1
    have halen : a < C.gates.length := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp ha).1
    have hlt := P2.opnd_lt n C hA a halen (opnd C a) (P2.opnd_eq n C hA a halen) b
    have hbig : opnd C a b < n + C.gates.length := hlt.trans (by omega)
    have hpath := P2.orReaches_orR n C _ hbig g hr
    have hm := mixing_on_junk_path G C hA g hg _ hbig hpath
      (Finset.nonempty_iff_ne_empty.mpr he)
    have hpos := Finset.card_pos.mpr hm
    omega

end PEqualNP.Outside.L_meta_1477.OneJunk


namespace PEqualNP.Outside.L_meta_1477

def planeEdges : List (ℕ × ℕ) :=
  [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

lemma planeEdges_length : planeEdges.length = 105 := by decide

lemma planeEdges_nodup : planeEdges.Nodup := by decide


lemma planeEdges_bounds : ∀ e ∈ planeEdges, e.1 < 21 ∧ 21 ≤ e.2 ∧ e.2 < 42 := by
  decide

lemma planeEdges_card : planeEdges.toFinset.card = 105 := by
  rw [List.toFinset_card_of_nodup planeEdges_nodup, planeEdges_length]

def planeNeighbors (i : Fin 21) : Finset (Fin 21) :=
  Finset.univ.filter (fun j => (i.val, j.val + 21) ∈ planeEdges)

def planeRightNeighbors (j : Fin 21) : Finset (Fin 21) :=
  Finset.univ.filter (fun i => (i.val, j.val + 21) ∈ planeEdges)

lemma planeNeighbors_card (i : Fin 21) : (planeNeighbors i).card = 5 := by
  fin_cases i <;> decide

lemma planeRightNeighbors_card (j : Fin 21) : (planeRightNeighbors j).card = 5 := by
  fin_cases j <;> decide

lemma planeEdges_diagonal (i : Fin 21) : (i.val, i.val + 21) ∈ planeEdges := by
  fin_cases i <;> decide

lemma planeEdges_vertexCover_lower (s : Finset ℕ)
    (hcover : ∀ u v, (u, v) ∈ planeEdges → u ∈ s ∨ v ∈ s) :
    21 ≤ s.card := by
  let f : Fin 21 → ℕ := fun i => if i.val ∈ s then i.val else i.val + 21
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    dsimp [f] at hij
    split_ifs at hij <;> omega
  have hsub : Finset.univ.image f ⊆ s := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
    dsimp [f]
    split_ifs with hi
    · exact hi
    · exact (hcover i.val (i.val + 21) (planeEdges_diagonal i)).resolve_left hi
  calc
    21 = (Finset.univ : Finset (Fin 21)).card := by simp
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hf).symm
    _ ≤ s.card := Finset.card_le_card hsub

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma planeNeighbors_inter_card (i j : Fin 21) (h : i ≠ j) :
    (planeNeighbors i ∩ planeNeighbors j).card = 1 := by
  revert j
  fin_cases i <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma planeRightNeighbors_inter_card (i j : Fin 21) (h : i ≠ j) :
    (planeRightNeighbors i ∩ planeRightNeighbors j).card = 1 := by
  revert j
  fin_cases i <;> decide


lemma mem_planeNeighbors {i j : Fin 21} :
    j ∈ planeNeighbors i ↔ (i.val, j.val + 21) ∈ planeEdges := by
  simp [planeNeighbors]

lemma planeNeighbors_common_unique {i j a b : Fin 21} (hij : i ≠ j)
    (hai : a ∈ planeNeighbors i) (haj : a ∈ planeNeighbors j)
    (hbi : b ∈ planeNeighbors i) (hbj : b ∈ planeNeighbors j) : a = b := by
  have hc : (planeNeighbors i ∩ planeNeighbors j).card ≤ 1 := by
    rw [planeNeighbors_inter_card i j hij]
  exact Finset.card_le_one.mp hc a (Finset.mem_inter.mpr ⟨hai, haj⟩)
    b (Finset.mem_inter.mpr ⟨hbi, hbj⟩)

lemma planeEdges_no_rectangle {a b c d : ℕ} (hab : a ≠ b) (hcd : c ≠ d)
    (hac : (a, c) ∈ planeEdges) (had : (a, d) ∈ planeEdges)
    (hbc : (b, c) ∈ planeEdges) (hbd : (b, d) ∈ planeEdges) : False := by
  have hacb := planeEdges_bounds (a, c) hac
  have hadb := planeEdges_bounds (a, d) had
  have hbcb := planeEdges_bounds (b, c) hbc
  let aa : Fin 21 := ⟨a, hacb.1⟩
  let bb : Fin 21 := ⟨b, hbcb.1⟩
  let cc : Fin 21 := ⟨c - 21, by omega⟩
  let dd : Fin 21 := ⟨d - 21, by omega⟩
  have haab : aa ≠ bb := by
    intro h
    exact hab (congrArg Fin.val h)
  have hcc : cc ∈ planeNeighbors aa ∧ cc ∈ planeNeighbors bb := by
    constructor
    · apply mem_planeNeighbors.mpr
      change (a, c - 21 + 21) ∈ planeEdges
      simpa only [Nat.sub_add_cancel hacb.2.1] using hac
    · apply mem_planeNeighbors.mpr
      change (b, c - 21 + 21) ∈ planeEdges
      simpa only [Nat.sub_add_cancel hacb.2.1] using hbc
  have hdd : dd ∈ planeNeighbors aa ∧ dd ∈ planeNeighbors bb := by
    constructor
    · apply mem_planeNeighbors.mpr
      change (a, d - 21 + 21) ∈ planeEdges
      simpa only [Nat.sub_add_cancel hadb.2.1] using had
    · apply mem_planeNeighbors.mpr
      change (b, d - 21 + 21) ∈ planeEdges
      simpa only [Nat.sub_add_cancel hadb.2.1] using hbd
  have heq := planeNeighbors_common_unique haab hcc.1 hcc.2 hdd.1 hdd.2
  have heqv := congrArg Fin.val heq
  dsimp [cc, dd] at heqv
  exact hcd (by omega)

def planeGraph : SimpleGraph (Fin 42) where
  Adj u v := (u.val, v.val) ∈ planeEdges ∨ (v.val, u.val) ∈ planeEdges
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by
    intro u h
    rcases h with h | h <;> have hb := planeEdges_bounds (u.val, u.val) h <;> omega⟩

lemma planeGraph_adj (u v : Fin 42) :
    planeGraph.Adj u v ↔ (u.val, v.val) ∈ planeEdges ∨ (v.val, u.val) ∈ planeEdges := Iff.rfl

lemma planeGraph_cover_lower (T : Finset (Fin 42))
    (hcover : ∀ u v, planeGraph.Adj u v → u ∈ T ∨ v ∈ T) : 21 ≤ T.card := by
  let S : Finset ℕ := T.image Fin.val
  have hs : 21 ≤ S.card := by
    apply planeEdges_vertexCover_lower
    intro u v huv
    have hbounds := planeEdges_bounds (u, v) huv
    let uu : Fin 42 := ⟨u, by omega⟩
    let vv : Fin 42 := ⟨v, hbounds.2.2⟩
    have hc := hcover uu vv (Or.inl huv)
    rcases hc with hu | hv
    · exact Or.inl (Finset.mem_image.mpr ⟨uu, hu, rfl⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨vv, hv, rfl⟩)
  exact hs.trans Finset.card_image_le

lemma planeGraph_card [Fintype planeGraph.edgeSet] : planeGraph.edgeFinset.card = 105 := by
  let f : ↥planeEdges.toFinset → planeGraph.edgeSet := fun e =>
    ⟨s((⟨e.val.1, by have h := planeEdges_bounds e.val (List.mem_toFinset.mp e.property); omega⟩ : Fin 42),
       (⟨e.val.2, (planeEdges_bounds e.val (List.mem_toFinset.mp e.property)).2.2⟩ : Fin 42)),
       Or.inl (List.mem_toFinset.mp e.property)⟩
  have hinj : Function.Injective f := by
    intro e t h
    have he := planeEdges_bounds e.val (List.mem_toFinset.mp e.property)
    have ht := planeEdges_bounds t.val (List.mem_toFinset.mp t.property)
    have hv := congrArg Subtype.val h
    dsimp [f] at hv
    rcases Sym2.eq_iff.mp hv with hh | hh
    · apply Subtype.ext
      exact Prod.ext (congrArg Fin.val hh.1) (congrArg Fin.val hh.2)
    · have hv := congrArg Fin.val hh.1
      change e.val.1 = t.val.2 at hv
      omega
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ u v =>
      change planeGraph.Adj u v at he
      rcases he with he | he
      · refine ⟨⟨(u.val, v.val), List.mem_toFinset.mpr he⟩, ?_⟩
        apply Subtype.ext
        rfl
      · refine ⟨⟨(v.val, u.val), List.mem_toFinset.mpr he⟩, ?_⟩
        apply Subtype.ext
        dsimp [f]
        exact Sym2.eq_swap
  rw [SimpleGraph.edgeFinset_card, ← Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
  simpa only [Fintype.card_coe] using planeEdges_card


lemma planeGraph_no_four_cycle (a b c d : Fin 42) (hac : a ≠ c) (hbd : b ≠ d) :
    ¬ (planeGraph.Adj a b ∧ planeGraph.Adj b c ∧
      planeGraph.Adj c d ∧ planeGraph.Adj d a) := by
  have hacv : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hbdv : b.val ≠ d.val := fun h => hbd (Fin.ext h)
  rintro ⟨hab, hbc, hcd, hda⟩
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc <;>
    rcases hcd with hcd | hcd <;> rcases hda with hda | hda
  all_goals
    first
    | exact planeEdges_no_rectangle hacv hbdv hab hda hbc hcd
    | exact planeEdges_no_rectangle hbdv hacv hab hbc hda hcd
    | have ha := planeEdges_bounds _ hab
      have hb := planeEdges_bounds _ hbc
      have hc := planeEdges_bounds _ hcd
      have hd := planeEdges_bounds _ hda
      omega

lemma planeGraph_fun_iff (x : Fin 42 → Bool) :
    (∃ u v : Fin 42, planeGraph.Adj u v ∧ x u = true ∧ x v = true) ↔
      ∃ u v : Fin 42, (u.val, v.val) ∈ planeEdges ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases huv with huv | huv
    · exact ⟨u, v, huv, hu, hv⟩
    · exact ⟨v, u, huv, hv, hu⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨u, v, Or.inl huv, hu, hv⟩

end PEqualNP.Outside.L_meta_1477


namespace PEqualNP.Outside.L_meta_1477.PlaneRobustCover

def planeEdges : List (ℕ × ℕ) :=
  [(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)]

def shifts : Finset (Fin 21) := {0, 5, 7, 17, 20}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma shift_edge : ∀ d ∈ shifts, ∀ i : Fin 21,
    (i.val, (i + d).val + 21) ∈ planeEdges := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma edge_has_shift : ∀ a b : Fin 21, (a.val, b.val + 21) ∈ planeEdges →
    ∃ d ∈ shifts, a + d = b := by
  decide

lemma shift_injective (d : Fin 21) : Function.Injective (fun i : Fin 21 => i + d) := by
  intro i j hij
  exact add_right_cancel hij

lemma residual_cover_lower (a b : Fin 21) (hab : (a.val, b.val + 21) ∈ planeEdges)
    (s : Finset ℕ)
    (hcover : ∀ i j : Fin 21, i ≠ a → j ≠ b →
      (i.val, j.val + 21) ∈ planeEdges → i.val ∈ s ∨ j.val + 21 ∈ s) :
    20 ≤ s.card := by
  obtain ⟨d, hd, had⟩ := edge_has_shift a b hab
  let f : Fin 21 → ℕ := fun i => if i.val ∈ s then i.val else (i + d).val + 21
  have hf : Function.Injective f := by
    intro i j hij
    by_cases hi : i.val ∈ s <;> by_cases hj : j.val ∈ s
    · apply Fin.ext
      simpa [f, hi, hj] using hij
    · have he : i.val = (j + d).val + 21 := by simpa [f, hi, hj] using hij
      have := i.isLt
      omega
    · have he : (i + d).val + 21 = j.val := by simpa [f, hi, hj] using hij
      have := j.isLt
      omega
    · have he : (i + d).val + 21 = (j + d).val + 21 := by simpa [f, hi, hj] using hij
      exact shift_injective d (Fin.ext (Nat.add_right_cancel he))
  have hsub : ((Finset.univ.erase a).image f) ⊆ s := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    have hia : i ≠ a := (Finset.mem_erase.mp hi).1
    have hid : i + d ≠ b := by
      intro h
      exact hia (shift_injective d (h.trans had.symm))
    have hc := hcover i (i + d) hia hid (shift_edge d hd i)
    dsimp [f]
    split_ifs with his
    · exact his
    · exact hc.resolve_left his
  have hcard : (Finset.univ.erase a : Finset (Fin 21)).card = 20 := by simp
  calc
    20 = (Finset.univ.erase a : Finset (Fin 21)).card := hcard.symm
    _ = ((Finset.univ.erase a).image f).card := (Finset.card_image_of_injective _ hf).symm
    _ ≤ s.card := Finset.card_le_card hsub


def residualMatch (d a : Fin 21) : Finset (Fin 21 × Fin 21) :=
  (Finset.univ.erase a).image (fun i => (i, i + d))

lemma residualMatch_card (d a : Fin 21) : (residualMatch d a).card = 20 := by
  rw [residualMatch, Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)]
  simp

lemma residualMatch_no_shared_endpoint (d a : Fin 21) (e f : Fin 21 × Fin 21)
    (he : e ∈ residualMatch d a) (hf : f ∈ residualMatch d a) (hef : e ≠ f) :
    e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
  rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
  rcases Finset.mem_image.mp hf with ⟨j, _, rfl⟩
  have hij : i ≠ j := fun h => hef (by simp [h])
  exact ⟨hij, fun h => hij (shift_injective d h)⟩

lemma residual_matching (a b : Fin 21) (hab : (a.val, b.val + 21) ∈ planeEdges) :
    ∃ M : Finset (Fin 21 × Fin 21), M.card = 20 ∧
      (∀ e ∈ M, (e.1.val, e.2.val + 21) ∈ planeEdges ∧ e.1 ≠ a ∧ e.2 ≠ b) ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) := by
  obtain ⟨d, hd, had⟩ := edge_has_shift a b hab
  refine ⟨residualMatch d a, residualMatch_card d a, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
    have hia : i ≠ a := (Finset.mem_erase.mp hi).1
    refine ⟨shift_edge d hd i, hia, ?_⟩
    intro h
    exact hia (shift_injective d (h.trans had.symm))
  · intro e he f hf hef
    exact residualMatch_no_shared_endpoint d a e f he hf hef

lemma planeEdges_bounds : ∀ e ∈ planeEdges, e.1 < 21 ∧ 21 ≤ e.2 ∧ e.2 < 42 := by
  decide

lemma residual_nat_cover_lower (a b : ℕ) (hab : (a, b) ∈ planeEdges) (s : Finset ℕ)
    (hcover : ∀ u v : ℕ, (u, v) ∈ planeEdges → u ≠ a → v ≠ b →
      u ∈ s ∨ v ∈ s) : 20 ≤ s.card := by
  have hb := planeEdges_bounds (a, b) hab
  let aa : Fin 21 := ⟨a, hb.1⟩
  let bb : Fin 21 := ⟨b - 21, by omega⟩
  have hab' : (aa.val, bb.val + 21) ∈ planeEdges := by
    change (a, b - 21 + 21) ∈ planeEdges
    simpa only [Nat.sub_add_cancel hb.2.1] using hab
  apply residual_cover_lower aa bb hab' s
  intro i j hia hjb hij
  apply hcover i.val (j.val + 21) hij
  · intro h
    exact hia (Fin.ext h)
  · intro h
    apply hjb
    apply Fin.ext
    change j.val = b - 21
    omega

def leftVertex (i : Fin 21) : Fin 42 := ⟨i.val, by omega⟩

def rightVertex (j : Fin 21) : Fin 42 := ⟨j.val + 21, by omega⟩

lemma residual_graph_cover_lower (G : SimpleGraph (Fin 42)) (a b : Fin 21)
    (hab : (a.val, b.val + 21) ∈ planeEdges)
    (hkeep : ∀ i j : Fin 21, i ≠ a → j ≠ b →
      (i.val, j.val + 21) ∈ planeEdges → G.Adj (leftVertex i) (rightVertex j))
    (T : Finset (Fin 42)) (hcover : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
    20 ≤ T.card := by
  let S : Finset ℕ := T.image Fin.val
  have hs : 20 ≤ S.card := by
    apply residual_cover_lower a b hab S
    intro i j hia hjb hij
    rcases hcover (leftVertex i) (rightVertex j) (hkeep i j hia hjb hij) with hi | hj
    · exact Or.inl (Finset.mem_image.mpr ⟨leftVertex i, hi, rfl⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨rightVertex j, hj, rfl⟩)
  exact hs.trans Finset.card_image_le


lemma residual_cover_lower_with_center (a b : Fin 21)
    (hab : (a.val, b.val + 21) ∈ planeEdges) (s : Finset ℕ)
    (hcenter : a.val ∈ s ∨ b.val + 21 ∈ s)
    (hcover : ∀ i j : Fin 21, i ≠ a → j ≠ b →
      (i.val, j.val + 21) ∈ planeEdges → i.val ∈ s ∨ j.val + 21 ∈ s) :
    21 ≤ s.card := by
  obtain ⟨d, hd, had⟩ := edge_has_shift a b hab
  let f : Fin 21 → ℕ := fun i => if i.val ∈ s then i.val else (i + d).val + 21
  have hf : Function.Injective f := by
    intro i j hij
    by_cases hi : i.val ∈ s <;> by_cases hj : j.val ∈ s
    · apply Fin.ext
      simpa [f, hi, hj] using hij
    · have he : i.val = (j + d).val + 21 := by simpa [f, hi, hj] using hij
      have := i.isLt
      omega
    · have he : (i + d).val + 21 = j.val := by simpa [f, hi, hj] using hij
      have := j.isLt
      omega
    · have he : (i + d).val + 21 = (j + d).val + 21 := by simpa [f, hi, hj] using hij
      exact shift_injective d (Fin.ext (Nat.add_right_cancel he))
  have hsub : Finset.univ.image f ⊆ s := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, _, rfl⟩
    have hc : i.val ∈ s ∨ (i + d).val + 21 ∈ s := by
      by_cases hia : i = a
      · subst i
        simpa only [had] using hcenter
      · have hid : i + d ≠ b := by
          intro h
          exact hia (shift_injective d (h.trans had.symm))
        exact hcover i (i + d) hia hid (shift_edge d hd i)
    dsimp [f]
    split_ifs with his
    · exact his
    · exact hc.resolve_left his
  calc
    21 = (Finset.univ : Finset (Fin 21)).card := by simp
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hf).symm
    _ ≤ s.card := Finset.card_le_card hsub

lemma residual_nat_cover_lower_with_center (a b : ℕ) (hab : (a, b) ∈ planeEdges)
    (s : Finset ℕ) (hcenter : a ∈ s ∨ b ∈ s)
    (hcover : ∀ u v : ℕ, (u, v) ∈ planeEdges → u ≠ a → v ≠ b →
      u ∈ s ∨ v ∈ s) : 21 ≤ s.card := by
  have hb := planeEdges_bounds (a, b) hab
  let aa : Fin 21 := ⟨a, hb.1⟩
  let bb : Fin 21 := ⟨b - 21, by omega⟩
  have hab' : (aa.val, bb.val + 21) ∈ planeEdges := by
    change (a, b - 21 + 21) ∈ planeEdges
    simpa only [Nat.sub_add_cancel hb.2.1] using hab
  apply residual_cover_lower_with_center aa bb hab' s
  · change a ∈ s ∨ b - 21 + 21 ∈ s
    simpa only [Nat.sub_add_cancel hb.2.1] using hcenter
  · intro i j hia hjb hij
    apply hcover i.val (j.val + 21) hij
    · intro h
      exact hia (Fin.ext h)
    · intro h
      apply hjb
      apply Fin.ext
      change j.val = b - 21
      omega

lemma residual_graph_cover_lower_with_center (G : SimpleGraph (Fin 42)) (a b : Fin 21)
    (hab : (a.val, b.val + 21) ∈ planeEdges)
    (hcenter : G.Adj (leftVertex a) (rightVertex b))
    (hkeep : ∀ i j : Fin 21, i ≠ a → j ≠ b →
      (i.val, j.val + 21) ∈ planeEdges → G.Adj (leftVertex i) (rightVertex j))
    (T : Finset (Fin 42)) (hcover : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
    21 ≤ T.card := by
  let S : Finset ℕ := T.image Fin.val
  have hs : 21 ≤ S.card := by
    apply residual_cover_lower_with_center a b hab S
    · rcases hcover (leftVertex a) (rightVertex b) hcenter with ha | hb
      · exact Or.inl (Finset.mem_image.mpr ⟨leftVertex a, ha, rfl⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨rightVertex b, hb, rfl⟩)
    · intro i j hia hjb hij
      rcases hcover (leftVertex i) (rightVertex j) (hkeep i j hia hjb hij) with hi | hj
      · exact Or.inl (Finset.mem_image.mpr ⟨leftVertex i, hi, rfl⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨rightVertex j, hj, rfl⟩)
  exact hs.trans Finset.card_image_le

end PEqualNP.Outside.L_meta_1477.PlaneRobustCover

namespace PEqualNP.Outside.L_meta_1477.PlaneTwoCenters

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1477

lemma plane_noFourCycle [DecidableRel planeGraph.Adj] : NoFourCycle planeGraph := by
  classical
  intro a b hab
  rw [Finset.card_le_one]
  intro u hu v hv
  have h1 := (Finset.mem_filter.mp hu).2
  have h2 := (Finset.mem_filter.mp hv).2
  by_contra huv
  exact planeGraph_no_four_cycle a u b v hab huv ⟨h1.1, h1.2.symm, h2.2, h2.1.symm⟩

lemma star_cover_residual_ordered [DecidableRel planeGraph.Adj]
    (C : Circuit) (a b : Fin 42) (hab : (a.val, b.val) ∈ planeEdges)
    (hU : ∀ e ∈ Ustar planeGraph C, a ∈ e ∨ b ∈ e)
    (K : Finset (Fin 42))
    (hK : ∀ e ∈ starEdges planeGraph C, ∃ v ∈ K, v ∈ e) :
    20 ≤ K.card ∧ (s(a, b) ∉ Ustar planeGraph C → 21 ≤ K.card) := by
  classical
  let S : Finset ℕ := K.image Fin.val
  have habounds := planeEdges_bounds (a.val, b.val) hab
  have hcover : ∀ u v : ℕ, (u, v) ∈ PlaneRobustCover.planeEdges →
      u ≠ a.val → v ≠ b.val → u ∈ S ∨ v ∈ S := by
    intro u v huv hua hvb
    have hp : (u, v) ∈ planeEdges := huv
    have hbounds := planeEdges_bounds (u, v) hp
    let uu : Fin 42 := ⟨u, by omega⟩
    let vv : Fin 42 := ⟨v, hbounds.2.2⟩
    have hstar : s(uu, vv) ∈ starEdges planeGraph C := by
      by_contra hn
      have hm : s(uu, vv) ∈ Ustar planeGraph C :=
        Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr
          ((SimpleGraph.mem_edgeSet planeGraph).mpr (Or.inl hp)), hn⟩
      rcases hU _ hm with ha | hb
      · rcases Sym2.mem_iff.mp ha with he | he
        · exact hua (congrArg Fin.val he).symm
        · have he' := congrArg Fin.val he
          change a.val = v at he'
          omega
      · rcases Sym2.mem_iff.mp hb with he | he
        · have he' := congrArg Fin.val he
          change b.val = u at he'
          omega
        · exact hvb (congrArg Fin.val he).symm
    obtain ⟨w, hw, hwe⟩ := hK _ hstar
    rcases Sym2.mem_iff.mp hwe with rfl | rfl
    · exact Or.inl (Finset.mem_image.mpr ⟨uu, hw, rfl⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨vv, hw, rfl⟩)
  have hab' : (a.val, b.val) ∈ PlaneRobustCover.planeEdges := hab
  constructor
  · exact (PlaneRobustCover.residual_nat_cover_lower a.val b.val hab' S hcover).trans
      Finset.card_image_le
  · intro hnU
    have hs : s(a, b) ∈ starEdges planeGraph C := by
      by_contra hns
      exact hnU (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr
        ((SimpleGraph.mem_edgeSet planeGraph).mpr (Or.inl hab)), hns⟩)
    obtain ⟨w, hw, hwe⟩ := hK _ hs
    have hcenter : a.val ∈ S ∨ b.val ∈ S := by
      rcases Sym2.mem_iff.mp hwe with hwa | hwb
      · exact Or.inl (Finset.mem_image.mpr ⟨w, hw, congrArg Fin.val hwa⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨w, hw, congrArg Fin.val hwb⟩)
    exact (PlaneRobustCover.residual_nat_cover_lower_with_center a.val b.val hab' S
      hcenter hcover).trans Finset.card_image_le

lemma star_cover_residual [DecidableRel planeGraph.Adj]
    (C : Circuit) (a b : Fin 42) (hab : planeGraph.Adj a b)
    (hU : ∀ e ∈ Ustar planeGraph C, a ∈ e ∨ b ∈ e)
    (K : Finset (Fin 42))
    (hK : ∀ e ∈ starEdges planeGraph C, ∃ v ∈ K, v ∈ e) :
    20 ≤ K.card ∧ (s(a, b) ∉ Ustar planeGraph C → 21 ≤ K.card) := by
  rcases hab with hab | hab
  · exact star_cover_residual_ordered C a b hab hU K hK
  · have h := star_cover_residual_ordered C b a hab (fun e he => (hU e he).symm) K hK
    exact ⟨h.1, fun hn => h.2 (by simpa only [Sym2.eq_swap] using hn)⟩

lemma disjoint_two_centers_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hT : TopForm planeGraph C)
    (g : ℕ) (hg : junk planeGraph C = {g}) (a b : Fin 42)
    (hdis : Disjoint (side (n := 42) C g 0) (side (n := 42) C g 1))
    (ha : a ∈ side (n := 42) C g 0) (hb : b ∈ side (n := 42) C g 1)
    (ham : a ∈ wmax planeGraph C g) (hbm : b ∈ wmax planeGraph C g)
    (hAcard : 2 ≤ (side (n := 42) C g 0).card)
    (hBcard : 2 ≤ (side (n := 42) C g 1).card) : 125 ≤ C.size := by
  classical
  have hG := plane_noFourCycle
  have hE : planeGraph.edgeFinset.Nonempty := by
    apply Finset.card_pos.mp
    rw [planeGraph_card]
    omega
  obtain ⟨K, hK, hKU, hKZ, hcount⟩ :=
    OneJunk.oneJunkBound 42 planeGraph C hG hE hL hT g hg
  have hcone := ResidualCone.disjoint_two_centers_cone_bound planeGraph hG C hL hT g hg
    a b hdis ha hb ham hbm hAcard hBcard
  have hUsub := ResidualCone.disjoint_two_centers_ustar_subset planeGraph hG C hL hT g hg
    a b hdis ha hb ham hbm hAcard hBcard
  have hU : ∀ e ∈ Ustar planeGraph C, a ∈ e ∨ b ∈ e := by
    intro e he
    rcases Finset.mem_union.mp (hUsub he) with h0 | h1
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h0
      exact Or.inr (Sym2.mem_mk_left _ _)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h1
      exact Or.inl (Sym2.mem_mk_left _ _)
  have hab := ResidualCone.mask_side_adj planeGraph C (OneJunk.P2.ao_of 42 C hL.1)
    hT g hg 0 a ham ha b hb
  have hcover := star_cover_residual C a b hab hU K hK
  rw [planeGraph_card] at hcount
  by_cases hempty : Ustar planeGraph C = ∅
  · rw [hempty, Finset.card_empty] at hcount
    omega
  · have hne := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨e, he⟩ := hne
    have hreader : 1 ≤ (mixing planeGraph C).card + 2 * (centreless planeGraph C).card := by
      induction e using Sym2.inductionOn with
      | _ u v => exact OneJunk.off_star_reader_overhead planeGraph C hL hT u v he
    by_cases hc : s(a, b) ∈ Ustar planeGraph C
    · rw [ite_eq_left hc] at hcone
      omega
    · rw [ite_eq_right hc] at hcone
      have hK21 := hcover.2 hc
      omega

end PEqualNP.Outside.L_meta_1477.PlaneTwoCenters

namespace PEqualNP.Outside.L_meta_1477.OneJunk
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma lambda_filtered_support_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (k : ℕ) (hk : k ∈ lam G C) (a : Fin n)
    (hlarge : 2 ≤ ((orIn n C (n + k)).filter (G.Adj a)).card) :
    (∀ v ∈ orIn n C (n + k), G.Adj a v) ∧
      (∀ v ∈ orIn n C (n + k), s(a, v) ∈ starEdges G C) := by
  obtain ⟨hkN, _, _, t, ht, b, hb, hr⟩ := (P2.mem_filter' _ _ _ _).mp hk
  have hklen : k < C.gates.length := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp hkN).1
  have htlen : t < C.gates.length := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp ht).1
  have hA := P2.ao_of n C hL.1
  have htl := P2.opnd_lt n C hA t htlen (opnd C t) (P2.opnd_eq n C hA t htlen) b
  have htbig : opnd C t b < n + C.gates.length := htl.trans (by omega)
  have hkr := P2.orReaches_orR n C _ htbig k hr
  have hsub : orIn n C (n + k) ⊆ side (n := n) C t b :=
    orIn_subset_of_orR C hA _ _ htbig (by omega) hkr
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hb
  have hcadj : ∀ v ∈ orIn n C (n + k), G.Adj c v := by
    intro v hv
    have hcside : c ∈ side (n := n) C t (1 - b) := by rw [hc]; simp
    have hvside := hsub hv
    have hf := (P1.S90.top_facts G C hG hL t ht).2.1
    rcases P2.fin2_sub b with ⟨hb0, hb1⟩ | ⟨hb0, hb1⟩
    · rw [hb0] at hvside
      rw [hb1] at hcside
      exact (hf v hvside c hcside).symm
    · rw [hb0] at hvside
      rw [hb1] at hcside
      exact hf c hcside v hvside
  have hac : a = c := by
    by_contra hne
    have hs : (orIn n C (n + k)).filter (G.Adj a) ⊆
        Finset.univ.filter (fun v => G.Adj a v ∧ G.Adj c v) := by
      intro v hv
      obtain ⟨hv, hav⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hav, hcadj v hv⟩
    have hbound := (Finset.card_le_card hs).trans (hG a c hne)
    omega
  subst c
  refine ⟨hcadj, lambda_support_star G hG C hL k hk a hcadj ?_⟩
  exact hlarge.trans (Finset.card_filter_le _ _)

end PEqualNP.Outside.L_meta_1477.OneJunk

namespace PEqualNP.Outside.L_meta_1477.FilteredResidualCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_1477.OneJunk

lemma filtered_residual_side_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (g : ℕ) (hg : g < C.gates.length) (b : Fin 2) (c : Fin n) :
    ((((side (n := n) C g b).filter (G.Adj c)).image (fun v => s(c, v))) \ starEdges G C).card ≤
      (coneGates G C g).card + 1 := by
  classical
  let f : ℕ → Finset (Fin n) := fun w => (orIn n C w).filter (G.Adj c)
  have hRB := hL.1.2.1
  have h2 := hL.1.2.2
  have hlen : ∀ k, (gateAt C k).op = GateOp.or → (gateAt C k).inputs.length ≤ 2 := by
    intro k _
    by_cases hk : k < C.gates.length
    · rw [h2 _ (P1.S90.gateAt_mem hk)]
    · rw [P1.gateAt_ge (by omega)]
      simp
  have hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k := by
    intro k i hi
    by_cases hk : k < C.gates.length
    · exact hRB k hk i hi
    · rw [P1.gateAt_ge (by omega)] at hi
      simp at hi
  have hf1 : ∀ w, w < n → (f w).card ≤ 1 := by
    intro w hw
    exact (Finset.card_filter_le _ _).trans (P1.orIn_input C w hw)
  have hf2' : ∀ k, (gateAt C k).op = GateOp.or → ∀ u,
      u ∈ orIn n C (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, u ∈ orIn n C w := by
    intro k hop u
    rw [P1.orIn_gate]
    constructor
    · rintro ⟨_, _, w, hw, _, hu⟩
      exact ⟨w, hw, hu⟩
    · rintro ⟨w, hw, hu⟩
      have hk : k < C.gates.length := by
        by_contra hk
        rw [P1.gateAt_ge (by omega)] at hw
        simp at hw
      exact ⟨hk, hop, w, hw, hRB k hk w hw, hu⟩
  have hf2 : ∀ k, (gateAt C k).op = GateOp.or → ∀ u,
      u ∈ f (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, u ∈ f w := by
    intro k hop u
    simp only [f, Finset.mem_filter, hf2' k hop u]
    constructor
    · rintro ⟨⟨w, hw, hu⟩, hadj⟩
      exact ⟨w, hw, hu, hadj⟩
    · rintro ⟨w, hw, hu, hadj⟩
      exact ⟨⟨w, hw, hu⟩, hadj⟩
  have hf3 : ∀ k, (gateAt C k).op ≠ GateOp.or → (f (n + k)).card ≤ 1 := by
    intro k hop
    apply (Finset.card_filter_le _ _).trans
    rw [Finset.card_le_one]
    intro a ha
    exact absurd ((P1.orIn_gate C k a).1 ha).2.1 hop
  have hstop : ∀ k, k ∈ lam G C → f (n + k) ⊆ f (opnd C g b) →
      (∀ v ∈ f (n + k), s(c, v) ∈ starEdges G C) ∨ (f (n + k)).card ≤ 1 := by
    intro k hk _
    by_cases hsmall : (f (n + k)).card ≤ 1
    · exact Or.inr hsmall
    · have hh := lambda_filtered_support_star G hG C hL k hk c
        (by change 2 ≤ (f (n + k)).card; omega)
      exact Or.inl (fun v hv => hh.2 v (Finset.mem_filter.mp hv).1)
  obtain ⟨Q, hQlam, hQ, hcount⟩ := P1.top_step2 n (gateAt C) hlen hback f hf1 hf2 hf3
    (lam G C) (opnd C g b) c (starEdges G C) hstop
  have hroot : opnd C g b < n + C.gates.length :=
    (P1.opnd_lt h2 hRB hg b).trans (by omega)
  have hQsub : Q ⊆ coneGates G C g := by
    intro k hk
    obtain ⟨hop, htwo, hn, hr, hsub⟩ := hQ k hk
    have hrlen : opnd C g b - n < C.gates.length := by omega
    obtain ⟨hpath, hklen⟩ := P1.rtg_conv C hRB _ k hr hrlen
    have he : n + (opnd C g b - n) = opnd C g b := by omega
    rw [he] at hpath
    have hreach := P1.S90.reach_orReaches hpath k rfl hklen
    have htwo' : P1.TwoNe (gateAt C) (orIn n C) k := by
      obtain ⟨w, hw, z, hz, hne, hwne, hzne⟩ := htwo
      obtain ⟨u, hu⟩ := hwne
      obtain ⟨v, hv⟩ := hzne
      exact ⟨w, hw, z, hz, hne, ⟨u, (Finset.mem_filter.mp hu).1⟩,
        ⟨v, (Finset.mem_filter.mp hv).1⟩⟩
    obtain ⟨hbel, hne0, hne1⟩ := P1.two_facts G C h2 hRB hklen hop htwo'
    have hkN : k ∈ orN G C := by
      simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨hklen, hop, hbel⟩
    have hnlam : k ∉ lam G C := fun h => Finset.disjoint_left.mp hQlam h hk
    have hnmix : k ∉ mixing G C := by
      intro hm
      have hm' := (P2.mem_filter' _ _ _ _).mp hm
      exact hm'.2 (propext (iff_of_false hne0.ne_empty hne1.ne_empty))
    apply (P2.mem_filter' _ _ _ _).mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hkN, hnlam⟩, hnmix⟩, ?_⟩
    fin_cases b
    · exact Or.inl hreach
    · exact Or.inr (Or.inl hreach)
  exact hcount.trans (Nat.add_le_add_right (Finset.card_le_card hQsub) 1)

lemma centered_ustar_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (b : Fin 2) (c : Fin n)
    (hc : c ∉ side (n := n) C g b)
    (hU : ∀ e ∈ Ustar G C, c ∈ e) :
    (Ustar G C).card ≤ (coneGates G C g).card + 1 := by
  classical
  let R := (((side (n := n) C g b).filter (G.Adj c)).image (fun v => s(c, v))) \ starEdges G C
  have hsub : Ustar G C ⊆ R := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hcup := Sym2.mem_iff.mp (hU _ he)
      obtain ⟨z, hz, hzuv, hfire⟩ := off_star_mask G C hL hT g hg u v he
      rw [junk_value_product G C (P2.ao_of n C hL.1) hT g hg] at hfire
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hfire
      have hactive : ∃ w ∈ side (n := n) C g b, pairInput u v w = true := by
        fin_cases b
        · exact hfire.1
        · exact hfire.2
      obtain ⟨w, hw, hwp⟩ := hactive
      have hwc : w ≠ c := fun heq => hc (heq ▸ hw)
      have hwp' := of_decide_eq_true hwp
      have heq : s(c, w) = s(u, v) := by
        rcases hcup with rfl | rfl <;> rcases hwp' with rfl | rfl
        · exact (hwc rfl).elim
        · rfl
        · exact Sym2.eq_swap
        · exact (hwc rfl).elim
      have hAdj : G.Adj c w := by
        apply (SimpleGraph.mem_edgeSet G).mp
        apply SimpleGraph.mem_edgeFinset.mp
        rw [heq]
        exact (Finset.mem_sdiff.mp he).1
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr
        ⟨w, Finset.mem_filter.mpr ⟨hw, hAdj⟩, heq⟩, (Finset.mem_sdiff.mp he).2⟩
  have hgj : g ∈ junk G C := by rw [hg]; simp
  have hglen := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp hgj).1
  exact (Finset.card_le_card hsub).trans (filtered_residual_side_cone G hG C hL g hglen b c)

end PEqualNP.Outside.L_meta_1477.FilteredResidualCone

namespace PEqualNP.Outside.L_meta_1477.PlaneCentered

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1477

lemma empty_ustar_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hT : TopForm planeGraph C)
    (g : ℕ) (hg : junk planeGraph C = {g}) (he : Ustar planeGraph C = ∅) :
    125 ≤ C.size := by
  classical
  have hE : planeGraph.edgeFinset.Nonempty := by
    apply Finset.card_pos.mp
    rw [planeGraph_card]
    omega
  obtain ⟨K, hK, hKU, hKZ, hcount⟩ :=
    OneJunk.oneJunkBound 42 planeGraph C PlaneTwoCenters.plane_noFourCycle hE hL hT g hg
  have hcov : ∀ u v, planeGraph.Adj u v → u ∈ K ∨ v ∈ K := by
    intro u v huv
    have hstar : s(u, v) ∈ starEdges planeGraph C := by
      by_contra hns
      have hm : s(u, v) ∈ Ustar planeGraph C := Finset.mem_sdiff.mpr
        ⟨SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet planeGraph).mpr huv), hns⟩
      rw [he] at hm
      exact Finset.notMem_empty _ hm
    obtain ⟨w, hw, hwe⟩ := hK _ hstar
    rcases Sym2.mem_iff.mp hwe with rfl | rfl
    · exact Or.inl hw
    · exact Or.inr hw
  have hcard := planeGraph_cover_lower K hcov
  rw [planeGraph_card, he, Finset.card_empty] at hcount
  omega

lemma centered_ustar_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hT : TopForm planeGraph C)
    (g : ℕ) (hg : junk planeGraph C = {g}) (b : Fin 2) (c : Fin 42)
    (hc : c ∉ side (n := 42) C g b)
    (hU : ∀ e ∈ Ustar planeGraph C, c ∈ e) : 125 ≤ C.size := by
  classical
  by_cases hempty : Ustar planeGraph C = ∅
  · exact empty_ustar_size C hL hT g hg hempty
  have hG := PlaneTwoCenters.plane_noFourCycle
  have hE : planeGraph.edgeFinset.Nonempty := by
    apply Finset.card_pos.mp
    rw [planeGraph_card]
    omega
  obtain ⟨K, hK, hKU, hKZ, hcount⟩ :=
    OneJunk.oneJunkBound 42 planeGraph C hG hE hL hT g hg
  have hcone := FilteredResidualCone.centered_ustar_cone planeGraph hG C hL hT g hg b c hc hU
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hreader : 1 ≤ (mixing planeGraph C).card + 2 * (centreless planeGraph C).card := by
    induction e using Sym2.inductionOn with
    | _ u v => exact OneJunk.off_star_reader_overhead planeGraph C hL hT u v he
  obtain ⟨d, hcd⟩ : ∃ d : Fin 42, planeGraph.Adj c d := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : planeGraph.Adj u v := (SimpleGraph.mem_edgeSet planeGraph).mp
        (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1)
      rcases Sym2.mem_iff.mp (hU _ he) with hcu | hcv
      · exact ⟨v, by simpa only [hcu] using huv⟩
      · exact ⟨u, by simpa only [hcv] using huv.symm⟩
  have hK20 := (PlaneTwoCenters.star_cover_residual C c d hcd
    (fun e he => Or.inl (hU e he)) K hK).1
  rw [planeGraph_card] at hcount
  omega

end PEqualNP.Outside.L_meta_1477.PlaneCentered

namespace PEqualNP.Outside.L_meta_1477.OneJunkIsolation
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_1477.OneJunk

lemma mask_not_both_junk_sides {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C) (g : ℕ)
    (hg : junk G C = {g}) (c : Fin n) (hc : c ∈ wmax G C g) :
    ¬ (c ∈ side (n := n) C g 0 ∧ c ∈ side (n := n) C g 1) := by
  rintro ⟨hc0, hc1⟩
  have hfire : gateVal n C g (pairInput c c) = true := by
    rw [junk_value_product G C hA hT g hg]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨c, hc0, by simp [pairInput]⟩, ⟨c, hc1, by simp [pairInput]⟩⟩
  have hgraph := (Finset.mem_filter.mp hc).2 (pairInput c c) hfire (by simp [pairInput])
  exact G.loopless.irrefl c ((P2.graphFun_pair G c c).mp hgraph)

lemma mask_excluded_from_some_side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C) (g : ℕ)
    (hg : junk G C = {g}) (c : Fin n) (hc : c ∈ wmax G C g) :
    ∃ b : Fin 2, c ∉ side (n := n) C g b := by
  by_cases h0 : c ∈ side (n := n) C g 0
  · exact ⟨1, fun h1 => mask_not_both_junk_sides G C hA hT g hg c hc ⟨h0, h1⟩⟩
  · exact ⟨0, h0⟩

lemma unique_effective_mask_covers_ustar {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (a : Fin n)
    (hunique : ∀ c : Fin n, c ∈ wmax G C g →
      (∃ u v : Fin n, G.Adj u v ∧ (c = u ∨ c = v) ∧
        gateVal n C g (pairInput u v) = true) → c = a)
    (u v : Fin n) (huv : s(u, v) ∈ Ustar G C) : u = a ∨ v = a := by
  obtain ⟨c, hc, hcu, hfire⟩ := off_star_mask G C hL hT g hg u v huv
  have hadj : G.Adj u v := by
    have he := (Finset.mem_sdiff.mp huv).1
    simpa using he
  have he := hunique c hc ⟨u, v, hadj, hcu, hfire⟩
  subst c
  exact hcu.imp Eq.symm Eq.symm

end PEqualNP.Outside.L_meta_1477.OneJunkIsolation

namespace PEqualNP.Outside.L_meta_1477.PlaneOneCleaner

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1477

lemma at_most_one_effective_mask_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hT : TopForm planeGraph C)
    (g : ℕ) (hg : junk planeGraph C = {g}) (a : Fin 42)
    (hunique : ∀ c : Fin 42, c ∈ wmax planeGraph C g →
      (∃ u v : Fin 42, planeGraph.Adj u v ∧ (c = u ∨ c = v) ∧
        gateVal 42 C g (pairInput u v) = true) → c = a) : 125 ≤ C.size := by
  classical
  by_cases he : Ustar planeGraph C = ∅
  · exact PlaneCentered.empty_ustar_size C hL hT g hg he
  obtain ⟨e, hem⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have ham : a ∈ wmax planeGraph C g := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨c, hc, hcu, hfire⟩ := OneJunk.off_star_mask planeGraph C hL hT g hg u v hem
      have hadj : planeGraph.Adj u v := (SimpleGraph.mem_edgeSet planeGraph).mp
        (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hem).1)
      have hca := hunique c hc ⟨u, v, hadj, hcu, hfire⟩
      exact hca ▸ hc
  obtain ⟨b, hab⟩ := OneJunkIsolation.mask_excluded_from_some_side planeGraph C
    (OneJunk.P2.ao_of 42 C hL.1) hT g hg a ham
  apply PlaneCentered.centered_ustar_size C hL hT g hg b a hab
  intro e hem
  induction e using Sym2.inductionOn with
  | _ u v =>
    have h := OneJunkIsolation.unique_effective_mask_covers_ustar planeGraph C hL hT g hg a hunique u v hem
    exact Sym2.mem_iff.mpr (h.imp Eq.symm Eq.symm)

lemma singleton_side_other_excludes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (b : Fin 2) (a : Fin n)
    (hs : side (n := n) C g b = {a}) : a ∉ side (n := n) C g (1 - b) := by
  intro ha
  have hA := OneJunk.P2.ao_of n C hL.1
  have hiff (x : Fin n → Bool) : gateVal n C g x = true ↔ x a = true := by
    rw [OneJunk.junk_value_product G C hA hT g hg, Bool.and_eq_true]
    fin_cases b
    · have hs0 : side (n := n) C g 0 = {a} := hs
      rw [hs0]
      simp only [Finset.mem_singleton, exists_eq_left, decide_eq_true_eq]
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, a, ha, hx⟩⟩
    · have hs1 : side (n := n) C g 1 = {a} := hs
      rw [hs1]
      simp only [Finset.mem_singleton, exists_eq_left, decide_eq_true_eq]
      exact ⟨fun hx => hx.2, fun hx => ⟨⟨a, ha, hx⟩, hx⟩⟩
  have hgj : g ∈ junk G C := by rw [hg]; simp
  have hglen := Finset.mem_range.mp ((OneJunk.P2.mem_filter' _ _ _ _).mp hgj).1
  have hleast : OneJunk.P1.S98.Least n C :=
    ⟨OneJunk.P1.S98.AO_of_IsAO2 n C hL.1, fun D hD hfun =>
      hL.2.2 D (OneJunk.P1.S98.IsAO2_of_AO n D hD)
        (funext fun x => (hfun x).trans (congrFun hL.2.1 x))⟩
  obtain ⟨x, hneq⟩ := OneJunk.P1.S98.least_nodup n C hleast a.val g
    (by have := a.isLt; omega) hglen
  change OneJunk.P2.W n C x a.val ≠ OneJunk.P2.W n C x (n + g) at hneq
  have hgv : OneJunk.P2.W n C x (n + g) = x a := Bool.eq_iff_iff.mpr (hiff x)
  rw [OneJunk.P2.W_input n C x a.val a.isLt, hgv] at hneq
  exact hneq rfl

lemma singleton_side_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hT : TopForm planeGraph C)
    (g : ℕ) (hg : junk planeGraph C = {g}) (b : Fin 2) (a : Fin 42)
    (hs : side (n := 42) C g b = {a}) : 125 ≤ C.size := by
  have hnot := singleton_side_other_excludes planeGraph C hL hT g hg b a hs
  apply PlaneCentered.centered_ustar_size C hL hT g hg (1 - b) a hnot
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨c, hc, hcu, hfire⟩ := OneJunk.off_star_mask planeGraph C hL hT g hg u v he
    rw [OneJunk.junk_value_product planeGraph C (OneJunk.P2.ao_of 42 C hL.1) hT g hg] at hfire
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfire
    have hactive : ∃ w ∈ side (n := 42) C g b, pairInput u v w = true := by
      fin_cases b
      · exact hfire.1
      · exact hfire.2
    rw [hs] at hactive
    have hv : pairInput u v a = true := by simpa only [Finset.mem_singleton, exists_eq_left] using hactive
    exact Sym2.mem_iff.mpr (of_decide_eq_true hv)

end PEqualNP.Outside.L_meta_1477.PlaneOneCleaner

namespace PEqualNP.Outside.L_meta_1477.PlaneDisjoint

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1477

def Effective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (c : Fin n) : Prop := c ∈ wmax G C g ∧
  ∃ u v : Fin n, G.Adj u v ∧ (c = u ∨ c = v) ∧ gateVal n C g (pairInput u v) = true

lemma effective_mem_sides {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : OneJunk.P2.AO n C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g})
    (hdis : Disjoint (side (n := n) C g 0) (side (n := n) C g 1))
    (c : Fin n) (hc : Effective G C g c) :
    c ∈ side (n := n) C g 0 ∪ side (n := n) C g 1 := by
  obtain ⟨hcm, u, v, huv, hcu, hfire⟩ := hc
  have hcross := ResidualCone.disjoint_product_pair_cross G C hA hT g hg hdis u v hfire
  rcases hcross with ⟨hu, hv⟩ | ⟨hv, hu⟩ <;> rcases hcu with rfl | rfl
  · exact Finset.mem_union_left _ hu
  · exact Finset.mem_union_right _ hv
  · exact Finset.mem_union_right _ hu
  · exact Finset.mem_union_left _ hv

lemma same_side_masks_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hA : OneJunk.P2.AO n C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (b : Fin 2)
    (hlarge : 2 ≤ (side (n := n) C g (1 - b)).card) (c d : Fin n)
    (hc : c ∈ wmax G C g) (hd : d ∈ wmax G C g)
    (hcs : c ∈ side (n := n) C g b) (hds : d ∈ side (n := n) C g b) : c = d := by
  by_contra hne
  have hca := ResidualCone.mask_side_adj G C hA hT g hg b c hc hcs
  have hda := ResidualCone.mask_side_adj G C hA hT g hg b d hd hds
  have hsub : side (n := n) C g (1 - b) ⊆
      Finset.univ.filter (fun v => G.Adj c v ∧ G.Adj d v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca v hv, hda v hv⟩
  have hbound := (Finset.card_le_card hsub).trans (hG c d hne)
  omega

lemma disjoint_sides_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hT : TopForm planeGraph C)
    (g : ℕ) (hg : junk planeGraph C = {g})
    (hdis : Disjoint (side (n := 42) C g 0) (side (n := 42) C g 1)) : 125 ≤ C.size := by
  classical
  have hA := OneJunk.P2.ao_of 42 C hL.1
  have hG := PlaneTwoCenters.plane_noFourCycle
  by_cases hs0 : (side (n := 42) C g 0).card ≤ 1
  · have hp := Finset.card_pos.mpr (OneJunk.junk_sides_nonempty planeGraph C hA hT g hg 0)
    have he : (side (n := 42) C g 0).card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp he
    exact PlaneOneCleaner.singleton_side_size C hL hT g hg 0 a ha
  by_cases hs1 : (side (n := 42) C g 1).card ≤ 1
  · have hp := Finset.card_pos.mpr (OneJunk.junk_sides_nonempty planeGraph C hA hT g hg 1)
    have he : (side (n := 42) C g 1).card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp he
    exact PlaneOneCleaner.singleton_side_size C hL hT g hg 1 a ha
  have hlarge0 : 2 ≤ (side (n := 42) C g 0).card := by omega
  have hlarge1 : 2 ≤ (side (n := 42) C g 1).card := by omega
  by_cases hl : ∃ a : Fin 42, a ∈ side (n := 42) C g 0 ∧ Effective planeGraph C g a
  · obtain ⟨a, ha, hae⟩ := hl
    by_cases hr : ∃ b : Fin 42, b ∈ side (n := 42) C g 1 ∧ Effective planeGraph C g b
    · obtain ⟨b, hb, hbe⟩ := hr
      exact PlaneTwoCenters.disjoint_two_centers_size C hL hT g hg a b hdis ha hb
        hae.1 hbe.1 hlarge0 hlarge1
    · apply PlaneOneCleaner.at_most_one_effective_mask_size C hL hT g hg a
      intro c hc hce
      have hmem := effective_mem_sides planeGraph C hA hT g hg hdis c ⟨hc, hce⟩
      rcases Finset.mem_union.mp hmem with hc0 | hc1
      · exact same_side_masks_eq planeGraph hG C hA hT g hg 0 hlarge1 c a hc hae.1 hc0 ha
      · exact (hr ⟨c, hc1, hc, hce⟩).elim
  · by_cases hr : ∃ b : Fin 42, b ∈ side (n := 42) C g 1 ∧ Effective planeGraph C g b
    · obtain ⟨b, hb, hbe⟩ := hr
      apply PlaneOneCleaner.at_most_one_effective_mask_size C hL hT g hg b
      intro c hc hce
      have hmem := effective_mem_sides planeGraph C hA hT g hg hdis c ⟨hc, hce⟩
      rcases Finset.mem_union.mp hmem with hc0 | hc1
      · exact (hl ⟨c, hc0, hc, hce⟩).elim
      · exact same_side_masks_eq planeGraph hG C hA hT g hg 1 hlarge0 c b hc hbe.1 hc1 hb
    · apply PlaneOneCleaner.at_most_one_effective_mask_size C hL hT g hg 0
      intro c hc hce
      have hmem := effective_mem_sides planeGraph C hA hT g hg hdis c ⟨hc, hce⟩
      rcases Finset.mem_union.mp hmem with hc0 | hc1
      · exact (hl ⟨c, hc0, hc, hce⟩).elim
      · exact (hr ⟨c, hc1, hc, hce⟩).elim

end PEqualNP.Outside.L_meta_1477.PlaneDisjoint

namespace PEqualNP.Outside.L_meta_1477.PlaneOverlap

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1477

lemma mask_adj_overlap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : OneJunk.P2.AO n C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (c : Fin n) (hc : c ∈ wmax G C g)
    (z : Fin n) (hz : z ∈ side (n := n) C g 0 ∩ side (n := n) C g 1) : G.Adj c z := by
  have hfire : gateVal n C g (pairInput c z) = true := by
    rw [OneJunk.junk_value_product G C hA hT g hg]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨z, (Finset.mem_inter.mp hz).1, by simp [pairInput]⟩,
      ⟨z, (Finset.mem_inter.mp hz).2, by simp [pairInput]⟩⟩
  have hgraph := ((OneJunk.P2.mem_filter' _ _ _ _).mp hc).2 (pairInput c z) hfire (by simp [pairInput])
  exact (OneJunk.P1.S90.graphFun_pair G c z).mp hgraph

lemma large_overlap_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hT : TopForm planeGraph C)
    (g : ℕ) (hg : junk planeGraph C = {g})
    (hlarge : 2 ≤ (side (n := 42) C g 0 ∩ side (n := 42) C g 1).card) : 125 ≤ C.size := by
  classical
  have hA := OneJunk.P2.ao_of 42 C hL.1
  have hG := PlaneTwoCenters.plane_noFourCycle
  by_cases hex : ∃ a : Fin 42, a ∈ wmax planeGraph C g
  · obtain ⟨a, ha⟩ := hex
    apply PlaneOneCleaner.at_most_one_effective_mask_size C hL hT g hg a
    intro c hc _
    by_contra hne
    have hsub : side (n := 42) C g 0 ∩ side (n := 42) C g 1 ⊆
        Finset.univ.filter (fun z => planeGraph.Adj c z ∧ planeGraph.Adj a z) := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        mask_adj_overlap planeGraph C hA hT g hg c hc z hz,
        mask_adj_overlap planeGraph C hA hT g hg a ha z hz⟩
    have hbound := (Finset.card_le_card hsub).trans (hG c a hne)
    omega
  · apply PlaneOneCleaner.at_most_one_effective_mask_size C hL hT g hg 0
    intro c hc _
    exact (hex ⟨c, hc⟩).elim

lemma nonsingleton_overlap_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hT : TopForm planeGraph C)
    (g : ℕ) (hg : junk planeGraph C = {g})
    (hnot : (side (n := 42) C g 0 ∩ side (n := 42) C g 1).card ≠ 1) : 125 ≤ C.size := by
  by_cases he : side (n := 42) C g 0 ∩ side (n := 42) C g 1 = ∅
  · exact PlaneDisjoint.disjoint_sides_size C hL hT g hg (Finset.disjoint_iff_inter_eq_empty.mpr he)
  · have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    exact large_overlap_size C hL hT g hg (by omega)

lemma short_onejunk_overlap_card [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hT : TopForm planeGraph C)
    (g : ℕ) (hg : junk planeGraph C = {g}) (hsize : C.size ≤ 124) :
    (side (n := 42) C g 0 ∩ side (n := 42) C g 1).card = 1 := by
  by_contra hnot
  have hbound := nonsingleton_overlap_size C hL hT g hg hnot
  omega

end PEqualNP.Outside.L_meta_1477.PlaneOverlap


namespace PEqualNP.Outside.L_meta_1477.SensitivePath
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]




def zeroAt (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩

lemma zeroAt_size (C : Circuit) (j : ℕ) : (zeroAt C j).size = C.size := by
  simp [zeroAt, Circuit.size]

lemma zeroAt_gate (C : Circuit) (j k : ℕ) (hk : k < C.gates.length) (hne : j ≠ k) :
    (zeroAt C j).gates[k]'(by simpa [zeroAt] using hk) = C.gates[k] := by
  exact List.getElem_set_of_ne hne _ _

def Changed {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j w : ℕ) : Prop :=
  value C x w = true ∧ value (zeroAt C j) x w = false

lemma changed_bounds {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j w : ℕ)
    (hw : Changed C x j w) : n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra h
    have hn : w < n := by omega
    have hv := input_value C x ⟨w, hn⟩
    have hz := input_value (zeroAt C j) x ⟨w, hn⟩
    change value C x w = x ⟨w, hn⟩ at hv
    change value (zeroAt C j) x w = x ⟨w, hn⟩ at hz
    change value C x w = true ∧ value (zeroAt C j) x w = false at hw
    rw [hv, hz] at hw
    exact Bool.noConfusion (hw.1.symm.trans hw.2)
  · by_contra h
    have hfalse := missing_value C x w (by omega)
    exact Bool.noConfusion (hw.1.symm.trans hfalse)

lemma eval_change_input (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hi lo : ℕ → Bool)
    (hhi : op.eval (l.map hi) = true) (hlo : op.eval (l.map lo) = false) :
    (∃ a ∈ l, hi a = true ∧ lo a = false) ∧
      (op = GateOp.and → ∀ a ∈ l, hi a = true) ∧
      (op = GateOp.or → ∀ a ∈ l, lo a = false) := by
  rcases hop with rfl | rfl
  · have hall : ∀ a ∈ l, hi a = true := by simpa [GateOp.eval] using hhi
    have hex : ∃ a ∈ l, lo a = false := by
      by_contra hn
      have hl : ∀ a ∈ l, lo a = true := by
        intro a ha
        cases h : lo a
        · exact False.elim (hn ⟨a, ha, h⟩)
        · rfl
      have ht : GateOp.and.eval (l.map lo) = true := by simpa [GateOp.eval] using hl
      rw [hlo] at ht
      cases ht
    obtain ⟨a, ha, hla⟩ := hex
    exact ⟨⟨a, ha, hall a ha, hla⟩, fun _ => hall, by simp⟩
  · have hex : ∃ a ∈ l, hi a = true := by simpa [GateOp.eval] using hhi
    have hall : ∀ a ∈ l, lo a = false := by
      intro a ha
      apply Bool.eq_false_iff.mpr
      intro ht
      have ht' : GateOp.or.eval (l.map lo) = true := by
        simpa [GateOp.eval] using (show ∃ b ∈ l, lo b = true from ⟨a, ha, ht⟩)
      rw [hlo] at ht'
      cases ht'
    obtain ⟨a, ha, hha⟩ := hex
    exact ⟨⟨a, ha, hha, hall a ha⟩, by simp, fun _ => hall⟩

lemma changed_predecessor {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (x : Fin n → Bool) (j w : ℕ) (hw : Changed C x j w) (hne : w ≠ n + j) :
    ∃ (a : ℕ) (h : w - n < C.gates.length), a < w ∧
      a ∈ C.gates[w - n].inputs ∧ Changed C x j a ∧
      (C.gates[w - n].op = GateOp.and →
        ∀ b ∈ C.gates[w - n].inputs, b < w ∧ value C x b = true) ∧
      (C.gates[w - n].op = GateOp.or →
        ∀ b ∈ C.gates[w - n].inputs, b < w → value (zeroAt C j) x b = false) := by
  have hb := changed_bounds C x j w hw
  have hk : w - n < C.gates.length := by
    have hh := hb.2
    change w < n + C.gates.length at hh
    omega
  have hne' : j ≠ w - n := by omega
  let g := C.gates[w - n]
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g (List.getElem_mem hk)).1
  have hv := gate_value C x w hb.1 hb.2
  have hz := gate_value (zeroAt C j) x w hb.1 (by rw [zeroAt_size]; exact hb.2)
  have hzk : w - n < (zeroAt C j).gates.length := by simpa [zeroAt] using hk
  have hzg := zeroAt_gate C j (w - n) hk hne'
  change value (zeroAt C j) x w =
    (zeroAt C j).gates[w - n].op.eval
      ((zeroAt C j).gates[w - n].inputs.map
        fun r => if r < w then value (zeroAt C j) x r else false) at hz
  rw [hzg] at hz
  have hh : g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) = true :=
    hv.symm.trans hw.1
  have hl : g.op.eval (g.inputs.map fun r => if r < w then value (zeroAt C j) x r else false) = false :=
    hz.symm.trans hw.2
  obtain ⟨⟨a, ha, hat, haf⟩, hand, hor⟩ := eval_change_input g.op hop g.inputs _ _ hh hl
  have haw : a < w := by
    by_contra h
    simp [h] at hat
  refine ⟨a, hk, haw, ha, ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa [haw] using hat
  · simpa [haw] using haf
  · intro hop b hb
    have ht := hand hop b hb
    have hbw : b < w := by
      by_contra h
      simp [h] at ht
    exact ⟨hbw, by simpa [hbw] using ht⟩
  · intro hop b hb hbw
    simpa [hbw] using hor hop b hb



def SensitiveStep {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) : Prop :=
  a < b ∧ n ≤ b ∧ b < n + C.size ∧
    a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (b - n)).inputs ∧
    Changed C x j a ∧ Changed C x j b ∧
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C (b - n)).op = GateOp.and →
      ∀ r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (b - n)).inputs,
        r < b ∧ value C x r = true) ∧
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C (b - n)).op = GateOp.or →
      ∀ r ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (b - n)).inputs,
        r < b → value (zeroAt C j) x r = false)

lemma changed_sensitive_step {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (x : Fin n → Bool) (j w : ℕ) (hw : Changed C x j w) (hne : w ≠ n + j) :
    ∃ a, SensitiveStep C x j a w := by
  obtain ⟨a, h, haw, ha, hac, hand, hor⟩ := changed_predecessor C hC x j w hw hne
  have hb := changed_bounds C x j w hw
  refine ⟨a, haw, hb.1, hb.2, ?_, hac, hw, ?_, ?_⟩
  · simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt,
      List.getD_eq_getElem _ _ h] using ha
  · simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt,
      List.getD_eq_getElem _ _ h] using hand
  · simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt,
      List.getD_eq_getElem _ _ h] using hor

lemma changed_path {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (x : Fin n → Bool) (j w : ℕ)
    (hw : Changed C x j w) :
    Relation.ReflTransGen (SensitiveStep C x j) (n + j) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases he : w = n + j
    · subst w
      exact Relation.ReflTransGen.refl
    · obtain ⟨a, ha⟩ := changed_sensitive_step C hC x j w hw he
      exact (ih a ha.1 ha.2.2.2.2.1).tail ha

lemma changed_after {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (x : Fin n → Bool) (j w : ℕ)
    (hw : Changed C x j w) : n + j ≤ w := by
  have hp := changed_path C hC x j w hw
  clear hw
  induction hp with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans hstep.1.le



def CleanWire {n : ℕ} (C : Circuit) (F : (Fin n → Bool) → Bool) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, value C x w = true → F x = true

lemma value_gateAt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    value C x w = (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op.eval
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs.map
        fun r => if r < w then value C x r else false) := by
  have hk : w - n < C.gates.length := by
    change w < n + C.gates.length at hw
    omega
  simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt,
    List.getD_eq_getElem _ _ hk] using gate_value C x w hn hw

lemma or_input_clean {n : ℕ} (C : Circuit) (F : (Fin n → Bool) → Bool)
    (a w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) (ha : a < w)
    (hai : a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.or)
    (hclean : CleanWire C F w) : CleanWire C F a := by
  intro x hx
  apply hclean x
  rw [value_gateAt C x w hn hw, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  refine ⟨true, ⟨a, hai, ?_⟩, rfl⟩
  simp [ha, hx]

lemma first_changed_clean_and {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (F : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (j o : ℕ)
    (ho : Changed C x j o) (hco : CleanWire C F o)
    (hjdirty : ¬ CleanWire C F (n + j)) :
    ∃ w a : ℕ, n + j < w ∧ Changed C x j w ∧ CleanWire C F w ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.and ∧
      SensitiveStep C x j a w ∧
      ∀ r < w, Changed C x j r → ¬ CleanWire C F r := by
  classical
  have hex : ∃ w, Changed C x j w ∧ CleanWire C F w := ⟨o, ho, hco⟩
  let w := Nat.find hex
  have hwp : Changed C x j w ∧ CleanWire C F w := Nat.find_spec hex
  have hleast (r : ℕ) (hr : r < w) (hrc : Changed C x j r) : ¬ CleanWire C F r := by
    intro hcl
    exact Nat.find_min hex hr ⟨hrc, hcl⟩
  have hafter := changed_after C hC x j w hwp.1
  have hne : w ≠ n + j := by
    intro h
    rw [h] at hwp
    exact hjdirty hwp.2
  have hstrict : n + j < w := by omega
  obtain ⟨a, has⟩ := changed_sensitive_step C hC x j w hwp.1 hne
  have hk : w - n < C.gates.length := by
    have ht := has.2.2.1
    change w < n + C.gates.length at ht
    omega
  have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.or := by
    simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hk,
      Set.mem_insert_iff, Set.mem_singleton_iff] using
      (hC C.gates[w - n] (List.getElem_mem hk)).1
  have hand : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.and := by
    rcases hop with h | h
    · exact h
    · exact False.elim (hleast a has.1 has.2.2.2.2.1
        (or_input_clean C F a w has.2.1 has.2.2.1 has.1 has.2.2.2.1 h hwp.2))
  exact ⟨w, a, hstrict, hwp.1, hwp.2, hand, has, hleast⟩



def OrSensitiveStep {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j a b : ℕ) : Prop :=
  SensitiveStep C x j a b ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (b - n)).op = GateOp.or

lemma changed_or_path_before {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (F : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (j stop : ℕ)
    (hunclean : ∀ r < stop, Changed C x j r → ¬ CleanWire C F r)
    (hunique : ∀ r, n ≤ r → r < n + C.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (r - n)).op = GateOp.and →
      ¬ CleanWire C F r → r = n + j)
    (w : ℕ) (hws : w < stop) (hw : Changed C x j w) :
    Relation.ReflTransGen (OrSensitiveStep C x j) (n + j) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases he : w = n + j
    · subst w
      exact Relation.ReflTransGen.refl
    · obtain ⟨a, has⟩ := changed_sensitive_step C hC x j w hw he
      have hk : w - n < C.gates.length := by
        have hlow := has.2.1
        have ht := has.2.2.1
        change w < n + C.gates.length at ht
        omega
      have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.and ∨
          (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.or := by
        simpa only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hk,
          Set.mem_insert_iff, Set.mem_singleton_iff] using
          (hC C.gates[w - n] (List.getElem_mem hk)).1
      have hor : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.or := by
        rcases hop with h | h
        · exact False.elim (he (hunique w has.2.1 has.2.2.1 h (hunclean w hws hw)))
        · exact h
      exact (ih a has.1 (has.1.trans hws) has.2.2.2.2.1).tail ⟨has, hor⟩

lemma first_changed_clean_and_or_path {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (F : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (j o : ℕ)
    (ho : Changed C x j o) (hco : CleanWire C F o)
    (hjdirty : ¬ CleanWire C F (n + j))
    (hunique : ∀ r, n ≤ r → r < n + C.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (r - n)).op = GateOp.and →
      ¬ CleanWire C F r → r = n + j) :
    ∃ w a : ℕ, n + j < w ∧ Changed C x j w ∧ CleanWire C F w ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.and ∧
      SensitiveStep C x j a w ∧
      Relation.ReflTransGen (OrSensitiveStep C x j) (n + j) a := by
  obtain ⟨w, a, hjw, hw, hclean, hop, has, hfirst⟩ :=
    first_changed_clean_and C hC F x j o ho hco hjdirty
  exact ⟨w, a, hjw, hw, hclean, hop, has,
    changed_or_path_before C hC F x j w hfirst hunique a has.1 has.2.2.2.2.1⟩



lemma or_input_true {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (a w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) (ha : a < w)
    (hai : a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).inputs)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op = GateOp.or)
    (hat : value C x a = true) : value C x w = true := by
  rw [value_gateAt C x w hn hw, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  refine ⟨true, ⟨a, hai, ?_⟩, rfl⟩
  simp [ha, hat]

lemma or_sensitive_path_true {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (j a b : ℕ)
    (hp : Relation.ReflTransGen (OrSensitiveStep C x j) a b)
    (ha : value C y a = true) : value C y b = true := by
  induction hp with
  | refl => exact ha
  | tail _ hs ih =>
    exact or_input_true C y _ _ hs.1.2.1 hs.1.2.2.1 hs.1.1 hs.1.2.2.2.1 hs.2 ih

lemma clean_and_mask {n : ℕ} (C : Circuit) (F : (Fin n → Bool) → Bool)
    (w a b g : ℕ) (c : Fin n) (hn : n ≤ w) (hw : w < n + C.size)
    (ha : a < w) (hb : b < w)
    (hg : PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n) = ⟨GateOp.and, [a, b]⟩)
    (hclean : CleanWire C F w)
    (hga : ∀ y : Fin n → Bool, value C y g = true → value C y a = true)
    (hcb : ∀ y : Fin n → Bool, y c = true → value C y b = true) :
    ∀ y : Fin n → Bool, value C y g = true → y c = true → F y = true := by
  intro y hgy hcy
  apply hclean y
  rw [value_gateAt C y w hn hw, hg]
  simp [GateOp.eval, ha, hb, hga y hgy, hcb y hcy]



open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

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


lemma or_sensitive_path_reaches {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j w : ℕ)
    (hj : j < C.gates.length)
    (hp : Relation.ReflTransGen (OrSensitiveStep C x j) (n + j) w) :
    OrReaches n C w j := by
  induction hp with
  | refl => exact (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩
  | @tail a b hp hs ih =>
    have hab : a < b := hs.1.1
    have hbn : n ≤ b := hs.1.2.1
    have hbl : b < n + C.gates.length := hs.1.2.2.1
    have hbe : b = n + (b - n) := by omega
    rw [hbe]
    apply (orReaches_iff n C (b - n) j).mpr
    exact ⟨by omega, Or.inr ⟨hs.2, a, hs.1.2.2.2.1, by omega, ih⟩⟩

lemma first_changed_clean_and_orReaches {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (F : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) (j o : ℕ) (hj : j < C.gates.length)
    (ho : Changed C x j o) (hco : CleanWire C F o)
    (hjdirty : ¬ CleanWire C F (n + j))
    (hunique : ∀ r, n ≤ r → r < n + C.size →
      (gateAt C (r - n)).op = GateOp.and → ¬ CleanWire C F r → r = n + j) :
    ∃ w a : ℕ, n + j < w ∧ Changed C x j w ∧ CleanWire C F w ∧
      (gateAt C (w - n)).op = GateOp.and ∧ SensitiveStep C x j a w ∧
      OrReaches n C a j := by
  obtain ⟨w, a, hjw, hw, hclean, hop, has, hpath⟩ :=
    first_changed_clean_and_or_path C hC F x j o ho hco hjdirty hunique
  exact ⟨w, a, hjw, hw, hclean, hop, has, or_sensitive_path_reaches C x j a hj hpath⟩



lemma changed_origin {n : ℕ} (C : Circuit)
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (x : Fin n → Bool) (j w : ℕ)
    (hw : Changed C x j w) : Changed C x j (n + j) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases he : w = n + j
    · simpa only [he] using hw
    · obtain ⟨a, ha⟩ := changed_sensitive_step C hC x j w hw he
      exact ih a ha.1 ha.2.2.2.2.1

open PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma ao_monotone {n : ℕ} (C : Circuit) (hA : IsAO2 n C) :
    PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hA.1 g hg,
    (hA.2.2 g hg).le⟩

lemma dirty_wire_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) :
    ¬ CleanWire C (graphFun G ∅) (n + j) ↔ ¬ BelowF G C j := Iff.rfl

lemma unique_junk_wire {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hjunk : junk G C = {j})
    (r : ℕ) (hn : n ≤ r) (hr : r < n + C.size)
    (hop : (gateAt C (r - n)).op = GateOp.and)
    (hdirty : ¬ CleanWire C (graphFun G ∅) r) : r = n + j := by
  classical
  have hk : r - n < C.gates.length := by change r < n + C.gates.length at hr; omega
  have he : n + (r - n) = r := by omega
  have hd : IsDirtyAnd n G C (r - n) := by
    refine ⟨hop, hk, ?_⟩
    have hx : ∃ x : Fin n → Bool, value C x r = true ∧ graphFun G ∅ x = false := by
      simpa only [CleanWire, not_forall, not_imp, Bool.not_eq_true, exists_prop] using hdirty
    obtain ⟨x, hx, hf⟩ := hx
    refine ⟨x, ?_, hf⟩
    change value C x (n + (r - n)) = true
    rw [he]
    exact hx
  have hm : r - n ∈ junk G C := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hd⟩
  rw [hjunk] at hm
  have heq := Finset.mem_singleton.mp hm
  omega

lemma junk_origin_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hjunk : junk G C = {j}) :
    j < C.gates.length ∧ ¬ CleanWire C (graphFun G ∅) (n + j) := by
  have hm : j ∈ junk G C := by rw [hjunk]; simp
  obtain ⟨hjr, hdirty⟩ := Finset.mem_filter.mp hm
  have hj := Finset.mem_range.mp hjr
  obtain ⟨hop, hj', x, hx, hf⟩ := hdirty
  exact ⟨hj, fun h => Bool.noConfusion (hf.symm.trans (h x hx))⟩

lemma changed_output_reaches_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : IsAO2 n C) (j : ℕ) (hjunk : junk G C = {j})
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (x : Fin n → Bool) (hx : C.eval (List.ofFn x) = true)
    (hz : (zeroAt C j).eval (List.ofFn x) = false) :
    ∃ k ∈ tops G C, ∃ b : Fin 2, OrReaches n C (opnd C k b) j ∧
      gateVal n C k x = true ∧ gateVal n C j x = true := by
  classical
  have hC := ao_monotone C hA
  have hchanged : Changed C x j C.output := ⟨hx, hz⟩
  have hcleano : CleanWire C (graphFun G ∅) C.output := by
    intro y hy
    have h := congrFun hfun y
    exact h.symm.trans hy
  obtain ⟨hj, hdirty⟩ := junk_origin_dirty G C j hjunk
  obtain ⟨w, a, hjw, hw, hclean, hop, hstep, hreach⟩ :=
    first_changed_clean_and_orReaches C hC (graphFun G ∅) x j C.output hj
      hchanged hcleano hdirty (unique_junk_wire G C j hjunk)
  have hn : n ≤ w := hstep.2.1
  have hwl : w < n + C.gates.length := hstep.2.2.1
  have hk : w - n < C.gates.length := by omega
  have he : n + (w - n) = w := by omega
  have ht : w - n ∈ tops G C := by
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
    refine ⟨hk, hop, ?_⟩
    intro y hy
    apply hclean y
    change value C y (n + (w - n)) = true at hy
    simpa only [he] using hy
  have hlen : (gateAt C (w - n)).inputs.length = 2 := by
    apply hA.2.2
    rw [gateAt, List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  obtain ⟨u, v, huv⟩ := List.length_eq_two.mp hlen
  have hm : a = u ∨ a = v := by simpa only [huv, List.mem_cons, List.not_mem_nil, or_false] using hstep.2.2.2.1
  have hgv : gateVal n C (w - n) x = true := by
    change value C x (n + (w - n)) = true
    rw [he]
    exact hw.1
  have hjv : gateVal n C j x = true := (changed_origin C hC x j C.output hchanged).1
  refine ⟨w - n, ht, ?_⟩
  rcases hm with rfl | rfl
  · exact ⟨0, by simpa [opnd, huv] using hreach, hgv, hjv⟩
  · exact ⟨1, by simpa [opnd, huv] using hreach, hgv, hjv⟩

end PEqualNP.Outside.L_meta_1477.SensitivePath

namespace PEqualNP.Outside.L_meta_1477.SensitiveMask

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma sensitive_pair_mask {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : IsAO2 n C) (hT : TopForm G C)
    (j : ℕ) (hjunk : junk G C = {j})
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (u v : Fin n) (hx : C.eval (List.ofFn (pairInput u v)) = true)
    (hz : (PEqualNP.Outside.L_meta_1477.SensitivePath.zeroAt C j).eval
      (List.ofFn (pairInput u v)) = false) :
    ∃ c : Fin n, c ∈ wmax G C j ∧ (c = u ∨ c = v) ∧
      gateVal n C j (pairInput u v) = true := by
  obtain ⟨k, hk, b, hreach, hfire, hgf⟩ :=
    PEqualNP.Outside.L_meta_1477.SensitivePath.changed_output_reaches_top
      G C hA j hjunk hfun (pairInput u v) hx hz
  exact PEqualNP.Outside.L_meta_1477.OneJunk.top_pair_mask G C
    (PEqualNP.Outside.L_meta_1477.OneJunk.P2.ao_of n C hA)
    hT j hjunk k hk b hreach u v hfire hgf

end PEqualNP.Outside.L_meta_1477.SensitiveMask


namespace PEqualNP.Outside.L_meta_1477.GateReplacement

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

lemma bool_le_iff_true (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

lemma op_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i ≤ g i) :
    op.eval (ins.map f) ≤ op.eval (ins.map g) := by
  rw [bool_le_iff_true]
  intro hf
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true] at hf ⊢
    intro b hb
    rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
    exact (bool_le_iff_true _ _).mp (h i)
      (hf (f i) (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · simp only [GateOp.eval, List.any_eq_true] at hf ⊢
    rcases hf with ⟨b, hb, hbt⟩
    rcases List.mem_map.mp hb with ⟨i, hi, rfl⟩
    exact ⟨g i, List.mem_map.mpr ⟨i, hi, rfl⟩,
      (bool_le_iff_true _ _).mp (h i) hbt⟩

lemma step_mono (w v : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : w.length = v.length) (h : ∀ i, w.getD i false ≤ v.getD i false) :
    ∀ i, (step w g).getD i false ≤ (step v g).getD i false := by
  intro i
  by_cases hi : i < w.length
  · rw [step_lt _ _ _ hi, step_lt _ _ _ (by omega)]
    exact h i
  · by_cases heq : i = w.length
    · rw [step_last _ _ _ heq, step_last _ _ _ (heq.trans hlen)]
      exact op_mono g.op hop _ _ _ h
    · rw [List.getD_eq_default _ _ (by rw [step_len]; omega),
        List.getD_eq_default _ _ (by rw [step_len]; omega)]

lemma fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (h : ∀ i, w.getD i false ≤ v.getD i false) :
    ∀ i, (gs.foldl step w).getD i false ≤ (gs.foldl step v).getD i false := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
    · simp only [step_len, hlen]
    · exact step_mono w v g (hgs g (by simp)) hlen h

lemma fold_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by rw [step_len]; omega), step_lt _ _ _ hi]

def zeroGate : Gate := ⟨GateOp.or, []⟩

lemma step_zero_le (w : List Bool) (g : Gate) :
    ∀ i, (step w zeroGate).getD i false ≤ (step w g).getD i false := by
  intro i
  by_cases hi : i < w.length
  · rw [step_lt _ _ _ hi, step_lt _ _ _ hi]
  · by_cases heq : i = w.length
    · rw [step_last _ _ _ heq, step_last _ _ _ heq]
      simp [zeroGate, GateOp.eval]
    · rw [List.getD_eq_default _ _ (by rw [step_len]; omega),
        List.getD_eq_default _ _ (by rw [step_len]; omega)]


def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma step_replace_le (w : List Bool) (g h : Gate)
    (hle : gateValue w h ≤ gateValue w g) :
    ∀ i, (step w h).getD i false ≤ (step w g).getD i false := by
  intro i
  by_cases hi : i < w.length
  · rw [step_lt _ _ _ hi, step_lt _ _ _ hi]
  · by_cases heq : i = w.length
    · rw [step_last _ _ _ heq, step_last _ _ _ heq]
      exact hle
    · rw [List.getD_eq_default _ _ (by rw [step_len]; omega),
        List.getD_eq_default _ _ (by rw [step_len]; omega)]

lemma set_gate_le (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool) (k : ℕ) (h : Gate)
    (hle : gateValue ((gs.take k).foldl step w) h ≤
      gateValue ((gs.take k).foldl step w) (gs.getD k zeroGate)) :
    ∀ i, ((gs.set k h).foldl step w).getD i false ≤
      (gs.foldl step w).getD i false := by
  induction gs generalizing w k with
  | nil => intro i; simp
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      apply fold_mono gs (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
      · simp only [step_len]
      · apply step_replace_le
        simpa using hle
    | succ k =>
      simpa only [List.set_cons_succ, List.foldl_cons] using
        ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) (step w g) k
          (by simpa using hle)

lemma set_gate_eq_of_local_eq (gs : List Gate) (w : List Bool) (k : ℕ) (h : Gate)
    (heq : gateValue ((gs.take k).foldl step w) h =
      gateValue ((gs.take k).foldl step w) (gs.getD k zeroGate)) :
    (gs.set k h).foldl step w = gs.foldl step w := by
  induction gs generalizing w k with
  | nil => simp
  | cons g gs ih =>
    cases k with
    | zero =>
      have hs : step w h = step w g := by
        have he : gateValue w h = gateValue w g := by simpa using heq
        exact congrArg (fun b => w ++ [b]) he
      simp only [List.set_cons_zero, List.foldl_cons, hs]
    | succ k =>
      simpa only [List.set_cons_succ, List.foldl_cons] using
        ih (step w g) k (by simpa using heq)

lemma set_zero_le_set_gate (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool) (k : ℕ) (h : Gate) :
    ∀ i, ((gs.set k zeroGate).foldl step w).getD i false ≤
      ((gs.set k h).foldl step w).getD i false := by
  induction gs generalizing w k with
  | nil => intro i; simp
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      apply fold_mono gs (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
      · simp only [step_len]
      · exact step_zero_le w h
    | succ k =>
      simpa only [List.set_cons_succ, List.foldl_cons] using
        ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) (step w g) k

lemma set_gate_true_of_sensitive_preserved (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : List Bool) (k out : ℕ) (h : Gate)
    (hout : (gs.foldl step w).getD out false = true)
    (hsensitive : ((gs.set k zeroGate).foldl step w).getD out false = false →
      gateValue ((gs.take k).foldl step w) h =
        gateValue ((gs.take k).foldl step w) (gs.getD k zeroGate)) :
    ((gs.set k h).foldl step w).getD out false = true := by
  cases hz : ((gs.set k zeroGate).foldl step w).getD out false with
  | false => rw [set_gate_eq_of_local_eq gs w k h (hsensitive hz)]; exact hout
  | true => exact Bool.le_iff_imp.mp (set_zero_le_set_gate gs hgs w k h out) hz

def replaceGate (C : Circuit) (k : ℕ) (g : Gate) : Circuit :=
  { C with gates := C.gates.set k g }

lemma replaceGate_size (C : Circuit) (k : ℕ) (g : Gate) :
    (replaceGate C k g).size = C.size := by
  simp [replaceGate, Circuit.size]


lemma list_set_all {α : Type*} (P : α → Prop) (gs : List α) (k : ℕ) (h : α)
    (hgs : ∀ g ∈ gs, P g) (hh : P h) : ∀ g ∈ gs.set k h, P g := by
  induction gs generalizing k with
  | nil => simp
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons]
      intro a ha
      rcases ha with rfl | ha
      · exact hh
      · exact hgs a (List.mem_cons_of_mem _ ha)
    | succ k =>
      simp only [List.set_cons_succ, List.mem_cons]
      intro a ha
      rcases ha with rfl | ha
      · exact hgs _ (by simp)
      · exact ih k (fun b hb => hgs b (List.mem_cons_of_mem _ hb)) a ha

lemma replaceGate_monotone2 (C : Circuit) (k : ℕ) (g : Gate)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    PEqualNP.MetaComplexity.Monotone2 (replaceGate C k g) :=
  list_set_all _ C.gates k g hC hg

lemma circuitFun_monotone {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) :
    Monotone (PEqualNP.MetaComplexity.circuitFun n C) := by
  intro x y hxy
  apply fold_mono C.gates hC (List.ofFn x) (List.ofFn y) (by simp)
  intro i
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hi)]
    simpa using hxy ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simpa using hi),
      List.getD_eq_default _ _ (by simpa using hi)]

lemma pairInput_le {n : ℕ} {u v : Fin n} {x : Fin n → Bool}
    (hu : x u = true) (hv : x v = true) : PEqualNP.EdgeOwnership.pairInput u v ≤ x := by
  intro i
  rw [bool_le_iff_true]
  intro hi
  simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hi
  rcases hi with rfl | rfl <;> assumption

lemma graph_eq_of_le_and_pairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool) (hm : Monotone f)
    (hle : ∀ x, f x ≤ PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x)
    (hpairs : ∀ u v, G.Adj u v → f (PEqualNP.EdgeOwnership.pairInput u v) = true) :
    f = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  funext x
  apply le_antisymm (hle x)
  rw [bool_le_iff_true]
  intro hg
  simp [PEqualNP.MetaComplexity.NestedCover.graphFun] at hg
  rcases hg with ⟨u, v, huv, hu, hv⟩
  exact (bool_le_iff_true _ _).mp (hm (pairInput_le hu hv)) (hpairs u v huv)

lemma replaceGate_graph_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (k : ℕ) (h : Gate)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hh : h.op = GateOp.and ∨ h.op = GateOp.or)
    (hgraph : PEqualNP.MetaComplexity.circuitFun n C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (hle : ∀ x : Fin n → Bool,
      gateValue ((C.gates.take k).foldl step (List.ofFn x)) h ≤
        gateValue ((C.gates.take k).foldl step (List.ofFn x)) (C.gates.getD k zeroGate))
    (hkeep : ∀ u v : Fin n, G.Adj u v →
      ((C.gates.set k zeroGate).foldl step
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD C.output false = false →
      gateValue ((C.gates.take k).foldl step
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))) h =
      gateValue ((C.gates.take k).foldl step
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))) (C.gates.getD k zeroGate)) :
    PEqualNP.MetaComplexity.circuitFun n (replaceGate C k h) =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  apply graph_eq_of_le_and_pairs
  · exact circuitFun_monotone (replaceGate C k h) (list_set_all _ C.gates k h hC hh)
  · intro x
    rw [← hgraph]
    exact set_gate_le C.gates hC (List.ofFn x) k h (hle x) C.output
  · intro u v huv
    apply set_gate_true_of_sensitive_preserved C.gates hC
      (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) k C.output h
    · change PEqualNP.MetaComplexity.circuitFun n C
        (PEqualNP.EdgeOwnership.pairInput u v) = true
      rw [hgraph]
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
        false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
      exact ⟨u, v, huv, by simp [PEqualNP.EdgeOwnership.pairInput],
        by simp [PEqualNP.EdgeOwnership.pairInput]⟩
    · exact hkeep u v huv


lemma prefix_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (a : Fin n) :
    ((gs.take k).foldl step (List.ofFn x)).getD a.val false = x a := by
  rw [fold_preserves _ _ _ (by simpa using a.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using a.isLt)]
  simp

lemma set_gate_value_at (gs : List Gate) (w : List Bool) (k : ℕ) (h : Gate)
    (hk : k < gs.length) :
    ((gs.set k h).foldl step w).getD (w.length + k) false =
      gateValue ((gs.take k).foldl step w) h := by
  induction gs generalizing w k with
  | nil => simp at hk
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons, Nat.add_zero, List.take_zero,
        List.foldl_nil]
      rw [fold_preserves _ _ _ (by rw [step_len]; omega), step_last _ _ _ rfl]
      rfl
    | succ k =>
      have hi := ih (step w g) k (by simpa using hk)
      simpa only [List.set_cons_succ, List.foldl_cons, List.take_succ_cons,
        step_len, Nat.add_assoc, Nat.add_comm 1 k] using hi

lemma replace_and_with_input_graph_correct {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (k u v : ℕ) (a : Fin n)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hgraph : PEqualNP.MetaComplexity.circuitFun n C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (hgate : C.gates.getD k zeroGate = ⟨GateOp.and, [u, v]⟩)
    (hdom : ∀ x : Fin n → Bool,
      x a ≤ ((C.gates.take k).foldl step (List.ofFn x)).getD u false)
    (hkeep : ∀ p q : Fin n, G.Adj p q →
      ((C.gates.set k zeroGate).foldl step
        (List.ofFn (PEqualNP.EdgeOwnership.pairInput p q))).getD C.output false = false →
      PEqualNP.EdgeOwnership.pairInput p q a = true) :
    PEqualNP.MetaComplexity.circuitFun n (replaceGate C k ⟨GateOp.and, [a.val, v]⟩) =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  apply replaceGate_graph_correct G C k _ hC (Or.inl rfl) hgraph
  · intro x
    simp only [gateValue, hgate, List.map_cons, List.map_nil, GateOp.eval,
      List.all_cons, List.all_nil, Bool.and_true, prefix_input]
    apply Bool.le_iff_imp.mpr
    intro h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨Bool.le_iff_imp.mp (hdom x) h.1, h.2⟩
  · intro p q hpq hz
    have ha := hkeep p q hpq hz
    have hu := Bool.le_iff_imp.mp (hdom (PEqualNP.EdgeOwnership.pairInput p q)) ha
    rw [hgate]
    simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
      List.all_nil, Bool.and_true, prefix_input, ha, hu]

lemma replaced_star_below_graph {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (k v : ℕ) (a : Fin n)
    (hk : k < C.gates.length)
    (hmask : ∀ x : Fin n → Bool, x a = true →
      ((C.gates.take k).foldl step (List.ofFn x)).getD v false = true →
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) :
    PEqualNP.TopForm.BelowF G (replaceGate C k ⟨GateOp.and, [a.val, v]⟩) k := by
  intro x hx
  change ((C.gates.set k ⟨GateOp.and, [a.val, v]⟩).foldl step (List.ofFn x)).getD
    (n + k) false = true at hx
  have he := set_gate_value_at C.gates (List.ofFn x) k ⟨GateOp.and, [a.val, v]⟩ hk
  simp only [List.length_ofFn] at he
  rw [he] at hx
  simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval,
    List.all_cons, List.all_nil, Bool.and_true, prefix_input, Bool.and_eq_true] at hx
  exact hmask x hx.1 hx.2

end PEqualNP.Outside.L_meta_1477.GateReplacement

namespace PEqualNP.Outside.L_meta_1477.OneCenterElimination

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open GateReplacement

lemma prefix_wire_eq {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j r : ℕ)
    (hj : j < C.gates.length) (hr : r < n + j) :
    ((C.gates.take j).foldl step (List.ofFn x)).getD r false = OneJunk.P2.W n C x r := by
  have hlen : ((C.gates.take j).foldl step (List.ofFn x)).length = n + j := by
    change (W (C.gates.take j) x).length = _
    rw [W_len, List.length_take, Nat.min_eq_left (by omega)]
  have he := fold_preserves (C.gates.drop j) ((C.gates.take j).foldl step (List.ofFn x))
    r (by rw [hlen]; exact hr)
  change _ = (C.gates.foldl step (List.ofFn x)).getD r false
  symm
  simpa only [← List.foldl_append, List.take_append_drop] using he

lemma sole_effective_mask_replacement {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hA : IsAO2 n C) (hT : TopForm G C)
    (j : ℕ) (hjunk : junk G C = {j})
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (a : Fin n) (haside : a ∈ side (n := n) C j 0) (hamask : a ∈ wmax G C j)
    (hunique : ∀ c : Fin n, c ∈ wmax G C j →
      (∃ u v : Fin n, G.Adj u v ∧ (c = u ∨ c = v) ∧
        gateVal n C j (pairInput u v) = true) → c = a) :
    let D := replaceGate C j ⟨GateOp.and, [a.val, opnd C j 1]⟩
    PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ ∧
      D.size = C.size ∧ PEqualNP.MetaComplexity.Monotone2 D ∧ BelowF G D j := by
  dsimp only
  have hgj : j ∈ junk G C := by rw [hjunk]; exact Finset.mem_singleton_self j
  obtain ⟨-, hjop, hjlen, _⟩ := (OneJunk.P2.mem_filter' _ _ _ _).mp hgj
  have hao := OneJunk.P2.ao_of n C hA
  have hin := OneJunk.P2.opnd_eq n C hao j hjlen
  have hlt := OneJunk.P2.opnd_lt n C hao j hjlen (opnd C j) hin
  have hgate : C.gates.getD j zeroGate = ⟨GateOp.and, [opnd C j 0, opnd C j 1]⟩ := by
    change gateAt C j = _
    cases he : gateAt C j with
    | mk op ins =>
      simp only [he] at hjop hin
      subst op
      subst ins
      rfl
  have hdom : ∀ x : Fin n → Bool,
      x a ≤ ((C.gates.take j).foldl step (List.ofFn x)).getD (opnd C j 0) false := by
    intro x
    rw [prefix_wire_eq C x j _ hjlen (hlt 0)]
    apply Bool.le_iff_imp.mpr
    intro hxa
    apply OneJunk.P2.orR_mono n C hao x _ a.val
      ((OneJunk.P2.mem_orIn n C hao _ ((hlt 0).trans (by omega)) a).mp haside)
    rw [OneJunk.P2.W_input n C x a.val a.isLt]
    exact hxa
  have hCops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hA.1
  have hkeep : ∀ p q : Fin n, G.Adj p q →
      ((C.gates.set j zeroGate).foldl step (List.ofFn (pairInput p q))).getD C.output false = false →
      pairInput p q a = true := by
    intro p q hpq hz
    have hx : C.eval (List.ofFn (pairInput p q)) = true := by
      change PEqualNP.MetaComplexity.circuitFun n C (pairInput p q) = true
      rw [hfun]
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    obtain ⟨c, hc, hcpq, hfire⟩ :=
      SensitiveMask.sensitive_pair_mask G C hA hT j hjunk hfun p q hx hz
    have hca := hunique c hc ⟨p, q, hpq, hcpq, hfire⟩
    subst c
    simpa only [pairInput, decide_eq_true_eq] using hcpq
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    refine ⟨?_, by rw [hA.2.2 g hg]⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hCops g hg
  refine ⟨replace_and_with_input_graph_correct G C j _ _ a hCops hfun hgate hdom hkeep,
    replaceGate_size C j _, replaceGate_monotone2 C j _ hm (by simp), ?_⟩
  apply replaced_star_below_graph G C j _ a hjlen
  intro x hxa hv
  have hu := Bool.le_iff_imp.mp (hdom x) hxa
  rw [prefix_wire_eq C x j _ hjlen (hlt 0)] at hu
  rw [prefix_wire_eq C x j _ hjlen (hlt 1)] at hv
  have hfire : gateVal n C j x = true := by
    change OneJunk.P2.W n C x (n + j) = true
    rw [OneJunk.P2.W_and n C x j hjlen hjop _ _ hin (hlt 0) (hlt 1), hu, hv]
    rfl
  exact (Finset.mem_filter.mp hamask).2 x hfire hxa

lemma getD_set_ne (gs : List Gate) (k i : ℕ) (h d : Gate) (hne : i ≠ k) :
    (gs.set k h).getD i d = gs.getD i d := by
  induction gs generalizing k i with
  | nil => simp
  | cons g gs ih =>
    cases k <;> cases i <;> simp_all

lemma sole_effective_mask_replacement_side {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hA : IsAO2 n C) (hT : TopForm G C)
    (j : ℕ) (hjunk : junk G C = {j})
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (a : Fin n) (b : Fin 2) (haside : a ∈ side (n := n) C j b) (hamask : a ∈ wmax G C j)
    (hunique : ∀ c : Fin n, c ∈ wmax G C j →
      (∃ u v : Fin n, G.Adj u v ∧ (c = u ∨ c = v) ∧
        gateVal n C j (pairInput u v) = true) → c = a) :
    let D := replaceGate C j ⟨GateOp.and, [a.val, opnd C j (1 - b)]⟩
    PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ ∧
      D.size = C.size ∧ PEqualNP.MetaComplexity.Monotone2 D ∧ BelowF G D j ∧
      ∀ i < D.gates.length, (gateAt D i).op = GateOp.and → BelowF G D i := by
  dsimp only
  have hgj : j ∈ junk G C := by rw [hjunk]; exact Finset.mem_singleton_self j
  obtain ⟨-, hjop, hjlen, _⟩ := (OneJunk.P2.mem_filter' _ _ _ _).mp hgj
  have hao := OneJunk.P2.ao_of n C hA
  have hin := OneJunk.P2.opnd_eq n C hao j hjlen
  have hlt := OneJunk.P2.opnd_lt n C hao j hjlen (opnd C j) hin
  have hgate : C.gates.getD j zeroGate = ⟨GateOp.and, [opnd C j 0, opnd C j 1]⟩ := by
    change gateAt C j = _
    cases he : gateAt C j with
    | mk op ins =>
      simp only [he] at hjop hin
      subst op
      subst ins
      rfl
  have hdom : ∀ x : Fin n → Bool,
      x a ≤ ((C.gates.take j).foldl step (List.ofFn x)).getD (opnd C j b) false := by
    intro x
    rw [prefix_wire_eq C x j _ hjlen (hlt b)]
    apply Bool.le_iff_imp.mpr
    intro hxa
    apply OneJunk.P2.orR_mono n C hao x _ a.val
      ((OneJunk.P2.mem_orIn n C hao _ ((hlt b).trans (by omega)) a).mp haside)
    rw [OneJunk.P2.W_input n C x a.val a.isLt]
    exact hxa
  have hCops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hA.1
  have hkeep : ∀ p q : Fin n, G.Adj p q →
      ((C.gates.set j zeroGate).foldl step (List.ofFn (pairInput p q))).getD C.output false = false →
      pairInput p q a = true := by
    intro p q hpq hz
    have hx : C.eval (List.ofFn (pairInput p q)) = true := by
      change PEqualNP.MetaComplexity.circuitFun n C (pairInput p q) = true
      rw [hfun]
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      exact ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    obtain ⟨c, hc, hcpq, hfire⟩ :=
      SensitiveMask.sensitive_pair_mask G C hA hT j hjunk hfun p q hx hz
    have hca := hunique c hc ⟨p, q, hpq, hcpq, hfire⟩
    subst c
    simpa only [pairInput, decide_eq_true_eq] using hcpq
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    refine ⟨?_, by rw [hA.2.2 g hg]⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hCops g hg
  have hcorrect : PEqualNP.MetaComplexity.circuitFun n
      (replaceGate C j ⟨GateOp.and, [a.val, opnd C j (1 - b)]⟩) = graphFun G ∅ := by
    apply replaceGate_graph_correct G C j _ hCops (Or.inl rfl) hfun
    · intro x
      rw [hgate]
      simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval,
        List.all_cons, List.all_nil, Bool.and_true, prefix_input]
      apply Bool.le_iff_imp.mpr
      simp only [Bool.and_eq_true]
      rintro ⟨ha, hv⟩
      exact OneJunk.P2.fin2_both
        (fun c => ((C.gates.take j).foldl step (List.ofFn x)).getD (opnd C j c) false = true)
        b (Bool.le_iff_imp.mp (hdom x) ha) hv
    · intro p q hpq hz
      have ha := hkeep p q hpq hz
      have hu := Bool.le_iff_imp.mp (hdom (pairInput p q)) ha
      rw [hgate]
      simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval,
        List.all_cons, List.all_nil, Bool.and_true, prefix_input]
      rcases OneJunk.P2.fin2_sub b with ⟨hb, hc⟩ | ⟨hb, hc⟩
      · simp only [hb] at hu
        simp only [hc, ha, hu, id_eq, Bool.true_and, Bool.and_true]
      · simp only [hb] at hu
        simp only [hc, ha, hu, id_eq, Bool.true_and, Bool.and_true]
  have hnewbel : BelowF G (replaceGate C j ⟨GateOp.and, [a.val, opnd C j (1 - b)]⟩) j := by
    apply replaced_star_below_graph G C j _ a hjlen
    intro x hxa hv
    have hu := Bool.le_iff_imp.mp (hdom x) hxa
    rw [prefix_wire_eq C x j _ hjlen (hlt b)] at hu
    rw [prefix_wire_eq C x j _ hjlen (hlt (1 - b))] at hv
    have hfire : gateVal n C j x = true := by
      change OneJunk.P2.W n C x (n + j) = true
      have hboth := OneJunk.P2.fin2_both
        (fun c => OneJunk.P2.W n C x (opnd C j c) = true) b hu hv
      rw [OneJunk.P2.W_and n C x j hjlen hjop _ _ hin (hlt 0) (hlt 1), hboth.1, hboth.2]
      rfl
    exact (Finset.mem_filter.mp hamask).2 x hfire hxa
  refine ⟨hcorrect, replaceGate_size C j _,
    replaceGate_monotone2 C j _ hm (by simp), hnewbel, ?_⟩
  intro i hi hop
  by_cases he : i = j
  · subst i
    exact hnewbel
  have hiold : i < C.gates.length := by simpa only [replaceGate, List.length_set] using hi
  have hge : gateAt (replaceGate C j ⟨GateOp.and, [a.val, opnd C j (1 - b)]⟩) i =
      gateAt C i := getD_set_ne C.gates j i _ _ he
  rw [hge] at hop
  have hbel : BelowF G C i := by
    by_contra hn
    have hdirty : PEqualNP.CleanedNonEdge.IsDirtyAnd n G C i := by
      unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
      refine ⟨hop, hiold, ?_⟩
      by_contra hnone
      apply hn
      intro x hx
      by_contra hfx
      exact hnone ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
    have hmj : i ∈ junk G C :=
      (OneJunk.P2.mem_filter' _ _ _ _).mpr ⟨Finset.mem_range.mpr hiold, hdirty⟩
    rw [hjunk] at hmj
    exact he (Finset.mem_singleton.mp hmj)
  intro x hx
  apply hbel x
  have hlocal : gateValue ((C.gates.take j).foldl step (List.ofFn x))
      ⟨GateOp.and, [a.val, opnd C j (1 - b)]⟩ ≤
      gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate) := by
    rw [hgate]
    simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval,
      List.all_cons, List.all_nil, Bool.and_true, prefix_input]
    apply Bool.le_iff_imp.mpr
    simp only [Bool.and_eq_true]
    rintro ⟨ha, hv⟩
    exact OneJunk.P2.fin2_both
      (fun c => ((C.gates.take j).foldl step (List.ofFn x)).getD (opnd C j c) false = true)
      b (Bool.le_iff_imp.mp (hdom x) ha) hv
  exact Bool.le_iff_imp.mp (set_gate_le C.gates hCops (List.ofFn x) j _ hlocal (n + i)) hx

end PEqualNP.Outside.L_meta_1477.OneCenterElimination


namespace PEqualNP.Outside.L_meta_1477.OverlapAlias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open GateReplacement

lemma pair_overlap_of_outside_mask {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : OneJunk.P2.AO n C) (hT : TopForm G C) (j : ℕ)
    (hj : junk G C = {j}) (z c u v : Fin n)
    (hinter : side (n := n) C j 0 ∩ side (n := n) C j 1 = {z})
    (hc0 : c ∉ side (n := n) C j 0) (hc1 : c ∉ side (n := n) C j 1)
    (hcv : c = u ∨ c = v) (hfire : gateVal n C j (pairInput u v) = true) :
    pairInput u v z = true := by
  rw [OneJunk.junk_value_product G C hA hT j hj] at hfire
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfire
  obtain ⟨⟨p, hp, hpu⟩, ⟨q, hq, hqv⟩⟩ := hfire
  simp only [pairInput, decide_eq_true_eq] at hpu hqv
  rcases hcv with rfl | rfl
  · have hpn : p ≠ c := fun h => hc0 (h ▸ hp)
    have hqn : q ≠ c := fun h => hc1 (h ▸ hq)
    have hpv := hpu.resolve_left hpn
    have hqv := hqv.resolve_left hqn
    subst p
    subst q
    have hvz : v = z := Finset.mem_singleton.mp (hinter ▸ Finset.mem_inter.mpr ⟨hp, hq⟩)
    rw [← hvz]
    simp [pairInput]
  · have hpn : p ≠ c := fun h => hc0 (h ▸ hp)
    have hqn : q ≠ c := fun h => hc1 (h ▸ hq)
    have hpu := hpu.resolve_right hpn
    have hqu := hqv.resolve_right hqn
    subst p
    subst q
    have huz : u = z := Finset.mem_singleton.mp (hinter ▸ Finset.mem_inter.mpr ⟨hp, hq⟩)
    rw [← huz]
    simp [pairInput]

lemma no_internal_mask_alias {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : IsAO2 n C) (hT : TopForm G C) (j : ℕ)
    (hjunk : junk G C = {j})
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) (z : Fin n)
    (hinter : side (n := n) C j 0 ∩ side (n := n) C j 1 = {z})
    (houtside : ∀ c ∈ wmax G C j,
      c ∉ side (n := n) C j 0 ∪ side (n := n) C j 1) :
    let D := replaceGate C j ⟨GateOp.or, [z.val]⟩
    PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      PEqualNP.MetaComplexity.Monotone2 D ∧
      ∀ i < D.gates.length, (gateAt D i).op = GateOp.and → BelowF G D i := by
  classical
  dsimp only
  have hgj : j ∈ junk G C := by rw [hjunk]; simp
  obtain ⟨-, hjop, hjlen, _⟩ := (OneJunk.P2.mem_filter' _ _ _ _).mp hgj
  have hao := OneJunk.P2.ao_of n C hA
  have hin := OneJunk.P2.opnd_eq n C hao j hjlen
  have hlt := OneJunk.P2.opnd_lt n C hao j hjlen (opnd C j) hin
  have hgate : C.gates.getD j zeroGate = ⟨GateOp.and, [opnd C j 0, opnd C j 1]⟩ := by
    change gateAt C j = _
    cases he : gateAt C j with
    | mk op ins =>
      simp only [he] at hjop hin
      subst op
      subst ins
      rfl
  have hzmem : z ∈ side (n := n) C j 0 ∩ side (n := n) C j 1 := by rw [hinter]; simp
  have hzside (b : Fin 2) : z ∈ side (n := n) C j b := by
    rcases OneJunk.P2.fin2_sub b with ⟨hb, _⟩ | ⟨hb, _⟩
    · rw [hb]; exact (Finset.mem_inter.mp hzmem).1
    · rw [hb]; exact (Finset.mem_inter.mp hzmem).2
  have hdom (x : Fin n → Bool) (b : Fin 2) :
      x z ≤ ((C.gates.take j).foldl step (List.ofFn x)).getD (opnd C j b) false := by
    rw [OneCenterElimination.prefix_wire_eq C x j _ hjlen (hlt b)]
    apply Bool.le_iff_imp.mpr
    intro hxz
    apply OneJunk.P2.orR_mono n C hao x _ z.val
      ((OneJunk.P2.mem_orIn n C hao _ ((hlt b).trans (by omega)) z).mp (hzside b))
    rw [OneJunk.P2.W_input n C x z.val z.isLt]
    exact hxz
  have hlocal (x : Fin n → Bool) :
      gateValue ((C.gates.take j).foldl step (List.ofFn x)) ⟨GateOp.or, [z.val]⟩ ≤
        gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate) := by
    rw [hgate]
    simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
      List.any_nil, Bool.or_false, List.all_cons, List.all_nil, Bool.and_true, prefix_input]
    apply Bool.le_iff_imp.mpr
    intro hxz
    simp only [Bool.and_eq_true]
    exact ⟨Bool.le_iff_imp.mp (hdom x 0) hxz, Bool.le_iff_imp.mp (hdom x 1) hxz⟩
  have hkeep : ∀ u v : Fin n, G.Adj u v →
      ((C.gates.set j zeroGate).foldl step (List.ofFn (pairInput u v))).getD C.output false = false →
      pairInput u v z = true := by
    intro u v huv hz
    have hx : C.eval (List.ofFn (pairInput u v)) = true := by
      change PEqualNP.MetaComplexity.circuitFun n C (pairInput u v) = true
      rw [hfun]
      exact (OneJunk.P1.S90.graphFun_pair G u v).mpr huv
    obtain ⟨c, hc, hcv, hfire⟩ := SensitiveMask.sensitive_pair_mask G C hA hT j hjunk hfun u v hx hz
    have hcnot := houtside c hc
    exact pair_overlap_of_outside_mask G C hao hT j hjunk z c u v hinter
      (fun hc0 => hcnot (Finset.mem_union_left _ hc0))
      (fun hc1 => hcnot (Finset.mem_union_right _ hc1)) hcv hfire
  have hcorrect : PEqualNP.MetaComplexity.circuitFun n
      (replaceGate C j ⟨GateOp.or, [z.val]⟩) = graphFun G ∅ := by
    apply replaceGate_graph_correct G C j _ hA.1 (Or.inr rfl) hfun hlocal
    intro u v huv hz
    have hzv := hkeep u v huv hz
    have h0 := Bool.le_iff_imp.mp (hdom (pairInput u v) 0) hzv
    have h1 := Bool.le_iff_imp.mp (hdom (pairInput u v) 1) hzv
    rw [hgate]
    simp only [gateValue, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
      List.any_nil, Bool.or_false, List.all_cons, List.all_nil, Bool.and_true,
      prefix_input, id_eq, hzv, h0, h1]
  refine ⟨hcorrect, replaceGate_size C j _, replaceGate_monotone2 C j _ ?_ (by simp), ?_⟩
  · exact SensitivePath.ao_monotone C hA
  · intro i hi hop
    by_cases he : i = j
    · subst i
      have hnew : gateAt (replaceGate C j ⟨GateOp.or, [z.val]⟩) j = ⟨GateOp.or, [z.val]⟩ := by
        change (C.gates.set j ⟨GateOp.or, [z.val]⟩).getD j zeroGate = _
        rw [List.getD_eq_getElem _ _ (by simpa using hjlen)]
        simp
      rw [hnew] at hop
      cases hop
    · have hiold : i < C.gates.length := by simpa only [replaceGate, List.length_set] using hi
      have hge : gateAt (replaceGate C j ⟨GateOp.or, [z.val]⟩) i = gateAt C i :=
        OneCenterElimination.getD_set_ne C.gates j i _ _ he
      rw [hge] at hop
      have hbel : BelowF G C i := by
        by_contra hn
        have hmj : i ∈ junk G C := (OneJunk.P1.junk_iff G C i).mpr ⟨hiold, hop, hn⟩
        rw [hjunk] at hmj
        exact he (Finset.mem_singleton.mp hmj)
      intro x hx
      apply hbel x
      exact Bool.le_iff_imp.mp (set_gate_le C.gates hA.1 (List.ofFn x) j _ (hlocal x) (n + i)) hx

end PEqualNP.Outside.L_meta_1477.OverlapAlias

namespace PEqualNP.Outside.L_meta_1477.SemanticOverride

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open GateReplacement

def constantGate (b : Bool) : Gate :=
  if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩

lemma gateValue_constant (w : List Bool) (b : Bool) : gateValue w (constantGate b) = b := by
  cases b <;> rfl

def auxiliary {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : Circuit := replaceGate C j (constantGate (f x))

def value {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (w : ℕ) (x : Fin n → Bool) : Bool := SensitivePath.value (auxiliary C j f x) x w

lemma value_input {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (a : Fin n) (x : Fin n → Bool) : value C j f a.val x = x a :=
  SensitivePath.input_value (auxiliary C j f x) x a

lemma value_at {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hj : j < C.gates.length) (x : Fin n → Bool) : value C j f (n + j) x = f x := by
  have h := set_gate_value_at C.gates (List.ofFn x) j (constantGate (f x)) hj
  simp only [List.length_ofFn, gateValue_constant] at h
  exact h

lemma take_set_same {α : Type*} (gs : List α) (j : ℕ) (a : α) :
    (gs.set j a).take j = gs.take j := by
  induction gs generalizing j with
  | nil => simp
  | cons g gs ih => cases j <;> simp_all

lemma prefix_wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j r : ℕ)
    (hj : j < C.gates.length) (hr : r < n + j) :
    ((C.gates.take j).foldl step (List.ofFn x)).getD r false = SensitivePath.value C x r := by
  have hlen : ((C.gates.take j).foldl step (List.ofFn x)).length = n + j := by
    change (W (C.gates.take j) x).length = _
    rw [W_len, List.length_take, Nat.min_eq_left (by omega)]
  have he := fold_preserves (C.gates.drop j) ((C.gates.take j).foldl step (List.ofFn x))
    r (by rw [hlen]; exact hr)
  change _ = (C.gates.foldl step (List.ofFn x)).getD r false
  symm
  simpa only [← List.foldl_append, List.take_append_drop] using he

lemma value_before {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hj : j < C.gates.length) (r : ℕ) (hr : r < n + j) (x : Fin n → Bool) :
    value C j f r x = SensitivePath.value C x r := by
  have haux := prefix_wire (auxiliary C j f x) x j r (by simpa [auxiliary, replaceGate] using hj) hr
  have hold := prefix_wire C x j r hj hr
  change _ = SensitivePath.value (auxiliary C j f x) x r at haux
  rw [show (auxiliary C j f x).gates.take j = C.gates.take j by
    exact take_set_same C.gates j (constantGate (f x))] at haux
  exact haux.symm.trans hold

lemma value_binary {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (k : ℕ) (hk : k < C.gates.length) (hkj : k ≠ j)
    (op : GateOp) (l r : ℕ) (hg : C.gates[k] = ⟨op, [l, r]⟩)
    (hl : l < n + k) (hr : r < n + k) (x : Fin n → Bool) :
    value C j f (n + k) x = op.eval [value C j f l x, value C j f r x] := by
  let D := auxiliary C j f x
  have hkD : k < D.gates.length := by simpa [D, auxiliary, replaceGate] using hk
  have hD : D.gates[k] = ⟨op, [l, r]⟩ := by
    have he : (C.gates.set j (constantGate (f x)))[k]'(by simpa using hk) = C.gates[k] :=
      List.getElem_set_of_ne (Ne.symm hkj) _ _
    exact he.trans hg
  have hv := SensitivePath.gate_value D x (n + k) (by omega)
    (by change n + k < n + D.gates.length; omega)
  simp only [Nat.add_sub_cancel_left] at hv
  rw [hD] at hv
  simpa only [List.map_cons, List.map_nil, ite_eq_left hl, ite_eq_left hr, value, D] using hv

lemma value_le {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hle : ∀ x : Fin n → Bool, f x ≤
      gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate))
    (w : ℕ) (x : Fin n → Bool) : value C j f w x ≤ SensitivePath.value C x w := by
  apply set_gate_le C.gates hC (List.ofFn x) j (constantGate (f x))
  rw [gateValue_constant]
  exact hle x

lemma output_true {n : ℕ} (C : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (hx : C.eval (List.ofFn x) = true)
    (hkeep : ((C.gates.set j zeroGate).foldl step (List.ofFn x)).getD C.output false = false →
      f x = gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate)) :
    value C j f C.output x = true := by
  apply set_gate_true_of_sensitive_preserved C.gates hC (List.ofFn x) j C.output
    (constantGate (f x)) hx
  intro hz
  rw [gateValue_constant]
  exact hkeep hz

lemma compiled_graph_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (j : ℕ) (f : (Fin n → Bool) → Bool)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hle : ∀ x : Fin n → Bool, f x ≤
      gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate))
    (hkeep : ∀ u v : Fin n, G.Adj u v →
      ((C.gates.set j zeroGate).foldl step (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD
        C.output false = false → f (PEqualNP.EdgeOwnership.pairInput u v) =
      gateValue ((C.gates.take j).foldl step (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)))
        (C.gates.getD j zeroGate))
    (hD : PEqualNP.MetaComplexity.Monotone2 D)
    (hval : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = value C j f C.output x) :
    PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ := by
  apply graph_eq_of_le_and_pairs
  · apply circuitFun_monotone D
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hD g hg).1
  · intro x
    rw [show PEqualNP.MetaComplexity.circuitFun n D x = value C j f C.output x from hval x]
    rw [← hfun]
    exact value_le C j f hC hle C.output x
  · intro u v huv
    rw [show PEqualNP.MetaComplexity.circuitFun n D (PEqualNP.EdgeOwnership.pairInput u v) =
      value C j f C.output (PEqualNP.EdgeOwnership.pairInput u v) from hval _]
    apply output_true C j f hC _ ?_ (hkeep u v huv)
    change PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v) = true
    rw [hfun]
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [PEqualNP.EdgeOwnership.pairInput], by simp [PEqualNP.EdgeOwnership.pairInput]⟩

end PEqualNP.Outside.L_meta_1477.SemanticOverride

namespace PEqualNP.Outside.L_meta_1477.RotationSemantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open OneJunk GateReplacement

def rotatedValue {n : ℕ} (C : Circuit) (j : ℕ) (b : Fin 2) (a z : Fin n)
    (x : Fin n → Bool) : Bool := x z || (x a && P2.W n C x (opnd C j (1 - b)))

lemma local_gate_value_eq {n : ℕ} (C : Circuit) (hA : P2.AO n C)
    (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate) =
      gateVal n C j x := by
  have hin := P2.opnd_eq n C hA j hj
  have hlt := P2.opnd_lt n C hA j hj (opnd C j) hin
  have hv := P1.S90.val_gate (C := C) (x := List.ofFn x) (n := n) (by simp) hj
  change gateVal n C j x = _ at hv
  rw [hv]
  change (gateAt C j).op.eval ((gateAt C j).inputs.map
    (fun i => ((C.gates.take j).foldl step (List.ofFn x)).getD i false)) = _
  rw [hin]
  simp only [List.map_cons, List.map_nil, if_pos (hlt 0), if_pos (hlt 1)]
  rw [SemanticOverride.prefix_wire C x j _ hj (hlt 0),
    SemanticOverride.prefix_wire C x j _ hj (hlt 1)]
  rfl

lemma side_input_true {n : ℕ} (C : Circuit) (hA : P2.AO n C)
    (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) (a : Fin n)
    (ha : a ∈ side (n := n) C j b) (x : Fin n → Bool) (hx : x a = true) :
    P2.W n C x (opnd C j b) = true := by
  have hlt := P2.opnd_lt n C hA j hj (opnd C j) (P2.opnd_eq n C hA j hj) b
  apply P2.orR_mono n C hA x _ a.val
    ((P2.mem_orIn n C hA _ (hlt.trans (by omega)) a).mp ha)
  rw [P2.W_input n C x a.val a.isLt]
  exact hx

lemma local_decrease {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (j : ℕ) (hjunk : junk G C = {j})
    (b : Fin 2) (a z : Fin n)
    (hz : z ∈ side (n := n) C j 0 ∩ side (n := n) C j 1)
    (ha : a ∈ side (n := n) C j b) (x : Fin n → Bool) :
    rotatedValue C j b a z x ≤
      gateValue ((C.gates.take j).foldl step (List.ofFn x)) (C.gates.getD j zeroGate) := by
  have hgj : j ∈ junk G C := by rw [hjunk]; simp
  obtain ⟨-, hjop, hjlen, _⟩ := (P2.mem_filter' _ _ _ _).mp hgj
  rw [local_gate_value_eq C hA j hjlen x]
  change _ ≤ P2.W n C x (n + j)
  have hin := P2.opnd_eq n C hA j hjlen
  have hlt := P2.opnd_lt n C hA j hjlen (opnd C j) hin
  rw [P2.W_and n C x j hjlen hjop _ _ hin (hlt 0) (hlt 1)]
  apply Bool.le_iff_imp.mpr
  intro hx
  change x z || (x a && P2.W n C x (opnd C j (1 - b))) = true at hx
  have hchoice : x z = true ∨ (x a = true ∧ P2.W n C x (opnd C j (1 - b)) = true) := by
    cases hzv : x z <;> cases hav : x a <;> cases hqv : P2.W n C x (opnd C j (1 - b)) <;> simp_all
  simp only [Bool.and_eq_true]
  rcases hchoice with hxz | ⟨hxa, hq⟩
  · exact ⟨side_input_true C hA j hjlen 0 z (Finset.mem_inter.mp hz).1 x hxz,
      side_input_true C hA j hjlen 1 z (Finset.mem_inter.mp hz).2 x hxz⟩
  · exact P2.fin2_both (fun c => P2.W n C x (opnd C j c) = true) b
      (side_input_true C hA j hjlen b a ha x hxa) hq

lemma sensitive_pair_equal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : IsAO2 n C) (hT : TopForm G C) (j : ℕ)
    (hjunk : junk G C = {j})
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (b : Fin 2) (a z : Fin n)
    (hinter : side (n := n) C j 0 ∩ side (n := n) C j 1 = {z})
    (hunique : ∀ c ∈ wmax G C j,
      c ∈ side (n := n) C j 0 ∪ side (n := n) C j 1 → c = a)
    (u v : Fin n) (huv : G.Adj u v)
    (hzero : ((C.gates.set j zeroGate).foldl step (List.ofFn (pairInput u v))).getD
      C.output false = false) :
    rotatedValue C j b a z (pairInput u v) =
      gateValue ((C.gates.take j).foldl step (List.ofFn (pairInput u v)))
        (C.gates.getD j zeroGate) := by
  have hao := P2.ao_of n C hA
  have hgj : j ∈ junk G C := by rw [hjunk]; simp
  obtain ⟨-, hjop, hjlen, _⟩ := (P2.mem_filter' _ _ _ _).mp hgj
  have hx : C.eval (List.ofFn (pairInput u v)) = true := by
    change PEqualNP.MetaComplexity.circuitFun n C (pairInput u v) = true
    rw [hfun]
    exact (P2.graphFun_pair G u v).mpr huv
  obtain ⟨c, hc, hcv, hfire⟩ :=
    SensitiveMask.sensitive_pair_mask G C hA hT j hjunk hfun u v hx hzero
  rw [local_gate_value_eq C hao j hjlen, hfire]
  by_cases hcin : c ∈ side (n := n) C j 0 ∪ side (n := n) C j 1
  · have hca := hunique c hc hcin
    have hxa : pairInput u v a = true := by
      rcases hcv with hcu | hcv
      · rw [← hca, hcu]; simp [pairInput]
      · rw [← hca, hcv]; simp [pairInput]
    have hin := P2.opnd_eq n C hao j hjlen
    have hlt := P2.opnd_lt n C hao j hjlen (opnd C j) hin
    change P2.W n C (pairInput u v) (n + j) = true at hfire
    rw [P2.W_and n C (pairInput u v) j hjlen hjop _ _ hin (hlt 0) (hlt 1)] at hfire
    have hboth : P2.W n C (pairInput u v) (opnd C j 0) = true ∧
        P2.W n C (pairInput u v) (opnd C j 1) = true := by
      simpa only [Bool.and_eq_true] using hfire
    have hq : P2.W n C (pairInput u v) (opnd C j (1 - b)) = true := by
      rcases P2.fin2_sub b with ⟨_, hb⟩ | ⟨_, hb⟩
      · rw [hb]; exact hboth.2
      · rw [hb]; exact hboth.1
    simp [rotatedValue, hxa, hq]
  · have hz := OverlapAlias.pair_overlap_of_outside_mask G C hao hT j hjunk z c u v hinter
      (fun h => hcin (Finset.mem_union_left _ h))
      (fun h => hcin (Finset.mem_union_right _ h)) hcv hfire
    simp [rotatedValue, hz]

lemma special_equation {n : ℕ} (C : Circuit) (hA : P2.AO n C)
    (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) (a z : Fin n) (x : Fin n → Bool) :
    SemanticOverride.value C j (rotatedValue C j b a z) (n + j) x =
      (x z || (x a && SemanticOverride.value C j (rotatedValue C j b a z)
        (opnd C j (1 - b)) x)) := by
  rw [SemanticOverride.value_at C j _ hj x,
    SemanticOverride.value_before C j _ hj _
      (P2.opnd_lt n C hA j hj (opnd C j) (P2.opnd_eq n C hA j hj) (1 - b)) x]
  rfl

end PEqualNP.Outside.L_meta_1477.RotationSemantics


namespace PEqualNP.Outside.L_meta_1477.OneJunkIsolation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open OneJunk

lemma top_cross_paths_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (k : ℕ) (hk : k ∈ tops G C) (b : Fin 2)
    (u v : Fin n) (hu : P2.OrR n C (opnd C k b) u.val)
    (hv : P2.OrR n C (opnd C k (1 - b)) v.val) : G.Adj u v := by
  have hk0 := (P2.mem_filter' _ _ _ _).mp hk
  have hklen := Finset.mem_range.mp hk0.1
  have hin := P2.opnd_eq n C hA k hklen
  rcases P2.fin2_sub b with ⟨hb, hc⟩ | ⟨hb, hc⟩
  · rw [hb] at hu
    rw [hc] at hv
    exact (P2.graphFun_pair G u v).mp
      (hk0.2.2 _ (P2.sem_adj n C hA k hklen hk0.2.1 (opnd C k) hin u v hu hv))
  · rw [hb] at hu
    rw [hc] at hv
    exact ((P2.graphFun_pair G v u).mp
      (hk0.2.2 _ (P2.sem_adj n C hA k hklen hk0.2.1 (opnd C k) hin v u hv hu))).symm

lemma unmaskable_singleton_wire_not_top_operand {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (z : Fin n)
    (hz : gateVal n C g (pairInput z z) = true)
    (w : ℕ) (hw : w < n + C.gates.length) (hwz : P2.OrR n C w z.val)
    (hno : ¬ ∃ c : Fin n, ∀ u ∈ orIn n C w, G.Adj u c)
    (k : ℕ) (hk : k ∈ tops G C) (b : Fin 2) :
    ¬ P2.OrR n C (opnd C k b) w := by
  intro hreach
  have hk0 := (P2.mem_filter' _ _ _ _).mp hk
  have hklen := Finset.mem_range.mp hk0.1
  have hin := P2.opnd_eq n C hA k hklen
  have hlt := P2.opnd_lt n C hA k hklen (opnd C k) hin
  obtain ⟨v, hpath, hleaf⟩ := P2.orR_leaf n C hA (opnd C k (1 - b))
    ((hlt (1 - b)).trans (by omega))
  rcases hleaf with hv | ⟨h, rfl, hh, hhop⟩
  · apply hno
    refine ⟨⟨v, hv⟩, ?_⟩
    intro u hu
    exact top_cross_paths_adj G C hA k hk b u ⟨v, hv⟩
      (hreach.trans ((P2.mem_orIn n C hA w hw u).mp hu)) hpath
  · have hc := operand_orR_inCone C hA k hklen (1 - b) h hpath
    have he := dirty_ancestor_eq G C hT g hg k hk h hh hhop hc
    subst h
    have hleft : P2.W n C (pairInput z z) (opnd C k b) = true := by
      apply P2.orR_mono n C hA _ _ z.val (hreach.trans hwz)
      rw [P2.W_input n C (pairInput z z) z.val z.isLt]
      simp [pairInput]
    have hright := P2.orR_mono n C hA (pairInput z z) _ _ hpath hz
    have hboth := P2.fin2_both
      (fun c => P2.W n C (pairInput z z) (opnd C k c) = true) b hleft hright
    have htop : gateVal n C k (pairInput z z) = true := by
      change P2.W n C (pairInput z z) (n + k) = true
      rw [P2.W_and n C _ k hklen hk0.2.1 _ _ hin (hlt 0) (hlt 1), hboth.1, hboth.2]
      rfl
    exact G.loopless.irrefl z ((P2.graphFun_pair G z z).mp (hk0.2.2 _ htop))


end PEqualNP.Outside.L_meta_1477.OneJunkIsolation


namespace PEqualNP.Outside.L_meta_1477.StructuralIsolation

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (B : Finset (Fin n)) (hB : 2 ≤ B.card)
    (a c : Fin n) (ha : ∀ b ∈ B, G.Adj a b) (hc : ∀ b ∈ B, G.Adj c b) : a = c := by
  by_contra hac
  have hsub : B ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha b hb, hc b hb⟩
  have hsmall := (Finset.card_le_card hsub).trans (h4 a c hac)
  omega

lemma augmented_star_has_no_mask {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (B : Finset (Fin n)) (hB : 2 ≤ B.card)
    (a z : Fin n) (ha : ∀ b ∈ B, G.Adj a b) (haz : ¬ G.Adj a z) :
    ¬ ∃ c : Fin n, ∀ b ∈ insert z B, G.Adj c b := by
  rintro ⟨c, hc⟩
  have hac := common_neighbor_unique G h4 B hB a c ha
    (fun b hb => hc b (Finset.mem_insert_of_mem hb))
  subst c
  exact haz (hc z (Finset.mem_insert_self _ _))

lemma different_sides_no_mask {n : ℕ} (G : SimpleGraph (Fin n))
    (side : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → side u ≠ side v)
    (a b : Fin n) (hab : side a ≠ side b) :
    ¬ ∃ c : Fin n, G.Adj c a ∧ G.Adj c b := by
  rintro ⟨c, hca, hcb⟩
  have h1 := hbip c a hca
  have h2 := hbip c b hcb
  cases ha : side a <;> cases hb : side b <;> cases hc : side c <;> simp_all

lemma masked_support_no_other_input {n : ℕ} (G : SimpleGraph (Fin n))
    (side : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → side u ≠ side v)
    (S T : Finset (Fin n)) (a b : Fin n) (ha : a ∈ S) (hb : b ∈ S)
    (hab : side a ≠ side b) (hcross : ∀ s ∈ S, ∀ t ∈ T, G.Adj s t) : T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  exact different_sides_no_mask G side hbip a b hab
    ⟨t, (hcross a ha t ht).symm, (hcross b hb t ht).symm⟩

end PEqualNP.Outside.L_meta_1477.StructuralIsolation


namespace PEqualNP.Outside.L_meta_1477.PrivateCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open OneJunk OneJunkIsolation

def marked {n : ℕ} (C : Circuit) (z a : Fin n) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun i =>
    z ∈ orIn n C (n + i) ∧ a ∈ orIn n C (n + i)

lemma marked_bounds {n : ℕ} (C : Circuit) (z a : Fin n) (i : ℕ)
    (hi : i ∈ marked C z a) : i < C.gates.length :=
  Finset.mem_range.mp (Finset.mem_filter.mp hi).1

lemma marked_op_or {n : ℕ} (C : Circuit) (z a : Fin n) (i : ℕ)
    (hi : i ∈ marked C z a) : (gateAt C i).op = GateOp.or :=
  ((P1.orIn_gate C i z).mp (Finset.mem_filter.mp hi).2.1).2.1

lemma marked_or_reader {n : ℕ} (C : Circuit) (hA : P2.AO n C)
    (z a : Fin n) (i k : ℕ) (hi : i ∈ marked C z a) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hread : n + i ∈ (gateAt C k).inputs) :
    k ∈ marked C z a := by
  have hi0 := (Finset.mem_filter.mp hi).2
  have hil := marked_bounds C z a i hi
  have hp : P2.OrR n C (n + k) (n + i) :=
    Relation.ReflTransGen.single ⟨k, rfl, hk, hop, hread⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr hk, ?_, ?_⟩
  · exact (P2.mem_orIn n C hA (n + k) (by omega) z).mpr
      (hp.trans ((P2.mem_orIn n C hA (n + i) (by omega) z).mp hi0.1))
  · exact (P2.mem_orIn n C hA (n + k) (by omega) a).mpr
      (hp.trans ((P2.mem_orIn n C hA (n + i) (by omega) a).mp hi0.2))

lemma marked_private_reads {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g}) (z a : Fin n)
    (hz : gateVal n C g (pairInput z z) = true) (hza : G.Adj z a)
    (sideB : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → sideB u ≠ sideB v)
    (k : ℕ) (hk : k < C.gates.length) (hkm : k ∉ marked C z a) (hkg : k ≠ g)
    (r : ℕ) (hr : r ∈ (gateAt C k).inputs) : r < n ∨ r - n ∉ marked C z a := by
  by_cases hrn : r < n
  · exact Or.inl hrn
  apply Or.inr
  intro hrm
  have hre : r = n + (r - n) := by omega
  have hir := marked_bounds C z a (r - n) hrm
  obtain ⟨hop, _, _, _, _, _⟩ := hA k hk
  rcases hop with hop | hop
  · have hbel : BelowF G C k := by
      by_contra hn
      have hmem := (P1.junk_iff G C k).mpr ⟨hk, hop, hn⟩
      rw [hg] at hmem
      exact hkg (Finset.mem_singleton.mp hmem)
    have htop : k ∈ tops G C :=
      (P2.mem_filter' _ _ _ _).mpr ⟨Finset.mem_range.mpr hk, hop, hbel⟩
    have hin := P2.opnd_eq n C hA k hk
    rw [hin] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨b, hb⟩ : ∃ b : Fin 2, opnd C k b = r := by
      rcases hr with hr | hr
      · exact ⟨0, hr.symm⟩
      · exact ⟨1, hr.symm⟩
    have hmem := (Finset.mem_filter.mp hrm).2
    have hpath : P2.OrR n C (n + (r - n)) z.val :=
      (P2.mem_orIn n C hA _ (by omega) z).mp hmem.1
    have hno : ¬ ∃ c : Fin n, ∀ u ∈ orIn n C (n + (r - n)), G.Adj u c := by
      rintro ⟨c, hc⟩
      exact StructuralIsolation.different_sides_no_mask G sideB hbip z a (hbip z a hza)
        ⟨c, (hc z hmem.1).symm, (hc a hmem.2).symm⟩
    apply unmaskable_singleton_wire_not_top_operand G C hA hT g hg z hz
      (n + (r - n)) (by omega) hpath hno k htop b
    rw [hb, ← hre]
    exact Relation.ReflTransGen.refl
  · apply hkm
    apply marked_or_reader C hA z a (r - n) k hrm hk hop
    simpa only [← hre] using hr

lemma marked_output_unmarked {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C)
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) (z a : Fin n)
    (hout : C.output < n + C.gates.length) :
    C.output < n ∨ C.output - n ∉ marked C z a := by
  by_cases ho : C.output < n
  · exact Or.inl ho
  apply Or.inr
  intro hm
  have he : C.output = n + (C.output - n) := by omega
  have hmem := (Finset.mem_filter.mp hm).2.1
  have hp := (P2.mem_orIn n C hA (n + (C.output - n)) (by omega) z).mp hmem
  have hx : P2.W n C (pairInput z z) C.output = true := by
    rw [he]
    apply P2.orR_mono n C hA _ _ z.val hp
    rw [P2.W_input n C (pairInput z z) z.val z.isLt]
    simp [pairInput]
  change PEqualNP.MetaComplexity.circuitFun n C (pairInput z z) = true at hx
  rw [hfun] at hx
  exact G.loopless.irrefl z ((P2.graphFun_pair G z z).mp hx)

lemma marked_nonempty_from_side {n : ℕ} (C : Circuit) (hA : P2.AO n C)
    (g : ℕ) (hg : g < C.gates.length) (b : Fin 2) (z a : Fin n) (hza : z ≠ a)
    (hz : z ∈ side (n := n) C g b) (ha : a ∈ side (n := n) C g b) :
    (marked C z a).Nonempty := by
  let w := opnd C g b
  have hlt := P2.opnd_lt n C hA g hg (opnd C g) (P2.opnd_eq n C hA g hg) b
  have hwn : ¬ w < n := by
    intro h
    have hsmall := P1.orIn_input (n := n) C w h
    exact hza (Finset.card_le_one.mp hsmall z hz a ha)
  have he : w = n + (w - n) := by omega
  refine ⟨w - n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp [w] at *; omega), ?_, ?_⟩⟩
  · change z ∈ orIn n C (n + (w - n))
    rw [← he]
    exact hz
  · change a ∈ orIn n C (n + (w - n))
    rw [← he]
    exact ha

lemma operand_excluded_marked {n : ℕ} (C : Circuit) (g : ℕ) (b : Fin 2)
    (z a : Fin n) (ha : a ∉ side (n := n) C g b) :
    opnd C g b < n ∨ opnd C g b - n ∉ marked C z a := by
  by_cases h : opnd C g b < n
  · exact Or.inl h
  apply Or.inr
  intro hm
  have he : opnd C g b = n + (opnd C g b - n) := by omega
  have ham := (Finset.mem_filter.mp hm).2.2
  rw [← he] at ham
  exact ha ham

end PEqualNP.Outside.L_meta_1477.PrivateCone


namespace PEqualNP.Outside.L_meta_1477.PrivateRotation

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]


def WireRep {n : ℕ} (gs : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ r : ℕ, r < n + gs.length ∧ ∀ x, (W gs x).getD r false = f x

def MonoList (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def CleanList {n : ℕ} (F : (Fin n → Bool) → Bool) (gs : List Gate) : Prop :=
  ∀ i < gs.length, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
    ∀ x, (W gs x).getD (n + i) false = true → F x = true

lemma wireRep_snoc {n : ℕ} (gs : List Gate) (g : Gate)
    (f : (Fin n → Bool) → Bool) (hf : WireRep gs f) : WireRep (gs ++ [g]) f := by
  obtain ⟨r, hr, hv⟩ := hf
  refine ⟨r, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
  intro x
  rw [W_val, if_neg (by omega)]
  exact hv x

lemma append_binary {n : ℕ} (F : (Fin n → Bool) → Bool) (gs : List Gate)
    (hm : MonoList gs) (hc : CleanList F gs)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (f h : (Fin n → Bool) → Bool) (hf : WireRep gs f) (hh : WireRep gs h)
    (hclean : op = GateOp.and → ∀ x, op.eval [f x, h x] = true → F x = true) :
    ∃ new : List Gate, new.length = gs.length + 1 ∧ MonoList new ∧ CleanList F new ∧
      WireRep new (fun x => op.eval [f x, h x]) ∧
      ∀ q : (Fin n → Bool) → Bool, WireRep gs q → WireRep new q := by
  obtain ⟨r, hr, hfr⟩ := hf
  obtain ⟨s, hs, hhs⟩ := hh
  let g : Gate := ⟨op, [r, s]⟩
  have hlast (x : Fin n → Bool) :
      (W (gs ++ [g]) x).getD (n + gs.length) false = op.eval [f x, h x] := by
    rw [W_val, if_pos rfl]
    simp only [g, List.map_cons, List.map_nil, hfr x, hhs x]
  refine ⟨gs ++ [g], by simp, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hm t ht
    · have he : t = g := List.mem_singleton.mp ht
      subst t
      exact ⟨hop, by simp [g]⟩
  · intro i hi hiop x hx
    by_cases hlt : i < gs.length
    · have hgate : (gs ++ [g]).getD i ⟨GateOp.or, []⟩ = gs.getD i ⟨GateOp.or, []⟩ := by
        simp [List.getD, List.getElem?_append_left hlt]
      rw [hgate] at hiop
      rw [W_val, if_neg (by omega)] at hx
      exact hc i hlt hiop x hx
    · have he : i = gs.length := by simp only [List.length_append, List.length_singleton] at hi; omega
      subst i
      have hgate : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by simp [List.getD]
      rw [hgate] at hiop
      rw [hlast x] at hx
      exact hclean hiop x hx
  · exact ⟨n + gs.length, by simp, hlast⟩
  · intro q hq
    exact wireRep_snoc gs g q hq

lemma count_marked_succ (M : Finset ℕ) (k : ℕ) :
    (M.filter fun i => i < k + 1).card =
      (M.filter fun i => i < k).card + if k ∈ M then 1 else 0 := by
  by_cases hk : k ∈ M
  · have he : M.filter (fun i => i < k + 1) = insert k (M.filter fun i => i < k) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi, hil⟩
        by_cases he : i = k
        · exact Or.inl he
        · exact Or.inr ⟨hi, by omega⟩
      · rintro (rfl | ⟨hi, hil⟩)
        · exact ⟨hk, by omega⟩
        · exact ⟨hi, by omega⟩
    rw [he, Finset.card_insert_of_notMem (by simp), if_pos hk]
  · have he : M.filter (fun i => i < k + 1) = M.filter fun i => i < k := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi, hil⟩
        have hne : i ≠ k := fun he => hk (he ▸ hi)
        exact ⟨hi, by omega⟩
      · rintro ⟨hi, hil⟩
        exact ⟨hi, by omega⟩
    rw [he, if_neg hk, Nat.add_zero]


lemma wireRep_congr {n : ℕ} (gs : List Gate) (f h : (Fin n → Bool) → Bool)
    (he : ∀ x, f x = h x) (hf : WireRep gs f) : WireRep gs h := by
  obtain ⟨r, hr, hv⟩ := hf
  exact ⟨r, hr, fun x => (hv x).trans (he x)⟩

def BuildInv {n : ℕ} (F : (Fin n → Bool) → Bool)
    (val : ℕ → (Fin n → Bool) → Bool) (M : Finset ℕ) (g k : ℕ) : Prop :=
  ∃ gs : List Gate, MonoList gs ∧ CleanList F gs ∧
    gs.length + (M.filter fun i => i < k).card = k + (if g < k then 1 else 0) ∧
    ∀ r, r < n + k → (r < n ∨ r - n ∉ M) → WireRep gs (val r)

lemma compile_private_rotation {n : ℕ} (N : ℕ)
    (F : (Fin n → Bool) → Bool) (val : ℕ → (Fin n → Bool) → Bool)
    (op : ℕ → GateOp) (left right : ℕ → ℕ) (M : Finset ℕ) (g : ℕ)
    (hM : M.Nonempty) (hMbound : ∀ k ∈ M, k < N) (hg : g < N) (hgn : g ∉ M)
    (hop : ∀ k < N, op k = GateOp.and ∨ op k = GateOp.or)
    (hlt : ∀ k < N, left k < n + k ∧ right k < n + k)
    (hvals : ∀ k < N, k ≠ g → ∀ x, val (n + k) x = (op k).eval [val (left k) x, val (right k) x])
    (hinput : ∀ a : Fin n, ∀ x, val a.val x = x a)
    (hkeep : ∀ k < N, k ∉ M → k ≠ g →
      ∀ r, r = left k ∨ r = right k → r < n ∨ r - n ∉ M)
    (q : ℕ) (hq : q < n + g) (hqun : q < n ∨ q - n ∉ M) (a z : Fin n)
    (hspecial : ∀ x, val (n + g) x = (x z || (x a && val q x)))
    (holdclean : ∀ k < N, k ≠ g → op k = GateOp.and → ∀ x, val (n + k) x = true → F x = true)
    (hnewclean : ∀ x, x a = true → val q x = true → F x = true)
    (out : ℕ) (hout : out < n + N) (houtun : out < n ∨ out - n ∉ M) :
    ∃ D : Circuit, D.size ≤ N ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
      CleanList F D.gates ∧ ∀ x, D.eval (List.ofFn x) = val out x := by
  have hinv : ∀ k, k ≤ N → BuildInv F val M g k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], by simp [MonoList], by simp [CleanList], by simp, ?_⟩
      intro r hr _
      have hrn : r < n := by omega
      refine ⟨r, by simpa using hrn, ?_⟩
      intro x
      have he : (W [] x).getD r false = x ⟨r, hrn⟩ := by
        change (List.ofFn x).getD r false = _
        rw [List.getD_eq_getElem _ _ (by simpa using hrn)]
        simp
      exact he.trans (hinput ⟨r, hrn⟩ x).symm
    | succ k ih =>
      intro hkN
      have hk : k < N := by omega
      obtain ⟨gs, hm, hc, hcount, hrep⟩ := ih (by omega)
      by_cases hkm : k ∈ M
      · have hkg : k ≠ g := fun he => hgn (he ▸ hkm)
        have hdelta : (if g < k + 1 then 1 else 0) = (if g < k then 1 else 0) := by
          split_ifs <;> omega
        refine ⟨gs, hm, hc, ?_, ?_⟩
        · rw [count_marked_succ, if_pos hkm, hdelta]
          omega
        · intro r hr hur
          by_cases he : r = n + k
          · subst r
            rcases hur with hri | hrm
            · omega
            · exact (hrm (by simpa using hkm)).elim
          · exact hrep r (by omega) hur
      · by_cases hkg : k = g
        · subst k
          have har : WireRep gs (fun x => x a) :=
            wireRep_congr gs _ _ (hinput a) (hrep a.val (by have := a.isLt; omega) (Or.inl a.isLt))
          have hzr : WireRep gs (fun x => x z) :=
            wireRep_congr gs _ _ (hinput z) (hrep z.val (by have := z.isLt; omega) (Or.inl z.isLt))
          obtain ⟨gs1, hl1, hm1, hc1, hr1, hp1⟩ :=
            append_binary F gs hm hc GateOp.and (Or.inl rfl) (fun x => x a) (val q)
              har (hrep q hq hqun) (by
                intro _ x hx
                simp only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true,
                  id_eq, Bool.and_eq_true] at hx
                exact hnewclean x hx.1 hx.2)
          have hinner : WireRep gs1 (fun x => x a && val q x) :=
            wireRep_congr gs1 _ _ (fun x => by simp [GateOp.eval]) hr1
          obtain ⟨gs2, hl2, hm2, hc2, hr2, hp2⟩ :=
            append_binary F gs1 hm1 hc1 GateOp.or (Or.inr rfl) (fun x => x z)
              (fun x => x a && val q x) (hp1 _ hzr) hinner (by intro h; cases h)
          have hnew : WireRep gs2 (val (n + g)) :=
            wireRep_congr gs2 _ _ (fun x => by simp only [GateOp.eval, List.any_cons,
              List.any_nil, Bool.or_false, id_eq]; exact (hspecial x).symm) hr2
          refine ⟨gs2, hm2, hc2, ?_, ?_⟩
          · rw [count_marked_succ, if_neg hgn]
            simp only [Nat.lt_succ_self, if_true, Nat.add_zero]
            simp only [lt_self_iff_false, if_false, Nat.add_zero] at hcount
            omega
          · intro r hr hur
            by_cases he : r = n + g
            · simpa only [he] using hnew
            · exact hp2 _ (hp1 _ (hrep r (by omega) hur))
        · have hl := (hlt k hk).1
          have hr := (hlt k hk).2
          have hlrep := hrep (left k) hl (hkeep k hk hkm hkg _ (Or.inl rfl))
          have hrrep := hrep (right k) hr (hkeep k hk hkm hkg _ (Or.inr rfl))
          obtain ⟨new, hlen, hm', hc', hnew, hpres⟩ :=
            append_binary F gs hm hc (op k) (hop k hk) (val (left k)) (val (right k))
              hlrep hrrep (fun ho x hx => holdclean k hk hkg ho x ((hvals k hk hkg x).trans hx))
          have hnew' : WireRep new (val (n + k)) :=
            wireRep_congr new _ _ (fun x => (hvals k hk hkg x).symm) hnew
          have hdelta : (if g < k + 1 then 1 else 0) = (if g < k then 1 else 0) := by
            split_ifs <;> omega
          refine ⟨new, hm', hc', ?_, ?_⟩
          · rw [count_marked_succ, if_neg hkm, hdelta]
            omega
          · intro r hr hur
            by_cases he : r = n + k
            · simpa only [he] using hnew'
            · exact hpres _ (hrep r (by omega) hur)
  obtain ⟨gs, hm, hc, hcount, hrep⟩ := hinv N le_rfl
  obtain ⟨r, hr, hv⟩ := hrep out hout houtun
  have hfilter : M.filter (fun i => i < N) = M := Finset.filter_eq_self.mpr hMbound
  rw [hfilter, if_pos hg] at hcount
  have hpos := Finset.card_pos.mpr hM
  refine ⟨⟨gs, r⟩, ?_, ?_, hc, hv⟩
  · change gs.length ≤ N
    omega
  · intro t ht
    obtain ⟨htop, htlen⟩ := hm t ht
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using htop, htlen⟩

end PEqualNP.Outside.L_meta_1477.PrivateRotation


namespace PEqualNP.Outside.L_meta_1477.PrivateRotationAdapter

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open OneJunk PrivateCone

lemma rotate_internal_mask_from_values {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hA : IsAO2 n C) (hT : TopForm G C)
    (g : ℕ) (hg : junk G C = {g})
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (sideB : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → sideB u ≠ sideB v)
    (z a : Fin n) (b : Fin 2) (hz : z ∈ side (n := n) C g 0 ∩ side (n := n) C g 1)
    (ha : a ∈ side (n := n) C g b) (hamask : a ∈ wmax G C g)
    (val : ℕ → (Fin n → Bool) → Bool)
    (hinput : ∀ i : Fin n, ∀ x, val i.val x = x i)
    (hvals : ∀ k < C.gates.length, k ≠ g → ∀ x,
      val (n + k) x = (gateAt C k).op.eval [val (opnd C k 0) x, val (opnd C k 1) x])
    (hspecial : ∀ x, val (n + g) x = (x z || (x a && val (opnd C g (1 - b)) x)))
    (hle : ∀ x r, val r x ≤ P2.W n C x r)
    (hpairs : ∀ u v : Fin n, G.Adj u v → val C.output (pairInput u v) = true) :
    ∃ D : Circuit, D.size ≤ C.size ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ ∧
      ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → BelowF G D k := by
  have hao := P2.ao_of n C hA
  have hgj : g ∈ junk G C := by rw [hg]; exact Finset.mem_singleton_self g
  obtain ⟨-, hgop, hglen, _⟩ := (P2.mem_filter' _ _ _ _).mp hgj
  have hgin := P2.opnd_eq n C hao g hglen
  have hgl := P2.opnd_lt n C hao g hglen (opnd C g) hgin
  have hzside (c : Fin 2) : z ∈ side (n := n) C g c := by
    rcases P2.fin2_sub c with ⟨hc, _⟩ | ⟨hc, _⟩
    · rw [hc]; exact (Finset.mem_inter.mp hz).1
    · rw [hc]; exact (Finset.mem_inter.mp hz).2
  have hzfire : gateVal n C g (pairInput z z) = true := by
    rw [junk_value_product G C hao hT g hg]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨z, hzside 0, by simp [pairInput]⟩, ⟨z, hzside 1, by simp [pairInput]⟩⟩
  have hza : G.Adj z a := by
    have hfire : gateVal n C g (pairInput z a) = true := by
      rw [junk_value_product G C hao hT g hg]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨z, hzside 0, by simp [pairInput]⟩, ⟨z, hzside 1, by simp [pairInput]⟩⟩
    exact (P2.graphFun_pair G z a).mp
      ((Finset.mem_filter.mp hamask).2 (pairInput z a) hfire (by simp [pairInput]))
  have haother : a ∉ side (n := n) C g (1 - b) := by
    intro hh
    exact OneJunkIsolation.mask_not_both_junk_sides G C hao hT g hg a hamask
      (P2.fin2_both (fun c => a ∈ side (n := n) C g c) b ha hh)
  have hgn : g ∉ marked C z a := by
    intro hh
    have hor := marked_op_or C z a g hh
    rw [hgop] at hor
    cases hor
  have hnonempty := marked_nonempty_from_side C hao g hglen b z a hza.ne (hzside b) ha
  have hout : C.output < n + C.gates.length := by
    by_contra hn
    have hx : C.eval (List.ofFn (pairInput z a)) = true := by
      change PEqualNP.MetaComplexity.circuitFun n C (pairInput z a) = true
      rw [hfun]
      exact (P2.graphFun_pair G z a).mpr hza
    have hlen : (C.wires (List.ofFn (pairInput z a))).length = n + C.gates.length := by
      change (PrivateRotation.W C.gates (pairInput z a)).length = _
      exact PrivateRotation.W_len _ _
    change (C.wires (List.ofFn (pairInput z a))).getD C.output false = true at hx
    rw [List.getD_eq_default _ _ (by rw [hlen]; omega)] at hx
    cases hx
  have holdclean : ∀ k < C.gates.length, k ≠ g → (gateAt C k).op = GateOp.and →
      ∀ x, val (n + k) x = true → graphFun G ∅ x = true := by
    intro k hk hkg hkop x hx
    have hbel : BelowF G C k := by
      by_contra hn
      have hmj := (P1.junk_iff G C k).mpr ⟨hk, hkop, hn⟩
      rw [hg] at hmj
      exact hkg (Finset.mem_singleton.mp hmj)
    exact hbel x (Bool.le_iff_imp.mp (hle x (n + k)) hx)
  have hnewclean : ∀ x, x a = true → val (opnd C g (1 - b)) x = true → graphFun G ∅ x = true := by
    intro x hxa hq
    have hv := Bool.le_iff_imp.mp (hle x (opnd C g (1 - b))) hq
    have hu : P2.W n C x (opnd C g b) = true := by
      apply P2.orR_mono n C hao x _ a.val
        ((P2.mem_orIn n C hao _ ((hgl b).trans (by omega)) a).mp ha)
      rw [P2.W_input n C x a.val a.isLt]
      exact hxa
    have hboth := P2.fin2_both (fun c => P2.W n C x (opnd C g c) = true) b hu hv
    have hfire : gateVal n C g x = true := by
      change P2.W n C x (n + g) = true
      rw [P2.W_and n C x g hglen hgop _ _ hgin (hgl 0) (hgl 1), hboth.1, hboth.2]
      rfl
    exact (Finset.mem_filter.mp hamask).2 x hfire hxa
  obtain ⟨D, hsize, hm, hclean, hev⟩ := PrivateRotation.compile_private_rotation C.gates.length
    (graphFun G ∅) val (fun k => (gateAt C k).op) (fun k => opnd C k 0)
    (fun k => opnd C k 1) (marked C z a) g hnonempty (marked_bounds C z a) hglen hgn
    (fun k hk => (hao k hk).1)
    (fun k hk => ⟨P2.opnd_lt n C hao k hk (opnd C k) (P2.opnd_eq n C hao k hk) 0,
      P2.opnd_lt n C hao k hk (opnd C k) (P2.opnd_eq n C hao k hk) 1⟩)
    hvals hinput (by
      intro k hk hkm hkg r hr
      apply marked_private_reads G C hao hT g hg z a hzfire hza sideB hbip k hk hkm hkg r
      rw [P2.opnd_eq n C hao k hk]
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)
    (opnd C g (1 - b)) (hgl (1 - b)) (operand_excluded_marked C g (1 - b) z a haother)
    a z hspecial holdclean hnewclean C.output hout
    (marked_output_unmarked G C hao hfun z a hout)
  refine ⟨D, hsize, hm, ?_, hclean⟩
  apply GateReplacement.graph_eq_of_le_and_pairs
  · apply GateReplacement.circuitFun_monotone
    intro t ht
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hm t ht).1
  · intro x
    change D.eval (List.ofFn x) ≤ graphFun G ∅ x
    rw [hev x, ← hfun]
    exact hle x C.output
  · intro u v huv
    change D.eval (List.ofFn (pairInput u v)) = true
    rw [hev]
    exact hpairs u v huv

end PEqualNP.Outside.L_meta_1477.PrivateRotationAdapter


namespace PEqualNP.Outside.L_meta_1477.InternalMask

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open OneJunk

lemma mask_side_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C) (g : ℕ)
    (hg : junk G C = {g}) (a : Fin n) (ha : a ∈ wmax G C g)
    (b : Fin 2) (hab : a ∈ side (n := n) C g b)
    (v : Fin n) (hv : v ∈ side (n := n) C g (1 - b)) : G.Adj a v := by
  have hboth := P2.fin2_both
    (fun c => ∃ u ∈ side (n := n) C g c, pairInput a v u = true) b
    ⟨a, hab, by simp [pairInput]⟩ ⟨v, hv, by simp [pairInput]⟩
  have hfire : gateVal n C g (pairInput a v) = true := by
    rw [junk_value_product G C hA hT g hg]
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hboth
  exact (P2.graphFun_pair G a v).mp
    ((Finset.mem_filter.mp ha).2 (pairInput a v) hfire (by simp [pairInput]))

lemma mask_common_input_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C) (g : ℕ)
    (hg : junk G C = {g}) (z a : Fin n)
    (hz : z ∈ side (n := n) C g 0 ∩ side (n := n) C g 1)
    (ha : a ∈ wmax G C g) : G.Adj z a := by
  have hfire : gateVal n C g (pairInput z a) = true := by
    rw [junk_value_product G C hA hT g hg]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨z, (Finset.mem_inter.mp hz).1, by simp [pairInput]⟩,
      ⟨z, (Finset.mem_inter.mp hz).2, by simp [pairInput]⟩⟩
  exact (P2.graphFun_pair G z a).mp
    ((Finset.mem_filter.mp ha).2 (pairInput z a) hfire (by simp [pairInput]))

lemma internal_masks_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (sideB : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → sideB u ≠ sideB v)
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C) (g : ℕ)
    (hg : junk G C = {g}) (z a : Fin n) (b : Fin 2)
    (hz : z ∈ side (n := n) C g 0 ∩ side (n := n) C g 1)
    (ha : a ∈ wmax G C g) (hab : a ∈ side (n := n) C g b)
    (hlarge : 2 ≤ (side (n := n) C g (1 - b)).card)
    (c : Fin n) (hc : c ∈ wmax G C g)
    (hcunion : c ∈ side (n := n) C g 0 ∪ side (n := n) C g 1) : c = a := by
  by_cases hcb : c ∈ side (n := n) C g b
  · exact (StructuralIsolation.common_neighbor_unique G h4 (side (n := n) C g (1 - b))
      hlarge a c (mask_side_adj G C hA hT g hg a ha b hab)
      (mask_side_adj G C hA hT g hg c hc b hcb)).symm
  · have hcother : c ∈ side (n := n) C g (1 - b) := by
      rcases P2.fin2_sub b with ⟨hb, hother⟩ | ⟨hb, hother⟩
      · rw [hother]
        exact (Finset.mem_union.mp hcunion).resolve_left (by simpa only [hb] using hcb)
      · rw [hother]
        exact (Finset.mem_union.mp hcunion).resolve_right (by simpa only [hb] using hcb)
    have hza := mask_common_input_adj G C hA hT g hg z a hz ha
    have hzc := mask_common_input_adj G C hA hT g hg z c hz hc
    have hac := mask_side_adj G C hA hT g hg a ha b hab c hcother
    exact (StructuralIsolation.different_sides_no_mask G sideB hbip z a (hbip z a hza)
      ⟨c, hzc.symm, hac.symm⟩).elim

end PEqualNP.Outside.L_meta_1477.InternalMask

namespace PEqualNP.Outside.L_meta_1477.OneJunkSingleton

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership
open OneJunk

lemma singleton_overlap_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (sideB : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → sideB u ≠ sideB v)
    (C : Circuit) (hA : IsAO2 n C) (hT : TopForm G C) (g : ℕ)
    (hg : junk G C = {g})
    (hfun : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (z : Fin n) (hinter : side (n := n) C g 0 ∩ side (n := n) C g 1 = {z})
    (hcard0 : 2 ≤ (side (n := n) C g 0).card)
    (hcard1 : 2 ≤ (side (n := n) C g 1).card) :
    ∃ D : Circuit, D.size ≤ C.size ∧ PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ ∧
      ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → BelowF G D k := by
  have hao := P2.ao_of n C hA
  have hgj : g ∈ junk G C := by rw [hg]; exact Finset.mem_singleton_self g
  obtain ⟨-, hgop, hglen, _⟩ := (P2.mem_filter' _ _ _ _).mp hgj
  have hz : z ∈ side (n := n) C g 0 ∩ side (n := n) C g 1 := by rw [hinter]; simp
  by_cases hinternal : ∃ a : Fin n, a ∈ wmax G C g ∧
      a ∈ side (n := n) C g 0 ∪ side (n := n) C g 1
  · obtain ⟨a, hamask, haunion⟩ := hinternal
    obtain ⟨b, hab⟩ : ∃ b : Fin 2, a ∈ side (n := n) C g b := by
      rcases Finset.mem_union.mp haunion with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
    have hlarge : 2 ≤ (side (n := n) C g (1 - b)).card := by
      rcases P2.fin2_sub b with ⟨_, hb⟩ | ⟨_, hb⟩
      · simpa only [hb] using hcard1
      · simpa only [hb] using hcard0
    have hunique : ∀ c ∈ wmax G C g,
        c ∈ side (n := n) C g 0 ∪ side (n := n) C g 1 → c = a :=
      InternalMask.internal_masks_unique G h4 sideB hbip C hao hT g hg z a b hz hamask hab hlarge
    let f := RotationSemantics.rotatedValue C g b a z
    let val := SemanticOverride.value C g f
    apply PrivateRotationAdapter.rotate_internal_mask_from_values G C hA hT g hg hfun
      sideB hbip z a b hz hab hamask val
    · exact SemanticOverride.value_input C g f
    · intro k hk hkg x
      have hin := P2.opnd_eq n C hao k hk
      have hlt := P2.opnd_lt n C hao k hk (opnd C k) hin
      have he : C.gates[k] = ⟨(gateAt C k).op, [opnd C k 0, opnd C k 1]⟩ := by
        rw [← P1.S90.gateAt_eq hk]
        cases hgate : gateAt C k with
        | mk op ins =>
          simp only [hgate] at hin
          subst ins
          rfl
      exact SemanticOverride.value_binary C g f k hk hkg _ _ _ he (hlt 0) (hlt 1) x
    · exact RotationSemantics.special_equation C hao g hglen b a z
    · intro x r
      exact SemanticOverride.value_le C g f hA.1
        (RotationSemantics.local_decrease G C hao g hg b a z hz hab) r x
    · intro u v huv
      apply SemanticOverride.output_true C g f hA.1 (pairInput u v)
      · change PEqualNP.MetaComplexity.circuitFun n C (pairInput u v) = true
        rw [hfun]
        exact (P2.graphFun_pair G u v).mpr huv
      · exact RotationSemantics.sensitive_pair_equal G C hA hT g hg hfun b a z hinter hunique u v huv
  · have houtside : ∀ c ∈ wmax G C g,
        c ∉ side (n := n) C g 0 ∪ side (n := n) C g 1 :=
      fun c hc hm => hinternal ⟨c, hc, hm⟩
    obtain ⟨hf, hs, hm, hc⟩ := OverlapAlias.no_internal_mask_alias G C hA hT g hg hfun z hinter houtside
    exact ⟨_, le_of_eq hs, hm, hf, hc⟩

end PEqualNP.Outside.L_meta_1477.OneJunkSingleton


namespace PEqualNP.Outside.L_meta_1477.Library

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


def posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  match w with
  | 0 => false
  | i + 1 => (wiresFrom gs (List.ofFn x)).getD i false

def clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

def gateAtPos (n : ℕ) (gs : List Gate) (w : ℕ) : Gate :=
  gs.getD (w - (n + 1)) ⟨GateOp.or, []⟩

def firstWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 0 (w-1))

def secondWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 1 ((gateAtPos n gs w).inputs.getD 0 (w-1)))

def andPos (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  match (gateAtPos n gs w).op with
  | GateOp.and => true
  | _ => false

lemma clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w-1) i < w := by
  unfold clampWire
  split <;> omega

lemma pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire lim i) x =
    (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
  simp only [clampWire]
  split <;> rfl

lemma pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    posRead gs (i+1) x = x ⟨i,hi⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i,hi⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi),List.getElem_ofFn]

lemma pos_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
    posRead gs w x = true → posRead gs w y = true := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    apply wiresFrom_mono gs ops _ _ (by simp)
    intro j h
    by_cases hj : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def singletonBits {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)
def pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

lemma edge_single {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ¬ edgeTrue G (singletonBits u) := by
  rintro ⟨i,j,h,hi,hj⟩
  simp only [singletonBits, decide_eq_true_eq] at hi hj
  subst i
  subst j
  exact G.loopless.irrefl u h

lemma edge_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    edgeTrue G (pairBits u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    simp only [pairBits, decide_eq_true_eq] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (G.loopless.irrefl _ h).elim
    · exact h
    · exact h.symm
    · exact (G.loopless.irrefl _ h).elim
  · intro h
    exact ⟨u,v,h,by simp [pairBits],by simp [pairBits]⟩

lemma binary_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (nonempty : op = GateOp.and → l ≠ [])
    (v : ℕ → Bool) (lim : ℕ) (vd : v lim = false) :
    op.eval (l.map v) =
      (if (match op with | GateOp.and => true | _ => false) then
        v (l.getD 0 lim) && v (l.getD 1 (l.getD 0 lim))
       else v (l.getD 0 lim) || v (l.getD 1 (l.getD 0 lim))) := by
  cases l with
  | nil =>
    rcases hop with rfl | rfl
    · exact (nonempty rfl rfl).elim
    · simp [GateOp.eval,vd]
  | cons i t =>
    cases t with
    | nil => rcases hop with rfl | rfl <;> simp [GateOp.eval]
    | cons j t =>
      have ht : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst t
      rcases hop with rfl | rfl <;> simp [GateOp.eval]

def supports {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => posRead gs w (singletonBits u) = true

lemma mem_support {n : ℕ} (gs : List Gate) (w : ℕ) (u : Fin n) :
    u ∈ supports gs w ↔ posRead gs w (singletonBits u) = true := by simp [supports]


def cleanOn {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ (j : Fin gs.length) (x : Fin n → Bool),
    (x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) →
    (gs.get j).op = GateOp.and →
    (wiresFrom gs (List.ofFn x)).getD (n + j.val) false = true → edgeTrue G x

def binaryOps (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma gateAt_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtPos n gs (n+j+1) = gs[j] := by
  unfold gateAtPos
  rw [show n+j+1-(n+1) = j by omega,List.getD_eq_getElem _ _ hj]

lemma pos_gate {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs)
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have nonempty : gs[j].op = GateOp.and → gs[j].inputs ≠ [] := by
    intro ha hempty
    let z : Fin n → Bool := fun _ => false
    have eqg := getD_wiresFrom_gate gs (List.ofFn z) j hj
    simp only [List.length_ofFn, hempty, List.map_nil, ha, GateOp.eval, List.all_nil] at eqg
    obtain ⟨u,v,_,h,_⟩ := clean ⟨j,hj⟩ z (Or.inl rfl) ha eqg
    contradiction
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)

lemma pos_clean {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) (x : Fin n → Bool)
    (hx : x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) :
    posRead gs w x = true → edgeTrue G x := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  rw [hw] at ha ⊢
  simp only [andPos, gateAt_index gs j hj] at ha
  have hop : gs[j].op = GateOp.and := by
    cases h : gs[j].op <;> simp_all
  exact clean ⟨j,hj⟩ x hx hop

lemma support_base {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n+1) :
    (supports (n:=n) gs w).card ≤ 1 := by
  cases w with
  | zero => simp [supports,posRead]
  | succ i =>
    have hi : i < n := by omega
    have hs : supports gs (i+1) = {⟨i,hi⟩} := by
      ext u
      simp [mem_support,pos_input gs i hi,singletonBits,eq_comm]
    simp [hs]

lemma hit_base {n : ℕ} (gs : List Gate) (w : ℕ) (u v : Fin n) (hw : w < n+1) :
    posRead gs w (pairBits u v) = true → u ∈ supports gs w ∨ v ∈ supports gs w := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    have hi : i<n := by omega
    simp [mem_support,pos_input gs i hi,pairBits,singletonBits]

lemma support_and {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) : supports (n:=n) gs w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact edge_single G u (pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inl ⟨u, rfl⟩)) ((mem_support gs w u).mp hu))

lemma support_or {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = false) :
    supports (n:=n) gs w = supports gs (firstWire n gs w) ∪ supports gs (secondWire n gs w) := by
  ext u
  simp only [Finset.mem_union,mem_support,pos_gate G gs ops clean w lo hi,ha]
  simp

lemma cross_support {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = true)
    (u : Fin n) (hu : u ∈ supports gs (firstWire n gs w))
    (v : Fin n) (hv : v ∈ supports gs (secondWire n gs w)) : G.Adj u v := by
  apply (edge_pair G u v).mp
  apply pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inr ⟨u, v, rfl⟩))
  rw [pos_gate G gs ops clean w lo hi,ha]
  simp only [ite_true, Bool.and_eq_true]
  have hm := pos_mono (n:=n) gs (fun g h => (ops g h).1)
  constructor
  · apply hm (firstWire n gs w) (singletonBits u) (pairBits u v) _ ((mem_support _ _ _).mp hu)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]
  · apply hm (secondWire n gs w) (singletonBits v) (pairBits u v) _ ((mem_support _ _ _).mp hv)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]


lemma root_read {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire (n+gs.length) out) x = (Circuit.mk gs out).eval (List.ofFn x) := by
  rw [pos_clamp]
  change (if out < n+gs.length then _ else _) = (wiresFrom gs (List.ofFn x)).getD out false
  split_ifs with h
  · rfl
  · symm
    apply List.getD_eq_default
    simpa only [length_wiresFrom, List.length_ofFn] using Nat.le_of_not_lt h

lemma root_bound (n len out : ℕ) : clampWire (n+len) out < n+1+len := by
  unfold clampWire
  split <;> omega

lemma root_support_empty {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    supports (n:=n) gs (clampWire (n+gs.length) out) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u h
  apply edge_single G u
  apply (heval _).mp
  rw [← root_read]
  exact (mem_support _ _ _).mp h

lemma root_hits {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    ∀ u v, G.Adj u v → posRead gs (clampWire (n+gs.length) out) (pairBits u v) = true := by
  intro u v h
  rw [root_read,heval]
  exact (edge_pair G u v).mpr h

lemma countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

lemma dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

lemma gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      1 < (S w).card)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      (S w).card ≤ 1)).card ≤ len := by
  classical
  let gates := Finset.range (n + 1 + len)
  let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
  let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  change ands.card + large.card + small.card ≤ len
  have hdis : Disjoint ands large := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have a := (Finset.mem_filter.mp h₁).2.2
    have b := (Finset.mem_filter.mp h₂).2.2.1
    simp_all
  have hdis' : Disjoint (ands ∪ large) small := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have b := (Finset.mem_filter.mp h₂).2.2
    rcases Finset.mem_union.mp h₁ with ha | hl
    · have a := (Finset.mem_filter.mp ha).2.2
      simp_all
    · have a := (Finset.mem_filter.mp hl).2.2.2
      exact (Nat.not_lt_of_ge b.2) a
  have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n+1) (n+1+len) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases Finset.mem_union.mp h with h | h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
        Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
  simpa using Finset.card_le_card hsub

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else
        coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

lemma cover_half (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdag : ∀ (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
      (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
        (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
      (R.biUnion f).card ≤ R.card + B.card) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ 1 + ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).card := by
  let f := coverCert k N S a b A ha hb
  let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by
    exact coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 →
      ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_right
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v h
            simp only [Finset.mem_union]
            tauto
          · have hitB := ih _ hib (hib.trans hw) htb u v h
            simp only [Finset.mem_union]
            tauto
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨f r, fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨
        (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht
      rw [feq, ite_eq_right ht] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
        a w, hia, b w, hib, ?_⟩
      rw [feq, ite_eq_left ht, ite_eq_left hg, hop]
      simp
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right htA]
  simpa [B] using hdag f {r} B hstep

lemma edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, ?_⟩
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)

lemma edge_finset_gate_bound (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    G.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : G.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w),
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => simp [hzero i hk hgood.1 he] at hi
        have ⟨ha,hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, owner_eq i c hi hgood.2]
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
    have subset : G.edgeFinset ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        have huv : G.Adj u v := G.mem_edgeFinset.mp he
        obtain ⟨w,hk,hN,hA,how⟩ := hcover u v huv
        have hw : w ∈ AS := by simp [AS,hN,hk,hA]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w,t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
        rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
        · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]

lemma total_from_model (n k N r L : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hr : r < N) (hrS : S r = ∅) (hrH : ∀ u v, G.Adj u v → H r u v)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hpartition :
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card ≤ L) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ L + 1 := by
  classical
  have hd (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) : Disjoint (S (a w)) (S (b w)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    exact G.loopless.irrefl t (hjoin w hk hN hA t ht t ht')
  have hside (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) :
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1 := by
    by_contra! hf
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hf.1
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hf.2
    have hJ := hjoin w hk hN hA
    exact hc4 u x v y huv hxy ⟨hJ u hu x hx, (hJ v hv x hx).symm, hJ v hv y hy, (hJ u hu y hy).symm⟩
  have births (u v) (huv : G.Adj u v) := edge_birth n k N r S H a b A u v hr
    (hrH u v huv) (by simp [hrS]) (by simp [hrS]) hinput ha hb horS horH handH hd
  have edgeCount := edge_finset_gate_bound n k N G S a b A hc4 hsmall
    (fun w hk hN => ⟨ha w hk hN, hb w hk hN⟩) hzero horS hjoin hside births
  obtain ⟨T,hT,hcard⟩ := cover_half n k N r G S H a b A hr hrS hrH hinput ha hb
    horS horH hside handH (fun f R B step => dag_union_bound f R B step)
  exact ⟨T,hT,by omega⟩

lemma pairCleanBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (x = (fun _ => false) ∨ (∃ u : Fin n, x = fun z => decide (z = u)) ∨ (∃ u v : Fin n, x = fun z => decide (z = u ∨ z = v))) → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G inst hc4 gs out ops eval clean
  have he : ∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x := by
    intro x
    rw [eval]
    exact decide_eq_true_iff
  apply total_from_model n (n+1) (n+1+gs.length) (clampWire (n+gs.length) out) gs.length G
    (supports gs) (fun w u v => posRead gs w (pairBits u v) = true)
    (firstWire n gs) (secondWire n gs) (andPos n gs) hc4 (root_bound n gs.length out)
    (root_support_empty G gs out he) (root_hits G gs out he) (support_base gs) (hit_base gs)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · exact support_or G gs ops clean
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,Bool.false_eq_true,ite_false,Bool.or_eq_true]
      using h
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,ite_true,Bool.and_eq_true] using h
  · exact support_and G gs clean
  · exact cross_support G gs ops clean
  · exact gate_partition_count n gs.length (andPos n gs) (supports gs)


lemma clean_graph_lower_bound : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 := by
  intro m H _ h4 D hM hfun hclean
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨∅, fun y => y.elim0, ?_⟩
    have he : H.edgeFinset = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun e _ => Sym2.inductionOn e (fun a _ => a.elim0))
    simp [he]
  · have hmono : ∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro g hg
      have := (hM g hg).1
      simpa using this
    refine PEqualNP.Outside.L_meta_1477.Library.pairCleanBound m H h4 D.gates D.output
      (fun g hg => ⟨hmono g hg, (hM g hg).2⟩) (fun x => ?_) (fun i x hx hop hv => ?_)
    · have := congrFun hfun x
      simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.MetaComplexity.NestedCover.graphFun]
        using this
    · have hop' : (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op =
          PEqualNP.CircuitLowerBounds.GateOp.and := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ i.2]
        exact hop
      have hval : ∀ e w : Fin m, ¬ H.Adj e w →
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨D.gates, 0⟩
            (List.ofFn (PEqualNP.EdgeOwnership.pairInput e w))).getD (m + (i : ℕ)) false = true →
          False := by
        intro e w hew h
        have h2 := hclean i i.2 hop' e w hew
        have h3 : PEqualNP.EdgeOwnership.gateVal m D i (PEqualNP.EdgeOwnership.pairInput e w)
            = true := h
        rw [h2] at h3
        exact Bool.false_ne_true h3
      rcases hx with rfl | ⟨u, rfl⟩ | ⟨u, v, rfl⟩
      · exfalso
        refine hval ⟨0, hm⟩ ⟨0, hm⟩ (H.irrefl) ?_
        refine PEqualNP.Outside.L_meta_1477.Library.wiresFrom_mono D.gates hmono _ _ (by simp) ?_ _ hv
        intro j h
        by_cases hj : j < m
        · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h
          exact absurd h Bool.false_ne_true
        · rw [List.getD_eq_default _ _ (by simp; omega)] at h
          exact absurd h Bool.false_ne_true
      · exfalso
        refine hval u u (H.irrefl) ?_
        have hxe : (fun z : Fin m => decide (z = u)) = PEqualNP.EdgeOwnership.pairInput u u := by
          funext z
          simp [PEqualNP.EdgeOwnership.pairInput]
        rw [← hxe]
        exact hv
      · by_cases hadj : H.Adj u v
        · exact ⟨u, v, hadj, by simp, by simp⟩
        · exact (hval u v hadj hv).elim

end PEqualNP.Outside.L_meta_1477.Library

namespace PEqualNP.Outside.L_meta_1477.PlaneOneJunkFull

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma plane_clean_size [DecidableRel planeGraph.Adj] (D : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 D)
    (hf : PEqualNP.MetaComplexity.circuitFun 42 D = graphFun planeGraph ∅)
    (hc : ∀ k < D.gates.length, (gateAt D k).op = GateOp.and → BelowF planeGraph D k) :
    125 ≤ D.size := by
  classical
  have hpair : ∀ k < D.gates.length, (gateAt D k).op = GateOp.and →
      ∀ u v : Fin 42, ¬ planeGraph.Adj u v → gateVal 42 D k (pairInput u v) = false := by
    intro k hk hop u v huv
    apply Bool.eq_false_of_not_eq_true
    intro hx
    exact huv ((OneJunk.P2.graphFun_pair planeGraph u v).mp (hc k hk hop _ hx))
  obtain ⟨S, hcover, hcount⟩ := Library.clean_graph_lower_bound 42 planeGraph
    planeGraph_no_four_cycle D hm hf hpair
  have hlower := planeGraph_cover_lower S hcover
  rw [planeGraph_card] at hcount
  omega

lemma plane_bipartite (u v : Fin 42) (huv : planeGraph.Adj u v) :
    decide (u.val < 21) ≠ decide (v.val < 21) := by
  rcases (planeGraph_adj u v).mp huv with h | h
  · have hb := planeEdges_bounds (u.val, v.val) h
    simp [hb.1, show ¬ v.val < 21 by omega]
  · have hb := planeEdges_bounds (v.val, u.val) h
    simp [hb.1, show ¬ u.val < 21 by omega]

lemma one_junk_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hT : TopForm planeGraph C)
    (g : ℕ) (hg : junk planeGraph C = {g}) : 125 ≤ C.size := by
  classical
  by_contra hn
  have hsize : C.size ≤ 124 := by omega
  have hcard := PlaneOverlap.short_onejunk_overlap_card C hL hT g hg hsize
  obtain ⟨z, hinter⟩ := Finset.card_eq_one.mp hcard
  have hA := OneJunk.P2.ao_of 42 C hL.1
  have hlarge (b : Fin 2) : 2 ≤ (side (n := 42) C g b).card := by
    by_contra hsmall
    have hpos := Finset.card_pos.mpr (OneJunk.junk_sides_nonempty planeGraph C hA hT g hg b)
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (show (side (n := 42) C g b).card = 1 by omega)
    have hb := PlaneOneCleaner.singleton_side_size C hL hT g hg b a ha
    omega
  obtain ⟨D, hDsize, hm, hf, hc⟩ := OneJunkSingleton.singleton_overlap_clean planeGraph
    PlaneTwoCenters.plane_noFourCycle (fun u => decide (u.val < 21)) plane_bipartite
    C hL.1 hT g hg hL.2.1 z hinter (hlarge 0) (hlarge 1)
  have hbound := plane_clean_size D hm hf hc
  omega

lemma no_junk_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hg : junk planeGraph C = ∅) :
    125 ≤ C.size := by
  apply plane_clean_size C (SensitivePath.ao_monotone C hL.1) hL.2.1
  intro k hk hop
  by_contra hn
  have hm := (OneJunk.P1.junk_iff planeGraph C k).mpr ⟨hk, hop, hn⟩
  rw [hg] at hm
  exact Finset.notMem_empty _ hm

lemma short_circuit_two_junk [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hT : TopForm planeGraph C)
    (hsize : C.size ≤ 124) : 2 ≤ (junk planeGraph C).card := by
  by_contra hn
  by_cases he : junk planeGraph C = ∅
  · have hb := no_junk_size C hL he
    omega
  · have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    obtain ⟨g, hg⟩ := Finset.card_eq_one.mp (show (junk planeGraph C).card = 1 by omega)
    have hb := one_junk_size C hL hT g hg
    omega

end PEqualNP.Outside.L_meta_1477.PlaneOneJunkFull


namespace PEqualNP.Outside.L_meta_1477.Normalization

namespace A1527

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext n new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext n new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB n new ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hrb, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, _, hkb⟩
    · exact hrb
    · exact rb_snoc hrb hkb
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_pos ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_neg ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, (by intro j hj; simp at hj), le_refl _, rep_input ρ hρ⟩

lemma eval_eq {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = (W gs x).getD o false := rfl

lemma main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ C'.size ≤ C.size := by
  intro n G inst C hm hC
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    have h := hm g hgm
    refine ⟨?_, h.2⟩
    have h1 := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  obtain ⟨new, hfan, hrb, hl, hrep⟩ :=
    inv_all (fun (x : Fin n → Bool) => x) (fun i => Or.inr (fun x => rfl)) C.gates hg
  have hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = (W C.gates x).getD C.output false :=
    fun x => rfl
  have hgf : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x
      = C.eval (List.ofFn x) := by
    intro x
    rw [Bool.eq_iff_iff, hC x]
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
  rcases hrep C.output with ⟨c, hc⟩ | ⟨j, _, hj⟩
  · have hc' : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = c := fun x => (hev x).trans (hc x)
    have hcf : c = false := by
      have h0 := hC (fun _ => false)
      rw [hc'] at h0
      cases c with
      | false => rfl
      | true =>
        obtain ⟨u, v, _, hu, _⟩ := h0.mp rfl
        exact absurd hu (by simp)
    subst hcf
    refine ⟨⟨[], n⟩, ⟨?_, ?_, ?_⟩, ?_, Nat.zero_le _⟩
    · intro g hgm
      simp at hgm
    · intro k hk
      simp at hk
    · intro g hgm
      simp at hgm
    · funext x
      rw [hgf x, hc' x]
      show (W ([] : List Gate) x).getD n false = false
      exact List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)
  · refine ⟨⟨new, j⟩, ⟨?_, ?_, ?_⟩, ?_, hl⟩
    · intro g hgm
      exact (hfan g hgm).1
    · exact hrb
    · intro g hgm
      exact (hfan g hgm).2
    · funext x
      rw [hgf x, hev x]
      exact hj x

end A1527

namespace A1501

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

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

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = wv n C x C.output) →
    C.gates.length ≤ D.gates.length

lemma reader_or (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hL hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma step3_core (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (reader_unique n C hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma least_of_same (n : ℕ) (C D : Circuit) (hL : Least n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) : Least n D :=
  ⟨hD, fun E hE hEf => by rw [hlen]; exact hL.2 E hE (fun x => (hEf x).trans (hfun x))⟩

lemma V2_gateval (n : ℕ) (C : Circuit) (r c i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    wv n (V2 n C r c i) x (n + k') = wv n C x (n + rho r k') := by
  have h := V2_same n C r c i x hC hr hb hi hout h0 (n + rho r k')
    (by have := rho_lt r k' _ hr hk'; omega)
  rw [tau_rho] at h
  exact h

lemma V2_below (n : ℕ) (C : Circuit) (r c i : ℕ) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbelF : ∀ x, wv n C x (n + i) = true → F x = true)
    (h0 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    (∀ x, wv n (V2 n C r c i) x (n + k') = true → F x = true) ↔
      (∀ x, wv n C x (n + rho r k') = true → F x = true) := by
  constructor
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [← V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv


lemma card_filter_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q]
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    ((Finset.range m).filter Q).card = ((Finset.range m).filter P).card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [Finset.mem_filter, Finset.mem_range] at hk' ⊢
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩


lemma step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : Least n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, least_of_same n C _ hL hD hfun (V2_len n C r c i),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma card_mem_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < m ∧ P k) (hS' : ∀ k, k ∈ S' ↔ k < m ∧ Q k)
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    S'.card = S.card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [hS'] at hk'
    rw [hS]
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [hS] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [hS']
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma junk_eq (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)
    (hS' : ∀ k, k ∈ S' ↔ k < C'.gates.length ∧ (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true) :
    S'.card = S.card := by
  rw [hlen] at hS'
  apply card_mem_rho C.gates.length r hr _ _ S S' hS hS'
  · intro k' hk'
    rw [hops k' hk', hbelow k' hk']
  · rintro ⟨h, _⟩
    rw [hopr] at h
    exact absurd h (by simp)
  · rintro ⟨h, _⟩
    rw [htop] at h
    exact absurd h (by simp)


lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma mem_gateAt (C : Circuit) (g : Gate) (hg : g ∈ C.gates) :
    ∃ j, j < C.gates.length ∧ gateAt C j = g := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  exact ⟨j, hj, by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]⟩


lemma ao2_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro j hj
  have hm := gateAt_mem C j hj
  exact ⟨h1 _ hm, List.length_eq_two.mp (h3 _ hm), h2 j hj⟩

lemma ao2_to (n : ℕ) (C : Circuit) (h : AO2 n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    exact (h j hj).1
  · intro j hj
    exact (h j hj).2.2
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    obtain ⟨a, b, hab⟩ := (h j hj).2.1
    rw [hab]
    rfl

lemma least_glue (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : PEqualNP.TopForm.IsLeastAO G C) :
    Least n C ∧ ∀ x, wv n C x C.output = graphFun G ∅ x := by
  obtain ⟨h1, h2, h3⟩ := hL
  have hF : ∀ x, wv n C x C.output = graphFun G ∅ x := fun x => congrFun h2 x
  refine ⟨⟨ao2_of n C h1, ?_⟩, hF⟩
  intro D hD hDf
  exact h3 D (ao2_to n D hD) (funext fun x => (hDf x).trans (hF x))

lemma least_glue' (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : Least n C) (hF : ∀ x, wv n C x C.output = graphFun G ∅ x) :
    PEqualNP.TopForm.IsLeastAO G C := by
  refine ⟨ao2_to n C hL.1, funext hF, ?_⟩
  intro D hD hDf
  exact hL.2 D (ao2_of n D hD) (fun x => (congrFun hDf x).trans (hF x).symm)

lemma exists_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  refine ⟨fun _ => true, ?_⟩
  obtain ⟨e, he⟩ := hG
  rw [SimpleGraph.mem_edgeFinset] at he
  revert he
  refine Sym2.inductionOn e ?_
  intro u v he
  have hadj : G.Adj u v := he
  unfold graphFun
  have hd : decide (∃ u v, G.Adj u v ∧ (fun _ : Fin n => true) u = true ∧
      (fun _ : Fin n => true) v = true) = true := decide_eq_true ⟨u, v, hadj, rfl, rfl⟩
  rw [hd]
  simp

lemma mem_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → graphFun G ∅ x = true := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hne
    apply h3
    intro x hx
    by_contra hF
    exact hne ⟨x, hx, by simpa using hF⟩

open Classical in
lemma main_ind (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) :
    ∀ k : ℕ, ∀ C : Circuit, PEqualNP.TopForm.IsLeastAO G C →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G C' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hC hk
    by_cases htop : PEqualNP.TopForm.TopForm G C
    · exact ⟨C, hC, rfl, rfl, htop⟩
    · have hex : ∃ i j, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone n C i j := by
        by_contra hne
        apply htop
        intro i hi j hj h1 h2 h3 h4
        exact hne ⟨i, j, hi, hj, h1, h2, h3, h4⟩
      obtain ⟨i, j, hi, hj, hopi, hbi, hopj, hcone⟩ := hex
      obtain ⟨hL, hF⟩ := least_glue n G C hC
      obtain ⟨x1, hx1⟩ := exists_true n G hG
      have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF]; exact hx1)
      obtain ⟨C', r, hr, hir, hL', hF', hlen, hops, htop', hopr, hbelow, hcn, hno⟩ :=
        step3_struct n C (graphFun G ∅) hL hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'', h1, h2, h3, h4⟩ := ih _ hlt C' (least_glue' n G C' hL' hF') rfl
      refine ⟨C'', h1, h2.trans hlen, h3.trans ?_, h4⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro k
        exact mem_junk n G C k
      · intro k
        exact mem_junk n G C' k

end A1501

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma exists_least (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C' : Circuit)
    (h1 : PEqualNP.TopForm.IsAO2 n C') (h2 : circuitFun n C' = graphFun G ∅) :
    ∃ C : Circuit, PEqualNP.TopForm.IsLeastAO G C ∧ C.size ≤ C'.size := by
  classical
  have hex : ∃ k : ℕ, ∃ C : Circuit, PEqualNP.TopForm.IsAO2 n C ∧ circuitFun n C = graphFun G ∅ ∧
      C.size = k := ⟨_, C', h1, h2, rfl⟩
  obtain ⟨C, hC1, hC2, hC3⟩ := Nat.find_spec hex
  refine ⟨C, ⟨hC1, hC2, ?_⟩, ?_⟩
  · intro D hD1 hD2
    rw [hC3]
    exact Nat.find_min' hex ⟨D, hD1, hD2, rfl⟩
  · rw [hC3]
    exact Nat.find_min' hex ⟨C', h1, h2, rfl⟩


lemma normalized (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hne : G.edgeFinset.Nonempty) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hf : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ D : Circuit, PEqualNP.TopForm.IsLeastAO G D ∧
      PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size := by
  obtain ⟨C1, hA, hF, hS⟩ := A1527.main_aux n G ‹DecidableRel G.Adj› C hm hf
  obtain ⟨C2, hL2, hS2⟩ := exists_least n G C1 hA hF
  obtain ⟨C3, hL3, hS3, _, hT3⟩ := A1501.main_ind n G hne _ C2 hL2 rfl
  exact ⟨C3, hL3, hT3, by omega⟩

end PEqualNP.Outside.L_meta_1477.Normalization

namespace PEqualNP.Outside.L_meta_1477.PlaneNormalized

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma posted_short_circuit_two_junk [DecidableRel planeGraph.Adj] (C : Circuit)
    (hmono : PEqualNP.MetaComplexity.Monotone2 C) (hsize : C.size ≤ 124)
    (hfun : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42, (u.val, v.val) ∈ planeEdges ∧ x u = true ∧ x v = true) :
    ∃ D : Circuit, IsLeastAO planeGraph D ∧ TopForm planeGraph D ∧
      D.size ≤ C.size ∧ 2 ≤ (junk planeGraph D).card := by
  classical
  have hne : planeGraph.edgeFinset.Nonempty := by
    apply Finset.card_pos.mp
    rw [planeGraph_card]
    omega
  have hf : ∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 42, planeGraph.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    exact (hfun x).trans (planeGraph_fun_iff x).symm
  obtain ⟨D, hL, hT, hD⟩ := Normalization.normalized 42 planeGraph hne C hmono hf
  exact ⟨D, hL, hT, hD,
    PlaneOneJunkFull.short_circuit_two_junk D hL hT (hD.trans hsize)⟩

end PEqualNP.Outside.L_meta_1477.PlaneNormalized

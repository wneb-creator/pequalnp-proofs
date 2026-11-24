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

lemma PEqualNP.Outside.L_meta_1477.OneJunk.oneJunkBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
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

namespace PEqualNP.Outside.L_meta_1477.ResidualRootCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge OneJunk

lemma root_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (root : ℕ) (hroot : root < n + C.gates.length) (c : Fin n)
    (R : Finset (Fin n)) (hR : ∀ v ∈ R, G.Adj c v) (Z : Finset ℕ)
    (hZ : ∀ k ∈ Z,
      (∀ v ∈ orIn n C (n + k) ∩ R, s(c, v) ∈ starEdges G C) ∨
        (orIn n C (n + k) ∩ R).card ≤ 1) :
    ∃ B : Finset ℕ, B ⊆ orN G C \ lam G C ∧ Disjoint B Z ∧
      (∀ k ∈ B, P2.OrR n C root (n + k) ∧
        (orIn n C (n + k)).Nonempty ∧ orIn n C (n + k) ⊆ orIn n C root) ∧
      (((orIn n C root ∩ R).image (fun v => s(c, v))) \ starEdges G C).card ≤ B.card + 1 := by
  classical
  let f : ℕ → Finset (Fin n) := fun w => orIn n C w ∩ R
  have hRB := hL.1.2.1
  have h2 := hL.1.2.2
  have hA := P2.ao_of n C hL.1
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
    exact (Finset.card_le_card Finset.inter_subset_left).trans (P1.orIn_input C w hw)
  have hf2 : ∀ k, (gateAt C k).op = GateOp.or → ∀ u,
      u ∈ f (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, u ∈ f w := by
    intro k hop u
    constructor
    · rintro hu
      obtain ⟨hu, huR⟩ := Finset.mem_inter.mp hu
      obtain ⟨_, _, w, hw, _, huw⟩ := (P1.orIn_gate C k u).mp hu
      exact ⟨w, hw, Finset.mem_inter.mpr ⟨huw, huR⟩⟩
    · rintro ⟨w, hw, hu⟩
      obtain ⟨hu, huR⟩ := Finset.mem_inter.mp hu
      have hk : k < C.gates.length := by
        by_contra hk
        rw [P1.gateAt_ge (by omega)] at hw
        simp at hw
      exact Finset.mem_inter.mpr ⟨(P1.orIn_gate C k u).mpr
        ⟨hk, hop, w, hw, hback k w hw, hu⟩, huR⟩
  have hf3 : ∀ k, (gateAt C k).op ≠ GateOp.or → (f (n + k)).card ≤ 1 := by
    intro k hop
    apply (Finset.card_le_card Finset.inter_subset_left).trans
    rw [Finset.card_le_one]
    intro a ha
    exact absurd ((P1.orIn_gate C k a).mp ha).2.1 hop
  have hstop : ∀ k ∈ lam G C ∪ Z, f (n + k) ⊆ f root →
      (∀ v ∈ f (n + k), s(c, v) ∈ starEdges G C) ∨ (f (n + k)).card ≤ 1 := by
    intro k hk _
    rcases Finset.mem_union.mp hk with hk | hk
    · by_cases hs : (f (n + k)).card ≤ 1
      · exact Or.inr hs
      · have hsub : f (n + k) ⊆ (orIn n C (n + k)).filter (G.Adj c) := by
          intro v hv
          obtain ⟨hv, hvR⟩ := Finset.mem_inter.mp hv
          exact Finset.mem_filter.mpr ⟨hv, hR v hvR⟩
        have hc := Finset.card_le_card hsub
        have hh := lambda_filtered_support_star G hG C hL k hk c (by omega)
        exact Or.inl (fun v hv => hh.2 v (Finset.mem_inter.mp hv).1)
    · exact hZ k hk
  obtain ⟨B, hBstop, hB, hcount⟩ := P1.top_step2 n (gateAt C) hlen hback f hf1 hf2 hf3
    (lam G C ∪ Z) root c (starEdges G C) hstop
  have hBfacts : ∀ k ∈ B, k ∈ orN G C \ lam G C ∧
      P2.OrR n C root (n + k) ∧ (orIn n C (n + k)).Nonempty ∧
      orIn n C (n + k) ⊆ orIn n C root := by
    intro k hk
    obtain ⟨hop, htwo, hn, hr, _⟩ := hB k hk
    have hrlen : root - n < C.gates.length := by omega
    obtain ⟨hpath, hklen⟩ := P1.rtg_conv C hRB _ k hr hrlen
    have he : n + (root - n) = root := by omega
    rw [he] at hpath
    have hreach := P1.S90.reach_orReaches hpath k rfl hklen
    have hpath2 := P2.orReaches_orR n C root hroot k hreach
    obtain ⟨w, hw, z, hz, hne, hwne, hzne⟩ := htwo
    obtain ⟨u, hu⟩ := hwne
    obtain ⟨v, hv⟩ := hzne
    have htwo' : P1.TwoNe (gateAt C) (orIn n C) k :=
      ⟨w, hw, z, hz, hne, ⟨u, (Finset.mem_inter.mp hu).1⟩,
        ⟨v, (Finset.mem_inter.mp hv).1⟩⟩
    obtain ⟨hbel, _, _⟩ := P1.two_facts G C h2 hRB hklen hop htwo'
    have hkN : k ∈ orN G C := by
      simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨hklen, hop, hbel⟩
    have hnl : k ∉ lam G C := fun h => Finset.disjoint_left.mp hBstop (Finset.mem_union_left Z h) hk
    refine ⟨Finset.mem_sdiff.mpr ⟨hkN, hnl⟩, hpath2, ?_, ?_⟩
    · exact ⟨u, (P1.orIn_gate C k u).mpr
        ⟨hklen, hop, w, hw, hback k w hw, (Finset.mem_inter.mp hu).1⟩⟩
    · intro a ha
      exact (P1.orIn_iff_reach root a).mpr (hpath.trans ((P1.orIn_iff_reach _ a).mp ha))
  refine ⟨B, fun k hk => (hBfacts k hk).1, ?_, fun k hk => (hBfacts k hk).2, hcount⟩
  apply Finset.disjoint_left.mpr
  intro k hk hz
  exact Finset.disjoint_left.mp hBstop (Finset.mem_union_right _ hz) hk

end PEqualNP.Outside.L_meta_1477.ResidualRootCone


namespace PEqualNP.Outside.L_meta_1477.ResidualRootCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge OneJunk

lemma two_disjoint_roots {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (r₀ r₁ : ℕ) (hroot₀ : r₀ < n + C.gates.length) (hroot₁ : r₁ < n + C.gates.length)
    (c₀ c₁ : Fin n) (R₀ R₁ : Finset (Fin n))
    (hR₀ : ∀ v ∈ R₀, G.Adj c₀ v) (hR₁ : ∀ v ∈ R₁, G.Adj c₁ v)
    (hd : Disjoint (orIn n C r₀) (orIn n C r₁)) (U : Finset (Sym2 (Fin n)))
    (hU : U ⊆ (((orIn n C r₀ ∩ R₀).image (fun v => s(c₀, v))) \ starEdges G C) ∪
      (((orIn n C r₁ ∩ R₁).image (fun v => s(c₁, v))) \ starEdges G C)) :
    U.card ≤ (orN G C \ lam G C).card + 2 := by
  classical
  obtain ⟨B₀, hB₀, _, hf₀, hc₀⟩ := root_cone G hG C hL r₀ hroot₀ c₀ R₀ hR₀ ∅ (by simp)
  obtain ⟨B₁, hB₁, _, hf₁, hc₁⟩ := root_cone G hG C hL r₁ hroot₁ c₁ R₁ hR₁ ∅ (by simp)
  have hBdis : Disjoint B₀ B₁ := by
    apply Finset.disjoint_left.mpr
    intro k hk₀ hk₁
    obtain ⟨v, hv⟩ := (hf₀ k hk₀).2.1
    exact Finset.disjoint_left.mp hd ((hf₀ k hk₀).2.2 hv) ((hf₁ k hk₁).2.2 hv)
  have hBsub : B₀ ∪ B₁ ⊆ orN G C \ lam G C := Finset.union_subset hB₀ hB₁
  have hBcard := Finset.card_le_card hBsub
  rw [Finset.card_union_of_disjoint hBdis] at hBcard
  have hcard := (Finset.card_le_card hU).trans (Finset.card_union_le _ _)
  omega

lemma split_cover_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (r₀ r₁ : ℕ) (hroot₀ : r₀ < n + C.gates.length) (hroot₁ : r₁ < n + C.gates.length)
    (hd : Disjoint (orIn n C r₀) (orIn n C r₁))
    (a b : Fin n) (U : Finset (Sym2 (Fin n)))
    (hU : ∀ e ∈ U, e ∉ starEdges G C ∧ ∃ p ∈ orIn n C r₀, ∃ q ∈ orIn n C r₁,
      G.Adj p q ∧ e = s(p, q) ∧ (p = a ∨ q = b)) :
    U.card ≤ (orN G C \ lam G C).card + 2 := by
  classical
  let R₀ := Finset.univ.filter (G.Adj b)
  let R₁ := Finset.univ.filter (G.Adj a)
  apply two_disjoint_roots G hG C hL r₀ r₁ hroot₀ hroot₁ b a R₀ R₁
    (fun _ h => (Finset.mem_filter.mp h).2) (fun _ h => (Finset.mem_filter.mp h).2) hd U
  intro e he
  obtain ⟨hn, p, hp, q, hq, hpq, rfl, hcov⟩ := hU e he
  rcases hcov with rfl | rfl
  · apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr
      ⟨hq, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq⟩⟩, rfl⟩, hn⟩
  · apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_image.mpr ⟨p, Finset.mem_inter.mpr
      ⟨hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq.symm⟩⟩, Sym2.eq_swap⟩, hn⟩

end PEqualNP.Outside.L_meta_1477.ResidualRootCone


namespace PEqualNP.Outside.L_meta_1477.TwoJunkClauses

open PEqualNP.TopForm

lemma rectangle_cover_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (L R : Finset (Fin n))
    (hcross : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v) :
    ∃ T : Finset (Fin n), T.card ≤ 1 ∧
      ∀ u ∈ L, ∀ v ∈ R, u ∈ T ∨ v ∈ T := by
  classical
  by_cases hL : L.card ≤ 1
  · exact ⟨L, hL, fun _ hu _ _ => Or.inl hu⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < L.card)
  have hsub : R ⊆ Finset.univ.filter (fun v => G.Adj a v ∧ G.Adj b v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcross a ha v hv, hcross b hb v hv⟩
  exact ⟨R, (Finset.card_le_card hsub).trans (hG a b hab), fun _ _ _ hv => Or.inr hv⟩

lemma independent_clause {n m : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (clauses : Fin m → Finset (Fin n))
    (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v)
    (hclean : ∀ x : Fin n → Bool,
      (∀ i, ∃ v ∈ clauses i, x v = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ i, Disjoint (clauses i) S := by
  classical
  by_contra hnone
  have hall : ∀ i, ∃ v ∈ clauses i, v ∈ S := by
    intro i
    by_contra hnot
    apply hnone
    refine ⟨i, Finset.disjoint_left.mpr ?_⟩
    intro v hv hs
    exact hnot ⟨v, hv, hs⟩
  obtain ⟨u, v, huv, hu, hv⟩ := hclean (fun w => decide (w ∈ S)) (by
    intro i
    obtain ⟨w, hw, hs⟩ := hall i
    exact ⟨w, hw, by simpa⟩)
  exact hS u (of_decide_eq_true hu) v (of_decide_eq_true hv) huv

lemma bipartite_pure_clauses {n m : ℕ} (G : SimpleGraph (Fin n))
    (L : Finset (Fin n)) (clauses : Fin m → Finset (Fin n))
    (hL : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v)
    (hR : ∀ u ∉ L, ∀ v ∉ L, ¬ G.Adj u v)
    (hne : ∀ i, (clauses i).Nonempty)
    (hclean : ∀ x : Fin n → Bool,
      (∀ i, ∃ v ∈ clauses i, x v = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ i j, i ≠ j ∧ clauses i ⊆ L ∧ Disjoint (clauses j) L := by
  classical
  obtain ⟨j, hj⟩ := independent_clause G L clauses hL hclean
  obtain ⟨i, hi⟩ := independent_clause G (Finset.univ \ L) clauses (by
    intro u hu v hv
    exact hR u (Finset.mem_sdiff.mp hu).2 v (Finset.mem_sdiff.mp hv).2) hclean
  have hisub : clauses i ⊆ L := by
    intro v hv
    by_contra hn
    exact Finset.disjoint_left.mp hi hv (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩)
  refine ⟨i, j, ?_, hisub, hj⟩
  intro hij
  obtain ⟨v, hv⟩ := hne i
  exact Finset.disjoint_left.mp hj (hij ▸ hv) (hisub hv)

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses

namespace PEqualNP.Outside.L_meta_1477.TwoJunkClauses

open PEqualNP.TopForm

lemma two_filter_cover_no_both {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hnone : ¬ ∃ p ∈ P, p ∈ U ∧ p ∈ V) :
    ∃ T : Finset (Fin n), T.card ≤ 3 ∧
      ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → p ∈ T ∨ q ∈ T := by
  classical
  obtain ⟨T₁, h₁, hc₁⟩ := rectangle_cover_one G hG (P.filter (· ∈ U)) (Q.filter (· ∈ V)) (by
    intro p hp q hq
    exact hcross p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
      (Or.inl (Finset.mem_filter.mp hp).2) (Or.inr (Finset.mem_filter.mp hq).2))
  obtain ⟨T₂, h₂, hc₂⟩ := rectangle_cover_one G hG (P.filter (· ∈ V)) (Q.filter (· ∈ U)) (by
    intro p hp q hq
    exact hcross p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
      (Or.inr (Finset.mem_filter.mp hq).2) (Or.inl (Finset.mem_filter.mp hp).2))
  obtain ⟨T₃, h₃, hc₃⟩ := rectangle_cover_one G hG P (Q.filter (fun q => q ∈ U ∧ q ∈ V)) (by
    intro p hp q hq
    exact hcross p hp q (Finset.mem_filter.mp hq).1
      (Or.inr (Finset.mem_filter.mp hq).2.1) (Or.inr (Finset.mem_filter.mp hq).2.2))
  refine ⟨T₁ ∪ T₂ ∪ T₃, ?_, ?_⟩
  · have hx := Finset.card_union_le T₁ T₂
    have hy := Finset.card_union_le (T₁ ∪ T₂) T₃
    omega
  · intro p hp q hq hU hV
    have ht₁ : T₁ ⊆ T₁ ∪ T₂ ∪ T₃ := by intro w hw; simp only [Finset.mem_union]; exact Or.inl (Or.inl hw)
    have ht₂ : T₂ ⊆ T₁ ∪ T₂ ∪ T₃ := by intro w hw; simp only [Finset.mem_union]; exact Or.inl (Or.inr hw)
    have ht₃ : T₃ ⊆ T₁ ∪ T₂ ∪ T₃ := Finset.subset_union_right
    by_cases hpU : p ∈ U
    · have hpV : p ∉ V := fun h => hnone ⟨p, hp, hpU, h⟩
      exact (hc₁ p (Finset.mem_filter.mpr ⟨hp, hpU⟩) q
        (Finset.mem_filter.mpr ⟨hq, hV.resolve_left hpV⟩)).imp (ht₁ ·) (ht₁ ·)
    · by_cases hpV : p ∈ V
      · exact (hc₂ p (Finset.mem_filter.mpr ⟨hp, hpV⟩) q
          (Finset.mem_filter.mpr ⟨hq, hU.resolve_left hpU⟩)).imp (ht₂ ·) (ht₂ ·)
      · exact (hc₃ p hp q (Finset.mem_filter.mpr
          ⟨hq, hU.resolve_left hpU, hV.resolve_left hpV⟩)).imp (ht₃ ·) (ht₃ ·)

lemma two_filter_cover_anchor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hQ : 2 ≤ Q.card) (a b : Fin n)
    (haP : a ∈ P) (haU : a ∈ U) (haV : a ∈ V)
    (hbP : b ∈ P) (hbU : b ∈ U) (hbV : b ∉ V) :
    ∃ T : Finset (Fin n), T.card ≤ 3 ∧
      ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → p ∈ T ∨ q ∈ T := by
  classical
  have hab : a ≠ b := by intro h; exact hbV (h ▸ haV)
  have hadj (q : Fin n) (hq : q ∈ Q) : G.Adj a q :=
    hcross a haP q hq (Or.inl haU) (Or.inl haV)
  have hsmall : (Q.filter (· ∈ V)).card ≤ 1 := by
    have hsub : Q.filter (· ∈ V) ⊆ Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
      intro q hq
      obtain ⟨hq, hqV⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj q hq,
        hcross b hbP q hq (Or.inl hbU) (Or.inr hqV)⟩
    exact (Finset.card_le_card hsub).trans (hG a b hab)
  have huniq (p : Fin n) (hp : p ∈ P) (hpU : p ∈ U) (hpV : p ∈ V) : p = a := by
    by_contra hne
    have hsub : Q ⊆ Finset.univ.filter (fun q => G.Adj p q ∧ G.Adj a q) := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hcross p hp q hq (Or.inl hpU) (Or.inl hpV), hadj q hq⟩
    have hx := (Finset.card_le_card hsub).trans (hG p a hne)
    omega
  obtain ⟨S, hS, hcS⟩ := rectangle_cover_one G hG (P.filter (· ∈ V)) (Q.filter (· ∈ U)) (by
    intro p hp q hq
    exact hcross p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
      (Or.inr (Finset.mem_filter.mp hq).2) (Or.inl (Finset.mem_filter.mp hp).2))
  refine ⟨{a} ∪ Q.filter (· ∈ V) ∪ S, ?_, ?_⟩
  · have hx := Finset.card_union_le ({a} : Finset (Fin n)) (Q.filter (· ∈ V))
    have hy := Finset.card_union_le ({a} ∪ Q.filter (· ∈ V)) S
    have hz : ({a} : Finset (Fin n)).card = 1 := Finset.card_singleton a
    omega
  · intro p hp q hq hU hV
    have htA : a ∈ ({a} ∪ Q.filter (· ∈ V) ∪ S : Finset (Fin n)) := by simp
    have htQ : Q.filter (· ∈ V) ⊆ ({a} ∪ Q.filter (· ∈ V) ∪ S : Finset (Fin n)) := by
      intro w hw
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hw)
    have htS : S ⊆ ({a} ∪ Q.filter (· ∈ V) ∪ S : Finset (Fin n)) := Finset.subset_union_right
    by_cases hpV : p ∈ V
    · by_cases hpU : p ∈ U
      · exact Or.inl (huniq p hp hpU hpV ▸ htA)
      · exact (hcS p (Finset.mem_filter.mpr ⟨hp, hpV⟩) q
          (Finset.mem_filter.mpr ⟨hq, hU.resolve_left hpU⟩)).imp (htS ·) (htS ·)
    · exact Or.inr (htQ (Finset.mem_filter.mpr ⟨hq, hV.resolve_left hpV⟩))

lemma two_filter_cover_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q) :
    ∃ T : Finset (Fin n), T.card ≤ 3 ∧
      ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → p ∈ T ∨ q ∈ T := by
  classical
  by_cases hQ : Q.card ≤ 1
  · exact ⟨Q, by omega, fun _ _ _ hq _ _ => Or.inr hq⟩
  by_cases hboth : ∃ a ∈ P, a ∈ U ∧ a ∈ V
  · obtain ⟨a, haP, haU, haV⟩ := hboth
    by_cases hleft : ∃ b ∈ P, b ∈ U ∧ b ∉ V
    · obtain ⟨b, hbP, hbU, hbV⟩ := hleft
      exact two_filter_cover_anchor G hG P Q U V hcross (by omega) a b haP haU haV hbP hbU hbV
    by_cases hright : ∃ b ∈ P, b ∈ V ∧ b ∉ U
    · obtain ⟨b, hbP, hbV, hbU⟩ := hright
      obtain ⟨T, hT, hcT⟩ := two_filter_cover_anchor G hG P Q V U
        (fun p hp q hq hV hU => hcross p hp q hq hU hV) (by omega)
        a b haP haV haU hbP hbV hbU
      exact ⟨T, hT, fun p hp q hq hU hV => hcT p hp q hq hV hU⟩
    have hequiv (p : Fin n) (hp : p ∈ P) : p ∈ U ↔ p ∈ V := by
      constructor
      · intro h
        by_contra hn
        exact hleft ⟨p, hp, h, hn⟩
      · intro h
        by_contra hn
        exact hright ⟨p, hp, h, hn⟩
    obtain ⟨T₁, h₁, hc₁⟩ := rectangle_cover_one G hG (P.filter (· ∈ U)) Q (by
      intro p hp q hq
      obtain ⟨hp, hpU⟩ := Finset.mem_filter.mp hp
      exact hcross p hp q hq (Or.inl hpU) (Or.inl ((hequiv p hp).mp hpU)))
    obtain ⟨T₂, h₂, hc₂⟩ := rectangle_cover_one G hG P (Q.filter (fun q => q ∈ U ∧ q ∈ V)) (by
      intro p hp q hq
      obtain ⟨hq, hqU, hqV⟩ := Finset.mem_filter.mp hq
      exact hcross p hp q hq (Or.inr hqU) (Or.inr hqV))
    refine ⟨T₁ ∪ T₂, ?_, ?_⟩
    · have hx := Finset.card_union_le T₁ T₂
      omega
    · intro p hp q hq hU hV
      by_cases hpU : p ∈ U
      · exact (hc₁ p (Finset.mem_filter.mpr ⟨hp, hpU⟩) q hq).imp
          (Finset.mem_union_left T₂) (Finset.mem_union_left T₂)
      · have hpV : p ∉ V := fun hv => hpU ((hequiv p hp).mpr hv)
        exact (hc₂ p hp q (Finset.mem_filter.mpr ⟨hq, hU.resolve_left hpU, hV.resolve_left hpV⟩)).imp
          (Finset.mem_union_right T₁) (Finset.mem_union_right T₁)
  · exact two_filter_cover_no_both G hG P Q U V hcross hboth

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses

namespace PEqualNP.Outside.L_meta_1477.TwoJunkClauses

open PEqualNP.TopForm

lemma nested_neighbor_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P : Finset (Fin n)) (N : Fin n → Finset (Fin n))
    (hAdj : ∀ p ∈ P, ∀ q ∈ N p, G.Adj p q) (a b : Fin n)
    (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b) (hsub : N a ⊆ N b) :
    (N a).card ≤ 1 := by
  have hinc : N a ⊆ Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAdj a ha q hq, hAdj b hb q (hsub hq)⟩
  exact (Finset.card_le_card hinc).trans (hG a b hne)

lemma two_filter_heavy_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q) :
    (P.filter (fun p => 2 ≤ (Q.filter (fun q =>
      (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))).card)).card ≤ 2 := by
  classical
  let N : Fin n → Finset (Fin n) := fun p => Q.filter (fun q =>
    (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))
  let H := P.filter (fun p => 2 ≤ (N p).card)
  change H.card ≤ 2
  have hAdj : ∀ p ∈ P, ∀ q ∈ N p, G.Adj p q := by
    intro p hp q hq
    obtain ⟨hq, hU, hV⟩ := Finset.mem_filter.mp hq
    exact hcross p hp q hq hU hV
  by_cases hboth : ∃ a ∈ H, a ∈ U ∧ a ∈ V
  · obtain ⟨a, ha, haU, haV⟩ := hboth
    have hcard : H.card ≤ 1 := Finset.card_le_one.mpr (by
      intro b hb c hc
      have heq (b : Fin n) (hb : b ∈ H) : b = a := by
        by_contra hne
        obtain ⟨hbP, hbN⟩ := Finset.mem_filter.mp hb
        have hsub : N b ⊆ N a := by
          intro q hq
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1, Or.inl haU, Or.inl haV⟩
        have hx := nested_neighbor_small G hG P N hAdj b a hbP (Finset.mem_filter.mp ha).1 hne hsub
        omega
      exact (heq b hb).trans (heq c hc).symm)
    omega
  by_cases hneither : ∃ a ∈ H, a ∉ U ∧ a ∉ V
  · obtain ⟨a, ha, haU, haV⟩ := hneither
    have hcard : H.card ≤ 1 := Finset.card_le_one.mpr (by
      intro b hb c hc
      have heq (b : Fin n) (hb : b ∈ H) : b = a := by
        by_contra hne
        have hsub : N a ⊆ N b := by
          intro q hq
          obtain ⟨hq, hU, hV⟩ := Finset.mem_filter.mp hq
          exact Finset.mem_filter.mpr ⟨hq, Or.inr (hU.resolve_left haU), Or.inr (hV.resolve_left haV)⟩
        have hx := nested_neighbor_small G hG P N hAdj a b (Finset.mem_filter.mp ha).1
          (Finset.mem_filter.mp hb).1 (Ne.symm hne) hsub
        have haN := (Finset.mem_filter.mp ha).2
        omega
      exact (heq b hb).trans (heq c hc).symm)
    omega
  have hsmallU : (H.filter (· ∈ U)).card ≤ 1 := Finset.card_le_one.mpr (by
    intro a ha b hb
    obtain ⟨ha, haU⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hbU⟩ := Finset.mem_filter.mp hb
    have haV : a ∉ V := fun h => hboth ⟨a, ha, haU, h⟩
    have hbV : b ∉ V := fun h => hboth ⟨b, hb, hbU, h⟩
    by_contra hne
    have hsub : N a ⊆ N b := by
      intro q hq
      obtain ⟨hq, _, hV⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hq, Or.inl hbU, Or.inr (hV.resolve_left haV)⟩
    have hx := nested_neighbor_small G hG P N hAdj a b (Finset.mem_filter.mp ha).1
      (Finset.mem_filter.mp hb).1 hne hsub
    have haN := (Finset.mem_filter.mp ha).2
    omega)
  have hsmallV : (H.filter (· ∈ V)).card ≤ 1 := Finset.card_le_one.mpr (by
    intro a ha b hb
    obtain ⟨ha, haV⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hbV⟩ := Finset.mem_filter.mp hb
    have haU : a ∉ U := fun h => hboth ⟨a, ha, h, haV⟩
    by_contra hne
    have hsub : N a ⊆ N b := by
      intro q hq
      obtain ⟨hq, hU, _⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hq, Or.inr (hU.resolve_left haU), Or.inl hbV⟩
    have hx := nested_neighbor_small G hG P N hAdj a b (Finset.mem_filter.mp ha).1
      (Finset.mem_filter.mp hb).1 hne hsub
    have haN := (Finset.mem_filter.mp ha).2
    omega)
  have hsub : H ⊆ H.filter (· ∈ U) ∪ H.filter (· ∈ V) := by
    intro p hp
    by_cases hpU : p ∈ U
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hpU⟩)
    · have hpV : p ∈ V := by
        by_contra hn
        exact hneither ⟨p, hp, hpU, hn⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hpV⟩)
  have hx := Finset.card_le_card hsub
  have hy := Finset.card_union_le (H.filter (· ∈ U)) (H.filter (· ∈ V))
  omega

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses

namespace PEqualNP.Outside.L_meta_1477.TwoJunkClauses

open PEqualNP.TopForm

lemma degree_sum_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q : Finset (Fin n)) (N : Fin n → Finset (Fin n))
    (hQ : Q.Nonempty) (hsub : ∀ p ∈ P, N p ⊆ Q)
    (hAdj : ∀ p ∈ P, ∀ q ∈ N p, G.Adj p q)
    (hheavy : (P.filter (fun p => 2 ≤ (N p).card)).card ≤ 2) :
    (∑ p ∈ P, (N p).card) + 1 ≤ P.card + Q.card := by
  classical
  let H := P.filter (fun p => 2 ≤ (N p).card)
  have hHP : H ⊆ P := Finset.filter_subset _ _
  have hsum : (∑ p ∈ P \ H, (N p).card) + (∑ p ∈ H, (N p).card) = ∑ p ∈ P, (N p).card :=
    Finset.sum_sdiff hHP
  have hcard := Finset.card_sdiff_add_card_eq_card hHP
  have hlight : (∑ p ∈ P \ H, (N p).card) ≤ (P \ H).card := by
    calc
      _ ≤ ∑ _p ∈ P \ H, 1 := Finset.sum_le_sum (by
        intro p hp
        obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hp
        have hn2 : ¬ 2 ≤ (N p).card := fun h => hn (Finset.mem_filter.mpr ⟨hp, h⟩)
        omega)
      _ = _ := by simp
  have hQpos := Finset.card_pos.mpr hQ
  by_cases h0 : H.card = 0
  · have he : H = ∅ := Finset.card_eq_zero.mp h0
    have hsum0 : (∑ p ∈ H, (N p).card) = 0 := by rw [he]; simp
    omega
  have hlarge : (∑ p ∈ H, (N p).card) + 1 ≤ Q.card + H.card := by
    by_cases h1 : H.card = 1
    · obtain ⟨a, he⟩ := Finset.card_eq_one.mp h1
      have haH : a ∈ H := by rw [he]; simp
      have ha := Finset.card_le_card (hsub a (hHP haH))
      have hs : (∑ p ∈ H, (N p).card) = (N a).card := by rw [he]; simp
      omega
    · have h2 : H.card = 2 := by change H.card ≤ 2 at hheavy; omega
      obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp h2
      have haH : a ∈ H := by rw [he]; simp
      have hbH : b ∈ H := by rw [he]; simp
      have haP := hHP haH
      have hbP := hHP hbH
      have huni : (N a ∪ N b).card ≤ Q.card := Finset.card_le_card
        (Finset.union_subset (hsub a haP) (hsub b hbP))
      have hinter : (N a ∩ N b).card ≤ 1 := by
        have hinc : N a ∩ N b ⊆ Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
          intro q hq
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hAdj a haP q (Finset.mem_inter.mp hq).1,
            hAdj b hbP q (Finset.mem_inter.mp hq).2⟩
        exact (Finset.card_le_card hinc).trans (hG a b hab)
      have hx := Finset.card_union_add_card_inter (N a) (N b)
      have hs : (∑ p ∈ H, (N p).card) = (N a).card + (N b).card := by rw [he]; simp [hab]
      omega
  omega

lemma two_filter_edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n)) (hQ : Q.Nonempty)
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q) :
    (∑ p ∈ P, (Q.filter (fun q => (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))).card) + 1 ≤
      P.card + Q.card := by
  apply degree_sum_bound G hG P Q _ hQ
  · intro p _
    exact Finset.filter_subset _ _
  · intro p hp q hq
    obtain ⟨hq, hU, hV⟩ := Finset.mem_filter.mp hq
    exact hcross p hp q hq hU hV
  · exact two_filter_heavy_card G hG P Q U V hcross

lemma two_filter_gate_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q) :
    ∃ T : Finset (Fin n), T.card ≤ 3 ∧
      ((∑ p ∈ P, (Q.filter (fun q => (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))).card) +
        T.card - 1 ≤ P.card + Q.card + 1) ∧
      ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → p ∈ T ∨ q ∈ T := by
  classical
  by_cases hQ : Q.Nonempty
  · obtain ⟨T, hT, hcT⟩ := two_filter_cover_three G hG P Q U V hcross
    have he := two_filter_edge_bound G hG P Q U V hQ hcross
    exact ⟨T, hT, by omega, hcT⟩
  · have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQ
    refine ⟨∅, by simp, ?_, ?_⟩
    · simp [he]
    · intro p hp q hq
      rw [he] at hq
      simp at hq

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses

namespace PEqualNP.Outside.L_meta_1477.StarDecomposition

lemma directed_stars {n : ℕ} (R : Finset (Fin n × Fin n)) (T : Finset (Fin n))
    (hne : R.Nonempty) (hT : ∀ e ∈ R, e.1 ∈ T) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ T.card ∧
      (ss.map fun s => s.2.length).sum = R.card ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ R) ∧
      (∀ e ∈ R, ∃ s ∈ ss, s.1 = e.1 ∧ e.2 ∈ s.2) := by
  classical
  let S := R.image Prod.fst
  let N : Fin n → Finset (Fin n) := fun c => (R.filter (fun e => e.1 = c)).image Prod.snd
  let ss : List (Fin n × List (Fin n)) := S.toList.map (fun c => (c, (N c).toList))
  have hNm (c v : Fin n) : v ∈ N c ↔ (c, v) ∈ R := by
    constructor
    · intro hv
      obtain ⟨⟨a, b⟩, he, hv⟩ := Finset.mem_image.mp hv
      obtain ⟨he, ha⟩ := Finset.mem_filter.mp he
      dsimp at ha hv
      subst a
      subst b
      exact he
    · intro hv
      exact Finset.mem_image.mpr ⟨(c, v), Finset.mem_filter.mpr ⟨hv, rfl⟩, rfl⟩
  have hNcard (c : Fin n) : (N c).card = (R.filter (fun e => e.1 = c)).card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab
  have hlen : ss.length = S.card := by simp [ss]
  have hScard : S.card ≤ T.card := Finset.card_le_card (by
    intro c hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
    exact hT e he)
  have hssne : ss ≠ [] := by
    intro he
    obtain ⟨e, heR⟩ := hne
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e.1, Finset.mem_image.mpr ⟨e, heR, rfl⟩⟩
    simp only [he, List.length_nil] at hlen
    omega
  have hentry : ∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ R := by
    intro s hs v hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    exact (hNm c v).mp (by simpa using hv)
  have hall : ∀ e ∈ R, ∃ s ∈ ss, s.1 = e.1 ∧ e.2 ∈ s.2 := by
    intro e he
    refine ⟨(e.1, (N e.1).toList), ?_, rfl, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨e.1, Finset.mem_toList.mpr (Finset.mem_image.mpr ⟨e, he, rfl⟩), rfl⟩
    · exact Finset.mem_toList.mpr ((hNm e.1 e.2).mpr he)
  have hnonempty : ∀ s ∈ ss, s.2 ≠ [] := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    have hcS : c ∈ S := by simpa using hc
    obtain ⟨e, he, hc⟩ := Finset.mem_image.mp hcS
    have hmem : e.2 ∈ (N c).toList := Finset.mem_toList.mpr ((hNm c e.2).mpr (by rw [← hc]; exact he))
    intro hn
    change (N c).toList = [] at hn
    rw [hn] at hmem
    simp at hmem
  have hcost : (ss.map fun s => s.2.length).sum = R.card := by
    simp only [ss, List.map_map, Function.comp_def, Finset.length_toList]
    rw [Finset.sum_map_toList]
    simp_rw [hNcard]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    apply Finset.filter_eq_self.mpr
    intro e he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  exact ⟨ss, hssne, hnonempty, hlen.trans_le hScard, hcost, hentry, hall⟩

lemma oriented_stars {n : ℕ} (E : Finset (Fin n × Fin n)) (T : Finset (Fin n))
    (hne : E.Nonempty) (hT : ∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ T.card ∧
      (ss.map fun s => s.2.length).sum ≤ E.card ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ E ∨ (v, s.1) ∈ E) ∧
      (∀ x : Fin n → Bool,
        (ss.any fun s => x s.1 && s.2.any x) =
          decide (∃ e ∈ E, x e.1 = true ∧ x e.2 = true)) := by
  classical
  let orient : (Fin n × Fin n) → (Fin n × Fin n) := fun e =>
    if e.1 ∈ T then e else (e.2, e.1)
  let R := E.image orient
  have hRne : R.Nonempty := Finset.Nonempty.image hne orient
  have hRT : ∀ e ∈ R, e.1 ∈ T := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    by_cases hh : f.1 ∈ T
    · simpa [orient, hh] using hh
    · simpa [orient, hh] using (hT f hf).resolve_left hh
  obtain ⟨ss, hss, hneigh, hlen, hcost, hentry, hall⟩ := directed_stars R T hRne hRT
  have hedges : ∀ s ∈ ss, ∀ v ∈ s.2, (s.1, v) ∈ E ∨ (v, s.1) ∈ E := by
    intro s hs v hv
    obtain ⟨e, he, hor⟩ := Finset.mem_image.mp (hentry s hs v hv)
    by_cases hh : e.1 ∈ T
    · have heq : e = (s.1, v) := by simpa [orient, hh] using hor
      exact Or.inl (heq ▸ he)
    · have heq : (e.2, e.1) = (s.1, v) := by simpa [orient, hh] using hor
      have heq' : e = (v, s.1) := by
        apply Prod.ext
        · exact congrArg Prod.snd heq
        · exact congrArg Prod.fst heq
      exact Or.inr (heq' ▸ he)
  refine ⟨ss, hss, hneigh, hlen, hcost.trans_le (Finset.card_image_le), hedges, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, hxs, v, hv, hxv⟩
    rcases hedges s hs v hv with he | he
    · exact ⟨(s.1, v), he, hxs, hxv⟩
    · exact ⟨(v, s.1), he, hxv, hxs⟩
  · rintro ⟨e, he, hx1, hx2⟩
    have heR : orient e ∈ R := Finset.mem_image.mpr ⟨e, he, rfl⟩
    obtain ⟨s, hs, hs1, hv⟩ := hall (orient e) heR
    refine ⟨s, hs, ?_, (orient e).2, hv, ?_⟩
    · rw [hs1]
      by_cases hh : e.1 ∈ T
      · simpa [orient, hh] using hx1
      · simpa [orient, hh] using hx2
    · by_cases hh : e.1 ∈ T
      · simpa [orient, hh] using hx2
      · simpa [orient, hh] using hx1

end PEqualNP.Outside.L_meta_1477.StarDecomposition


namespace PEqualNP.Outside.L_meta_1477.TwoJunkClauses

open PEqualNP.TopForm

def filteredEdges {n : ℕ} (P Q U V : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (P ×ˢ Q).filter (fun e => (e.1 ∈ U ∨ e.2 ∈ U) ∧ (e.1 ∈ V ∨ e.2 ∈ V))

lemma filteredEdges_card {n : ℕ} (P Q U V : Finset (Fin n)) :
    (filteredEdges P Q U V).card =
      ∑ p ∈ P, (Q.filter (fun q => (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))).card := by
  classical
  let E := filteredEdges P Q U V
  have hfiber (p : Fin n) (hp : p ∈ P) :
      E.filter (fun e => e.1 = p) =
        (Q.filter (fun q => (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))).image (fun q => (p, q)) := by
    ext e
    constructor
    · intro he
      obtain ⟨he, hep⟩ := Finset.mem_filter.mp he
      obtain ⟨hepQ, hU, hV⟩ := Finset.mem_filter.mp he
      obtain ⟨_, heQ⟩ := Finset.mem_product.mp hepQ
      refine Finset.mem_image.mpr ⟨e.2, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨heQ, hep ▸ hU, hep ▸ hV⟩
      · exact Prod.ext hep.symm rfl
    · intro he
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hq, hU, hV⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hU, hV⟩, rfl⟩
  have hcard (p : Fin n) (hp : p ∈ P) :
      (E.filter (fun e => e.1 = p)).card =
        (Q.filter (fun q => (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))).card := by
    rw [hfiber p hp]
    apply Finset.card_image_of_injective
    intro q r h
    exact congrArg Prod.snd h
  have hs := Finset.sum_card_fiberwise_eq_card_filter E P Prod.fst
  have hfilter : E.filter (fun e => e.1 ∈ P) = E := Finset.filter_eq_self.mpr (by
    intro e he
    exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1)
  rw [hfilter] at hs
  rw [← hs]
  exact Finset.sum_congr rfl hcard

lemma filtered_stars {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hne : (filteredEdges P Q U V).Nonempty) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ 3 ∧
      (ss.map fun s => s.2.length).sum + ss.length ≤ P.card + Q.card + 2 ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, G.Adj s.1 v) ∧
      (∀ x : Fin n → Bool,
        (ss.any fun s => x s.1 && s.2.any x) =
          decide (∃ e ∈ filteredEdges P Q U V, x e.1 = true ∧ x e.2 = true)) := by
  classical
  obtain ⟨T, hT, hbudget, hcover⟩ := two_filter_gate_budget G hG P Q U V hcross
  have hcov : ∀ e ∈ filteredEdges P Q U V, e.1 ∈ T ∨ e.2 ∈ T := by
    intro e he
    obtain ⟨hePQ, hU, hV⟩ := Finset.mem_filter.mp he
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hePQ
    exact hcover e.1 hp e.2 hq hU hV
  obtain ⟨ss, hss, hsne, hlen, hcost, hentry, hfun⟩ :=
    StarDecomposition.oriented_stars (filteredEdges P Q U V) T hne hcov
  have hcard := filteredEdges_card P Q U V
  have hpos := Finset.card_pos.mpr hne
  refine ⟨ss, hss, hsne, hlen.trans hT, ?_, ?_, hfun⟩
  · omega
  · intro s hs v hv
    rcases hentry s hs v hv with he | he
    · obtain ⟨hePQ, hU, hV⟩ := Finset.mem_filter.mp he
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hePQ
      exact hcross s.1 hp v hq hU hV
    · obtain ⟨hePQ, hU, hV⟩ := Finset.mem_filter.mp he
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hePQ
      exact (hcross v hp s.1 hq hU hV).symm

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses


namespace PEqualNP.Outside.L_meta_1477.TwoJunkClauses

open PEqualNP.TopForm PEqualNP.EdgeOwnership

def clauseValue {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def fourValue {n : ℕ} (P Q U V : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  (clauseValue P x && clauseValue Q x) && (clauseValue U x && clauseValue V x)

def edgeValue {n : ℕ} (P Q U V : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ e ∈ filteredEdges P Q U V, x e.1 = true ∧ x e.2 = true)

lemma edgeValue_le_fourValue {n : ℕ} (P Q U V : Finset (Fin n)) (x : Fin n → Bool) :
    edgeValue P Q U V x ≤ fourValue P Q U V x := by
  apply Bool.le_iff_imp.mpr
  intro hx
  obtain ⟨e, he, hx1, hx2⟩ := of_decide_eq_true hx
  obtain ⟨hePQ, hU, hV⟩ := Finset.mem_filter.mp he
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hePQ
  simp only [fourValue, clauseValue, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨e.1, hp, hx1⟩, ⟨e.2, hq, hx2⟩⟩, ?_, ?_⟩
  · rcases hU with h | h
    · exact ⟨e.1, h, hx1⟩
    · exact ⟨e.2, h, hx2⟩
  · rcases hV with h | h
    · exact ⟨e.1, h, hx1⟩
    · exact ⟨e.2, h, hx2⟩

lemma edgeValue_pair_eq_fourValue {n : ℕ} (P Q U V : Finset (Fin n))
    (hdis : Disjoint P Q) (u v : Fin n) :
    edgeValue P Q U V (pairInput u v) = fourValue P Q U V (pairInput u v) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact Bool.le_iff_imp.mp (edgeValue_le_fourValue P Q U V (pairInput u v))
  · intro hf
    simp only [fourValue, clauseValue, Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨⟨⟨p, hp, hpx⟩, ⟨q, hq, hqx⟩⟩, ⟨r, hr, hrx⟩, ⟨s, hs, hsx⟩⟩ := hf
    simp only [pairInput, decide_eq_true_eq] at hpx hqx hrx hsx
    have hUV : u ∈ U ∨ v ∈ U := by rcases hrx with rfl | rfl <;> simp_all
    have hVV : u ∈ V ∨ v ∈ V := by rcases hsx with rfl | rfl <;> simp_all
    have hpq : p ≠ q := fun he => Finset.disjoint_left.mp hdis hp (he ▸ hq)
    simp only [edgeValue, decide_eq_true_eq]
    change ∃ e ∈ filteredEdges P Q U V, pairInput u v e.1 = true ∧ pairInput u v e.2 = true
    rcases hpx with rfl | rfl <;> rcases hqx with rfl | rfl
    · exact (hpq rfl).elim
    · refine ⟨(p, q), ?_, by simp [pairInput], by simp [pairInput]⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hUV, hVV⟩
    · refine ⟨(p, q), ?_, by simp [pairInput], by simp [pairInput]⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hUV.symm, hVV.symm⟩
    · exact (hpq rfl).elim

lemma filtered_stars_semantic {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n)) (hdis : Disjoint P Q)
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hne : (filteredEdges P Q U V).Nonempty) :
    ∃ ss : List (Fin n × List (Fin n)), ss ≠ [] ∧
      (∀ s ∈ ss, s.2 ≠ []) ∧ ss.length ≤ 3 ∧
      (ss.map fun s => s.2.length).sum + ss.length ≤ P.card + Q.card + 2 ∧
      (∀ s ∈ ss, ∀ v ∈ s.2, G.Adj s.1 v) ∧
      (∀ x : Fin n → Bool, (ss.any fun s => x s.1 && s.2.any x) ≤ fourValue P Q U V x) ∧
      (∀ u v : Fin n, (ss.any fun s => pairInput u v s.1 && s.2.any (pairInput u v)) =
        fourValue P Q U V (pairInput u v)) := by
  obtain ⟨ss, hss, hsne, hlen, hcost, hclean, hfun⟩ := filtered_stars G hG P Q U V hcross hne
  refine ⟨ss, hss, hsne, hlen, hcost, hclean, ?_, ?_⟩
  · intro x
    rw [hfun x]
    exact edgeValue_le_fourValue P Q U V x
  · intro u v
    rw [hfun (pairInput u v)]
    exact edgeValue_pair_eq_fourValue P Q U V hdis u v

end PEqualNP.Outside.L_meta_1477.TwoJunkClauses

namespace PEqualNP.Outside.L_meta_1477.MixedShared
open PEqualNP.TopForm

lemma common_filter_forces_centers {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ a ∈ P, ∀ b ∈ Q,
      (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) → G.Adj a b)
    (p q : Fin n) (hp : p ∈ P) (hq : q ∈ Q)
    (hpU : p ∈ U) (hpV : p ∈ V) (hqU : q ∈ U) (hqV : q ∈ V) :
    ∀ a ∈ P, ∀ b ∈ Q, (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) →
      a = p ∨ b = q := by
  classical
  intro a ha b hb hU hV
  by_cases hap : a = p
  · exact Or.inl hap
  apply Or.inr
  have hs := Finset.card_le_one.mp (hG a p hap)
  apply hs
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcross a ha b hb hU hV,
      hcross p hp b hb (Or.inl hpU) (Or.inl hpV)⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hcross a ha q hq (Or.inr hqU) (Or.inr hqV),
      hcross p hp q hq (Or.inl hpU) (Or.inl hpV)⟩

lemma common_filter_cover_two {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ a ∈ P, ∀ b ∈ Q,
      (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) → G.Adj a b)
    (p q : Fin n) (hp : p ∈ P) (hq : q ∈ Q)
    (hpU : p ∈ U) (hpV : p ∈ V) (hqU : q ∈ U) (hqV : q ∈ V) :
    ∃ T : Finset (Fin n), T.card ≤ 2 ∧ G.Adj p q ∧
      ∀ a ∈ P, ∀ b ∈ Q, (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) →
        a ∈ T ∨ b ∈ T := by
  classical
  refine ⟨{p, q}, by simpa using (Finset.card_insert_le p ({q} : Finset (Fin n))),
    hcross p hp q hq (Or.inl hpU) (Or.inl hpV), ?_⟩
  intro a ha b hb hU hV
  rcases common_filter_forces_centers G hG P Q U V hcross p q hp hq hpU hpV hqU hqV
    a ha b hb hU hV with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

lemma two_common_left_force_right_small {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ a ∈ P, ∀ b ∈ Q,
      (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) → G.Adj a b)
    (hP : 2 ≤ (P.filter fun p => p ∈ U ∧ p ∈ V).card) : Q.card ≤ 1 := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
    1 < (P.filter fun p => p ∈ U ∧ p ∈ V).card)
  obtain ⟨haP, haU, haV⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbP, hbU, hbV⟩ := Finset.mem_filter.mp hb
  have hsub : Q ⊆ Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hcross a haP q hq (Or.inl haU) (Or.inl haV),
      hcross b hbP q hq (Or.inl hbU) (Or.inl hbV)⟩
  exact (Finset.card_le_card hsub).trans (hG a b hab)

lemma two_common_right_force_left_small {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ a ∈ P, ∀ b ∈ Q,
      (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) → G.Adj a b)
    (hQ : 2 ≤ (Q.filter fun q => q ∈ U ∧ q ∈ V).card) : P.card ≤ 1 :=
  two_common_left_force_right_small G hG Q P U V
    (fun a ha b hb hU hV => (hcross b hb a ha hU.symm hV.symm).symm) hQ

end PEqualNP.Outside.L_meta_1477.MixedShared


namespace PEqualNP.Outside.L_meta_1477.FourClauseCover

open PEqualNP.TopForm TwoJunkClauses

def Obstruction {n : ℕ} (P Q U V : Finset (Fin n)) : Prop :=
  (P.filter (fun p => p ∈ U ∧ p ∉ V)).Nonempty ∧
  (P.filter (fun p => p ∈ V ∧ p ∉ U)).Nonempty ∧
  (P.filter (fun p => p ∉ U ∧ p ∉ V)).Nonempty ∧
  (Q.filter (fun q => q ∈ U ∧ q ∉ V)).Nonempty ∧
  (Q.filter (fun q => q ∈ V ∧ q ∉ U)).Nonempty ∧
  (Q.filter (fun q => q ∈ U ∧ q ∈ V)).Nonempty

lemma clean_no_obstruction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hQ : ∀ q ∈ Q, ∀ r ∈ Q, ¬ G.Adj q r)
    (hclean : ∀ x : Fin n → Bool, fourValue P Q U V x = true →
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) : ¬ Obstruction P Q U V := by
  classical
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨y, hy⟩, ⟨x, hx⟩, ⟨z, hz⟩⟩
  obtain ⟨haP, haU, haV⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbP, hbV, hbU⟩ := Finset.mem_filter.mp hb
  obtain ⟨hcP, hcU, hcV⟩ := Finset.mem_filter.mp hc
  obtain ⟨hyQ, hyU, hyV⟩ := Finset.mem_filter.mp hy
  obtain ⟨hxQ, hxV, hxU⟩ := Finset.mem_filter.mp hx
  obtain ⟨hzQ, hzU, hzV⟩ := Finset.mem_filter.mp hz
  have hcz := hcross c hcP z hzQ (Or.inr hzU) (Or.inr hzV)
  have hax := hcross a haP x hxQ (Or.inl haU) (Or.inr hxV)
  have haz := hcross a haP z hzQ (Or.inl haU) (Or.inr hzV)
  have hby := hcross b hbP y hyQ (Or.inr hyU) (Or.inl hbV)
  have hbz := hcross b hbP z hzQ (Or.inr hzU) (Or.inl hbV)
  have hca : c ≠ a := by intro he; exact hcU (he ▸ haU)
  have hcb : c ≠ b := by intro he; exact hcV (he ▸ hbV)
  have hcx : ¬ G.Adj c x := by
    intro hh
    have he : x = z := Finset.card_le_one.mp (hG c a hca) x
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, hax⟩) z
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcz, haz⟩)
    exact hxU (he ▸ hzU)
  have hcy : ¬ G.Adj c y := by
    intro hh
    have he : y = z := Finset.card_le_one.mp (hG c b hcb) y
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, hby⟩) z
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcz, hbz⟩)
    exact hyV (he ▸ hzV)
  let input : Fin n → Bool := fun w => decide (w = c ∨ w = x ∨ w = y)
  have hf : fourValue P Q U V input = true := by
    simp only [fourValue, clauseValue, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨c, hcP, by simp [input]⟩, ⟨x, hxQ, by simp [input]⟩⟩,
      ⟨y, hyU, by simp [input]⟩, ⟨x, hxV, by simp [input]⟩⟩
  obtain ⟨u, v, huv, hu, hv⟩ := hclean input hf
  simp only [input, decide_eq_true_eq] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact G.loopless.irrefl _ huv
  · exact hcx huv
  · exact hcy huv
  · exact hcx huv.symm
  · exact G.loopless.irrefl _ huv
  · exact hQ _ hxQ _ hyQ huv
  · exact hcy huv.symm
  · exact hQ _ hyQ _ hxQ huv
  · exact G.loopless.irrefl _ huv

end PEqualNP.Outside.L_meta_1477.FourClauseCover

namespace PEqualNP.Outside.L_meta_1477.FourClauseCover

open PEqualNP.TopForm TwoJunkClauses

lemma no_both_cover_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hnone : ¬ ∃ p ∈ P, p ∈ U ∧ p ∈ V) (hbad : ¬ Obstruction P Q U V) :
    ∃ T : Finset (Fin n), T.card ≤ 2 ∧
      ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → p ∈ T ∨ q ∈ T := by
  classical
  obtain ⟨T₁, h₁, hc₁⟩ := rectangle_cover_one G hG (P.filter (· ∈ U)) (Q.filter (· ∈ V)) (by
    intro p hp q hq
    exact hcross p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
      (Or.inl (Finset.mem_filter.mp hp).2) (Or.inr (Finset.mem_filter.mp hq).2))
  obtain ⟨T₂, h₂, hc₂⟩ := rectangle_cover_one G hG (P.filter (· ∈ V)) (Q.filter (· ∈ U)) (by
    intro p hp q hq
    exact hcross p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
      (Or.inr (Finset.mem_filter.mp hq).2) (Or.inl (Finset.mem_filter.mp hp).2))
  obtain ⟨T₃, h₃, hc₃⟩ := rectangle_cover_one G hG P (Q.filter (fun q => q ∈ U ∧ q ∈ V)) (by
    intro p hp q hq
    exact hcross p hp q (Finset.mem_filter.mp hq).1
      (Or.inr (Finset.mem_filter.mp hq).2.1) (Or.inr (Finset.mem_filter.mp hq).2.2))
  have hfirst (p) (hp : p ∈ P) (q) (hq : q ∈ Q) (hpU : p ∈ U) (hqV : q ∈ V) :
      p ∈ T₁ ∨ q ∈ T₁ := hc₁ p (Finset.mem_filter.mpr ⟨hp, hpU⟩) q (Finset.mem_filter.mpr ⟨hq, hqV⟩)
  have hsecond (p) (hp : p ∈ P) (q) (hq : q ∈ Q) (hpV : p ∈ V) (hqU : q ∈ U) :
      p ∈ T₂ ∨ q ∈ T₂ := hc₂ p (Finset.mem_filter.mpr ⟨hp, hpV⟩) q (Finset.mem_filter.mpr ⟨hq, hqU⟩)
  have hthird (p) (hp : p ∈ P) (q) (hq : q ∈ Q) (hqU : q ∈ U) (hqV : q ∈ V) :
      p ∈ T₃ ∨ q ∈ T₃ := hc₃ p hp q (Finset.mem_filter.mpr ⟨hq, hqU, hqV⟩)
  have h12 : (T₁ ∪ T₂).card ≤ 2 := by have h := Finset.card_union_le T₁ T₂; omega
  have h13 : (T₁ ∪ T₃).card ≤ 2 := by have h := Finset.card_union_le T₁ T₃; omega
  have h23 : (T₂ ∪ T₃).card ≤ 2 := by have h := Finset.card_union_le T₂ T₃; omega
  by_cases hB : (P.filter (fun p => p ∈ U ∧ p ∉ V)).Nonempty
  swap
  · refine ⟨T₂ ∪ T₃, h23, ?_⟩
    intro p hp q hq hU hV
    have hpU : p ∉ U := by
      intro hu
      have hv : p ∉ V := fun hv => hnone ⟨p, hp, hu, hv⟩
      exact hB ⟨p, Finset.mem_filter.mpr ⟨hp, hu, hv⟩⟩
    have hqU := hU.resolve_left hpU
    by_cases hpV : p ∈ V
    · exact (hsecond p hp q hq hpV hqU).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
    · exact (hthird p hp q hq hqU (hV.resolve_left hpV)).imp
        (Finset.mem_union_right _) (Finset.mem_union_right _)
  by_cases hC : (P.filter (fun p => p ∈ V ∧ p ∉ U)).Nonempty
  swap
  · refine ⟨T₁ ∪ T₃, h13, ?_⟩
    intro p hp q hq hU hV
    have hpV : p ∉ V := by
      intro hv
      have hu : p ∉ U := fun hu => hnone ⟨p, hp, hu, hv⟩
      exact hC ⟨p, Finset.mem_filter.mpr ⟨hp, hv, hu⟩⟩
    have hqV := hV.resolve_left hpV
    by_cases hpU : p ∈ U
    · exact (hfirst p hp q hq hpU hqV).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
    · exact (hthird p hp q hq (hU.resolve_left hpU) hqV).imp
        (Finset.mem_union_right _) (Finset.mem_union_right _)
  by_cases hD : (P.filter (fun p => p ∉ U ∧ p ∉ V)).Nonempty
  swap
  · refine ⟨T₁ ∪ T₂, h12, ?_⟩
    intro p hp q hq hU hV
    by_cases hpU : p ∈ U
    · have hpV : p ∉ V := fun hv => hnone ⟨p, hp, hpU, hv⟩
      exact (hfirst p hp q hq hpU (hV.resolve_left hpV)).imp
        (Finset.mem_union_left _) (Finset.mem_union_left _)
    · have hpV : p ∈ V := by
        by_contra hn
        exact hD ⟨p, Finset.mem_filter.mpr ⟨hp, hpU, hn⟩⟩
      exact (hsecond p hp q hq hpV (hU.resolve_left hpU)).imp
        (Finset.mem_union_right _) (Finset.mem_union_right _)
  by_cases hRU : (Q.filter (fun q => q ∈ U ∧ q ∉ V)).Nonempty
  swap
  · refine ⟨T₁ ∪ T₃, h13, ?_⟩
    intro p hp q hq hU hV
    by_cases hqU : q ∈ U
    · have hqV : q ∈ V := by
        by_contra hn
        exact hRU ⟨q, Finset.mem_filter.mpr ⟨hq, hqU, hn⟩⟩
      exact (hthird p hp q hq hqU hqV).imp (Finset.mem_union_right _) (Finset.mem_union_right _)
    · have hpU := hU.resolve_right hqU
      have hpV : p ∉ V := fun hv => hnone ⟨p, hp, hpU, hv⟩
      exact (hfirst p hp q hq hpU (hV.resolve_left hpV)).imp
        (Finset.mem_union_left _) (Finset.mem_union_left _)
  by_cases hRV : (Q.filter (fun q => q ∈ V ∧ q ∉ U)).Nonempty
  swap
  · refine ⟨T₂ ∪ T₃, h23, ?_⟩
    intro p hp q hq hU hV
    by_cases hqV : q ∈ V
    · have hqU : q ∈ U := by
        by_contra hn
        exact hRV ⟨q, Finset.mem_filter.mpr ⟨hq, hqV, hn⟩⟩
      exact (hthird p hp q hq hqU hqV).imp (Finset.mem_union_right _) (Finset.mem_union_right _)
    · have hpV := hV.resolve_right hqV
      have hpU : p ∉ U := fun hu => hnone ⟨p, hp, hu, hpV⟩
      exact (hsecond p hp q hq hpV (hU.resolve_left hpU)).imp
        (Finset.mem_union_left _) (Finset.mem_union_left _)
  by_cases hRB : (Q.filter (fun q => q ∈ U ∧ q ∈ V)).Nonempty
  · exact (hbad ⟨hB, hC, hD, hRU, hRV, hRB⟩).elim
  · refine ⟨T₁ ∪ T₂, h12, ?_⟩
    intro p hp q hq hU hV
    by_cases hpU : p ∈ U
    · have hpV : p ∉ V := fun hv => hnone ⟨p, hp, hpU, hv⟩
      exact (hfirst p hp q hq hpU (hV.resolve_left hpV)).imp
        (Finset.mem_union_left _) (Finset.mem_union_left _)
    · have hqU := hU.resolve_left hpU
      have hpV : p ∈ V := by
        by_contra hn
        exact hRB ⟨q, Finset.mem_filter.mpr ⟨hq, hqU, hV.resolve_left hn⟩⟩
      exact (hsecond p hp q hq hpV hqU).imp (Finset.mem_union_right _) (Finset.mem_union_right _)

lemma clean_cover_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hP : ∀ p ∈ P, ∀ r ∈ P, ¬ G.Adj p r)
    (hQ : ∀ q ∈ Q, ∀ r ∈ Q, ¬ G.Adj q r)
    (hclean : ∀ x : Fin n → Bool, fourValue P Q U V x = true →
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) :
    ∃ T : Finset (Fin n), T.card ≤ 2 ∧
      ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → p ∈ T ∨ q ∈ T := by
  classical
  have hbad := clean_no_obstruction G hG P Q U V hcross hQ hclean
  by_cases hPB : ∃ p ∈ P, p ∈ U ∧ p ∈ V
  · obtain ⟨p, hp, hpU, hpV⟩ := hPB
    by_cases hQB : ∃ q ∈ Q, q ∈ U ∧ q ∈ V
    · obtain ⟨q, hq, hqU, hqV⟩ := hQB
      obtain ⟨T, hT, _, hc⟩ := MixedShared.common_filter_cover_two G hG P Q U V hcross
        p q hp hq hpU hpV hqU hqV
      exact ⟨T, hT, hc⟩
    · have hcross' : ∀ q ∈ Q, ∀ p ∈ P, (q ∈ U ∨ p ∈ U) → (q ∈ V ∨ p ∈ V) → G.Adj q p :=
        fun q hq p hp hU hV => (hcross p hp q hq hU.symm hV.symm).symm
      have hclean' : ∀ x : Fin n → Bool, fourValue Q P U V x = true →
          ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
        intro x hx
        apply hclean x
        simpa only [fourValue, Bool.and_comm] using hx
      have hbad' := clean_no_obstruction G hG Q P U V hcross' hP hclean'
      obtain ⟨T, hT, hc⟩ := no_both_cover_two G hG Q P U V hcross' hQB hbad'
      exact ⟨T, hT, fun p hp q hq hU hV => (hc q hq p hp hU.symm hV.symm).symm⟩
  · exact no_both_cover_two G hG P Q U V hcross hPB hbad

end PEqualNP.Outside.L_meta_1477.FourClauseCover



namespace PEqualNP.Outside.L_meta_1477.SharedResidualRoots

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk

lemma shared_stop_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (w₀ w₁ : ℕ) (hw₀ : w₀ < n + C.gates.length) (hw₁ : w₁ < n + C.gates.length)
    (a b : Fin n) (R₀ R₁ : Finset (Fin n))
    (hR₀ : ∀ v ∈ R₀, G.Adj a v) (hR₁ : ∀ v ∈ R₁, G.Adj b v)
    (hcommon : ∀ k < C.gates.length, P2.OrR n C w₀ (n + k) → P2.OrR n C w₁ (n + k) →
      (orIn n C (n + k) ∩ R₀).card ≤ 1 ∧ (orIn n C (n + k) ∩ R₁).card ≤ 1) :
    (((orIn n C w₀ ∩ R₀).image (fun v => s(a, v))) \ starEdges G C).card +
      (((orIn n C w₁ ∩ R₁).image (fun v => s(b, v))) \ starEdges G C).card ≤
        (orN G C \ lam G C).card + 2 := by
  classical
  let Z := (Finset.range C.gates.length).filter (fun k =>
    P2.OrR n C w₀ (n + k) ∧ P2.OrR n C w₁ (n + k))
  have hZ₀ : ∀ k ∈ Z,
      (∀ v ∈ orIn n C (n + k) ∩ R₀, s(a, v) ∈ starEdges G C) ∨
        (orIn n C (n + k) ∩ R₀).card ≤ 1 := by
    intro k hk
    obtain ⟨hk, hr₀, hr₁⟩ := Finset.mem_filter.mp hk
    exact Or.inr (hcommon k (Finset.mem_range.mp hk) hr₀ hr₁).1
  have hZ₁ : ∀ k ∈ Z,
      (∀ v ∈ orIn n C (n + k) ∩ R₁, s(b, v) ∈ starEdges G C) ∨
        (orIn n C (n + k) ∩ R₁).card ≤ 1 := by
    intro k hk
    obtain ⟨hk, hr₀, hr₁⟩ := Finset.mem_filter.mp hk
    exact Or.inr (hcommon k (Finset.mem_range.mp hk) hr₀ hr₁).2
  obtain ⟨B₀, hB₀, hd₀, hf₀, hc₀⟩ := ResidualRootCone.root_cone G hG C hL w₀ hw₀ a R₀ hR₀ Z hZ₀
  obtain ⟨B₁, hB₁, hd₁, hf₁, hc₁⟩ := ResidualRootCone.root_cone G hG C hL w₁ hw₁ b R₁ hR₁ Z hZ₁
  have hdis : Disjoint B₀ B₁ := Finset.disjoint_left.mpr (by
    intro k hk₀ hk₁
    have hkN := (Finset.mem_sdiff.mp (hB₀ hk₀)).1
    have hklen : k < C.gates.length := by
      simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hkN
      exact hkN.1
    have hkZ : k ∈ Z := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hklen, (hf₀ k hk₀).1, (hf₁ k hk₁).1⟩
    exact Finset.disjoint_left.mp hd₀ hk₀ hkZ)
  have hcard := Finset.card_le_card (Finset.union_subset hB₀ hB₁)
  rw [Finset.card_union_of_disjoint hdis] at hcard
  omega

lemma same_side_spokes_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (wU wV : ℕ) (hwU : wU < n + C.gates.length) (hwV : wV < n + C.gates.length)
    (Q U V : Finset (Fin n)) (hU : orIn n C wU = U) (hV : orIn n C wV = V)
    (a b : Fin n) (hsmall : (Q.filter (fun q => q ∈ U ∧ q ∈ V)).card ≤ 1) :
    (((V ∩ Q.filter (G.Adj a)).image (fun v => s(a, v))) \ starEdges G C).card +
      (((U ∩ Q.filter (G.Adj b)).image (fun v => s(b, v))) \ starEdges G C).card ≤
        (orN G C \ lam G C).card + 2 := by
  have hA := P2.ao_of n C hL.1
  have hbound := shared_stop_count G hG C hL wV wU hwV hwU a b
    (Q.filter (G.Adj a)) (Q.filter (G.Adj b))
    (fun _ h => (Finset.mem_filter.mp h).2) (fun _ h => (Finset.mem_filter.mp h).2) (by
      intro k hk hrV hrU
      have hklen : n + k < n + C.gates.length := by omega
      have hsubU := orIn_subset_of_orR C hA wU (n + k) hwU hklen hrU
      have hsubV := orIn_subset_of_orR C hA wV (n + k) hwV hklen hrV
      rw [hU] at hsubU
      rw [hV] at hsubV
      have hfiltered (c : Fin n) : orIn n C (n + k) ∩ Q.filter (G.Adj c) ⊆
          Q.filter (fun q => q ∈ U ∧ q ∈ V) := by
        intro q hq
        obtain ⟨hq, hQ⟩ := Finset.mem_inter.mp hq
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hQ).1, hsubU hq, hsubV hq⟩
      exact ⟨(Finset.card_le_card (hfiltered a)).trans hsmall,
        (Finset.card_le_card (hfiltered b)).trans hsmall⟩)
  simpa only [hU, hV] using hbound

lemma same_side_ustar_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (wU wV : ℕ) (hwU : wU < n + C.gates.length) (hwV : wV < n + C.gates.length)
    (Q U V : Finset (Fin n)) (hU : orIn n C wU = U) (hV : orIn n C wV = V)
    (a b : Fin n) (hsmall : (Q.filter (fun q => q ∈ U ∧ q ∈ V)).card ≤ 1)
    (hcover : ∀ e ∈ Ustar G C,
      (∃ q ∈ Q, q ∈ V ∧ G.Adj a q ∧ e = s(a, q)) ∨
        (∃ q ∈ Q, q ∈ U ∧ G.Adj b q ∧ e = s(b, q))) :
    (Ustar G C).card ≤ (orN G C \ lam G C).card + 2 := by
  have hbound := same_side_spokes_count G hG C hL wU wV hwU hwV Q U V hU hV a b hsmall
  have hsub : Ustar G C ⊆
      ((V ∩ Q.filter (G.Adj a)).image (fun v => s(a, v)) \ starEdges G C) ∪
        ((U ∩ Q.filter (G.Adj b)).image (fun v => s(b, v)) \ starEdges G C) := by
    intro e he
    have hnot : e ∉ starEdges G C := (Finset.mem_sdiff.mp he).2
    rcases hcover e he with ⟨q, hq, hVq, haq, rfl⟩ | ⟨q, hq, hUq, hbq, rfl⟩
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr
        ⟨q, Finset.mem_inter.mpr ⟨hVq, Finset.mem_filter.mpr ⟨hq, haq⟩⟩, rfl⟩, hnot⟩
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr
        ⟨q, Finset.mem_inter.mpr ⟨hUq, Finset.mem_filter.mpr ⟨hq, hbq⟩⟩, rfl⟩, hnot⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans hbound)

end PEqualNP.Outside.L_meta_1477.SharedResidualRoots



namespace PEqualNP.Outside.L_meta_1477.SharedResidualRoots

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk

lemma same_side_pair_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (wU wV : ℕ) (hwU : wU < n + C.gates.length) (hwV : wV < n + C.gates.length)
    (P Q U V : Finset (Fin n)) (hU : orIn n C wU = U) (hV : orIn n C wV = V)
    (a b : Fin n) (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b) (haV : a ∉ V) (hbU : b ∉ U)
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hcover : ∀ e ∈ Ustar G C, ∃ p ∈ P, ∃ q ∈ Q,
      e = s(p, q) ∧ (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V) ∧ (p = a ∨ p = b)) :
    (Ustar G C).card ≤ (orN G C \ lam G C).card + 2 := by
  have hsmall : (Q.filter (fun q => q ∈ U ∧ q ∈ V)).card ≤ 1 := by
    have hsub : Q.filter (fun q => q ∈ U ∧ q ∈ V) ⊆
        Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
      intro q hq
      obtain ⟨hq, hqU, hqV⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hcross a ha q hq (Or.inr hqU) (Or.inr hqV),
        hcross b hb q hq (Or.inr hqU) (Or.inr hqV)⟩
    exact (Finset.card_le_card hsub).trans (hG a b hne)
  apply same_side_ustar_count G hG C hL wU wV hwU hwV Q U V hU hV a b hsmall
  intro e he
  obtain ⟨p, hp, q, hq, heq, hqU, hqV, hpab⟩ := hcover e he
  rcases hpab with rfl | rfl
  · exact Or.inl ⟨q, hq, hqV.resolve_left haV, hcross _ hp q hq hqU hqV, heq⟩
  · exact Or.inr ⟨q, hq, hqU.resolve_left hbU, hcross _ hp q hq hqU hqV, heq⟩

end PEqualNP.Outside.L_meta_1477.SharedResidualRoots

namespace PEqualNP.Outside.L_meta_1477.TwoCenterSignatures

open PEqualNP.TopForm TwoJunkClauses

lemma heavy_centers_incomparable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (a b : Fin n) (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b)
    (hadegree : 2 ≤ (Q.filter (fun q => (a ∈ U ∨ q ∈ U) ∧ (a ∈ V ∨ q ∈ V))).card)
    (hbdegree : 2 ≤ (Q.filter (fun q => (b ∈ U ∨ q ∈ U) ∧ (b ∈ V ∨ q ∈ V))).card) :
    (a ∈ U ∧ a ∉ V ∧ b ∈ V ∧ b ∉ U) ∨
      (b ∈ U ∧ b ∉ V ∧ a ∈ V ∧ a ∉ U) := by
  classical
  let N : Fin n → Finset (Fin n) := fun p => Q.filter (fun q =>
    (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))
  have hAdj : ∀ p ∈ P, ∀ q ∈ N p, G.Adj p q := by
    intro p hp q hq
    obtain ⟨hq, hU, hV⟩ := Finset.mem_filter.mp hq
    exact hcross p hp q hq hU hV
  have hAB : ¬ ((a ∈ U → b ∈ U) ∧ (a ∈ V → b ∈ V)) := by
    rintro ⟨hU, hV⟩
    have hsub : N a ⊆ N b := by
      intro q hq
      obtain ⟨hq, hqa, hqv⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hq, hqa.imp hU id, hqv.imp hV id⟩
    have hsmall := nested_neighbor_small G hG P N hAdj a b ha hb hne hsub
    change 2 ≤ (N a).card at hadegree
    omega
  have hBA : ¬ ((b ∈ U → a ∈ U) ∧ (b ∈ V → a ∈ V)) := by
    rintro ⟨hU, hV⟩
    have hsub : N b ⊆ N a := by
      intro q hq
      obtain ⟨hq, hqb, hqv⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hq, hqb.imp hU id, hqv.imp hV id⟩
    have hsmall := nested_neighbor_small G hG P N hAdj b a hb ha hne.symm hsub
    change 2 ≤ (N b).card at hbdegree
    omega
  tauto

lemma common_filter_support_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (a b : Fin n) (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b) :
    (Q.filter (fun q => q ∈ U ∧ q ∈ V)).card ≤ 1 := by
  have hsub : Q.filter (fun q => q ∈ U ∧ q ∈ V) ⊆
      Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
    intro q hq
    obtain ⟨hq, hU, hV⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hcross a ha q hq (Or.inr hU) (Or.inr hV),
      hcross b hb q hq (Or.inr hU) (Or.inr hV)⟩
  exact (Finset.card_le_card hsub).trans (hG a b hne)

end PEqualNP.Outside.L_meta_1477.TwoCenterSignatures

namespace PEqualNP.Outside.L_meta_1477.SharedResidualRoots

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk

lemma same_side_heavy_pair_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (wU wV : ℕ) (hwU : wU < n + C.gates.length) (hwV : wV < n + C.gates.length)
    (P Q U V : Finset (Fin n)) (hU : orIn n C wU = U) (hV : orIn n C wV = V)
    (a b : Fin n) (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b)
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hadegree : 2 ≤ (Q.filter (fun q => (a ∈ U ∨ q ∈ U) ∧ (a ∈ V ∨ q ∈ V))).card)
    (hbdegree : 2 ≤ (Q.filter (fun q => (b ∈ U ∨ q ∈ U) ∧ (b ∈ V ∨ q ∈ V))).card)
    (hcover : ∀ e ∈ Ustar G C, ∃ p ∈ P, ∃ q ∈ Q,
      e = s(p, q) ∧ (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V) ∧ (p = a ∨ p = b)) :
    (Ustar G C).card ≤ (orN G C \ lam G C).card + 2 := by
  have hsig := TwoCenterSignatures.heavy_centers_incomparable G hG P Q U V hcross
    a b ha hb hne hadegree hbdegree
  rcases hsig with ⟨_, haV, _, hbU⟩ | ⟨_, hbV, _, haU⟩
  · exact same_side_pair_cover G hG C hL wU wV hwU hwV P Q U V hU hV
      a b ha hb hne haV hbU hcross hcover
  · apply same_side_pair_cover G hG C hL wU wV hwU hwV P Q U V hU hV
      b a hb ha hne.symm hbV haU hcross
    intro e he
    obtain ⟨p, hp, q, hq, heq, hqU, hqV, hpab⟩ := hcover e he
    exact ⟨p, hp, q, hq, heq, hqU, hqV, hpab.symm⟩

end PEqualNP.Outside.L_meta_1477.SharedResidualRoots


namespace PEqualNP.Outside.L_meta_1477.CoverConversion

lemma low_row_to_split {α : Type*} [DecidableEq α]
    (P Q : Finset α) (R : α → α → Prop) [DecidableRel R]
    (a b : α) (hQ : Q.Nonempty)
    (hcover : ∀ x ∈ P, ∀ y ∈ Q, R x y → x = a ∨ x = b)
    (hdegree : (Q.filter (R b)).card ≤ 1) :
    ∃ q ∈ Q, ∀ x ∈ P, ∀ y ∈ Q, R x y → x = a ∨ y = q := by
  classical
  by_cases hne : (Q.filter (R b)).Nonempty
  · obtain ⟨q, hq⟩ := hne
    refine ⟨q, (Finset.mem_filter.mp hq).1, ?_⟩
    intro x hx y hy hxy
    rcases hcover x hx y hy hxy with hxa | hxb
    · exact Or.inl hxa
    · right
      exact (Finset.card_le_one.mp hdegree) y
        (Finset.mem_filter.mpr ⟨hy, hxb ▸ hxy⟩) q hq
  · obtain ⟨q, hq⟩ := hQ
    refine ⟨q, hq, ?_⟩
    intro x hx y hy hxy
    rcases hcover x hx y hy hxy with hxa | hxb
    · exact Or.inl hxa
    · exact False.elim (hne ⟨y, Finset.mem_filter.mpr ⟨hy, hxb ▸ hxy⟩⟩)

lemma row_cover_split_or_heavy {α : Type*} [DecidableEq α]
    (P Q : Finset α) (R : α → α → Prop) [DecidableRel R]
    (a b : α) (ha : a ∈ P) (hb : b ∈ P) (hQ : Q.Nonempty)
    (hcover : ∀ x ∈ P, ∀ y ∈ Q, R x y → x = a ∨ x = b) :
    (∃ p ∈ P, ∃ q ∈ Q, ∀ x ∈ P, ∀ y ∈ Q, R x y → x = p ∨ y = q) ∨
      (2 ≤ (Q.filter (R a)).card ∧ 2 ≤ (Q.filter (R b)).card) := by
  classical
  by_cases ha2 : 2 ≤ (Q.filter (R a)).card
  · by_cases hb2 : 2 ≤ (Q.filter (R b)).card
    · exact Or.inr ⟨ha2, hb2⟩
    · obtain ⟨q, hq, hc⟩ := low_row_to_split P Q R a b hQ hcover (by omega)
      exact Or.inl ⟨a, ha, q, hq, hc⟩
  · obtain ⟨q, hq, hc⟩ := low_row_to_split P Q R b a hQ
      (fun x hx y hy hxy => (hcover x hx y hy hxy).symm) (by omega)
    exact Or.inl ⟨b, hb, q, hq, hc⟩

end PEqualNP.Outside.L_meta_1477.CoverConversion

namespace PEqualNP.Outside.L_meta_1477.CoverLocations

open CoverConversion

def SplitCover {α : Type*} [DecidableEq α] (P Q : Finset α) (R : α → α → Prop) : Prop :=
  ∃ p ∈ P, ∃ q ∈ Q, ∀ x ∈ P, ∀ y ∈ Q, R x y → x = p ∨ y = q

def HeavyRows {α : Type*} [DecidableEq α] (P Q : Finset α)
    (R : α → α → Prop) [DecidableRel R] : Prop :=
  ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧
    2 ≤ (Q.filter (R a)).card ∧ 2 ≤ (Q.filter (R b)).card ∧
    ∀ x ∈ P, ∀ y ∈ Q, R x y → x = a ∨ x = b

lemma row_classify {α : Type*} [DecidableEq α] (P Q : Finset α)
    (R : α → α → Prop) [DecidableRel R] (hQ : Q.Nonempty)
    (a b : α) (ha : a ∈ P) (hb : b ∈ P) (hne : a ≠ b)
    (hc : ∀ x ∈ P, ∀ y ∈ Q, R x y → x = a ∨ x = b) :
    SplitCover P Q R ∨ HeavyRows P Q R := by
  rcases row_cover_split_or_heavy P Q R a b ha hb hQ hc with h | h
  · exact Or.inl h
  · exact Or.inr ⟨a, ha, b, hb, hne, h.1, h.2, hc⟩

lemma split_flip {α : Type*} [DecidableEq α] (P Q : Finset α)
    (R : α → α → Prop) (h : SplitCover Q P (fun y x => R x y)) :
    SplitCover P Q R := by
  obtain ⟨q, hq, p, hp, hc⟩ := h
  exact ⟨p, hp, q, hq, fun x hx y hy hxy => (hc y hy x hx hxy).symm⟩

lemma cover_locations {α : Type*} [DecidableEq α]
    (P Q T : Finset α) (R : α → α → Prop) [DecidableRel R]
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hdis : Disjoint P Q)
    (hcard : T.card ≤ 2)
    (hcover : ∀ x ∈ P, ∀ y ∈ Q, R x y → x ∈ T ∨ y ∈ T) :
    SplitCover P Q R ∨ HeavyRows P Q R ∨ HeavyRows Q P (fun y x => R x y) := by
  classical
  let S := T ∩ (P ∪ Q)
  have hScard : S.card ≤ 2 := (Finset.card_le_card Finset.inter_subset_left).trans hcard
  have hSloc : ∀ a ∈ S, a ∈ P ∨ a ∈ Q := by
    intro a ha
    exact Finset.mem_union.mp (Finset.mem_inter.mp ha).2
  have hc : ∀ x ∈ P, ∀ y ∈ Q, R x y → x ∈ S ∨ y ∈ S := by
    intro x hx y hy hxy
    exact (hcover x hx y hy hxy).imp
      (fun h => Finset.mem_inter.mpr ⟨h, Finset.mem_union_left _ hx⟩)
      (fun h => Finset.mem_inter.mpr ⟨h, Finset.mem_union_right _ hy⟩)
  have hneq : ∀ p ∈ P, ∀ q ∈ Q, p ≠ q := by
    intro p hp q hq he
    exact Finset.disjoint_left.mp hdis hp (he.symm ▸ hq)
  obtain ⟨p, hp⟩ := hP
  obtain ⟨q, hq⟩ := hQ
  by_cases hs : S.card ≤ 1
  · by_cases he : S.Nonempty
    · obtain ⟨a, ha⟩ := he
      have hall : ∀ z ∈ S, z = a := fun z hz => Finset.card_le_one.mp hs z hz a ha
      rcases hSloc a ha with haP | haQ
      · left
        refine ⟨a, haP, q, hq, ?_⟩
        intro x hx y hy hxy
        rcases hc x hx y hy hxy with hxs | hys
        · exact Or.inl (hall x hxs)
        · exact False.elim ((hneq a haP y hy) (hall y hys).symm)
      · left
        refine ⟨p, hp, a, haQ, ?_⟩
        intro x hx y hy hxy
        rcases hc x hx y hy hxy with hxs | hys
        · exact False.elim ((hneq x hx a haQ) (hall x hxs))
        · exact Or.inr (hall y hys)
    · left
      refine ⟨p, hp, q, hq, ?_⟩
      intro x hx y hy hxy
      rcases hc x hx y hy hxy with hxs | hys
      · exact False.elim (he ⟨x, hxs⟩)
      · exact False.elim (he ⟨y, hys⟩)
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have hsub : {a, b} ⊆ S := by
      intro z hz
      rcases Finset.mem_insert.mp hz with h | h
      · exact h ▸ ha
      · exact (Finset.mem_singleton.mp h) ▸ hb
    have heq : ({a, b} : Finset α) = S :=
      Finset.eq_of_subset_of_card_le hsub (by simpa [hab] using hScard)
    have hmem : ∀ z ∈ S, z = a ∨ z = b := by
      intro z hz
      simpa only [← heq, Finset.mem_insert, Finset.mem_singleton] using hz
    rcases hSloc a ha with haP | haQ <;> rcases hSloc b hb with hbP | hbQ
    · have hr : ∀ x ∈ P, ∀ y ∈ Q, R x y → x = a ∨ x = b := by
        intro x hx y hy hxy
        rcases hc x hx y hy hxy with hxs | hys
        · exact hmem x hxs
        · rcases hmem y hys with he | he
          · exact False.elim ((hneq a haP y hy) he.symm)
          · exact False.elim ((hneq b hbP y hy) he.symm)
      exact (row_classify P Q R ⟨q, hq⟩ a b haP hbP hab hr).imp id Or.inl
    · left
      refine ⟨a, haP, b, hbQ, ?_⟩
      intro x hx y hy hxy
      rcases hc x hx y hy hxy with hxs | hys
      · rcases hmem x hxs with he | he
        · exact Or.inl he
        · exact False.elim ((hneq x hx b hbQ) he)
      · rcases hmem y hys with he | he
        · exact False.elim ((hneq a haP y hy) he.symm)
        · exact Or.inr he
    · left
      refine ⟨b, hbP, a, haQ, ?_⟩
      intro x hx y hy hxy
      rcases hc x hx y hy hxy with hxs | hys
      · rcases hmem x hxs with he | he
        · exact False.elim ((hneq x hx a haQ) he)
        · exact Or.inl he
      · rcases hmem y hys with he | he
        · exact Or.inr he
        · exact False.elim ((hneq b hbP y hy) he.symm)
    · have hr : ∀ y ∈ Q, ∀ x ∈ P, R x y → y = a ∨ y = b := by
        intro y hy x hx hxy
        rcases hc x hx y hy hxy with hxs | hys
        · rcases hmem x hxs with he | he
          · exact False.elim ((hneq x hx a haQ) he)
          · exact False.elim ((hneq x hx b hbQ) he)
        · exact hmem y hys
      rcases row_classify Q P (fun y x => R x y) ⟨p, hp⟩ a b haQ hbQ hab hr with h | h
      · exact Or.inl (split_flip P Q R h)
      · exact Or.inr (Or.inr h)

end PEqualNP.Outside.L_meta_1477.CoverLocations


namespace PEqualNP.Outside.L_meta_1477.FourClauseResidual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk TwoJunkClauses

lemma four_clause_ustar_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (wP wQ wU wV : ℕ)
    (hwP : wP < n + C.gates.length) (hwQ : wQ < n + C.gates.length)
    (hwU : wU < n + C.gates.length) (hwV : wV < n + C.gates.length)
    (P Q U V : Finset (Fin n))
    (hrootP : orIn n C wP = P) (hrootQ : orIn n C wQ = Q)
    (hrootU : orIn n C wU = U) (hrootV : orIn n C wV = V)
    (hdis : Disjoint P Q)
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → G.Adj p q)
    (hP : ∀ p ∈ P, ∀ r ∈ P, ¬ G.Adj p r)
    (hQ : ∀ q ∈ Q, ∀ r ∈ Q, ¬ G.Adj q r)
    (hclean : ∀ x : Fin n → Bool, fourValue P Q U V x = true →
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
    (hcover : ∀ e ∈ Ustar G C, ∃ p ∈ P, ∃ q ∈ Q,
      e = s(p, q) ∧ (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V)) :
    (Ustar G C).card ≤ (orN G C \ lam G C).card + 2 := by
  classical
  by_cases hUne : (Ustar G C).Nonempty
  swap
  · have he : Ustar G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUne
    simp [he]
  obtain ⟨e₀, he₀⟩ := hUne
  obtain ⟨p₀, hp₀, q₀, hq₀, _⟩ := hcover e₀ he₀
  have hPn : P.Nonempty := ⟨p₀, hp₀⟩
  have hQn : Q.Nonempty := ⟨q₀, hq₀⟩
  let R : Fin n → Fin n → Prop := fun p q =>
    (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V)
  obtain ⟨T, hT, hcT⟩ := FourClauseCover.clean_cover_two G hG P Q U V hcross hP hQ hclean
  have hloc := CoverLocations.cover_locations P Q T R hPn hQn hdis hT
    (fun p hp q hq hR => hcT p hp q hq hR.1 hR.2)
  rcases hloc with hsplit | hrow | hcol
  · obtain ⟨a, ha, b, hb, hc⟩ := hsplit
    apply ResidualRootCone.split_cover_edges G hG C hL wP wQ hwP hwQ
      (by simpa only [hrootP, hrootQ] using hdis) a b (Ustar G C)
    intro e he
    obtain ⟨p, hp, q, hq, heq, hU, hV⟩ := hcover e he
    refine ⟨(Finset.mem_sdiff.mp he).2, p, ?_, q, ?_, hcross p hp q hq hU hV, heq, hc p hp q hq ⟨hU, hV⟩⟩
    · simpa only [hrootP] using hp
    · simpa only [hrootQ] using hq
  · obtain ⟨a, ha, b, hb, hne, hda, hdb, hc⟩ := hrow
    apply SharedResidualRoots.same_side_heavy_pair_cover G hG C hL wU wV hwU hwV
      P Q U V hrootU hrootV a b ha hb hne hcross hda hdb
    intro e he
    obtain ⟨p, hp, q, hq, heq, hU, hV⟩ := hcover e he
    exact ⟨p, hp, q, hq, heq, hU, hV, hc p hp q hq ⟨hU, hV⟩⟩
  · obtain ⟨a, ha, b, hb, hne, hda, hdb, hc⟩ := hcol
    have hcross' : ∀ q ∈ Q, ∀ p ∈ P, (q ∈ U ∨ p ∈ U) → (q ∈ V ∨ p ∈ V) → G.Adj q p :=
      fun q hq p hp hU hV => (hcross p hp q hq hU.symm hV.symm).symm
    apply SharedResidualRoots.same_side_heavy_pair_cover G hG C hL wU wV hwU hwV
      Q P U V hrootU hrootV a b ha hb hne hcross'
      (by simpa only [R, or_comm] using hda) (by simpa only [R, or_comm] using hdb)
    intro e he
    obtain ⟨p, hp, q, hq, heq, hU, hV⟩ := hcover e he
    exact ⟨q, hq, p, hp, heq.trans Sym2.eq_swap, hU.symm, hV.symm, hc q hq p hp ⟨hU, hV⟩⟩

end PEqualNP.Outside.L_meta_1477.FourClauseResidual


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


namespace PEqualNP.Outside.L_meta_1477.PlaneFourClause

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk TwoJunkClauses

lemma exists_min_cover {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ K : Finset (Fin n), IsMinCover G K := by
  classical
  have hex : ∃ m : ℕ, ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧ K.card = m := by
    refine ⟨n, Finset.univ, ?_, by simp⟩
    intro u v _
    exact Or.inl (Finset.mem_univ u)
  obtain ⟨K, hK, hcard⟩ := Nat.find_spec hex
  refine ⟨K, hK, ?_⟩
  intro S hS
  rw [hcard]
  exact Nat.find_min' hex ⟨S, hS, rfl⟩

lemma accounting_with_residual_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    (hne : G.edgeFinset.Nonempty) (tau d : ℕ)
    (hmin : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) → tau ≤ K.card)
    (T : Finset (Fin n)) (hT : ∀ e ∈ Ustar G C, ∃ v ∈ T, v ∈ e)
    (hres : (Ustar G C).card ≤ (orN G C \ lam G C).card + d) :
    G.edgeFinset.card + tau + 2 * (centreless G C).card + (junk G C).card ≤
      C.size + T.card + d + 1 := by
  classical
  have hbase := P1.main n G C hG hne hL hTF
  obtain ⟨K, hK⟩ := exists_min_cover (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n))))
  have hKtop := hbase.2 K hK
  have hwhole : G.IsVertexCover ((K ∪ T : Finset (Fin n)) : Set (Fin n)) := by
    intro u v huv
    by_cases he : s(u, v) ∈ Ustar G C
    · obtain ⟨w, hw, hwe⟩ := hT s(u, v) he
      rcases Sym2.mem_iff.mp hwe with rfl | rfl
      · exact Or.inl (Finset.mem_union_right _ hw)
      · exact Or.inr (Finset.mem_union_right _ hw)
    · have hd : (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj u v := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨huv, he⟩
      rcases hK.1 hd with hu | hv
      · exact Or.inl (Finset.mem_union_left _ hu)
      · exact Or.inr (Finset.mem_union_left _ hv)
  have hwholeBound := hmin (K ∪ T) hwhole
  have hsumBound := Finset.card_union_le K T
  have hcount := hbase.1
  omega

lemma plane_noFourCycle [DecidableRel planeGraph.Adj] : NoFourCycle planeGraph := by
  intro a b hab
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨_, hau, hbu⟩ := Finset.mem_filter.mp hu
  obtain ⟨_, hav, hbv⟩ := Finset.mem_filter.mp hv
  by_contra huv
  exact planeGraph_no_four_cycle a u b v hab huv ⟨hau, hbu.symm, hbv, hav.symm⟩

lemma four_clause_coverage_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hTF : TopForm planeGraph C)
    (wP wQ wU wV : ℕ)
    (hwP : wP < 42 + C.gates.length) (hwQ : wQ < 42 + C.gates.length)
    (hwU : wU < 42 + C.gates.length) (hwV : wV < 42 + C.gates.length)
    (P Q U V : Finset (Fin 42))
    (hrootP : orIn 42 C wP = P) (hrootQ : orIn 42 C wQ = Q)
    (hrootU : orIn 42 C wU = U) (hrootV : orIn 42 C wV = V)
    (hdis : Disjoint P Q)
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, (p ∈ U ∨ q ∈ U) → (p ∈ V ∨ q ∈ V) → planeGraph.Adj p q)
    (hP : ∀ p ∈ P, ∀ r ∈ P, ¬ planeGraph.Adj p r)
    (hQ : ∀ q ∈ Q, ∀ r ∈ Q, ¬ planeGraph.Adj q r)
    (hclean : ∀ x : Fin 42 → Bool, fourValue P Q U V x = true →
      ∃ a b, planeGraph.Adj a b ∧ x a = true ∧ x b = true)
    (hcover : ∀ e ∈ Ustar planeGraph C, ∃ p ∈ P, ∃ q ∈ Q,
      e = s(p, q) ∧ (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V))
    (hjunk : 2 ≤ (junk planeGraph C).card)
    (hcentre : 1 ≤ (centreless planeGraph C).card) : 125 ≤ C.size := by
  classical
  have hG := plane_noFourCycle
  have hres := FourClauseResidual.four_clause_ustar_bound planeGraph hG C hL
    wP wQ wU wV hwP hwQ hwU hwV P Q U V hrootP hrootQ hrootU hrootV hdis
    hcross hP hQ hclean hcover
  obtain ⟨T, hTcard, hTc⟩ := FourClauseCover.clean_cover_two planeGraph hG P Q U V hcross hP hQ hclean
  have hTU : ∀ e ∈ Ustar planeGraph C, ∃ v ∈ T, v ∈ e := by
    intro e he
    obtain ⟨p, hp, q, hq, rfl, hU, hV⟩ := hcover e he
    rcases hTc p hp q hq hU hV with hpT | hqT
    · exact ⟨p, hpT, by simp⟩
    · exact ⟨q, hqT, by simp⟩
  have hEcard : planeGraph.edgeFinset.card = 105 := planeGraph_card
  have hEne : planeGraph.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  have hcount := accounting_with_residual_cover planeGraph hG C hL hTF hEne 21 2
    (fun K hK => planeGraph_cover_lower K (fun u v huv => hK huv)) T hTU hres
  omega

end PEqualNP.Outside.L_meta_1477.PlaneFourClause


namespace PEqualNP.Outside.L_meta_1477.AutomaticFourClauses

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk TwoJunkClauses

def ClausesTrue {n : ℕ} (clauses : Fin 4 → Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  ∀ i, ∃ v ∈ clauses i, x v = true

lemma four_indices : ∀ i j : Fin 4, i ≠ j →
    ∃ k l : Fin 4, ∀ r : Fin 4, r = i ∨ r = j ∨ r = k ∨ r = l := by decide

lemma select_pure_four {n : ℕ} (G : SimpleGraph (Fin n))
    (L : Finset (Fin n)) (clauses : Fin 4 → Finset (Fin n))
    (hL : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v)
    (hR : ∀ u ∉ L, ∀ v ∉ L, ¬ G.Adj u v)
    (hne : ∀ i, (clauses i).Nonempty)
    (hclean : ∀ x : Fin n → Bool, ClausesTrue clauses x →
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) :
    ∃ i j k l : Fin 4, Disjoint (clauses i) (clauses j) ∧
      (∀ u ∈ clauses i, ∀ v ∈ clauses i, ¬ G.Adj u v) ∧
      (∀ u ∈ clauses j, ∀ v ∈ clauses j, ¬ G.Adj u v) ∧
      (∀ x, fourValue (clauses i) (clauses j) (clauses k) (clauses l) x = true ↔
        ClausesTrue clauses x) := by
  classical
  obtain ⟨i, j, hij, hiL, hjL⟩ := bipartite_pure_clauses G L clauses hL hR hne hclean
  obtain ⟨k, l, hidx⟩ := four_indices i j hij
  refine ⟨i, j, k, l, ?_, ?_, ?_, ?_⟩
  · exact Finset.disjoint_left.mpr (fun u hui huj => Finset.disjoint_left.mp hjL huj (hiL hui))
  · exact fun u hu v hv => hL u (hiL hu) v (hiL hv)
  · intro u hu v hv
    exact hR u (fun h => Finset.disjoint_left.mp hjL hu h)
      v (fun h => Finset.disjoint_left.mp hjL hv h)
  · intro x
    simp only [fourValue, clauseValue, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro hx r
      rcases hidx r with hr | hr | hr | hr
      · simpa only [hr] using hx.1.1
      · simpa only [hr] using hx.1.2
      · simpa only [hr] using hx.2.1
      · simpa only [hr] using hx.2.2
    · intro hx
      exact ⟨⟨hx i, hx j⟩, hx k, hx l⟩

lemma graph_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (∃ a b, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true) ↔ G.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro h
    exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

lemma accepted_pair_order {n : ℕ} (P Q U V : Finset (Fin n)) (hdis : Disjoint P Q)
    (u v : Fin n) (hf : fourValue P Q U V (pairInput u v) = true) :
    ∃ p ∈ P, ∃ q ∈ Q, s(u, v) = s(p, q) ∧ (p ∈ U ∨ q ∈ U) ∧ (p ∈ V ∨ q ∈ V) := by
  have hE : edgeValue P Q U V (pairInput u v) = true := (edgeValue_pair_eq_fourValue P Q U V hdis u v).trans hf
  obtain ⟨⟨p, q⟩, he, hpv, hqv⟩ := of_decide_eq_true hE
  obtain ⟨hpq, hU, hV⟩ := Finset.mem_filter.mp he
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
  have hne : p ≠ q := fun he => Finset.disjoint_left.mp hdis hp (he ▸ hq)
  refine ⟨p, hp, q, hq, ?_, hU, hV⟩
  simp only [pairInput, decide_eq_true_eq] at hpv hqv
  rcases hpv with rfl | rfl <;> rcases hqv with rfl | rfl
  · exact (hne rfl).elim
  · rfl
  · exact Sym2.eq_swap
  · exact (hne rfl).elim

lemma indexed_four_clause_account {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hLeast : IsLeastAO G C)
    (roots : Fin 4 → ℕ) (hroots : ∀ i, roots i < n + C.gates.length)
    (clauses : Fin 4 → Finset (Fin n)) (hclauses : ∀ i, orIn n C (roots i) = clauses i)
    (L : Finset (Fin n))
    (hL : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v)
    (hR : ∀ u ∉ L, ∀ v ∉ L, ¬ G.Adj u v)
    (hclean : ∀ x : Fin n → Bool, ClausesTrue clauses x →
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
    (hcover : ∀ e ∈ Ustar G C, ∃ u v : Fin n, e = s(u, v) ∧ ClausesTrue clauses (pairInput u v)) :
    (Ustar G C).card ≤ (orN G C \ lam G C).card + 2 ∧
      ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ∀ e ∈ Ustar G C, ∃ v ∈ T, v ∈ e := by
  classical
  by_cases hUne : (Ustar G C).Nonempty
  swap
  · have he : Ustar G C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUne
    exact ⟨by simp [he], ∅, by simp, by simp [he]⟩
  obtain ⟨e₀, he₀⟩ := hUne
  obtain ⟨u₀, v₀, _, h₀⟩ := hcover e₀ he₀
  have hnonempty : ∀ i, (clauses i).Nonempty := by
    intro i
    obtain ⟨v, hv, _⟩ := h₀ i
    exact ⟨v, hv⟩
  obtain ⟨i, j, k, l, hdis, hPi, hQj, heq⟩ := select_pure_four G L clauses hL hR hnonempty hclean
  have hclean4 : ∀ x : Fin n → Bool,
      fourValue (clauses i) (clauses j) (clauses k) (clauses l) x = true →
        ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true :=
    fun x hx => hclean x ((heq x).mp hx)
  have hcross : ∀ p ∈ clauses i, ∀ q ∈ clauses j,
      (p ∈ clauses k ∨ q ∈ clauses k) → (p ∈ clauses l ∨ q ∈ clauses l) → G.Adj p q := by
    intro p hp q hq hU hV
    apply (graph_pair_iff G p q).mp
    apply hclean4 (pairInput p q)
    apply Bool.le_iff_imp.mp (edgeValue_le_fourValue (clauses i) (clauses j) (clauses k) (clauses l) (pairInput p q))
    simp only [edgeValue, decide_eq_true_eq]
    exact ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hU, hV⟩,
      by simp [pairInput], by simp [pairInput]⟩
  have hcover4 : ∀ e ∈ Ustar G C, ∃ p ∈ clauses i, ∃ q ∈ clauses j,
      e = s(p, q) ∧ (p ∈ clauses k ∨ q ∈ clauses k) ∧ (p ∈ clauses l ∨ q ∈ clauses l) := by
    intro e he
    obtain ⟨u, v, heqv, hv⟩ := hcover e he
    obtain ⟨p, hp, q, hq, hpq, hU, hV⟩ := accepted_pair_order
      (clauses i) (clauses j) (clauses k) (clauses l) hdis u v ((heq _).mpr hv)
    exact ⟨p, hp, q, hq, heqv.trans hpq, hU, hV⟩
  have hres := FourClauseResidual.four_clause_ustar_bound G hG C hLeast
    (roots i) (roots j) (roots k) (roots l) (hroots i) (hroots j) (hroots k) (hroots l)
    (clauses i) (clauses j) (clauses k) (clauses l)
    (hclauses i) (hclauses j) (hclauses k) (hclauses l) hdis hcross hPi hQj hclean4 hcover4
  obtain ⟨T, hT, hcT⟩ := FourClauseCover.clean_cover_two G hG
    (clauses i) (clauses j) (clauses k) (clauses l) hcross hPi hQj hclean4
  refine ⟨hres, T, hT, ?_⟩
  intro e he
  obtain ⟨p, hp, q, hq, rfl, hU, hV⟩ := hcover4 e he
  rcases hcT p hp q hq hU hV with hpT | hqT
  · exact ⟨p, hpT, by simp⟩
  · exact ⟨q, hqT, by simp⟩

end PEqualNP.Outside.L_meta_1477.AutomaticFourClauses

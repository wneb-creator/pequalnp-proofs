import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3678_aux.FlatBasic
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

end PEqualNP.Outside.L_meta_3678_aux.FlatBasic

namespace PEqualNP.Outside.L_meta_3678_aux.Minimal
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

theorem main_abs (n : ℕ) (C : Circuit) (hL : Least n C)
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

end PEqualNP.Outside.L_meta_3678_aux.Minimal

namespace PEqualNP.Outside.L_meta_3678_aux.Flat

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open FlatBasic

def IsFlat (n : ℕ) (C : Circuit) : Prop :=
  ∀ i < C.gates.length, ∀ j < C.gates.length,
    (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and → ¬ InCone n C i j

def andGates (C : Circuit) : Finset ℕ :=
  letI := gateOpDecEq
  (Finset.range C.gates.length).filter fun j => (gateAt C j).op = GateOp.and

lemma ao2_gate {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {k : ℕ}
    (hk : k < C.gates.length) :
    ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      ∃ a b, (gateAt C k).inputs = [a,b] ∧ a < n + k ∧ b < n + k := by
  exact Minimal.AO_of_IsAO2 n C hC k hk

lemma ao2_true {n : ℕ} {C : Circuit} (hC : IsAO2 n C) :
    ∀ w < n + C.gates.length, val C (List.ofFn (fun _ : Fin n => true)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · exact val_ofFn C (fun _ : Fin n => true) ⟨w,hwn⟩
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w-n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hin, ha, hb⟩ := ao2_gate hC hk
      have hva := ih a ha (by omega)
      have hvb := ih b hb (by omega)
      rcases hop with hop | hop
      · apply (val_and (n := n) (by simp) hk hop).mpr
        intro u hu
        rw [hin] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact ⟨ha, hva⟩
        · exact ⟨hb, hvb⟩
      · exact (val_or (n := n) (by simp) hk hop).mpr ⟨a, by simp [hin], ha, hva⟩

lemma operand_value {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (hflat : IsFlat n C)
    {a p : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hin : p ∈ (gateAt C a).inputs) (x : Fin n → Bool) :
    val C (List.ofFn x) p = true ↔ ∃ u ∈ orIn n C p, x u = true := by
  have hp : p < n+a := hC.2.1 a ha p hin
  constructor
  · intro hv
    obtain ⟨w, hr, hw, ht⟩ := or_trace (n := n) (by simp) p hv
    rcases ht with hwn | ⟨j, hj, rfl, hnot⟩
    · refine ⟨⟨w,hwn⟩, reach_mem_orIn _ hr, ?_⟩
      exact (val_ofFn C x ⟨w,hwn⟩).symm.trans hw
    · have hjop : (gateAt C j).op = GateOp.and := (ao2_gate hC hj).1.resolve_right hnot
      exact (hflat j hj a ha hjop hop (operand_cone ha hin hp hr)).elim
  · rintro ⟨u, hu, hx⟩
    exact reach_var_val x p u (mem_orIn_reach u hu) hx

lemma operand_nonempty {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (hflat : IsFlat n C)
    {a p : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hin : p ∈ (gateAt C a).inputs) : (orIn n C p).Nonempty := by
  have hp : p < n+a := hC.2.1 a ha p hin
  obtain ⟨u, hu, _⟩ := (operand_value hC hflat ha hop hin (fun _ => true)).mp
    (ao2_true hC p (by omega))
  exact ⟨u,hu⟩

lemma and_value {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (hflat : IsFlat n C)
    {a : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      ∃ u ∈ side (n := n) C a 0, ∃ v ∈ side (n := n) C a 1,
        x u = true ∧ x v = true := by
  obtain ⟨_, p, q, hin, hp, hq⟩ := ao2_gate hC ha
  have hpin : p ∈ (gateAt C a).inputs := by simp [hin]
  have hqin : q ∈ (gateAt C a).inputs := by simp [hin]
  have e0 : side (n := n) C a 0 = orIn n C p := by simp [side, opnd, hin]
  have e1 : side (n := n) C a 1 = orIn n C q := by simp [side, opnd, hin]
  rw [gateVal_eq_val, e0, e1, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    obtain ⟨u, hu, hx⟩ := (operand_value hC hflat ha hop hpin x).mp (h p hpin).2
    obtain ⟨v, hv, hy⟩ := (operand_value hC hflat ha hop hqin x).mp (h q hqin).2
    exact ⟨u,hu,v,hv,hx,hy⟩
  · rintro ⟨u,hu,v,hv,hx,hy⟩ w hw
    rw [hin] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨hp, (operand_value hC hflat ha hop hpin x).mpr ⟨u,hu,hx⟩⟩
    · exact ⟨hq, (operand_value hC hflat ha hop hqin x).mpr ⟨v,hv,hy⟩⟩

lemma least_abs {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) : Minimal.Least n C := by
  refine ⟨Minimal.AO_of_IsAO2 n C hL.1, ?_⟩
  intro D hD hfun
  exact hL.2.2 D (Minimal.IsAO2_of_AO n D hD) ((funext hfun).trans hL.2.1)

lemma graph_out {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) :
    ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
  congrFun hL.2.1

lemma least_output {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v) :
    n ≤ C.output ∧ C.output + 1 = n + C.gates.length := by
  apply Minimal.least_out n C (least_abs hL)
  · obtain ⟨u,v,huv⟩ := hne
    refine ⟨pairInput u v, ?_⟩
    exact (graph_out hL _).trans ((graphFun_pair G u v).mpr huv)
  · intro u
    refine ⟨pairInput u u, pairInput_left u u, ?_⟩
    change val C (List.ofFn (pairInput u u)) C.output = false
    rw [graph_out hL]
    cases h : graphFun G ∅ (pairInput u u)
    · rfl
    · exact (G.irrefl ((graphFun_pair G u u).mp h)).elim

lemma and_reaches_output {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (hflat : IsFlat n C) {i : ℕ} (hi : i < C.gates.length)
    (hiop : (gateAt C i).op = GateOp.and) :
    Relation.ReflTransGen (OrStep n C) C.output (n+i) := by
  have hout := (least_output hL hne).2
  have go : ∀ d j, j < C.gates.length → (j = i ∨ InCone n C i j) →
      C.gates.length - 1 - j = d →
      Relation.ReflTransGen (OrStep n C) C.output (n+j) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hj hconn hd
      by_cases hlast : j+1 = C.gates.length
      · have ho : C.output = n+j := by omega
        rw [ho]
      · obtain ⟨k,hjk,hk,hread⟩ := Minimal.least_read n C (least_abs hL) hout j (by omega)
        have hik : InCone n C i k := by
          rw [inCone_iff]
          exact ⟨hk,j,hjk,hread,by simpa [eq_comm] using hconn⟩
        have hkop : (gateAt C k).op = GateOp.or :=
          (ao2_gate hL.1 hk).1.resolve_left (fun h => hflat i hi k hk hiop h hik)
        have hkr := ih (C.gates.length-1-k) (by omega) k hk (Or.inr hik) rfl
        exact hkr.tail ⟨k,hk,rfl,hkop,hread,by omega⟩
  exact go (C.gates.length-1-i) i hi (Or.inl rfl) rfl

lemma and_below {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (hflat : IsFlat n C) {i : ℕ} (hi : i < C.gates.length)
    (hiop : (gateAt C i).op = GateOp.and) : BelowF G C i := by
  intro x hx
  exact below_of_reach (graphFun G ∅) (graph_out hL) i
    (and_reaches_output hL hne hflat hi hiop) x hx

lemma and_sides_nonempty {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (hflat : IsFlat n C)
    {a : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and) :
    (side (n := n) C a 0).Nonempty ∧ (side (n := n) C a 1).Nonempty := by
  obtain ⟨_,p,q,hin,_,_⟩ := ao2_gate hC ha
  have e0 : side (n := n) C a 0 = orIn n C p := by simp [side,opnd,hin]
  have e1 : side (n := n) C a 1 = orIn n C q := by simp [side,opnd,hin]
  rw [e0,e1]
  exact ⟨operand_nonempty hC hflat ha hop (by simp [hin]),
    operand_nonempty hC hflat ha hop (by simp [hin])⟩

lemma and_sides_adj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (hflat : IsFlat n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) :
    ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
  intro u hu v hv
  apply (graphFun_pair G u v).mp
  apply and_below hL hne hflat ha hop
  exact (and_value hL.1 hflat ha hop _).mpr
    ⟨u,hu,v,hv,pairInput_left u v,pairInput_right u v⟩

lemma and_sides_colors {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (hflat : IsFlat n C) (s : Fin n → Bool)
    (hcolor : ∀ u v, G.Adj u v → s u ≠ s v)
    {a : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and) :
    ∃ b : Fin 2,
      (∀ u ∈ side (n := n) C a b, s u = false) ∧
      (∀ v ∈ side (n := n) C a (1-b), s v = true) := by
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := and_sides_nonempty hL.1 hflat ha hop
  have hadj := and_sides_adj hL hne hflat ha hop
  have hdiff := hcolor u v (hadj u hu v hv)
  have hs0 : ∀ u' ∈ side (n := n) C a 0, s u' = s u := by
    intro u' hu'
    have h := hcolor u' v (hadj u' hu' v hv)
    cases hsu : s u <;> cases hsv : s v <;> cases hsu' : s u' <;> simp_all
  have hs1 : ∀ v' ∈ side (n := n) C a 1, s v' = !(s u) := by
    intro v' hv'
    have h := hcolor u v' (hadj u hu v' hv')
    cases hsu : s u <;> cases hsv' : s v' <;> simp_all
  cases hsu : s u
  · refine ⟨0, ?_, ?_⟩
    · simpa [hsu] using hs0
    · simpa [hsu] using hs1
  · refine ⟨1, ?_, ?_⟩
    · simpa [hsu] using hs1
    · simpa [hsu] using hs0

lemma bel_iff_below {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (j : ℕ) :
    Minimal.Bel n C j ↔ BelowF G C j := by
  constructor
  · intro h x hx
    exact (graph_out hL x).symm.trans (h x hx)
  · intro h x hx
    exact (graph_out hL x).trans (h x hx)

lemma graph_nonconstant {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v) :
    (∃ x : Fin n → Bool, C.eval (List.ofFn x) = true) ∧
    (∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false) := by
  constructor
  · obtain ⟨u,v,huv⟩ := hne
    exact ⟨pairInput u v, (graph_out hL _).trans ((graphFun_pair G u v).mpr huv)⟩
  · intro u
    refine ⟨pairInput u u, pairInput_left u u, ?_⟩
    change val C (List.ofFn (pairInput u u)) C.output = false
    rw [graph_out hL]
    cases h : graphFun G ∅ (pairInput u u)
    · rfl
    · exact (G.irrefl ((graphFun_pair G u u).mp h)).elim

lemma output_or_count {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (hflat : IsFlat n C) :
    (orT G C).card + 1 =
      (andGates C).card := by
  classical
  have hc := graph_nonconstant hL hne
  have hmain := Minimal.main_abs n C (least_abs hL) hc.1 hc.2 (InCone n C)
    (by
      intro i k hk hin
      rw [inCone_iff]
      have hi := hL.1.2.1 k hk (n+i) hin
      exact ⟨hk,i,by omega,hin,Or.inl rfl⟩)
    (by
      intro t i k hk hti hin
      rw [inCone_iff]
      have hi := hL.1.2.1 k hk (n+i) hin
      exact ⟨hk,i,by omega,hin,Or.inr hti⟩)
    (by intro t j ht hj hop _ hjop; exact hflat t ht j hj hop hjop)
  apply hmain.2.2
  · intro k
    simp only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range]
    rw [bel_iff_below hL]
  · intro k
    simp only [andGates, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hk
      exact ⟨hk.1,hk.2,(bel_iff_below hL k).mpr (and_below hL hne hflat hk.1 hk.2)⟩
    · rintro ⟨hk,hop,_⟩
      exact ⟨hk,hop⟩

lemma orIn_of_reach {n : ℕ} {C : Circuit} {p w : ℕ}
    (hr : Relation.ReflTransGen (OrStep n C) p w) :
    orIn n C w ⊆ orIn n C p := by
  intro u hu
  exact reach_mem_orIn u (hr.trans (mem_orIn_reach u hu))

lemma orN_reaches_and {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    {j : ℕ} (hj : j < C.gates.length) (hjnot : ¬ BelowF G C j) :
    ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧
      ∃ b : Fin 2, Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+j) := by
  have hout := (least_output hL hne).2
  have go : ∀ d j, j < C.gates.length → ¬ BelowF G C j →
      C.gates.length - 1 - j = d →
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧
        ∃ b : Fin 2, Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+j) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j hj hjnot hd
      have hlast : j+1 < C.gates.length := by
        by_contra h
        have ho : C.output = n+j := by omega
        apply hjnot
        intro x hx
        exact (graph_out hL x).symm.trans (by simpa [ho, gateVal_eq_val] using hx)
      obtain ⟨k,hjk,hk,hread⟩ := Minimal.least_read n C (least_abs hL) hout j hlast
      obtain ⟨hkop,p,q,hin,hp,hq⟩ := ao2_gate hL.1 hk
      rcases hkop with hkop | hkop
      · refine ⟨k,hk,hkop,?_⟩
        rw [hin] at hread
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hread
        rcases hread with hread | hread
        · refine ⟨0,?_⟩
          have he : opnd C k 0 = n+j := by simp [opnd,hin,← hread]
          rw [he]
        · refine ⟨1,?_⟩
          have he : opnd C k 1 = n+j := by simp [opnd,hin,← hread]
          rw [he]
      · have hknot : ¬ BelowF G C k := by
          intro hb
          apply hjnot
          intro x hx
          apply hb x
          exact (val_or (n := n) (by simp) hk hkop).mpr ⟨n+j,hread,by omega,hx⟩
        obtain ⟨a,ha,haop,b,hpath⟩ := ih (C.gates.length-1-k) (by omega) k hk hknot rfl
        exact ⟨a,ha,haop,b,hpath.tail ⟨k,hk,rfl,hkop,hread,by omega⟩⟩
  exact go (C.gates.length-1-j) j hj hjnot rfl

lemma descendant_value {n : ℕ} {C : Circuit} (hC : IsAO2 n C) (hflat : IsFlat n C)
    {a p w : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hin : p ∈ (gateAt C a).inputs)
    (hr : Relation.ReflTransGen (OrStep n C) p w) (x : Fin n → Bool) :
    val C (List.ofFn x) w = true ↔ ∃ u ∈ orIn n C w, x u = true := by
  have hp : p < n+a := hC.2.1 a ha p hin
  constructor
  · intro hv
    obtain ⟨w',hr',hw',ht⟩ := or_trace (n := n) (by simp) w hv
    rcases ht with hwn | ⟨j,hj,rfl,hnot⟩
    · exact ⟨⟨w',hwn⟩,reach_mem_orIn _ hr',(val_ofFn C x ⟨w',hwn⟩).symm.trans hw'⟩
    · have hjop : (gateAt C j).op = GateOp.and := (ao2_gate hC hj).1.resolve_right hnot
      exact (hflat j hj a ha hjop hop (operand_cone ha hin hp (hr.trans hr'))).elim
  · rintro ⟨u,hu,hx⟩
    exact reach_var_val x w u (mem_orIn_reach u hu) hx

lemma opnd_mem {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {a : ℕ}
    (ha : a < C.gates.length) (b : Fin 2) : opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨_,p,q,hin,_,_⟩ := ao2_gate hC ha
  fin_cases b <;> simp [opnd,hin]

lemma orN_value {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (hflat : IsFlat n C) {j : ℕ} (hj : j < C.gates.length) (hjnot : ¬ BelowF G C j)
    (x : Fin n → Bool) :
    gateVal n C j x = true ↔ ∃ u ∈ orIn n C (n+j), x u = true := by
  obtain ⟨a,ha,hop,b,hr⟩ := orN_reaches_and hL hne hj hjnot
  exact descendant_value hL.1 hflat ha hop (opnd_mem hL.1 ha b) hr x

lemma orN_nonempty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (hflat : IsFlat n C) {j : ℕ} (hj : j < C.gates.length) (hjnot : ¬ BelowF G C j) :
    (orIn n C (n+j)).Nonempty := by
  obtain ⟨u,hu,_⟩ := (orN_value hL hne hflat hj hjnot (fun _ => true)).mp
    (ao2_true hL.1 (n+j) (by omega))
  exact ⟨u,hu⟩

lemma orN_colors {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (hflat : IsFlat n C) (s : Fin n → Bool)
    (hcolor : ∀ u v, G.Adj u v → s u ≠ s v)
    {j : ℕ} (hj : j < C.gates.length) (hjnot : ¬ BelowF G C j) :
    ∃ c : Bool, ∀ u ∈ orIn n C (n+j), s u = c := by
  obtain ⟨a,ha,hop,b,hr⟩ := orN_reaches_and hL hne hj hjnot
  obtain ⟨d,hd0,hd1⟩ := and_sides_colors hL hne hflat s hcolor ha hop
  have hsub : orIn n C (n+j) ⊆ side (n := n) C a b := orIn_of_reach hr
  have hb : b=d ∨ b=1-d := by fin_cases b <;> fin_cases d <;> decide
  rcases hb with rfl | rfl
  · exact ⟨false,fun u hu => hd0 u (hsub hu)⟩
  · exact ⟨true,fun u hu => hd1 u (hsub hu)⟩

def colorOr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (c : Bool) : Finset ℕ :=
  (orN G C).filter fun j => ∀ u ∈ orIn n C (n+j), s u = c

lemma mem_colorOr {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {s : Fin n → Bool} {c : Bool} {j : ℕ} :
    j ∈ colorOr G C s c ↔ j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧
      ¬ BelowF G C j ∧ ∀ u ∈ orIn n C (n+j), s u = c := by
  simp only [colorOr,orN,gatesWhere,Finset.mem_filter,Finset.mem_range]
  tauto

lemma colorOr_partition {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (hflat : IsFlat n C) (s : Fin n → Bool)
    (hcolor : ∀ u v, G.Adj u v → s u ≠ s v) :
    orN G C = colorOr G C s false ∪ colorOr G C s true := by
  ext j
  simp only [Finset.mem_union,mem_colorOr,orN,gatesWhere,Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨hj,hop,hnot⟩
    obtain ⟨c,hc⟩ := orN_colors hL hne hflat s hcolor hj hnot
    cases c
    · exact Or.inl ⟨hj,hop,hnot,hc⟩
    · exact Or.inr ⟨hj,hop,hnot,hc⟩
  · rintro (⟨hj,hop,hnot,_⟩ | ⟨hj,hop,hnot,_⟩) <;> exact ⟨hj,hop,hnot⟩

lemma colorOr_disjoint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (hflat : IsFlat n C) (s : Fin n → Bool) :
    Disjoint (colorOr G C s false) (colorOr G C s true) := by
  rw [Finset.disjoint_left]
  intro j hj0 hj1
  obtain ⟨hj,_,hnot,hc0⟩ := mem_colorOr.mp hj0
  obtain ⟨_,_,_,hc1⟩ := mem_colorOr.mp hj1
  obtain ⟨u,hu⟩ := orN_nonempty hL hne hflat hj hnot
  have h0 := hc0 u hu
  have h1 := hc1 u hu
  rw [h0] at h1
  cases h1

lemma gates_partition {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) :
    C.size = (orT G C).card + (orN G C).card + (andGates C).card := by
  classical
  have hcover : Finset.range C.gates.length = (orT G C ∪ orN G C) ∪ andGates C := by
    ext j
    simp only [Finset.mem_range,Finset.mem_union,orT,orN,gatesWhere,andGates,
      Finset.mem_filter,Finset.mem_range]
    constructor
    · intro hj
      rcases (ao2_gate hC hj).1 with hop | hop
      · exact Or.inr ⟨hj,hop⟩
      · by_cases hb : BelowF G C j
        · exact Or.inl (Or.inl ⟨hj,hop,hb⟩)
        · exact Or.inl (Or.inr ⟨hj,hop,hb⟩)
    · tauto
  have hd1 : Disjoint (orT G C) (orN G C) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [orT,orN,gatesWhere,Finset.mem_filter,Finset.mem_range] at hj1 hj2
    exact hj2.2.2 hj1.2.2
  have hd2 : Disjoint (orT G C ∪ orN G C) (andGates C) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have hjop : (gateAt C j).op = GateOp.or := by
      rcases Finset.mem_union.mp hj1 with h | h
      · simp only [orT,gatesWhere,Finset.mem_filter,Finset.mem_range] at h
        exact h.2.1
      · simp only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range] at h
        exact h.2.1
    simp only [andGates,Finset.mem_filter,Finset.mem_range] at hj2
    have hja := hj2.2
    rw [hjop] at hja
    cases hja
  have hc := congrArg Finset.card hcover
  rw [Finset.card_range,Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1] at hc
  exact hc

lemma flat_size {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (hflat : IsFlat n C) (s : Fin n → Bool)
    (hcolor : ∀ u v, G.Adj u v → s u ≠ s v) :
    C.size + 1 = (colorOr G C s false).card + (colorOr G C s true).card +
      2 * (andGates C).card := by
  have hg := gates_partition (G := G) hL.1
  have ho : (orT G C).card + 1 = (andGates C).card := output_or_count hL hne hflat
  have hn : (orN G C).card = (colorOr G C s false).card + (colorOr G C s true).card := by
    rw [colorOr_partition hL hne hflat s hcolor,
      Finset.card_union_of_disjoint (colorOr_disjoint hL hne hflat s)]
  omega

end PEqualNP.Outside.L_meta_3678_aux.Flat

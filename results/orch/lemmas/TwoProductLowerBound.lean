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

namespace PEqualNP.Outside.L_meta_1477.MaskGraphSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk

def Assoc {n m : ℕ} (C : Circuit) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (c : Fin n) (w : ℕ) : Prop :=
  ∃ i : Fin m, center i = c ∧ P2.OrR n C (root i) w

noncomputable def gates {n m : ℕ} (C : Circuit) (center : Fin m → Fin n)
    (root : Fin m → ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    2 ≤ (orIn n C (n + k)).card ∧ ∃ c, Assoc C center root c (n + k)

noncomputable def edges {n m : ℕ} (C : Circuit) (center : Fin m → Fin n)
    (root : Fin m → ℕ) : Finset (Sym2 (Fin n)) := by
  classical
  exact Finset.univ.biUnion fun i : Fin m => (orIn n C (root i)).image fun v => s(center i, v)

lemma assoc_bound {n m : ℕ} (C : Circuit) (hA : P2.AO n C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length) (c : Fin n) (w : ℕ)
    (hassoc : Assoc C center root c w) : w < n + C.gates.length := by
  obtain ⟨i, _, hr⟩ := hassoc
  exact (P2.orR_le n C hA _ _ hr).trans_lt (hbound i)

lemma assoc_no_and {n m : ℕ} (C : Circuit) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) (c : Fin n) (w : ℕ)
    (hassoc : Assoc C center root c w) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ P2.OrR n C w (n + k) := by
  obtain ⟨i, _, hr⟩ := hassoc
  intro k hk hop hpath
  exact hpure i k hk hop (hr.trans hpath)

lemma assoc_nonempty {n m : ℕ} (C : Circuit) (hA : P2.AO n C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) (c : Fin n) (w : ℕ)
    (hassoc : Assoc C center root c w) : (orIn n C w).Nonempty := by
  have hw := assoc_bound C hA center root hbound c w hassoc
  obtain ⟨v, hr, hleaf⟩ := P2.orR_leaf n C hA w hw
  rcases hleaf with hv | ⟨k, rfl, hk, hop⟩
  · exact ⟨⟨v, hv⟩, (P2.mem_orIn n C hA w hw _).mpr hr⟩
  · exact (assoc_no_and C center root hpure c w hassoc k hk hop hr).elim

lemma assoc_adj {n m : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (hA : P2.AO n C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
    (c : Fin n) (w : ℕ) (hassoc : Assoc C center root c w) :
    ∀ v ∈ orIn n C w, G.Adj c v := by
  have hw := assoc_bound C hA center root hbound c w hassoc
  obtain ⟨i, rfl, hr⟩ := hassoc
  exact fun v hv => hclean i v (orIn_subset_of_orR C hA _ _ (hbound i) hw hr hv)

lemma assoc_center_unique {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hA : P2.AO n C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
    (c d : Fin n) (w : ℕ) (hc : Assoc C center root c w) (hd : Assoc C center root d w)
    (hlarge : 2 ≤ (orIn n C w).card) : c = d := by
  by_contra hne
  have hsub : orIn n C w ⊆ Finset.univ.filter (fun v => G.Adj c v ∧ G.Adj d v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      assoc_adj G C hA center root hbound hclean c w hc v hv,
      assoc_adj G C hA center root hbound hclean d w hd v hv⟩
  have hs := (Finset.card_le_card hsub).trans (hG c d hne)
  omega

lemma assoc_or {n m : ℕ} (C : Circuit) (hA : P2.AO n C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) (c : Fin n) (k : ℕ)
    (hassoc : Assoc C center root c (n + k)) : (gateAt C k).op = GateOp.or := by
  have hw := assoc_bound C hA center root hbound c (n + k) hassoc
  have hk : k < C.gates.length := by omega
  rcases (hA k hk).1 with hop | hop
  · exact (assoc_no_and C center root hpure c (n + k) hassoc k hk hop .refl).elim
  · exact hop

lemma assoc_child {n m : ℕ} (C : Circuit) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (c : Fin n) (k w : ℕ) (hassoc : Assoc C center root c (n + k))
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or)
    (hw : w ∈ (gateAt C k).inputs) : Assoc C center root c w := by
  obtain ⟨i, hci, hr⟩ := hassoc
  exact ⟨i, hci, hr.tail ⟨k, rfl, hk, hop, hw⟩⟩

lemma assoc_edge {n m : ℕ} (C : Circuit) (hA : P2.AO n C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (c : Fin n) (w : ℕ) (hassoc : Assoc C center root c w)
    (v : Fin n) (hv : v ∈ orIn n C w) : s(c, v) ∈ edges C center root := by
  classical
  have hw := assoc_bound C hA center root hbound c w hassoc
  obtain ⟨i, rfl, hr⟩ := hassoc
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨v, ?_, rfl⟩⟩
  exact orIn_subset_of_orR C hA _ _ (hbound i) hw hr hv

end PEqualNP.Outside.L_meta_1477.MaskGraphSupport

namespace PEqualNP.Outside.L_meta_1477.MaskGraphNetwork

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport

abbrev Vertex {n m : ℕ} (C : Circuit) (center : Fin m → Fin n) (root : Fin m → ℕ) :=
  Sum (edges C center root) (gates C center root)

lemma assoc_large {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) (c : Fin n) (k : ℕ)
    (ha : Assoc C center root c (n + k)) : 2 ≤ (orIn n C (n + k)).card := by
  have hb := assoc_bound C (P2.ao_of n C hL.1) center root hbound c (n + k) ha
  exact pure_gate_support_large G C hL k (by omega)
    (assoc_no_and C center root hpure c (n + k) ha)

lemma assoc_gate_mem {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) (c : Fin n) (k : ℕ)
    (ha : Assoc C center root c (n + k)) : k ∈ gates C center root := by
  classical
  have hb := assoc_bound C (P2.ao_of n C hL.1) center root hbound c (n + k) ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
    assoc_large G C hL center root hbound hpure c k ha, c, ha⟩

noncomputable def node {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) (c : Fin n) (w : ℕ)
    (ha : Assoc C center root c w) : Vertex C center root := by
  classical
  let hA := P2.ao_of n C hL.1
  by_cases hw : w < n
  · exact Sum.inl ⟨s(c, ⟨w, hw⟩), assoc_edge C hA center root hbound c w ha _
      ((P2.mem_orIn n C hA w (assoc_bound C hA center root hbound c w ha) _).mpr .refl)⟩
  · have he : w = n + (w - n) := by omega
    exact Sum.inr ⟨w - n, assoc_gate_mem G C hL center root hbound hpure c (w - n)
      (by simpa only [← he] using ha)⟩

lemma node_gate {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) (c : Fin n) (k : ℕ)
    (ha : Assoc C center root c (n + k)) (hk : k ∈ gates C center root) :
    node G C hL center root hbound hpure c (n + k) ha = Sum.inr ⟨k, hk⟩ := by
  simp [node, show ¬ n + k < n by omega, Nat.add_sub_cancel_left]

noncomputable def gateCenter {n m : ℕ} (C : Circuit) (center : Fin m → Fin n)
    (root : Fin m → ℕ) (k : gates C center root) : Fin n := by
  classical
  exact Classical.choose (Finset.mem_filter.mp k.property).2.2

lemma gateCenter_assoc {n m : ℕ} (C : Circuit) (center : Fin m → Fin n)
    (root : Fin m → ℕ) (k : gates C center root) :
    Assoc C center root (gateCenter C center root k) (n + k.val) := by
  classical
  exact Classical.choose_spec (Finset.mem_filter.mp k.property).2.2

lemma gate_child_assoc {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) (k : gates C center root) (b : Fin 2) :
    Assoc C center root (gateCenter C center root k) (opnd C k.val b) := by
  classical
  have hA := P2.ao_of n C hL.1
  have hk := Finset.mem_range.mp (Finset.mem_filter.mp k.property).1
  have ha := gateCenter_assoc C center root k
  have hop := assoc_or C hA center root hbound hpure _ k.val ha
  apply assoc_child C center root _ k.val _ ha hk hop
  rw [P2.opnd_eq n C hA k.val hk]
  fin_cases b <;> simp

noncomputable def links {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) : Finset (Sym2 (Vertex C center root)) := by
  classical
  exact Finset.univ.image fun t : (gates C center root) × Fin 2 =>
    s(Sum.inr t.1, node G C hL center root hbound hpure (gateCenter C center root t.1)
      (opnd C t.1.val t.2) (gate_child_assoc G C hL center root hbound hpure t.1 t.2))

noncomputable def network {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) : SimpleGraph (Vertex C center root) :=
  SimpleGraph.fromEdgeSet (links G C hL center root hbound hpure : Set (Sym2 (Vertex C center root)))

lemma network_edge_bound {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) :
    @Finset.card _ (@SimpleGraph.edgeFinset _
      (network G C hL center root hbound hpure)
      (by classical exact Fintype.ofFinite _)) ≤ 2 * (gates C center root).card := by
  classical
  let K := network G C hL center root hbound hpure
  have hs : K.edgeFinset ⊆ links G C hL center root hbound hpure := by
    intro e he
    have he' := SimpleGraph.mem_edgeFinset.mp he
    change e ∈ (SimpleGraph.fromEdgeSet
      (links G C hL center root hbound hpure : Set (Sym2 (Vertex C center root)))).edgeSet at he'
    rw [SimpleGraph.edgeSet_fromEdgeSet] at he'
    exact he'.1
  have hc : (links G C hL center root hbound hpure).card ≤
      (gates C center root).card * 2 := by
    apply (Finset.card_image_le).trans
    simp
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
    (Finset.card_le_card hs).trans (by simpa only [Nat.mul_comm] using hc)

end PEqualNP.Outside.L_meta_1477.MaskGraphNetwork
namespace PEqualNP.Outside.L_meta_1477.MaskGraphReach

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport MaskGraphNetwork

variable {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
  (center : Fin m → Fin n) (root : Fin m → ℕ)
  (hbound : ∀ i, root i < n + C.gates.length)
  (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
    ¬ P2.OrR n C (root i) (n + k))
  (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)

lemma node_input (c v : Fin n) (ha : Assoc C center root c v.val)
    (he : s(c, v) ∈ edges C center root) :
    node G C hL center root hbound hpure c v.val ha = Sum.inl ⟨s(c, v), he⟩ := by
  simp [node, v.isLt]

include hG hclean in
lemma parent_child (c : Fin n) (k : ℕ) (ha : Assoc C center root c (n + k))
    (b : Fin 2) (hb : Assoc C center root c (opnd C k b)) :
    (network G C hL center root hbound hpure).Reachable
      (node G C hL center root hbound hpure c (n + k) ha)
      (node G C hL center root hbound hpure c (opnd C k b) hb) := by
  classical
  have hk := assoc_gate_mem G C hL center root hbound hpure c k ha
  let kk : gates C center root := ⟨k, hk⟩
  have hc : gateCenter C center root kk = c :=
    assoc_center_unique G hG C (P2.ao_of n C hL.1) center root hbound hclean
      _ c (n + k) (gateCenter_assoc C center root kk) ha
      (assoc_large G C hL center root hbound hpure c k ha)
  subst c
  rw [node_gate G C hL center root hbound hpure _ k ha hk]
  by_cases he : (Sum.inr kk : Vertex C center root) =
      node G C hL center root hbound hpure (gateCenter C center root kk) (opnd C k b) hb
  · rw [he]
  · apply SimpleGraph.Adj.reachable
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨?_, he⟩
    exact Finset.mem_image.mpr ⟨(kk, b), Finset.mem_univ _, rfl⟩

include hG hclean in
lemma path_nodes (c : Fin n) (w z : ℕ) (ha : Assoc C center root c w)
    (hz : Assoc C center root c z) (hr : P2.OrR n C w z) :
    (network G C hL center root hbound hpure).Reachable
      (node G C hL center root hbound hpure c w ha)
      (node G C hL center root hbound hpure c z hz) := by
  classical
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _
  | @head w v hs hr ih =>
    obtain ⟨k, rfl, hk, hop, hv⟩ := hs
    have hb : Assoc C center root c v := assoc_child C center root c k v ha hk hop hv
    have he := P2.opnd_eq n C (P2.ao_of n C hL.1) k hk
    rw [he] at hv
    rcases List.mem_cons.mp hv with hv | hv
    · subst v
      exact (parent_child G hG C hL center root hbound hpure hclean c k ha 0 hb).trans (ih hb)
    · have hv : v = opnd C k 1 := by simpa using hv
      subst v
      exact (parent_child G hG C hL center root hbound hpure hclean c k ha 1 hb).trans (ih hb)

noncomputable def rootNode (i : Fin m) : Vertex C center root :=
  node G C hL center root hbound hpure (center i) (root i) ⟨i, rfl, .refl⟩

include hG hclean in
lemma all_reach_roots (v : Vertex C center root) :
    ∃ i : Fin m, (network G C hL center root hbound hpure).Reachable
      v (rootNode G C hL center root hbound hpure i) := by
  classical
  have hA := P2.ao_of n C hL.1
  cases v with
  | inl e =>
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp e.property
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hi
    have ha : Assoc C center root (center i) (root i) := ⟨i, rfl, .refl⟩
    have hr := (P2.mem_orIn n C hA (root i) (hbound i) u).mp hu
    have hb : Assoc C center root (center i) u.val := ⟨i, rfl, hr⟩
    have hre := path_nodes G hG C hL center root hbound hpure hclean _ _ _ ha hb hr
    have hem : s(center i, u) ∈ edges C center root := he.symm ▸ e.property
    rw [node_input G C hL center root hbound hpure _ _ hb hem] at hre
    refine ⟨i, ?_⟩
    convert hre.symm using 1
    · exact congrArg Sum.inl (Subtype.ext he.symm)
    · rfl
  | inr k =>
    obtain ⟨c, i, hci, hi⟩ := (Finset.mem_filter.mp k.property).2.2
    have ha : Assoc C center root (center i) (root i) := ⟨i, rfl, .refl⟩
    have hb : Assoc C center root (center i) (n + k.val) := ⟨i, rfl, hi⟩
    have hre := path_nodes G hG C hL center root hbound hpure hclean _ _ _ ha hb hi
    rw [node_gate G C hL center root hbound hpure _ _ hb k.property] at hre
    exact ⟨i, hre.symm⟩

include hG hclean in
lemma roots_meet (i j : Fin m) (u v : Fin n)
    (hu : u ∈ orIn n C (root i)) (hv : v ∈ orIn n C (root j))
    (he : s(center i, u) = s(center j, v)) :
    (network G C hL center root hbound hpure).Reachable
      (rootNode G C hL center root hbound hpure i)
      (rootNode G C hL center root hbound hpure j) := by
  classical
  have hA := P2.ao_of n C hL.1
  have hi := (P2.mem_orIn n C hA (root i) (hbound i) u).mp hu
  have hj := (P2.mem_orIn n C hA (root j) (hbound j) v).mp hv
  have hui : Assoc C center root (center i) u.val := ⟨i, rfl, hi⟩
  have hvj : Assoc C center root (center j) v.val := ⟨j, rfl, hj⟩
  have hri := path_nodes G hG C hL center root hbound hpure hclean _ _ _ ⟨i, rfl, .refl⟩ hui hi
  have hrj := path_nodes G hG C hL center root hbound hpure hclean _ _ _ ⟨j, rfl, .refl⟩ hvj hj
  have hmi := assoc_edge C hA center root hbound _ _ ⟨i, rfl, .refl⟩ _ hu
  have hmj := assoc_edge C hA center root hbound _ _ ⟨j, rfl, .refl⟩ _ hv
  rw [node_input G C hL center root hbound hpure _ _ hui hmi] at hri
  rw [node_input G C hL center root hbound hpure _ _ hvj hmj] at hrj
  have hh : (Sum.inl ⟨s(center i, u), hmi⟩ : Vertex C center root) = Sum.inl ⟨s(center j, v), hmj⟩ :=
    congrArg Sum.inl (Subtype.ext he)
  rw [hh] at hri
  exact hri.trans hrj.symm

end PEqualNP.Outside.L_meta_1477.MaskGraphReach
namespace PEqualNP.Outside.L_meta_1477.GraphRootCharge

lemma card_le_edges_add_roots {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (m : ℕ) (r : Fin m → V)
    (hreach : ∀ v : V, ∃ i : Fin m, K.Reachable v (r i)) :
    Fintype.card V ≤ K.edgeFinset.card + m := by
  classical
  let A : Finset (Sym2 (Option V)) := K.edgeFinset.image (Sym2.map Option.some)
  let B : Finset (Sym2 (Option V)) := Finset.univ.image (fun i : Fin m => s(none, some (r i)))
  let S := A ∪ B
  let H : SimpleGraph (Option V) := SimpleGraph.fromEdgeSet (S : Set (Sym2 (Option V)))
  have hmap (u v : V) (huv : K.Adj u v) : H.Adj (some u) (some v) := by
    apply (SimpleGraph.fromEdgeSet_adj (S : Set (Sym2 (Option V)))).mpr
    refine ⟨?_, fun he => K.ne_of_adj huv (Option.some.inj he)⟩
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨s(u, v), by simpa using huv, rfl⟩
  let hom : K →g H := ⟨Option.some, fun hu => hmap _ _ hu⟩
  have hstar (i : Fin m) : H.Adj none (some (r i)) := by
    apply (SimpleGraph.fromEdgeSet_adj (S : Set (Sym2 (Option V)))).mpr
    refine ⟨?_, by simp⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hconnected : H.Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
    refine ⟨none, ?_⟩
    intro w
    cases w with
    | none => exact ⟨.nil⟩
    | some v =>
      obtain ⟨i, hi⟩ := hreach v
      exact (hstar i).reachable.trans (hi.map hom).symm
  have hsub : H.edgeFinset ⊆ S := by
    intro e he
    have hh : e ∈ H.edgeSet := SimpleGraph.mem_edgeFinset.mp he
    dsimp only [H] at hh
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hh
    exact hh.1
  have hA : A.card ≤ K.edgeFinset.card := Finset.card_image_le
  have hB : B.card ≤ m := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := Finset.univ) (f := fun i : Fin m => s(none, some (r i))))
  have hS : S.card ≤ A.card + B.card := Finset.card_union_le _ _
  have hH : H.edgeFinset.card ≤ S.card := Finset.card_le_card hsub
  have hEuler := hconnected.card_vert_le_card_edgeSet_add_one
  have hEuler' : Fintype.card V + 1 ≤ H.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_option, SimpleGraph.edgeFinset_card] using hEuler
  omega

lemma label_charge {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (m : ℕ) (r : Fin m → V)
    (hreach : ∀ v : V, ∃ i : Fin m, K.Reachable v (r i))
    (labels gates : ℕ) (hvertices : Fintype.card V = labels + gates)
    (hedges : K.edgeFinset.card ≤ 2 * gates) : labels ≤ gates + m := by
  have h := card_le_edges_add_roots K m r hreach
  omega

end PEqualNP.Outside.L_meta_1477.GraphRootCharge


namespace PEqualNP.Outside.L_meta_1477.GraphRootCharge

lemma card_le_edges_add_groups {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (s m : ℕ)
    (r : Fin s → V) (grp : Fin s → Fin m)
    (hreach : ∀ v : V, ∃ i : Fin s, K.Reachable v (r i))
    (hgroup : ∀ i j : Fin s, grp i = grp j → K.Reachable (r i) (r j)) :
    Fintype.card V ≤ K.edgeFinset.card + m := by
  classical
  by_cases hV : Nonempty V
  · let representative (a : Fin m) : V :=
      if h : ∃ i : Fin s, grp i = a then r h.choose else Classical.choice hV
    apply card_le_edges_add_roots K m representative
    intro v
    obtain ⟨i, hi⟩ := hreach v
    refine ⟨grp i, ?_⟩
    have hex : ∃ j : Fin s, grp j = grp i := ⟨i, rfl⟩
    dsimp only [representative]
    rw [dif_pos hex]
    exact hi.trans (hgroup i hex.choose hex.choose_spec.symm)
  · have hcard : Fintype.card V = 0 :=
      Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hV)
    omega

lemma grouped_label_charge {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (s m : ℕ)
    (r : Fin s → V) (grp : Fin s → Fin m)
    (hreach : ∀ v : V, ∃ i : Fin s, K.Reachable v (r i))
    (hgroup : ∀ i j : Fin s, grp i = grp j → K.Reachable (r i) (r j))
    (labels gates : ℕ) (hvertices : Fintype.card V = labels + gates)
    (hedges : K.edgeFinset.card ≤ 2 * gates) : labels ≤ gates + m := by
  have h := card_le_edges_add_groups K s m r grp hreach hgroup
  omega

end PEqualNP.Outside.L_meta_1477.GraphRootCharge
namespace PEqualNP.Outside.L_meta_1477.MaskGraphCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport MaskGraphNetwork MaskGraphReach

lemma grouped_roots_charge {n m t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k))
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
    (grp : Fin m → Fin t)
    (hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v)) :
    (edges C center root).card ≤ (gates C center root).card + t := by
  classical
  let K := network G C hL center root hbound hpure
  apply GraphRootCharge.grouped_label_charge K m t
    (rootNode G C hL center root hbound hpure) grp
    (all_reach_roots G hG C hL center root hbound hpure hclean)
  · intro i j he
    obtain ⟨u, hu, v, hv, huv⟩ := hgroup i j he
    exact roots_meet G hG C hL center root hbound hpure hclean i j u v hu hv huv
  · simp only [Vertex, Fintype.card_sum, Fintype.card_coe]
  · simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      network_edge_bound G C hL center root hbound hpure

lemma active_gates_or {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) : gates C center root ⊆ orN G C := by
  classical
  intro k hk
  obtain ⟨hkb, _, c, hc⟩ := Finset.mem_filter.mp hk
  have hA := P2.ao_of n C hL.1
  have hop := assoc_or C hA center root hbound hpure c k hc
  have hn : ¬ BelowF G C k := by
    obtain ⟨u, hu⟩ := assoc_nonempty C hA center root hbound hpure c (n + k) hc
    have hr := (P2.mem_orIn n C hA (n + k)
      (assoc_bound C hA center root hbound c (n + k) hc) u).mp hu
    have hv := P2.orR_mono n C hA (pairInput u u) (n + k) u.val hr
      (by simp [P2.W_input, pairInput])
    intro hb
    exact G.irrefl ((P1.S90.graphFun_pair G u u).mp (hb _ hv))
  simpa only [orN, gatesWhere, Finset.mem_filter] using ⟨hkb, hop, hn⟩

end PEqualNP.Outside.L_meta_1477.MaskGraphCharge
namespace PEqualNP.Outside.L_meta_1477.MaskGraphPrune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport MaskGraphNetwork MaskGraphReach

noncomputable def live {n m : ℕ} (C : Circuit) (center : Fin m → Fin n)
    (root : Fin m → ℕ) (owned : Finset (Sym2 (Fin n))) : Finset (gates C center root) := by
  classical
  exact Finset.univ.filter fun k => ∃ u ∈ orIn n C (n + k.val),
    s(gateCenter C center root k, u) ∉ owned

abbrev Pruned {n m : ℕ} (C : Circuit) (center : Fin m → Fin n)
    (root : Fin m → ℕ) (owned : Finset (Sym2 (Fin n))) :=
  Option (Sum ↥(edges C center root \ owned) ↥(live C center root owned))

noncomputable def project {n m : ℕ} (C : Circuit) (center : Fin m → Fin n)
    (root : Fin m → ℕ) (owned : Finset (Sym2 (Fin n))) :
    Vertex C center root → Pruned C center root owned := by
  classical
  intro v
  cases v with
  | inl e =>
    exact if h : e.val ∉ owned then some (Sum.inl ⟨e.val, Finset.mem_sdiff.mpr ⟨e.property, h⟩⟩) else none
  | inr k => exact if h : k ∈ live C center root owned then some (Sum.inr ⟨k, h⟩) else none

variable {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
  (center : Fin m → Fin n) (root : Fin m → ℕ)
  (hbound : ∀ i, root i < n + C.gates.length)
  (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
    ¬ P2.OrR n C (root i) (n + k))
  (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
  (owned : Finset (Sym2 (Fin n)))

include hG hclean in
lemma dead_node (c : Fin n) (w : ℕ) (ha : Assoc C center root c w)
    (hdead : ∀ u ∈ orIn n C w, s(c, u) ∈ owned) :
    project C center root owned (node G C hL center root hbound hpure c w ha) = none := by
  classical
  by_cases hw : w < n
  · have hu : (⟨w, hw⟩ : Fin n) ∈ orIn n C w :=
      (P2.mem_orIn n C (P2.ao_of n C hL.1) w
        (assoc_bound C (P2.ao_of n C hL.1) center root hbound c w ha) _).mpr .refl
    have hd := hdead _ hu
    rw [node_input G C hL center root hbound hpure c ⟨w, hw⟩ ha
      (assoc_edge C (P2.ao_of n C hL.1) center root hbound c w ha _ hu)]
    simp [project, hd]
  · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk := assoc_gate_mem G C hL center root hbound hpure c k ha
    let kk : gates C center root := ⟨k, hk⟩
    have hc : gateCenter C center root kk = c :=
      assoc_center_unique G hG C (P2.ao_of n C hL.1) center root hbound hclean _ c _
        (gateCenter_assoc C center root kk) ha (assoc_large G C hL center root hbound hpure c k ha)
    have hn : kk ∉ live C center root owned := by
      intro hm
      obtain ⟨_, u, hu, hn⟩ := Finset.mem_filter.mp hm
      exact hn (hc.symm ▸ hdead u hu)
    rw [node_gate G C hL center root hbound hpure c k ha hk]
    change (if h : kk ∈ live C center root owned then
      (some (Sum.inr ⟨kk, h⟩) : Pruned C center root owned) else none) = none
    simp only [hn, dite_false]

include hG hclean in
lemma dead_child (k : gates C center root) (b : Fin 2)
    (hk : k ∉ live C center root owned) :
    project C center root owned
      (node G C hL center root hbound hpure (gateCenter C center root k)
        (opnd C k.val b) (gate_child_assoc G C hL center root hbound hpure k b)) = none := by
  classical
  have hparent := gateCenter_assoc C center root k
  have hdead : ∀ u ∈ orIn n C (n + k.val), s(gateCenter C center root k, u) ∈ owned := by
    intro u hu
    by_contra hn
    exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, hn⟩)
  apply dead_node G hG C hL center root hbound hpure hclean owned
  intro u hu
  have hA := P2.ao_of n C hL.1
  have hkl := Finset.mem_range.mp (Finset.mem_filter.mp k.property).1
  have hop := assoc_or C hA center root hbound hpure _ k.val hparent
  have hin : opnd C k.val b ∈ (gateAt C k.val).inputs := by
    rw [P2.opnd_eq n C hA k.val hkl]
    fin_cases b <;> simp
  have hr : P2.OrR n C (n + k.val) (opnd C k.val b) :=
    Relation.ReflTransGen.single ⟨k.val, rfl, hkl, hop, hin⟩
  exact hdead u (orIn_subset_of_orR C hA _ _
    (assoc_bound C hA center root hbound _ _ hparent)
    (assoc_bound C hA center root hbound _ _
      (gate_child_assoc G C hL center root hbound hpure k b)) hr hu)

noncomputable def links : Finset (Sym2 (Pruned C center root owned)) := by
  classical
  exact Finset.univ.image fun t : (live C center root owned) × Fin 2 =>
    s(some (Sum.inr t.1), project C center root owned
      (node G C hL center root hbound hpure (gateCenter C center root t.1.val)
        (opnd C t.1.val.val t.2)
        (gate_child_assoc G C hL center root hbound hpure t.1.val t.2)))

noncomputable def network : SimpleGraph (Pruned C center root owned) :=
  SimpleGraph.fromEdgeSet (links G C hL center root hbound hpure owned : Set _)

include hG hclean in
lemma child_connected (k : gates C center root) (b : Fin 2) :
    (network G C hL center root hbound hpure owned).Reachable
      (project C center root owned (Sum.inr k))
      (project C center root owned
        (node G C hL center root hbound hpure (gateCenter C center root k)
          (opnd C k.val b) (gate_child_assoc G C hL center root hbound hpure k b))) := by
  classical
  by_cases hk : k ∈ live C center root owned
  · have he : project C center root owned (Sum.inr k) = some (Sum.inr ⟨k, hk⟩) := by simp [project, hk]
    rw [he]
    by_cases hsame : some (Sum.inr ⟨k, hk⟩) = project C center root owned
        (node G C hL center root hbound hpure (gateCenter C center root k)
          (opnd C k.val b) (gate_child_assoc G C hL center root hbound hpure k b))
    · rw [hsame]
    · apply SimpleGraph.Adj.reachable
      apply (SimpleGraph.fromEdgeSet_adj _).mpr
      exact ⟨Finset.mem_image.mpr ⟨(⟨k, hk⟩, b), Finset.mem_univ _, rfl⟩, hsame⟩
  · rw [dead_child G hG C hL center root hbound hpure hclean owned k b hk]
    simp only [project, hk, dite_false]
    exact .refl _

end PEqualNP.Outside.L_meta_1477.MaskGraphPrune
namespace PEqualNP.Outside.L_meta_1477.MaskGraphPrune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport MaskGraphNetwork MaskGraphReach

variable {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
  (center : Fin m → Fin n) (root : Fin m → ℕ)
  (hbound : ∀ i, root i < n + C.gates.length)
  (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
    ¬ P2.OrR n C (root i) (n + k))
  (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
  (owned : Finset (Sym2 (Fin n)))

include hG hclean in
lemma map_adj (u v : Vertex C center root)
    (ha : (MaskGraphNetwork.network G C hL center root hbound hpure).Adj u v) :
    (network G C hL center root hbound hpure owned).Reachable
      (project C center root owned u) (project C center root owned v) := by
  classical
  have he := (SimpleGraph.fromEdgeSet_adj _).mp ha
  obtain ⟨⟨k, b⟩, _, hpair⟩ := Finset.mem_image.mp he.1
  have hr := child_connected G hG C hL center root hbound hpure hclean owned k b
  rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hr
  · exact hr.symm

include hG hclean in
lemma map_path (u v : Vertex C center root)
    (hr : (MaskGraphNetwork.network G C hL center root hbound hpure).Reachable u v) :
    (network G C hL center root hbound hpure owned).Reachable
      (project C center root owned u) (project C center root owned v) := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact .refl _
  | cons he p ih => exact (map_adj G hG C hL center root hbound hpure hclean owned _ _ he).trans ih

include hG hclean in
lemma retained_reach (v : Sum ↥(edges C center root \ owned) ↥(live C center root owned)) :
    ∃ i : Fin m, (network G C hL center root hbound hpure owned).Reachable
      (some v) (project C center root owned (rootNode G C hL center root hbound hpure i)) := by
  classical
  have hs : ∃ u : Vertex C center root, project C center root owned u = some v := by
    cases v with
    | inl e =>
      refine ⟨Sum.inl ⟨e.val, (Finset.mem_sdiff.mp e.property).1⟩, ?_⟩
      simp [project, (Finset.mem_sdiff.mp e.property).2]
    | inr k =>
      exact ⟨Sum.inr k.val, by simp [project, k.property]⟩
  obtain ⟨u, hu⟩ := hs
  obtain ⟨i, hi⟩ := all_reach_roots G hG C hL center root hbound hpure hclean u
  refine ⟨i, ?_⟩
  rw [← hu]
  exact map_path G hG C hL center root hbound hpure hclean owned _ _ hi

lemma pruned_edge_bound :
    @Finset.card _ (@SimpleGraph.edgeFinset _
      (network G C hL center root hbound hpure owned)
      (by classical exact Fintype.ofFinite _)) ≤ 2 * (live C center root owned).card := by
  classical
  let K := network G C hL center root hbound hpure owned
  have hs : K.edgeFinset ⊆ links G C hL center root hbound hpure owned := by
    intro e he
    have he' := SimpleGraph.mem_edgeFinset.mp he
    change e ∈ (SimpleGraph.fromEdgeSet
      (links G C hL center root hbound hpure owned : Set _)).edgeSet at he'
    rw [SimpleGraph.edgeSet_fromEdgeSet] at he'
    exact he'.1
  have hc : (links G C hL center root hbound hpure owned).card ≤
      (live C center root owned).card * 2 := by
    apply (Finset.card_image_le).trans
    simp
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
    (Finset.card_le_card hs).trans (by simpa only [Nat.mul_comm] using hc)

include hG hL hbound hpure hclean in
lemma live_outside_lambda :
    (live C center root (starEdges G C)).card ≤ (orN G C \ lam G C).card := by
  classical
  have hs : (live C center root (starEdges G C)).image (fun k => k.val) ⊆ orN G C \ lam G C := by
    intro k hk
    obtain ⟨kk, hkk, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_sdiff.mpr
    refine ⟨MaskGraphCharge.active_gates_or G C hL center root hbound hpure kk.property, ?_⟩
    intro hlam
    obtain ⟨_, u, hu, hnu⟩ := Finset.mem_filter.mp hkk
    have ha := gateCenter_assoc C center root kk
    have hadj := assoc_adj G C (P2.ao_of n C hL.1) center root hbound hclean _ _ ha
    have hlarge := (Finset.mem_filter.mp kk.property).2.1
    exact hnu (lambda_support_star G hG C hL kk.val hlam _ hadj hlarge u hu)
  simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using Finset.card_le_card hs

end PEqualNP.Outside.L_meta_1477.MaskGraphPrune
namespace PEqualNP.Outside.L_meta_1477.GraphRootCharge

lemma boundary_grouped_label_charge {L D : Type*} [Fintype L] [Fintype D]
    (K : SimpleGraph (Option (L ⊕ D))) [DecidableRel K.Adj] (s m : ℕ)
    (r : Fin s → Option (L ⊕ D)) (grp : Fin s → Fin m)
    (hreach : ∀ v : L ⊕ D, ∃ i : Fin s, K.Reachable (some v) (r i))
    (hgroup : ∀ i j : Fin s, grp i = grp j → K.Reachable (r i) (r j))
    (hedges : K.edgeFinset.card ≤ 2 * Fintype.card D) :
    Fintype.card L ≤ Fintype.card D + m := by
  classical
  let roots : Fin (s + 1) → Option (L ⊕ D) := Fin.cases none r
  let groups : Fin (s + 1) → Fin (m + 1) := Fin.cases 0 (fun i => (grp i).succ)
  have hreach' : ∀ v : Option (L ⊕ D), ∃ i : Fin (s + 1), K.Reachable v (roots i) := by
    intro v
    cases v with
    | none => exact ⟨0, by simp only [roots, Fin.cases_zero]; exact ⟨.nil⟩⟩
    | some v =>
      obtain ⟨i, hi⟩ := hreach v
      exact ⟨i.succ, by simpa only [roots, Fin.cases_succ] using hi⟩
  have hgroup' : ∀ i j : Fin (s + 1), groups i = groups j →
      K.Reachable (roots i) (roots j) := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        exact ⟨.nil⟩
      · intro h
        simp only [groups, Fin.cases_zero, Fin.cases_succ] at h
        exact False.elim (Fin.succ_ne_zero _ h.symm)
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        simp only [groups, Fin.cases_zero, Fin.cases_succ, Fin.succ_ne_zero] at h
      · intro h
        have hij : grp i = grp j := by
          simpa only [groups, Fin.cases_succ, Fin.succ_inj] using h
        simpa only [roots, Fin.cases_succ] using hgroup i j hij
  have h := card_le_edges_add_groups K (s + 1) (m + 1) roots groups hreach' hgroup'
  simp only [Fintype.card_option, Fintype.card_sum] at h
  omega

end PEqualNP.Outside.L_meta_1477.GraphRootCharge
namespace PEqualNP.Outside.L_meta_1477.MaskGraphResidual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport MaskGraphNetwork MaskGraphReach
  MaskGraphPrune

lemma pruned_grouped_charge {n m t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k))
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
    (owned : Finset (Sym2 (Fin n))) (grp : Fin m → Fin t)
    (hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v)) :
    (edges C center root \ owned).card ≤ (live C center root owned).card + t := by
  classical
  let K := MaskGraphPrune.network G C hL center root hbound hpure owned
  have h := GraphRootCharge.boundary_grouped_label_charge K m t
    (fun i => project C center root owned (rootNode G C hL center root hbound hpure i)) grp
    (retained_reach G hG C hL center root hbound hpure hclean owned) ?_ ?_
  · simpa only [Fintype.card_coe] using h
  · intro i j he
    obtain ⟨u, hu, v, hv, huv⟩ := hgroup i j he
    exact map_path G hG C hL center root hbound hpure hclean owned _ _
      (roots_meet G hG C hL center root hbound hpure hclean i j u v hu hv huv)
  · simp only [Fintype.card_coe]
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      pruned_edge_bound G C hL center root hbound hpure owned

lemma residual_grouped_charge {n m t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k))
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
    (grp : Fin m → Fin t)
    (hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v)) :
    (edges C center root \ starEdges G C).card ≤ (orN G C \ lam G C).card + t := by
  have h := pruned_grouped_charge G hG C hL center root hbound hpure hclean (starEdges G C) grp hgroup
  exact h.trans (Nat.add_le_add_right (live_outside_lambda G hG C hL center root hbound hpure hclean) t)

end PEqualNP.Outside.L_meta_1477.MaskGraphResidual
namespace PEqualNP.Outside.L_meta_1477.MaskGraphBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport MaskGraphNetwork MaskGraphReach
  MaskGraphPrune

lemma root_boundary {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k))
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
    (owned : Finset (Sym2 (Fin n))) (i : Fin m) (u : Fin n)
    (hu : u ∈ orIn n C (root i)) (howned : s(center i, u) ∈ owned) :
    (MaskGraphPrune.network G C hL center root hbound hpure owned).Reachable
      (project C center root owned (rootNode G C hL center root hbound hpure i)) none := by
  classical
  have hA := P2.ao_of n C hL.1
  have hi := (P2.mem_orIn n C hA (root i) (hbound i) u).mp hu
  have ha : Assoc C center root (center i) u.val := ⟨i, rfl, hi⟩
  have hr := path_nodes G hG C hL center root hbound hpure hclean _ _ _
    ⟨i, rfl, .refl⟩ ha hi
  have he := assoc_edge C hA center root hbound _ _ ⟨i, rfl, .refl⟩ u hu
  rw [node_input G C hL center root hbound hpure _ _ ha he] at hr
  have hm := map_path G hG C hL center root hbound hpure hclean owned _ _ hr
  have hp : project C center root owned (Sum.inl ⟨s(center i, u), he⟩) = none := by
    simp [project, howned]
  rw [hp] at hm
  exact hm

end PEqualNP.Outside.L_meta_1477.MaskGraphBoundary
namespace PEqualNP.Outside.L_meta_1477.GraphRootCharge

lemma boundary_group_credit {L D : Type*} [Fintype L] [Fintype D]
    (K : SimpleGraph (Option (L ⊕ D))) [DecidableRel K.Adj] (s m : ℕ)
    (r : Fin s → Option (L ⊕ D)) (grp : Fin s → Fin m)
    (hreach : ∀ v : L ⊕ D, ∃ i : Fin s, K.Reachable (some v) (r i))
    (hgroup : ∀ i j : Fin s, grp i = grp j → K.Reachable (r i) (r j))
    (B : Finset (Fin m)) (hboundary : ∀ i, grp i ∈ B → K.Reachable (r i) none)
    (hedges : K.edgeFinset.card ≤ 2 * Fintype.card D) :
    Fintype.card L + B.card ≤ Fintype.card D + m := by
  classical
  let Q := ↥(Finset.univ \ B)
  let representative (q : Q) : Option (L ⊕ D) :=
    if h : ∃ i : Fin s, grp i = q.val then r h.choose else none
  let root : Option Q → Option (L ⊕ D) := fun q =>
    match q with
    | none => none
    | some q => representative q
  let e := Fintype.equivFin (Option Q)
  have hr : ∀ v : Option (L ⊕ D), ∃ i : Fin (Fintype.card (Option Q)),
      K.Reachable v (root (e.symm i)) := by
    intro v
    cases v with
    | none => exact ⟨e none, by simp only [Equiv.symm_apply_apply, root]; exact ⟨.nil⟩⟩
    | some v =>
      obtain ⟨i, hi⟩ := hreach v
      by_cases hb : grp i ∈ B
      · refine ⟨e none, ?_⟩
        simpa only [Equiv.symm_apply_apply, root] using hi.trans (hboundary i hb)
      · let q : Q := ⟨grp i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb⟩⟩
        have hex : ∃ j : Fin s, grp j = q.val := ⟨i, rfl⟩
        refine ⟨e (some q), ?_⟩
        simp only [Equiv.symm_apply_apply, root, representative, dif_pos hex]
        exact hi.trans (hgroup i hex.choose hex.choose_spec.symm)
  have h := card_le_edges_add_roots K (Fintype.card (Option Q)) (fun i => root (e.symm i)) hr
  have hpart : Fintype.card Q + B.card = m := by
    dsimp only [Q]
    simpa only [Fintype.card_coe, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B))
  simp only [Fintype.card_option, Fintype.card_sum] at h
  omega

end PEqualNP.Outside.L_meta_1477.GraphRootCharge
namespace PEqualNP.Outside.L_meta_1477.MaskGraphBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport MaskGraphNetwork MaskGraphReach
  MaskGraphPrune

lemma pruned_grouped_credit {n m t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k))
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
    (owned : Finset (Sym2 (Fin n))) (grp : Fin m → Fin t)
    (hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v))
    (boundary : Finset (Fin t))
    (hboundary : ∀ i, grp i ∈ boundary → ∃ j, grp j = grp i ∧
      ∃ u ∈ orIn n C (root j), s(center j, u) ∈ owned) :
    (edges C center root \ owned).card + boundary.card ≤ (live C center root owned).card + t := by
  classical
  let K := MaskGraphPrune.network G C hL center root hbound hpure owned
  have hroots : ∀ i j, grp i = grp j → K.Reachable
      (project C center root owned (rootNode G C hL center root hbound hpure i))
      (project C center root owned (rootNode G C hL center root hbound hpure j)) := by
    intro i j he
    obtain ⟨u, hu, v, hv, huv⟩ := hgroup i j he
    exact map_path G hG C hL center root hbound hpure hclean owned _ _
      (roots_meet G hG C hL center root hbound hpure hclean i j u v hu hv huv)
  have h := GraphRootCharge.boundary_group_credit K m t
    (fun i => project C center root owned (rootNode G C hL center root hbound hpure i)) grp
    (retained_reach G hG C hL center root hbound hpure hclean owned) hroots boundary ?_ ?_
  · simpa only [Fintype.card_coe] using h
  · intro i hi
    obtain ⟨j, hj, u, hu, hown⟩ := hboundary i hi
    exact (hroots i j hj.symm).trans
      (root_boundary G hG C hL center root hbound hpure hclean owned j u hu hown)
  · simp only [Fintype.card_coe]
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using
      pruned_edge_bound G C hL center root hbound hpure owned

end PEqualNP.Outside.L_meta_1477.MaskGraphBoundary
namespace PEqualNP.Outside.L_meta_1477.StructuralMasks

def orValue {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def productValue {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  orValue A x && orValue B x

def CleanMask {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (c : Fin n) : Prop :=
  ∀ x : Fin n → Bool, productValue A B x = true → x c = true →
    ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

def EffectiveMask {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (c : Fin n) : Prop :=
  ∃ u v : Fin n, G.Adj u v ∧
    productValue A B (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
    PEqualNP.EdgeOwnership.pairInput u v c = true

lemma graph_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) (c d : Fin n) :
    (∃ u v : Fin n, G.Adj u v ∧ PEqualNP.EdgeOwnership.pairInput c d u = true ∧
      PEqualNP.EdgeOwnership.pairInput c d v = true) ↔ G.Adj c d := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (G.loopless.irrefl _ huv).elim
    · exact huv
    · exact huv.symm
    · exact (G.loopless.irrefl _ huv).elim
  · intro h
    exact ⟨c, d, h, by simp [PEqualNP.EdgeOwnership.pairInput],
      by simp [PEqualNP.EdgeOwnership.pairInput]⟩

lemma cleanMask_of_mem_left_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ A) :
    CleanMask G A B c ↔ ∀ b ∈ B, G.Adj c b := by
  constructor
  · intro h b hb
    apply (graph_pair_iff G c b).mp
    apply h (PEqualNP.EdgeOwnership.pairInput c b)
    · simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
      exact ⟨⟨c, hc, by simp [PEqualNP.EdgeOwnership.pairInput]⟩,
        ⟨b, hb, by simp [PEqualNP.EdgeOwnership.pairInput]⟩⟩
    · simp [PEqualNP.EdgeOwnership.pairInput]
  · intro h x hx hxc
    simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq] at hx
    obtain ⟨b, hb, hxb⟩ := hx.2
    exact ⟨c, b, h b hb, hxc, hxb⟩

lemma cleanMask_of_mem_right_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ B) :
    CleanMask G A B c ↔ ∀ a ∈ A, G.Adj a c := by
  have hs : CleanMask G A B c ↔ CleanMask G B A c := by
    simp only [CleanMask, productValue, Bool.and_comm]
  rw [hs, cleanMask_of_mem_left_iff G B A c hc]
  exact forall₂_congr fun a _ => G.adj_comm c a

lemma cleanMask_adj_overlap {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hc : CleanMask G A B c)
    (z : Fin n) (hz : z ∈ A ∩ B) : G.Adj c z := by
  apply (graph_pair_iff G c z).mp
  apply hc (PEqualNP.EdgeOwnership.pairInput c z)
  · simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
    exact ⟨⟨z, (Finset.mem_inter.mp hz).1, by simp [PEqualNP.EdgeOwnership.pairInput]⟩,
      ⟨z, (Finset.mem_inter.mp hz).2, by simp [PEqualNP.EdgeOwnership.pairInput]⟩⟩
  · simp [PEqualNP.EdgeOwnership.pairInput]

lemma effectiveMask_mem_union {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hdis : Disjoint A B) (c : Fin n)
    (hc : EffectiveMask G A B c) : c ∈ A ∪ B := by
  obtain ⟨u, v, _, hprod, hmask⟩ := hc
  simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq] at hprod
  obtain ⟨a, ha, hpa⟩ := hprod.1
  obtain ⟨b, hb, hpb⟩ := hprod.2
  simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hpa hpb hmask
  by_contra hnot
  have hca : c ∉ A := fun h => hnot (Finset.mem_union_left _ h)
  have hcb : c ∉ B := fun h => hnot (Finset.mem_union_right _ h)
  have hab : a ≠ b := fun h => (Finset.disjoint_left.mp hdis ha) (h ▸ hb)
  rcases hmask with rfl | rfl <;>
    rcases hpa with rfl | rfl <;> rcases hpb with rfl | rfl <;> contradiction

end PEqualNP.Outside.L_meta_1477.StructuralMasks


namespace PEqualNP.Outside.L_meta_1477.Structural

def cleanCenters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) : Finset (Fin n) :=
  (A.filter fun a => ∀ b ∈ B, G.Adj a b) ∪
    (B.filter fun b => ∀ a ∈ A, G.Adj a b)

lemma commonNeighbors_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hB : 2 ≤ B.card) :
    (A.filter fun a => ∀ b ∈ B, G.Adj a b).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha c hc
  by_contra hac
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  have hsub : ({b, d} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp ha).2 w hb, (Finset.mem_filter.mp hc).2 w hb⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp ha).2 w hd, (Finset.mem_filter.mp hc).2 w hd⟩
  have hcard := Finset.card_le_card hsub
  have hpair : ({b, d} : Finset (Fin n)).card = 2 := by simp [hbd]
  have hsmall := h4 a c hac
  omega

lemma cleanCenters_card_le_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) :
    (cleanCenters G A B).card ≤ 2 := by
  have hleft := commonNeighbors_card_le_one G h4 A B hB
  have hright := commonNeighbors_card_le_one G h4 B A hA
  have heq : (B.filter fun b => ∀ a ∈ A, G.Adj a b) =
      B.filter fun b => ∀ a ∈ A, G.Adj b a := by
    ext b
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hb, h⟩
      exact ⟨hb, fun a ha => (h a ha).symm⟩
    · rintro ⟨hb, h⟩
      exact ⟨hb, fun a ha => (h a ha).symm⟩
  unfold cleanCenters
  rw [heq]
  exact (Finset.card_union_le _ _).trans (by omega)

lemma opposite_centers_no_shared_neighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (side : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → side u ≠ side v)
    (a b : Fin n) (hab : G.Adj a b) :
    ¬ ∃ v, G.Adj a v ∧ G.Adj b v := by
  rintro ⟨v, hav, hbv⟩
  have h1 := hbip a b hab
  have h2 := hbip a v hav
  have h3 := hbip b v hbv
  cases ha : side a <;> cases hb : side b <;> cases hv : side v <;> simp_all

lemma common_mask_inputs_empty {n : ℕ} (G : SimpleGraph (Fin n))
    (side : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → side u ≠ side v)
    (a b : Fin n) (hab : G.Adj a b) (S : Finset (Fin n))
    (hS : ∀ v ∈ S, G.Adj a v ∧ G.Adj b v) : S = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact opposite_centers_no_shared_neighbors G side hbip a b hab ⟨v, hS v hv⟩

end PEqualNP.Outside.L_meta_1477.Structural

namespace PEqualNP.Outside.L_meta_1477.MaskGrouping

open Structural StructuralMasks PEqualNP.EdgeOwnership

noncomputable def neighbors {n : ℕ} (A B : Finset (Fin n)) (c : Fin n) : Finset (Fin n) :=
  if c ∈ A then B else A

noncomputable def starEdges {n : ℕ} (A B : Finset (Fin n)) (c : Fin n) : Finset (Sym2 (Fin n)) :=
  (neighbors A B c).image fun v => s(c, v)

lemma mem_centers_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) :
    c ∈ cleanCenters G A B ↔ c ∈ A ∪ B ∧ CleanMask G A B c := by
  simp only [cleanCenters, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hc, h⟩ | ⟨hc, h⟩)
    · exact ⟨Or.inl hc, (cleanMask_of_mem_left_iff G A B c hc).mpr h⟩
    · exact ⟨Or.inr hc, (cleanMask_of_mem_right_iff G A B c hc).mpr h⟩
  · rintro ⟨hc | hc, h⟩
    · exact Or.inl ⟨hc, (cleanMask_of_mem_left_iff G A B c hc).mp h⟩
    · exact Or.inr ⟨hc, (cleanMask_of_mem_right_iff G A B c hc).mp h⟩

lemma center_neighbors_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ cleanCenters G A B) :
    ∀ v ∈ neighbors A B c, G.Adj c v := by
  have hd := (mem_centers_iff G A B c).mp hc
  by_cases hca : c ∈ A
  · simpa only [neighbors, if_pos hca] using
      (cleanMask_of_mem_left_iff G A B c hca).mp hd.2
  · have hcb : c ∈ B := (Finset.mem_union.mp hd.1).resolve_left hca
    intro v hv
    have hva : v ∈ A := by simpa only [neighbors, if_neg hca] using hv
    exact ((cleanMask_of_mem_right_iff G A B c hcb).mp hd.2 v hva).symm

lemma neighbors_nonempty {n : ℕ} (A B : Finset (Fin n))
    (hA : A.Nonempty) (hB : B.Nonempty) (c : Fin n) :
    (neighbors A B c).Nonempty := by
  unfold neighbors
  split <;> assumption

lemma center_effective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (hA : A.Nonempty) (hB : B.Nonempty)
    (c : Fin n) (hc : c ∈ cleanCenters G A B) : EffectiveMask G A B c := by
  have hcm := (mem_centers_iff G A B c).mp hc
  obtain ⟨v, hv⟩ := neighbors_nonempty A B hA hB c
  refine ⟨c, v, center_neighbors_clean G A B c hc v hv, ?_, by simp [pairInput]⟩
  simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
  by_cases hca : c ∈ A
  · have hvb : v ∈ B := by simpa only [neighbors, if_pos hca] using hv
    exact ⟨⟨c, hca, by simp [pairInput]⟩, ⟨v, hvb, by simp [pairInput]⟩⟩
  · have hcb : c ∈ B := (Finset.mem_union.mp hcm.1).resolve_left hca
    have hva : v ∈ A := by simpa only [neighbors, if_neg hca] using hv
    exact ⟨⟨v, hva, by simp [pairInput]⟩, ⟨c, hcb, by simp [pairInput]⟩⟩

lemma centers_exact_effective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (hdis : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty) (c : Fin n) :
    c ∈ cleanCenters G A B ↔ CleanMask G A B c ∧ EffectiveMask G A B c := by
  constructor
  · intro hc
    exact ⟨((mem_centers_iff G A B c).mp hc).2, center_effective G A B hA hB c hc⟩
  · rintro ⟨hc, he⟩
    exact (mem_centers_iff G A B c).mpr ⟨effectiveMask_mem_union G A B hdis c he, hc⟩

lemma same_side_equal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hB : 2 ≤ B.card) (c d : Fin n)
    (hc : c ∈ A) (hd : d ∈ A) (hcm : CleanMask G A B c) (hdm : CleanMask G A B d) :
    c = d := by
  have hh := commonNeighbors_card_le_one G hG A B hB
  rw [Finset.card_le_one] at hh
  exact hh c (Finset.mem_filter.mpr ⟨hc, (cleanMask_of_mem_left_iff G A B c hc).mp hcm⟩)
    d (Finset.mem_filter.mpr ⟨hd, (cleanMask_of_mem_left_iff G A B d hd).mp hdm⟩)

lemma different_centers_cross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (c d : Fin n)
    (hc : c ∈ cleanCenters G A B) (hd : d ∈ cleanCenters G A B) (hne : c ≠ d) :
    (c ∈ A ∧ d ∈ B) ∨ (c ∈ B ∧ d ∈ A) := by
  obtain ⟨hcAB, hcm⟩ := (mem_centers_iff G A B c).mp hc
  obtain ⟨hdAB, hdm⟩ := (mem_centers_iff G A B d).mp hd
  rcases Finset.mem_union.mp hcAB with hcA | hcB <;>
    rcases Finset.mem_union.mp hdAB with hdA | hdB
  · exact (hne (same_side_equal G hG A B hB c d hcA hdA hcm hdm)).elim
  · exact Or.inl ⟨hcA, hdB⟩
  · exact Or.inr ⟨hcB, hdA⟩
  · apply (hne (same_side_equal G hG B A hA c d hcB hdB ?_ ?_)).elim
    · simpa only [CleanMask, productValue, Bool.and_comm] using hcm
    · simpa only [CleanMask, productValue, Bool.and_comm] using hdm

lemma centers_shared_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hdis : Disjoint A B) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (c d : Fin n)
    (hc : c ∈ cleanCenters G A B) (hd : d ∈ cleanCenters G A B) (hne : c ≠ d) :
    s(c, d) ∈ starEdges A B c ∩ starEdges A B d := by
  have finish (hcd : d ∈ neighbors A B c) (hdc : c ∈ neighbors A B d) :
      s(c, d) ∈ starEdges A B c ∩ starEdges A B d := by
    apply Finset.mem_inter.mpr
    exact ⟨Finset.mem_image.mpr ⟨d, hcd, rfl⟩,
      Finset.mem_image.mpr ⟨c, hdc, Sym2.eq_swap⟩⟩
  rcases different_centers_cross G hG A B hA hB c d hc hd hne with ⟨hcA, hdB⟩ | ⟨hcB, hdA⟩
  · have hdA : d ∉ A := fun h => Finset.disjoint_left.mp hdis h hdB
    exact finish (by simpa only [neighbors, if_pos hcA] using hdB)
      (by simpa only [neighbors, if_neg hdA] using hcA)
  · have hcA : c ∉ A := fun h => Finset.disjoint_left.mp hdis h hcB
    exact finish (by simpa only [neighbors, if_neg hcA] using hdA)
      (by simpa only [neighbors, if_pos hdA] using hcB)

lemma centers_stars_intersect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hdis : Disjoint A B) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (c d : Fin n)
    (hc : c ∈ cleanCenters G A B) (hd : d ∈ cleanCenters G A B) :
    (starEdges A B c ∩ starEdges A B d).Nonempty := by
  by_cases hcd : c = d
  · subst d
    obtain ⟨v, hv⟩ := neighbors_nonempty A B (Finset.card_pos.mp (by omega))
      (Finset.card_pos.mp (by omega)) c
    exact ⟨s(c, v), Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩⟩
  · exact ⟨s(c, d), centers_shared_edge G hG A B hdis hA hB c d hc hd hcd⟩

end PEqualNP.Outside.L_meta_1477.MaskGrouping
namespace PEqualNP.Outside.L_meta_1477.MaskAllCenters

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport

noncomputable def allStars {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Fin t → Finset (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact Finset.univ.biUnion fun a => (Structural.cleanCenters G (A a) (B a)).biUnion
    fun c => MaskGrouping.starEdges (A a) (B a) c

lemma all_centers_residual_credit {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (A B : Fin t → Finset (Fin n))
    (hdis : ∀ a, Disjoint (A a) (B a))
    (hA : ∀ a, 2 ≤ (A a).card) (hB : ∀ a, 2 ≤ (B a).card)
    (left right : Fin t → ℕ)
    (hleft : ∀ a, left a < n + C.gates.length)
    (hright : ∀ a, right a < n + C.gates.length)
    (hpureL : ∀ a, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (left a) (n + k))
    (hpureR : ∀ a, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (right a) (n + k))
    (hsupportL : ∀ a, orIn n C (left a) = A a)
    (hsupportR : ∀ a, orIn n C (right a) = B a)
    (boundary : Finset (Fin t))
    (hboundary : ∀ a ∈ boundary, ∃ c ∈ Structural.cleanCenters G (A a) (B a),
      ∃ u ∈ MaskGrouping.neighbors (A a) (B a) c, s(c, u) ∈ starEdges G C) :
    (allStars G A B \ starEdges G C).card + boundary.card ≤ (orN G C \ lam G C).card + t := by
  classical
  let I := Σ a : Fin t, ↥(Structural.cleanCenters G (A a) (B a))
  let e := Fintype.equivFin I
  let idx : Fin (Fintype.card I) → I := e.symm
  let grp : Fin (Fintype.card I) → Fin t := fun i => (idx i).1
  let center : Fin (Fintype.card I) → Fin n := fun i => (idx i).2.val
  let root : Fin (Fintype.card I) → ℕ := fun i =>
    if center i ∈ A (grp i) then right (grp i) else left (grp i)
  have hcenter : ∀ i, center i ∈ Structural.cleanCenters G (A (grp i)) (B (grp i)) :=
    fun i => (idx i).2.property
  have hsupport : ∀ i, orIn n C (root i) =
      MaskGrouping.neighbors (A (grp i)) (B (grp i)) (center i) := by
    intro i
    by_cases hi : center i ∈ A (grp i)
    · simp only [root, if_pos hi, hsupportR, MaskGrouping.neighbors, if_pos hi]
    · simp only [root, if_neg hi, hsupportL, MaskGrouping.neighbors, if_neg hi]
  have hbound : ∀ i, root i < n + C.gates.length := by
    intro i
    dsimp only [root]
    split
    · exact hright _
    · exact hleft _
  have hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k) := by
    intro i k hk hop
    dsimp only [root]
    split
    · exact hpureR _ k hk hop
    · exact hpureL _ k hk hop
  have hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v := by
    intro i v hv
    rw [hsupport i] at hv
    exact MaskGrouping.center_neighbors_clean G _ _ _ (hcenter i) v hv
  have hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v) := by
    intro i j hij
    have hj : center j ∈ Structural.cleanCenters G (A (grp i)) (B (grp i)) := by
      simpa only [hij] using hcenter j
    obtain ⟨z, hz⟩ := MaskGrouping.centers_stars_intersect G hG
      (A (grp i)) (B (grp i)) (hdis _) (hA _) (hB _) (center i) (center j)
      (hcenter i) hj
    obtain ⟨hzi, hzj⟩ := Finset.mem_inter.mp hz
    obtain ⟨u, hu, hue⟩ := Finset.mem_image.mp hzi
    obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp hzj
    refine ⟨u, ?_, v, ?_, hue.trans hve.symm⟩
    · simpa only [hsupport i] using hu
    · simpa only [hsupport j, ← hij] using hv
  have hsub : allStars G A B ⊆ edges C center root := by
    intro z hz
    obtain ⟨a, _, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨c, hc, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hz
    let i : Fin (Fintype.card I) := e ⟨a, ⟨c, hc⟩⟩
    have hgi : grp i = a := by simp [grp, idx, i]
    have hci : center i = c := by
      exact congrArg (fun j : I => j.2.val) (e.symm_apply_apply ⟨a, ⟨c, hc⟩⟩)
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨v, ?_, ?_⟩⟩
    · rw [hsupport i, hgi, hci]
      exact hv
    · simpa only [hci] using hvz
  have hboundaryidx : ∀ i, grp i ∈ boundary → ∃ j, grp j = grp i ∧
      ∃ u ∈ orIn n C (root j), s(center j, u) ∈ starEdges G C := by
    intro i hi
    obtain ⟨c, hc, u, hu, hown⟩ := hboundary (grp i) hi
    let j : Fin (Fintype.card I) := e ⟨grp i, ⟨c, hc⟩⟩
    have hgj : grp j = grp i := by simp [grp, idx, j]
    have hcj : center j = c := by
      exact congrArg (fun k : I => k.2.val) (e.symm_apply_apply ⟨grp i, ⟨c, hc⟩⟩)
    refine ⟨j, hgj, u, ?_, ?_⟩
    · simpa only [hsupport j, hgj, hcj] using hu
    · simpa only [hcj] using hown
  have hcount := MaskGraphBoundary.pruned_grouped_credit G hG C hL center root
    hbound hpure hclean (starEdges G C) grp hgroup boundary hboundaryidx
  have hlive := MaskGraphPrune.live_outside_lambda G hG C hL center root hbound hpure hclean
  have hdiff : allStars G A B \ starEdges G C ⊆ edges C center root \ starEdges G C := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩
  have hcard := Finset.card_le_card hdiff
  omega

end PEqualNP.Outside.L_meta_1477.MaskAllCenters
namespace PEqualNP.Outside.L_meta_1477.PrivateConeBudget

lemma binary_support_card_le {α : Type*} [DecidableEq α]
    (n : ℕ) (S : ℕ → Finset α) (left right : ℕ → ℕ)
    (hinput : ∀ r < n, (S r).card ≤ 1) :
    ∀ N (M R : Finset ℕ),
      (∀ k ∈ M, k < N) →
      (∀ k ∈ M, left k < n + k ∧ right k < n + k ∧
        S (n + k) ⊆ S (left k) ∪ S (right k)) →
      (∀ k ∈ M, ∀ r, r = left k ∨ r = right k → r < n ∨ r - n ∈ M) →
      (∀ r ∈ R, r < n + N ∧ (r < n ∨ r - n ∈ M)) →
      (R.biUnion S).card ≤ M.card + R.card := by
  intro N
  induction N with
  | zero =>
    intro M R hM hnode hclosed hroots
    calc
      (R.biUnion S).card ≤ ∑ r ∈ R, (S r).card := Finset.card_biUnion_le
      _ ≤ ∑ r ∈ R, 1 := Finset.sum_le_sum (fun r hr => hinput r (by have := (hroots r hr).1; omega))
      _ ≤ M.card + R.card := by simp
  | succ k ih =>
    intro M R hM hnode hclosed hroots
    let M' := M.erase k
    have hMb : ∀ i ∈ M', i < k := by
      intro i hi
      obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hi
      have hb := hM i hm
      omega
    have hn : ∀ i ∈ M', left i < n + i ∧ right i < n + i ∧
        S (n + i) ⊆ S (left i) ∪ S (right i) := by
      intro i hi
      exact hnode i (Finset.mem_of_mem_erase hi)
    have hbelow (r : ℕ) (hr : r < n + k) (hm : r < n ∨ r - n ∈ M) :
        r < n ∨ r - n ∈ M' := by
      rcases hm with h | h
      · exact Or.inl h
      · by_cases hi : r < n
        · exact Or.inl hi
        · exact Or.inr (Finset.mem_erase.mpr ⟨by omega, h⟩)
    have hcl : ∀ i ∈ M', ∀ r, r = left i ∨ r = right i → r < n ∨ r - n ∈ M' := by
      intro i hi r hr
      have hib := hMb i hi
      have hno := hn i hi
      apply hbelow r
      · rcases hr with rfl | rfl <;> omega
      · exact hclosed i (Finset.mem_of_mem_erase hi) r hr
    by_cases htop : n + k ∈ R
    · have hkm : k ∈ M := by
        rcases (hroots (n + k) htop).2 with h | h
        · omega
        · simpa using h
      let R' := R.erase (n + k) ∪ {left k, right k}
      have hrb : ∀ r ∈ R', r < n + k ∧ (r < n ∨ r - n ∈ M') := by
        intro r hr
        rcases Finset.mem_union.mp hr with hr | hr
        · obtain ⟨hne, hr⟩ := Finset.mem_erase.mp hr
          have hb := (hroots r hr).1
          have hl : r < n + k := by omega
          exact ⟨hl, hbelow r hl (hroots r hr).2⟩
        · have he : r = left k ∨ r = right k := by simpa only [Finset.mem_insert, Finset.mem_singleton] using hr
          have hkno := hnode k hkm
          have hl : r < n + k := by rcases he with rfl | rfl <;> omega
          exact ⟨hl, hbelow r hl (hclosed k hkm r he)⟩
      have hsub : R.biUnion S ⊆ R'.biUnion S := by
        intro a ha
        obtain ⟨r, hr, har⟩ := Finset.mem_biUnion.mp ha
        by_cases he : r = n + k
        · subst r
          have hx := (hnode k hkm).2.2 har
          rcases Finset.mem_union.mp hx with hx | hx
          · exact Finset.mem_biUnion.mpr ⟨left k, Finset.mem_union_right _ (by simp), hx⟩
          · exact Finset.mem_biUnion.mpr ⟨right k, Finset.mem_union_right _ (by simp), hx⟩
        · exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hr⟩), har⟩
      have hcount := (Finset.card_le_card hsub).trans (ih M' R' hMb hn hcl hrb)
      have hMcard : M'.card + 1 = M.card := Finset.card_erase_add_one hkm
      have hRcard : (R.erase (n + k)).card + 1 = R.card := Finset.card_erase_add_one htop
      have hUnion := Finset.card_union_le (R.erase (n + k)) ({left k, right k} : Finset ℕ)
      have hPair : ({left k, right k} : Finset ℕ).card ≤ 2 := by
        exact (Finset.card_insert_le _ _).trans (by simp)
      change R'.card ≤ (R.erase (n + k)).card + _ at hUnion
      omega
    · have hrb : ∀ r ∈ R, r < n + k ∧ (r < n ∨ r - n ∈ M') := by
        intro r hr
        have hne : r ≠ n + k := fun h => htop (h ▸ hr)
        have hb := (hroots r hr).1
        have hl : r < n + k := by omega
        exact ⟨hl, hbelow r hl (hroots r hr).2⟩
      have hcount := ih M' R hMb hn hcl hrb
      have hmcard : M'.card ≤ M.card := Finset.card_le_card (Finset.erase_subset _ _)
      omega

end PEqualNP.Outside.L_meta_1477.PrivateConeBudget


namespace PEqualNP.Outside.L_meta_1477.OrConeCredit

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover OneJunk

noncomputable def gates {n : ℕ} (C : Circuit) (R : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    (gateAt C k).op = GateOp.or ∧ ∃ r ∈ R, P2.OrR n C r (n + k)

lemma pure_roots_credit {n : ℕ} (C : Circuit) (hA : P2.AO n C) (R : Finset ℕ)
    (hbound : ∀ r ∈ R, r < n + C.gates.length)
    (hpure : ∀ r ∈ R, ∀ h < C.gates.length, (gateAt C h).op = GateOp.and →
      ¬ P2.OrR n C r (n + h)) :
    (R.biUnion (orIn n C)).card ≤ (gates (n := n) C R).card + R.card := by
  classical
  let O := gates (n := n) C R
  have hmem (k : ℕ) : k ∈ O ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ r ∈ R, P2.OrR n C r (n + k) := by simp [O, gates]
  have hnode (k : ℕ) (hk : k ∈ O) :
      opnd C k 0 < n + k ∧ opnd C k 1 < n + k ∧
      orIn n C (n + k) ⊆ orIn n C (opnd C k 0) ∪ orIn n C (opnd C k 1) := by
    obtain ⟨hkb, hko, _⟩ := (hmem k).mp hk
    have hin := P2.opnd_eq n C hA k hkb
    have hlt := P2.opnd_lt n C hA k hkb (opnd C k) hin
    refine ⟨hlt 0, hlt 1, ?_⟩
    intro u hu
    obtain ⟨_, _, w, hw, _, huw⟩ := (P1.orIn_gate C k u).mp hu
    rw [hin] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_union_left _ huw
    · exact Finset.mem_union_right _ huw
  have hclosed (k : ℕ) (hk : k ∈ O) (w : ℕ)
      (hw : w = opnd C k 0 ∨ w = opnd C k 1) : w < n ∨ w - n ∈ O := by
    by_cases hwn : w < n
    · exact Or.inl hwn
    obtain ⟨hkb, hko, r, hr, hpath⟩ := (hmem k).mp hk
    have hin := P2.opnd_eq n C hA k hkb
    have hlt := hnode k hk
    have hwb : w < n + k := by rcases hw with rfl | rfl <;> omega
    have hwi : w ∈ (gateAt C k).inputs := by rw [hin]; rcases hw with rfl | rfl <;> simp
    have hnext : P2.OrR n C r w := hpath.tail ⟨k, rfl, hkb, hko, hwi⟩
    have he : w = n + (w - n) := by omega
    have hidx : w - n < C.gates.length := by omega
    have hop : (gateAt C (w - n)).op = GateOp.or := by
      rcases (hA (w - n) hidx).1 with hop | hop
      · exact (hpure r hr (w - n) hidx hop (by simpa only [← he] using hnext)).elim
      · exact hop
    exact Or.inr ((hmem _).mpr ⟨hidx, hop, r, hr, by simpa only [← he] using hnext⟩)
  have hroots (r : ℕ) (hr : r ∈ R) : r < n + C.gates.length ∧ (r < n ∨ r - n ∈ O) := by
    refine ⟨hbound r hr, ?_⟩
    by_cases hn : r < n
    · exact Or.inl hn
    have hb : r - n < C.gates.length := by have := hbound r hr; omega
    have he : r = n + (r - n) := by omega
    have hpath : P2.OrR n C r (n + (r - n)) := by rw [← he]; exact .refl
    have hop : (gateAt C (r - n)).op = GateOp.or := by
      rcases (hA (r - n) hb).1 with hop | hop
      · exact (hpure r hr (r - n) hb hop hpath).elim
      · exact hop
    exact Or.inr ((hmem _).mpr ⟨hb, hop, r, hr, hpath⟩)
  exact PrivateConeBudget.binary_support_card_le n (orIn n C)
    (fun k => opnd C k 0) (fun k => opnd C k 1) (P1.orIn_input C)
    C.gates.length O R (fun k hk => ((hmem k).mp hk).1) hnode hclosed hroots

lemma two_roots_credit {n : ℕ} (C : Circuit) (hA : P2.AO n C) (r₀ r₁ : ℕ)
    (hbound : r₀ < n + C.gates.length ∧ r₁ < n + C.gates.length)
    (hpure : ∀ r ∈ ({r₀, r₁} : Finset ℕ), ∀ h < C.gates.length,
      (gateAt C h).op = GateOp.and → ¬ P2.OrR n C r (n + h)) :
    (orIn n C r₀ ∪ orIn n C r₁).card ≤ (gates (n := n) C {r₀, r₁}).card + 2 := by
  have hb : ∀ r ∈ ({r₀, r₁} : Finset ℕ), r < n + C.gates.length := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hbound.1
    · exact hbound.2
  have h := pure_roots_credit C hA {r₀, r₁} hb hpure
  have hc : ({r₀, r₁} : Finset ℕ).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  have hU : ({r₀, r₁} : Finset ℕ).biUnion (orIn n C) = orIn n C r₀ ∪ orIn n C r₁ := by
    ext u
    simp
  rw [hU] at h
  omega

lemma two_roots_private_credit {n : ℕ} (C : Circuit) (hA : P2.AO n C) (r₀ r₁ : ℕ)
    (hbound : r₀ < n + C.gates.length ∧ r₁ < n + C.gates.length)
    (hpure : ∀ r ∈ ({r₀, r₁} : Finset ℕ), ∀ h < C.gates.length,
      (gateAt C h).op = GateOp.and → ¬ P2.OrR n C r (n + h))
    (hd : Disjoint (orIn n C r₀) (orIn n C r₁)) (M : Finset ℕ)
    (hM : gates (n := n) C {r₀, r₁} ⊆ M) (a b : ℕ) (ha : a ∈ M) (hb : b ∈ M)
    (hne : a ≠ b) (haop : (gateAt C a).op = GateOp.and)
    (hbop : (gateAt C b).op = GateOp.and) :
    (orIn n C r₀).card + (orIn n C r₁).card ≤ M.card := by
  classical
  let O := gates (n := n) C {r₀, r₁}
  have hnot (k : ℕ) (hop : (gateAt C k).op = GateOp.and) : k ∉ O := by
    intro hk
    have hor := (Finset.mem_filter.mp hk).2.1
    rw [hop] at hor
    cases hor
  have hsub : insert a (insert b O) ⊆ M := by
    intro k hk
    simp only [Finset.mem_insert] at hk
    rcases hk with rfl | rfl | hk
    · exact ha
    · exact hb
    · exact hM hk
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hne, hnot a haop]),
    Finset.card_insert_of_notMem (hnot b hbop)] at hc
  have h := two_roots_credit C hA r₀ r₁ hbound hpure
  rw [Finset.card_union_of_disjoint hd] at h
  change (orIn n C r₀).card + (orIn n C r₁).card ≤ O.card + 2 at h
  change O.card + 1 + 1 ≤ M.card at hc
  omega

end PEqualNP.Outside.L_meta_1477.OrConeCredit
namespace PEqualNP.Outside.L_meta_1477.MaskFilterCommon

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping MaskGraphSupport

lemma mask_inter_left_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B Q : Finset (Fin n)) (hB : 2 ≤ B.card)
    (hmask : ∀ q ∈ Q, CleanMask G A B q) : (Q ∩ A).card ≤ 1 := by
  have hs : Q ∩ A ⊆ A.filter (fun a => ∀ b ∈ B, G.Adj a b) := by
    intro a ha
    obtain ⟨haQ, haA⟩ := Finset.mem_inter.mp ha
    exact Finset.mem_filter.mpr ⟨haA, (cleanMask_of_mem_left_iff G A B a haA).mp (hmask a haQ)⟩
  exact (Finset.card_le_card hs).trans (commonNeighbors_card_le_one G hG A B hB)

lemma mask_inter_right_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B Q : Finset (Fin n)) (hA : 2 ≤ A.card)
    (hmask : ∀ q ∈ Q, CleanMask G A B q) : (Q ∩ B).card ≤ 1 := by
  apply mask_inter_left_small G hG B A Q hA
  intro q hq
  simpa only [CleanMask, productValue, Bool.and_comm] using hmask q hq

lemma mask_inter_neighbors_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B Q : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (hmask : ∀ q ∈ Q, CleanMask G A B q) (c : Fin n) :
    (Q ∩ neighbors A B c).card ≤ 1 := by
  unfold neighbors
  split
  · exact mask_inter_right_small G hG A B Q hA hmask
  · exact mask_inter_left_small G hG A B Q hB hmask

lemma filter_cone_disjoint {n m : ℕ} (C : Circuit) (hA : P2.AO n C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (filterRoot : ℕ) (hfilter : filterRoot < n + C.gates.length)
    (hsmall : ∀ i, (orIn n C filterRoot ∩ orIn n C (root i)).card ≤ 1) :
    Disjoint (OrConeCredit.gates (n := n) C {filterRoot}) (MaskGraphSupport.gates C center root) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k hk hf
  obtain ⟨hkb, _, r, hr, hkr⟩ := Finset.mem_filter.mp hk
  have he : r = filterRoot := Finset.mem_singleton.mp hr
  subst r
  obtain ⟨_, hlarge, c, i, _, hi⟩ := Finset.mem_filter.mp hf
  have hsub : orIn n C (n + k) ⊆ orIn n C filterRoot ∩ orIn n C (root i) := by
    intro u hu
    have hkl := Finset.mem_range.mp hkb
    exact Finset.mem_inter.mpr
      ⟨orIn_subset_of_orR C hA _ _ hfilter (by omega) hkr hu,
        orIn_subset_of_orR C hA _ _ (hbound i) (by omega) hi hu⟩
  have hh := (Finset.card_le_card hsub).trans (hsmall i)
  omega

lemma filter_cone_cost {n : ℕ} (C : Circuit) (hA : P2.AO n C)
    (filterRoot : ℕ) (hfilter : filterRoot < n + C.gates.length)
    (hpure : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C filterRoot (n + k)) :
    (orIn n C filterRoot).card ≤ (OrConeCredit.gates (n := n) C {filterRoot}).card + 1 := by
  classical
  have h := OrConeCredit.pure_roots_credit C hA {filterRoot}
    (fun r hr => by simpa only [Finset.mem_singleton.mp hr] using hfilter)
    (fun r hr => by simpa only [Finset.mem_singleton.mp hr] using hpure)
  have he : ({filterRoot} : Finset ℕ).biUnion (orIn n C) = orIn n C filterRoot := by
    ext u
    simp
  rw [he] at h
  simpa only [Finset.card_singleton] using h

end PEqualNP.Outside.L_meta_1477.MaskFilterCommon
namespace PEqualNP.Outside.L_meta_1477.FilterConeCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge OneJunk

lemma filtered_root {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C)
    (root : ℕ) (hroot : root < n + C.gates.length) (c : Fin n) (R : Finset (Fin n))
    (hstop : ∀ k ∈ lam G C, P2.OrR n C root (n + k) → (orIn n C (n + k) ∩ R).card ≤ 1) :
    ∃ B : Finset ℕ, B ⊆ orN G C \ lam G C ∧ B ⊆ OrConeCredit.gates (n := n) C {root} ∧
      (orIn n C root ∩ R).card ≤ B.card + 1 := by
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
  let Z := (lam G C).filter fun k => P2.OrR n C root (n + k)
  have hZ : ∀ k ∈ Z, f (n + k) ⊆ f root →
      (∀ v ∈ f (n + k), s(c, v) ∈ (∅ : Finset (Sym2 (Fin n)))) ∨ (f (n + k)).card ≤ 1 := by
    intro k hk _
    exact Or.inr (hstop k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2)
  obtain ⟨B, hBstop, hB, hcount⟩ := P1.top_step2 n (gateAt C) hlen hback f hf1 hf2 hf3
    Z root c ∅ hZ
  have hBfacts : ∀ k ∈ B, k ∈ orN G C \ lam G C ∧ k ∈ OrConeCredit.gates (n := n) C {root} := by
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
    have hnl : k ∉ lam G C := by
      intro hl
      exact Finset.disjoint_left.mp hBstop (Finset.mem_filter.mpr ⟨hl, hpath2⟩) hk
    refine ⟨Finset.mem_sdiff.mpr ⟨hkN, hnl⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklen, hop, root, by simp, hpath2⟩
  refine ⟨B, fun k hk => (hBfacts k hk).1, fun k hk => (hBfacts k hk).2, ?_⟩
  have hinj : Function.Injective (fun v : Fin n => s(c, v)) := by
    intro u v he
    rcases Sym2.eq_iff.mp he with ⟨_, huv⟩ | ⟨hcv, huc⟩
    · exact huv
    · exact huc.trans hcv
  simpa only [Finset.sdiff_empty, Finset.card_image_of_injective _ hinj] using hcount

end PEqualNP.Outside.L_meta_1477.FilterConeCount
namespace PEqualNP.Outside.L_meta_1477.BoundaryProduct

open Structural StructuralMasks MaskGrouping

lemma mask_triple {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (q : Fin n) (hq : CleanMask G A B q) (a b : Fin n) (ha : a ∈ A) (hb : b ∈ B) :
    G.Adj a b ∨ G.Adj a q ∨ G.Adj b q := by
  let x : Fin n → Bool := fun v => decide (v = a ∨ v = b ∨ v = q)
  have hp : productValue A B x = true := by
    simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
    exact ⟨⟨a, ha, by simp [x]⟩, ⟨b, hb, by simp [x]⟩⟩
  obtain ⟨u, v, huv, hu, hv⟩ := hq x hp (by simp [x])
  simp only [x, decide_eq_true_eq] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact (G.irrefl huv).elim
  · exact Or.inl huv
  · exact Or.inr (Or.inl huv)
  · exact Or.inl huv.symm
  · exact (G.irrefl huv).elim
  · exact Or.inr (Or.inr huv)
  · exact Or.inr (Or.inl huv.symm)
  · exact Or.inr (Or.inr huv.symm)
  · exact (G.irrefl huv).elim

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (c q p b : Fin n) (hcq : c ≠ q)
    (hcp : G.Adj c p) (hqp : G.Adj q p) (hcb : G.Adj c b) (hqb : G.Adj q b) : b = p := by
  have hs : {p, b} ⊆ Finset.univ.filter (fun v => G.Adj c v ∧ G.Adj q v) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcp, hqp⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcb, hqb⟩
  have hh := (Finset.card_le_card hs).trans (hG c q hcq)
  by_contra hne
  have hcard : ({p, b} : Finset (Fin n)).card = 2 := by simp [show p ≠ b from fun he => hne he.symm]
  omega

lemma opposite_clean_away_boundary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (c q p : Fin n) (hcq : c ≠ q) (hcp : G.Adj c p) (hqp : G.Adj q p)
    (hcB : ∀ b ∈ B, G.Adj c b) (hqA : ∀ a ∈ A, ¬ G.Adj q a)
    (hmask : CleanMask G A B q) (b : Fin n) (hb : b ∈ B) (hbp : b ≠ p) :
    ∀ a ∈ A, G.Adj a b := by
  intro a ha
  rcases mask_triple G A B q hmask a b ha hb with hab | haq | hbq
  · exact hab
  · exact (hqA a ha haq.symm).elim
  · exact (hbp (common_neighbor_unique G hG c q p b hcq hcp hqp (hcB b hb) hbq.symm)).elim

lemma opposite_support_boundary {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (c q p b : Fin n) (hcq : c ≠ q) (hcp : G.Adj c p) (hqp : G.Adj q p)
    (hcB : ∀ v ∈ B, G.Adj c v) (hqA : ∀ a ∈ A, ¬ G.Adj q a)
    (hmask : CleanMask G A B q) (hb : b ∈ B) (hbA : ∀ a ∈ A, G.Adj a b) :
    p ∈ B ∧ B ⊆ {p, b} := by
  have hsmall := commonNeighbors_card_le_one G hG B A hA
  rw [Finset.card_le_one] at hsmall
  have hsub : B ⊆ {p, b} := by
    intro v hv
    by_cases hvp : v = p
    · simp [hvp]
    · have hvc := opposite_clean_away_boundary G hG A B c q p hcq hcp hqp hcB hqA hmask v hv hvp
      have hvb : v = b := hsmall v
        (Finset.mem_filter.mpr ⟨hv, fun a ha => (hvc a ha).symm⟩)
        b (Finset.mem_filter.mpr ⟨hb, fun a ha => (hbA a ha).symm⟩)
      simp [hvb]
  refine ⟨?_, hsub⟩
  by_contra hp
  have hs : B ⊆ {b} := by
    intro v hv
    have hh := Finset.mem_insert.mp (hsub hv)
    exact hh.resolve_left (fun he => hp (he ▸ hv))
  have hh := Finset.card_le_card hs
  simp only [Finset.card_singleton] at hh
  omega

end PEqualNP.Outside.L_meta_1477.BoundaryProduct
namespace PEqualNP.Outside.L_meta_1477.BoundaryProduct

open Structural StructuralMasks MaskGrouping

lemma no_adj_four_path {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Fin 2) (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (a b c p q : Fin n) (hab : G.Adj a b) (hcb : G.Adj c b)
    (hcp : G.Adj c p) (hqp : G.Adj q p) : ¬ G.Adj q a := by
  intro hqa
  have h1 := hcolor a b hab
  have h2 := hcolor c b hcb
  have h3 := hcolor c p hcp
  have h4 := hcolor q p hqp
  have h5 := hcolor q a hqa
  omega

lemma opposite_support_boundary_bipartite {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G)
    (color : Fin n → Fin 2) (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (c b p q : Fin n) (hc : c ∈ A) (hb : b ∈ B)
    (hcm : CleanMask G A B c) (hbm : CleanMask G A B b)
    (hcq : c ≠ q) (hcp : G.Adj c p) (hqp : G.Adj q p) (hqm : CleanMask G A B q) :
    p ∈ B ∧ B ⊆ {p, b} := by
  have hcB := (cleanMask_of_mem_left_iff G A B c hc).mp hcm
  have hbA := (cleanMask_of_mem_right_iff G A B b hb).mp hbm
  apply opposite_support_boundary G hG A B hA hB c q p b hcq hcp hqp hcB
    (fun a ha => no_adj_four_path G color hcolor a b c p q (hbA a ha) (hcB b hb) hcp hqp)
    hqm hb hbA

lemma boundary_mask_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (A B : Finset (Fin n))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (c b p : Fin n)
    (hc : c ∈ A) (hb : b ∈ B) (hcm : CleanMask G A B c) (hbm : CleanMask G A B b)
    (hsub : B ⊆ {p, b}) (owned : Finset (Sym2 (Fin n))) (howned : s(c, p) ∈ owned)
    (d : Fin n) (hd : d ∈ cleanCenters G A B) (e : Sym2 (Fin n))
    (he : e ∈ MaskGrouping.starEdges A B d) (hnot : e ∉ owned) : b ∈ e := by
  obtain ⟨hdAB, hdm⟩ := (mem_centers_iff G A B d).mp hd
  have hdc : d = c ∨ d = b := by
    rcases Finset.mem_union.mp hdAB with hdA | hdB
    · exact Or.inl (same_side_equal G hG A B hB d c hdA hc hdm hcm)
    · apply Or.inr
      apply same_side_equal G hG B A hA d b hdB hb
      · simpa only [CleanMask, productValue, Bool.and_comm] using hdm
      · simpa only [CleanMask, productValue, Bool.and_comm] using hbm
  rcases hdc with rfl | rfl
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    have hvB : v ∈ B := by simpa only [neighbors, if_pos hc] using hv
    rcases Finset.mem_insert.mp (hsub hvB) with rfl | hvb
    · exact (hnot howned).elim
    · have : v = b := Finset.mem_singleton.mp hvb
      simp [this]
  · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he
    simp

end PEqualNP.Outside.L_meta_1477.BoundaryProduct
namespace PEqualNP.Outside.L_meta_1477.LambdaMaskBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma lambda_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C) (k : ℕ) (hk : k ∈ lam G C) :
    ∃ p : Fin n, (∀ v ∈ orIn n C (n + k), G.Adj p v) ∧
      (∀ v ∈ orIn n C (n + k), s(p, v) ∈ PEqualNP.TopForm.starEdges G C) := by
  obtain ⟨hkN, _, _, t, ht, b, hb, hr⟩ := (P2.mem_filter' _ _ _ _).mp hk
  have hklen : k < C.gates.length := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp hkN).1
  have htlen : t < C.gates.length := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp ht).1
  have hA := P2.ao_of n C hL.1
  have htl := P2.opnd_lt n C hA t htlen (opnd C t) (P2.opnd_eq n C hA t htlen) b
  have htbig : opnd C t b < n + C.gates.length := htl.trans (by omega)
  have hkr := P2.orReaches_orR n C _ htbig k hr
  have hsub : orIn n C (n + k) ⊆ side (n := n) C t b :=
    orIn_subset_of_orR C hA _ _ htbig (by omega) hkr
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hb
  have hpSide : p ∈ side (n := n) C t (1 - b) := by rw [hp]; simp
  refine ⟨p, ?_, ?_⟩
  · intro v hv
    have hvSide := hsub hv
    have hf := (P1.S90.top_facts G C hG hL t ht).2.1
    rcases P2.fin2_sub b with ⟨hb0, hb1⟩ | ⟨hb0, hb1⟩
    · rw [hb0] at hvSide
      rw [hb1] at hpSide
      exact (hf v hvSide p hpSide).symm
    · rw [hb0] at hvSide
      rw [hb1] at hpSide
      exact hf p hpSide v hvSide
  · intro v hv
    have hvSide := hsub hv
    apply Finset.mem_biUnion.mpr
    refine ⟨t, ht, ?_⟩
    rcases P2.fin2_sub b with ⟨hb0, hb1⟩ | ⟨hb0, hb1⟩
    · rw [hb0] at hvSide
      rw [hb1] at hpSide
      exact Finset.mem_image.mpr ⟨(v, p), Finset.mem_product.mpr ⟨hvSide, hpSide⟩, Sym2.eq_swap⟩
    · rw [hb0] at hvSide
      rw [hb1] at hpSide
      exact Finset.mem_image.mpr ⟨(p, v), Finset.mem_product.mpr ⟨hpSide, hvSide⟩, rfl⟩

lemma effective_in_lambda_has_owned_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (filterRoot : ℕ)
    (hroot : filterRoot < n + C.gates.length)
    (hpure : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C filterRoot (n + k))
    (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (c b : Fin n) (hc : c ∈ A) (hb : b ∈ B)
    (hcm : CleanMask G A B c) (hbm : CleanMask G A B b)
    (hmask : ∀ q ∈ orIn n C filterRoot, CleanMask G A B q)
    (k : ℕ) (hk : k ∈ lam G C) (hr : P2.OrR n C filterRoot (n + k))
    (hck : c ∈ orIn n C (n + k)) :
    ∃ v ∈ neighbors A B c, s(c, v) ∈ PEqualNP.TopForm.starEdges G C := by
  classical
  have hAO := P2.ao_of n C hL.1
  have hkl : k < C.gates.length := by
    have hle := P2.orR_le n C hAO _ _ hr
    omega
  have hsub := orIn_subset_of_orR C hAO _ _ hroot (by omega) hr
  have hlarge := pure_gate_support_large G C hL k hkl
    (fun j hj hop hjr => hpure j hj hop (hr.trans hjr))
  have hex : ∃ q ∈ orIn n C (n + k), q ≠ c := by
    by_contra hh
    push_neg at hh
    have hs : orIn n C (n + k) ⊆ {c} := fun q hq => Finset.mem_singleton.mpr (hh q hq)
    have hh := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hh
    omega
  obtain ⟨q, hq, hqc⟩ := hex
  obtain ⟨p, hpAdj, hpOwned⟩ := lambda_center G hG C hL k hk
  have hbound := BoundaryProduct.opposite_support_boundary_bipartite G hG color hcolor
    A B hA hB c b p q hc hb hcm hbm (fun he => hqc he.symm)
    (hpAdj c hck).symm (hpAdj q hq).symm (hmask q (hsub hq))
  refine ⟨p, ?_, ?_⟩
  · simpa only [neighbors, if_pos hc] using hbound.1
  · simpa only [Sym2.eq_swap] using hpOwned c hck

end PEqualNP.Outside.L_meta_1477.LambdaMaskBoundary
namespace PEqualNP.Outside.L_meta_1477.UncreditedFilterCount

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma uncredited_centers_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (filterRoot : ℕ)
    (hroot : filterRoot < n + C.gates.length)
    (hpure : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C filterRoot (n + k))
    (R : Finset (Fin n)) (hR : R ⊆ orIn n C filterRoot)
    (hactive : ∀ c ∈ R, ∃ A B : Finset (Fin n), ∃ b : Fin n,
      2 ≤ A.card ∧ 2 ≤ B.card ∧ c ∈ A ∧ b ∈ B ∧
      CleanMask G A B c ∧ CleanMask G A B b ∧
      (∀ q ∈ orIn n C filterRoot, CleanMask G A B q) ∧
      (∀ v ∈ neighbors A B c, s(c, v) ∉ PEqualNP.TopForm.starEdges G C)) :
    ∃ D : Finset ℕ, D ⊆ orN G C \ lam G C ∧ D ⊆ OrConeCredit.gates (n := n) C {filterRoot} ∧
      R.card ≤ D.card + 1 := by
  classical
  by_cases hne : R.Nonempty
  · obtain ⟨c₀, hc₀⟩ := hne
    have hstop : ∀ k ∈ lam G C, P2.OrR n C filterRoot (n + k) →
        (orIn n C (n + k) ∩ R).card ≤ 1 := by
      intro k hk hr
      have hempty : orIn n C (n + k) ∩ R = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro c hc
        obtain ⟨hck, hcR⟩ := Finset.mem_inter.mp hc
        obtain ⟨A, B, b, hA, hB, hcA, hbB, hcm, hbm, hmask, hnot⟩ := hactive c hcR
        obtain ⟨v, hv, hown⟩ := LambdaMaskBoundary.effective_in_lambda_has_owned_edge
          G hG color hcolor C hL filterRoot hroot hpure A B hA hB c b hcA hbB hcm hbm hmask k hk hr hck
        exact hnot v hv hown
      simp only [hempty, Finset.card_empty, Nat.zero_le]
    obtain ⟨D, hD, hcone, hcard⟩ := FilterConeCount.filtered_root G C hL filterRoot hroot c₀ R hstop
    exact ⟨D, hD, hcone, by simpa only [Finset.inter_eq_right.mpr hR] using hcard⟩
  · refine ⟨∅, Finset.empty_subset _, Finset.empty_subset _, ?_⟩
    have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he]

end PEqualNP.Outside.L_meta_1477.UncreditedFilterCount
namespace PEqualNP.Outside.L_meta_1477.CommonFilterBudget

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping MaskGraphSupport MaskGraphNetwork

noncomputable def liveIndices {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (center : Fin m → Fin n) (root : Fin m → ℕ) : Finset ℕ :=
  (MaskGraphPrune.live C center root (PEqualNP.TopForm.starEdges G C)).image fun k => k.val

lemma live_indices_card {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (center : Fin m → Fin n) (root : Fin m → ℕ) :
    (liveIndices G C center root).card =
      (MaskGraphPrune.live C center root (PEqualNP.TopForm.starEdges G C)).card := by
  exact Finset.card_image_of_injective _ Subtype.val_injective

lemma live_indices_subset {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k))
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v) :
    liveIndices G C center root ⊆ orN G C \ lam G C := by
  classical
  intro k hk
  obtain ⟨kk, hkk, rfl⟩ := Finset.mem_image.mp hk
  apply Finset.mem_sdiff.mpr
  refine ⟨MaskGraphCharge.active_gates_or G C hL center root hbound hpure kk.property, ?_⟩
  intro hlam
  obtain ⟨_, u, hu, hnu⟩ := Finset.mem_filter.mp hkk
  have ha := gateCenter_assoc C center root kk
  have hadj := assoc_adj G C (P2.ao_of n C hL.1) center root hbound hclean _ _ ha
  have hlarge := (Finset.mem_filter.mp kk.property).2.1
  exact hnu (lambda_support_star G hG C hL kk.val hlam _ hadj hlarge u hu)

lemma common_filter_budget {n m t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k))
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
    (grp : Fin m → Fin t)
    (hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v))
    (boundary : Finset (Fin t))
    (hboundary : ∀ i, grp i ∈ boundary → ∃ j, grp j = grp i ∧
      ∃ u ∈ orIn n C (root j), s(center j, u) ∈ PEqualNP.TopForm.starEdges G C)
    (filterRoot : ℕ) (hfilter : filterRoot < n + C.gates.length)
    (hfilterPure : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C filterRoot (n + k))
    (hsmall : ∀ i, (orIn n C filterRoot ∩ orIn n C (root i)).card ≤ 1)
    (R : Finset (Fin n)) (hR : R ⊆ orIn n C filterRoot)
    (hactive : ∀ c ∈ R, ∃ A B : Finset (Fin n), ∃ b : Fin n,
      2 ≤ A.card ∧ 2 ≤ B.card ∧ c ∈ A ∧ b ∈ B ∧
      CleanMask G A B c ∧ CleanMask G A B b ∧
      (∀ q ∈ orIn n C filterRoot, CleanMask G A B q) ∧
      (∀ v ∈ neighbors A B c, s(c, v) ∉ PEqualNP.TopForm.starEdges G C)) :
    (edges C center root \ PEqualNP.TopForm.starEdges G C).card + boundary.card + R.card ≤
      (orN G C \ lam G C).card + t + 1 := by
  classical
  obtain ⟨D, hD, hDcone, hRcard⟩ := UncreditedFilterCount.uncredited_centers_count
    G hG color hcolor C hL filterRoot hfilter hfilterPure R hR hactive
  have hdis : Disjoint D (liveIndices G C center root) := by
    apply Finset.disjoint_left.mpr
    intro k hkD hkL
    obtain ⟨kk, _, hkk⟩ := Finset.mem_image.mp hkL
    have hkMask : k ∈ MaskGraphSupport.gates C center root := hkk ▸ kk.property
    exact Finset.disjoint_left.mp
      (MaskFilterCommon.filter_cone_disjoint C (P2.ao_of n C hL.1) center root hbound filterRoot hfilter hsmall)
      (hDcone hkD) hkMask
  have hsum := Finset.card_le_card
    (Finset.union_subset hD (live_indices_subset G hG C hL center root hbound hpure hclean))
  rw [Finset.card_union_of_disjoint hdis, live_indices_card] at hsum
  have hcount := MaskGraphBoundary.pruned_grouped_credit G hG C hL center root
    hbound hpure hclean (PEqualNP.TopForm.starEdges G C) grp hgroup boundary hboundary
  omega

end PEqualNP.Outside.L_meta_1477.CommonFilterBudget
namespace PEqualNP.Outside.L_meta_1477.ActualCommonMasks

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk StructuralMasks

lemma pure_product_value {n : ℕ} (C : Circuit) (hA : P2.AO n C)
    (g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = GateOp.and)
    (hpure : ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C g b) (n + k)) (x : Fin n → Bool) :
    gateVal n C g x = productValue (side (n := n) C g 0) (side (n := n) C g 1) x := by
  have hin := P2.opnd_eq n C hA g hg
  have hlt := P2.opnd_lt n C hA g hg (opnd C g) hin
  change P2.W n C x (n + g) = _
  rw [P2.W_and n C x g hg hop _ _ hin (hlt 0) (hlt 1)]
  rw [pure_wire_value C hA _ ((hlt 0).trans (by omega)) (hpure 0),
    pure_wire_value C hA _ ((hlt 1).trans (by omega)) (hpure 1)]
  rfl

lemma top_common_masks {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C)
    (g : ℕ) (hg : g < C.gates.length) (hgop : (gateAt C g).op = GateOp.and)
    (hpure : ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C g b) (n + k))
    (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2)
    (hreach : P2.OrR n C (opnd C a b) (n + g)) :
    ∀ q ∈ side (n := n) C a (1 - b),
      CleanMask G (side (n := n) C g 0) (side (n := n) C g 1) q := by
  intro q hq x hp hxq
  have ha0 := (P2.mem_filter' _ _ _ _).mp ha
  have hal := Finset.mem_range.mp ha0.1
  have hin := P2.opnd_eq n C hA a hal
  have hlt := P2.opnd_lt n C hA a hal (opnd C a) hin
  have hqpath := (P2.mem_orIn n C hA (opnd C a (1 - b))
    ((hlt (1 - b)).trans (by omega)) q).mp hq
  have hgp : P2.W n C x (n + g) = true := by
    change gateVal n C g x = true
    rw [pure_product_value C hA g hg hgop hpure]
    exact hp
  have ht := P2.sem_mixed n C hA a hal ha0.2.1 (opnd C a) hin g b q hreach hqpath x hgp hxq
  have hfx := ha0.2.2 x ht
  simpa only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] using hfx

end PEqualNP.Outside.L_meta_1477.ActualCommonMasks
namespace PEqualNP.Outside.L_meta_1477.LambdaMaskBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping MaskGraphSupport MaskGraphNetwork

lemma effective_in_lambda_large_has_owned_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (filterRoot : ℕ)
    (hroot : filterRoot < n + C.gates.length)
    (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (c b : Fin n) (hc : c ∈ A) (hb : b ∈ B)
    (hcm : CleanMask G A B c) (hbm : CleanMask G A B b)
    (hmask : ∀ q ∈ orIn n C filterRoot, CleanMask G A B q)
    (k : ℕ) (hk : k ∈ lam G C) (hr : P2.OrR n C filterRoot (n + k))
    (hck : c ∈ orIn n C (n + k)) (hlarge : 2 ≤ (orIn n C (n + k)).card) :
    ∃ v ∈ neighbors A B c, s(c, v) ∈ PEqualNP.TopForm.starEdges G C := by
  classical
  have hAO := P2.ao_of n C hL.1
  have hkl : k < C.gates.length := by
    have hle := P2.orR_le n C hAO _ _ hr
    omega
  have hsub := orIn_subset_of_orR C hAO _ _ hroot (by omega) hr
  have hex : ∃ q ∈ orIn n C (n + k), q ≠ c := by
    by_contra hh
    push_neg at hh
    have hs : orIn n C (n + k) ⊆ {c} := fun q hq => Finset.mem_singleton.mpr (hh q hq)
    have hh := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hh
    omega
  obtain ⟨q, hq, hqc⟩ := hex
  obtain ⟨p, hpAdj, hpOwned⟩ := lambda_center G hG C hL k hk
  have hbound := BoundaryProduct.opposite_support_boundary_bipartite G hG color hcolor
    A B hA hB c b p q hc hb hcm hbm (fun he => hqc he.symm)
    (hpAdj c hck).symm (hpAdj q hq).symm (hmask q (hsub hq))
  refine ⟨p, ?_, ?_⟩
  · simpa only [neighbors, if_pos hc] using hbound.1
  · simpa only [Sym2.eq_swap] using hpOwned c hck

end PEqualNP.Outside.L_meta_1477.LambdaMaskBoundary

namespace PEqualNP.Outside.L_meta_1477.UncreditedFilterCount

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping MaskGraphSupport MaskGraphNetwork

lemma uncredited_centers_count_general {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (filterRoot : ℕ)
    (hroot : filterRoot < n + C.gates.length)
    (R : Finset (Fin n)) (hR : R ⊆ orIn n C filterRoot)
    (hactive : ∀ c ∈ R, ∃ A B : Finset (Fin n), ∃ b : Fin n,
      2 ≤ A.card ∧ 2 ≤ B.card ∧ c ∈ A ∧ b ∈ B ∧
      CleanMask G A B c ∧ CleanMask G A B b ∧
      (∀ q ∈ orIn n C filterRoot, CleanMask G A B q) ∧
      (∀ v ∈ neighbors A B c, s(c, v) ∉ PEqualNP.TopForm.starEdges G C)) :
    ∃ D : Finset ℕ, D ⊆ orN G C \ lam G C ∧ D ⊆ OrConeCredit.gates (n := n) C {filterRoot} ∧
      R.card ≤ D.card + 1 := by
  classical
  by_cases hne : R.Nonempty
  · obtain ⟨c₀, hc₀⟩ := hne
    have hstop : ∀ k ∈ lam G C, P2.OrR n C filterRoot (n + k) →
        (orIn n C (n + k) ∩ R).card ≤ 1 := by
      intro k hk hr
      by_cases hs : (orIn n C (n + k) ∩ R).card ≤ 1
      · exact hs
      · have hlarge : 2 ≤ (orIn n C (n + k)).card :=
          (show 2 ≤ (orIn n C (n + k) ∩ R).card by omega).trans (Finset.card_le_card Finset.inter_subset_left)
        obtain ⟨c, hc⟩ := Finset.card_pos.mp (show 0 < (orIn n C (n + k) ∩ R).card by omega)
        obtain ⟨hck, hcR⟩ := Finset.mem_inter.mp hc
        obtain ⟨A, B, b, hA, hB, hcA, hbB, hcm, hbm, hmask, hnot⟩ := hactive c hcR
        obtain ⟨v, hv, hown⟩ := LambdaMaskBoundary.effective_in_lambda_large_has_owned_edge
          G hG color hcolor C hL filterRoot hroot A B hA hB c b hcA hbB hcm hbm hmask k hk hr hck hlarge
        exact (hnot v hv hown).elim
    obtain ⟨D, hD, hcone, hcard⟩ := FilterConeCount.filtered_root G C hL filterRoot hroot c₀ R hstop
    exact ⟨D, hD, hcone, by simpa only [Finset.inter_eq_right.mpr hR] using hcard⟩
  · refine ⟨∅, Finset.empty_subset _, Finset.empty_subset _, ?_⟩
    have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he]

end PEqualNP.Outside.L_meta_1477.UncreditedFilterCount

namespace PEqualNP.Outside.L_meta_1477.CommonFilterBudget

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping MaskGraphSupport MaskGraphNetwork

lemma common_filter_budget_general {n m t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k))
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
    (grp : Fin m → Fin t)
    (hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v))
    (boundary : Finset (Fin t))
    (hboundary : ∀ i, grp i ∈ boundary → ∃ j, grp j = grp i ∧
      ∃ u ∈ orIn n C (root j), s(center j, u) ∈ PEqualNP.TopForm.starEdges G C)
    (filterRoot : ℕ) (hfilter : filterRoot < n + C.gates.length)
    (hsmall : ∀ i, (orIn n C filterRoot ∩ orIn n C (root i)).card ≤ 1)
    (R : Finset (Fin n)) (hR : R ⊆ orIn n C filterRoot)
    (hactive : ∀ c ∈ R, ∃ A B : Finset (Fin n), ∃ b : Fin n,
      2 ≤ A.card ∧ 2 ≤ B.card ∧ c ∈ A ∧ b ∈ B ∧
      CleanMask G A B c ∧ CleanMask G A B b ∧
      (∀ q ∈ orIn n C filterRoot, CleanMask G A B q) ∧
      (∀ v ∈ neighbors A B c, s(c, v) ∉ PEqualNP.TopForm.starEdges G C)) :
    (edges C center root \ PEqualNP.TopForm.starEdges G C).card + boundary.card + R.card ≤
      (orN G C \ lam G C).card + t + 1 := by
  classical
  obtain ⟨D, hD, hDcone, hRcard⟩ := UncreditedFilterCount.uncredited_centers_count_general
    G hG color hcolor C hL filterRoot hfilter R hR hactive
  have hdis : Disjoint D (liveIndices G C center root) := by
    apply Finset.disjoint_left.mpr
    intro k hkD hkL
    obtain ⟨kk, _, hkk⟩ := Finset.mem_image.mp hkL
    have hkMask : k ∈ MaskGraphSupport.gates C center root := hkk ▸ kk.property
    exact Finset.disjoint_left.mp
      (MaskFilterCommon.filter_cone_disjoint C (P2.ao_of n C hL.1) center root hbound filterRoot hfilter hsmall)
      (hDcone hkD) hkMask
  have hsum := Finset.card_le_card
    (Finset.union_subset hD (live_indices_subset G hG C hL center root hbound hpure hclean))
  rw [Finset.card_union_of_disjoint hdis, live_indices_card] at hsum
  have hcount := MaskGraphBoundary.pruned_grouped_credit G hG C hL center root
    hbound hpure hclean (PEqualNP.TopForm.starEdges G C) grp hgroup boundary hboundary
  omega

end PEqualNP.Outside.L_meta_1477.CommonFilterBudget

namespace PEqualNP.Outside.L_meta_1477.CommonFamilyBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport Structural StructuralMasks MaskGrouping MaskAllCenters

noncomputable def boundaryProducts {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (A B : Fin t → Finset (Fin n)) : Finset (Fin t) := by
  classical
  exact Finset.univ.filter fun i => ∃ c ∈ cleanCenters G (A i) (B i),
    ∃ u ∈ neighbors (A i) (B i) c, s(c, u) ∈ PEqualNP.TopForm.starEdges G C

noncomputable def activeCenters {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (A B : Fin t → Finset (Fin n)) (filterRoot : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.biUnion fun i : Fin t =>
    if i ∈ boundaryProducts G C A B then ∅ else cleanCenters G (A i) (B i) ∩ orIn n C filterRoot

lemma opposite_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B : Finset (Fin n)) (hdis : Disjoint A B)
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (htwo : (cleanCenters G A B).card = 2)
    (c : Fin n) (hc : c ∈ cleanCenters G A B) :
    (c ∈ A → ∃ b ∈ B, CleanMask G A B b) ∧
      (c ∈ B → ∃ a ∈ A, CleanMask G A B a) := by
  have hex : ∃ d ∈ cleanCenters G A B, d ≠ c := by
    by_contra hh
    push_neg at hh
    have hs : cleanCenters G A B ⊆ {c} := fun d hd => Finset.mem_singleton.mpr (hh d hd)
    have hh := Finset.card_le_card hs
    simp only [htwo, Finset.card_singleton] at hh
    omega
  obtain ⟨d, hd, hdc⟩ := hex
  have hcross := different_centers_cross G hG A B hA hB c d hc hd (fun he => hdc he.symm)
  have hdm := ((mem_centers_iff G A B d).mp hd).2
  constructor
  · intro hcA
    rcases hcross with ⟨_, hdB⟩ | ⟨hcB, _⟩
    · exact ⟨d, hdB, hdm⟩
    · exact (Finset.disjoint_left.mp hdis hcA hcB).elim
  · intro hcB
    rcases hcross with ⟨hcA, _⟩ | ⟨_, hdA⟩
    · exact (Finset.disjoint_left.mp hdis hcA hcB).elim
    · exact ⟨d, hdA, hdm⟩
lemma common_family_budget {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C)
    (A B : Fin t → Finset (Fin n))
    (hdis : ∀ a, Disjoint (A a) (B a))
    (hA : ∀ a, 2 ≤ (A a).card) (hB : ∀ a, 2 ≤ (B a).card)
    (left right : Fin t → ℕ)
    (hleft : ∀ a, left a < n + C.gates.length)
    (hright : ∀ a, right a < n + C.gates.length)
    (hpureL : ∀ a, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (left a) (n + k))
    (hpureR : ∀ a, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (right a) (n + k))
    (hsupportL : ∀ a, orIn n C (left a) = A a)
    (hsupportR : ∀ a, orIn n C (right a) = B a)
    (htwo : ∀ a, (cleanCenters G (A a) (B a)).card = 2)
    (filterRoot : ℕ) (hfilter : filterRoot < n + C.gates.length)
    (hcommon : ∀ a, ∀ q ∈ orIn n C filterRoot, CleanMask G (A a) (B a) q) :
    (allStars G A B \ PEqualNP.TopForm.starEdges G C).card + (boundaryProducts G C A B).card +
      (activeCenters G C A B filterRoot).card ≤ (orN G C \ lam G C).card + t + 1 := by
  classical
  let boundary := boundaryProducts G C A B
  let R := activeCenters G C A B filterRoot
  have hboundary : ∀ a ∈ boundary, ∃ c ∈ cleanCenters G (A a) (B a),
      ∃ u ∈ neighbors (A a) (B a) c, s(c, u) ∈ PEqualNP.TopForm.starEdges G C :=
    fun a ha => (Finset.mem_filter.mp ha).2
  have hRsub : R ⊆ orIn n C filterRoot := by
    intro c hc
    obtain ⟨a, _, hc⟩ := Finset.mem_biUnion.mp hc
    by_cases ha : a ∈ boundaryProducts G C A B
    · simp only [if_pos ha, Finset.notMem_empty] at hc
    · rw [if_neg ha] at hc
      exact (Finset.mem_inter.mp hc).2
  have hactive : ∀ c ∈ R, ∃ A' B' : Finset (Fin n), ∃ b : Fin n,
      2 ≤ A'.card ∧ 2 ≤ B'.card ∧ c ∈ A' ∧ b ∈ B' ∧
      CleanMask G A' B' c ∧ CleanMask G A' B' b ∧
      (∀ q ∈ orIn n C filterRoot, CleanMask G A' B' q) ∧
      (∀ v ∈ neighbors A' B' c, s(c, v) ∉ PEqualNP.TopForm.starEdges G C) := by
    intro c hcR
    obtain ⟨a, _, hc⟩ := Finset.mem_biUnion.mp hcR
    have ha : a ∉ boundaryProducts G C A B := by
      intro ha
      simp only [if_pos ha, Finset.notMem_empty] at hc
    rw [if_neg ha] at hc
    have hcc := (Finset.mem_inter.mp hc).1
    obtain ⟨hcAB, hcm⟩ := (mem_centers_iff G (A a) (B a) c).mp hcc
    have hnot : ∀ v ∈ neighbors (A a) (B a) c, s(c, v) ∉ PEqualNP.TopForm.starEdges G C := by
      intro v hv hown
      exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hcc, v, hv, hown⟩)
    have hop := opposite_center G hG (A a) (B a) (hdis a) (hA a) (hB a) (htwo a) c hcc
    by_cases hcA : c ∈ A a
    · obtain ⟨b, hb, hbm⟩ := hop.1 hcA
      exact ⟨A a, B a, b, hA a, hB a, hcA, hb, hcm, hbm, hcommon a, hnot⟩
    · have hcB : c ∈ B a := (Finset.mem_union.mp hcAB).resolve_left hcA
      obtain ⟨b, hb, hbm⟩ := hop.2 hcB
      refine ⟨B a, A a, b, hB a, hA a, hcB, hb, ?_, ?_, ?_, ?_⟩
      · simpa only [CleanMask, productValue, Bool.and_comm] using hcm
      · simpa only [CleanMask, productValue, Bool.and_comm] using hbm
      · intro q hq
        simpa only [CleanMask, productValue, Bool.and_comm] using hcommon a q hq
      · simpa only [neighbors, if_pos hcB, if_neg hcA] using hnot
  let I := Σ a : Fin t, ↥(Structural.cleanCenters G (A a) (B a))
  let e := Fintype.equivFin I
  let idx : Fin (Fintype.card I) → I := e.symm
  let grp : Fin (Fintype.card I) → Fin t := fun i => (idx i).1
  let center : Fin (Fintype.card I) → Fin n := fun i => (idx i).2.val
  let root : Fin (Fintype.card I) → ℕ := fun i =>
    if center i ∈ A (grp i) then right (grp i) else left (grp i)
  have hcenter : ∀ i, center i ∈ Structural.cleanCenters G (A (grp i)) (B (grp i)) :=
    fun i => (idx i).2.property
  have hsupport : ∀ i, orIn n C (root i) =
      MaskGrouping.neighbors (A (grp i)) (B (grp i)) (center i) := by
    intro i
    by_cases hi : center i ∈ A (grp i)
    · simp only [root, if_pos hi, hsupportR, MaskGrouping.neighbors, if_pos hi]
    · simp only [root, if_neg hi, hsupportL, MaskGrouping.neighbors, if_neg hi]
  have hbound : ∀ i, root i < n + C.gates.length := by
    intro i
    dsimp only [root]
    split
    · exact hright _
    · exact hleft _
  have hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k) := by
    intro i k hk hop
    dsimp only [root]
    split
    · exact hpureR _ k hk hop
    · exact hpureL _ k hk hop
  have hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v := by
    intro i v hv
    rw [hsupport i] at hv
    exact MaskGrouping.center_neighbors_clean G _ _ _ (hcenter i) v hv
  have hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v) := by
    intro i j hij
    have hj : center j ∈ Structural.cleanCenters G (A (grp i)) (B (grp i)) := by
      simpa only [hij] using hcenter j
    obtain ⟨z, hz⟩ := MaskGrouping.centers_stars_intersect G hG
      (A (grp i)) (B (grp i)) (hdis _) (hA _) (hB _) (center i) (center j)
      (hcenter i) hj
    obtain ⟨hzi, hzj⟩ := Finset.mem_inter.mp hz
    obtain ⟨u, hu, hue⟩ := Finset.mem_image.mp hzi
    obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp hzj
    refine ⟨u, ?_, v, ?_, hue.trans hve.symm⟩
    · simpa only [hsupport i] using hu
    · simpa only [hsupport j, ← hij] using hv
  have hsub : allStars G A B ⊆ edges C center root := by
    intro z hz
    obtain ⟨a, _, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨c, hc, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hz
    let i : Fin (Fintype.card I) := e ⟨a, ⟨c, hc⟩⟩
    have hgi : grp i = a := by simp [grp, idx, i]
    have hci : center i = c := by
      exact congrArg (fun j : I => j.2.val) (e.symm_apply_apply ⟨a, ⟨c, hc⟩⟩)
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨v, ?_, ?_⟩⟩
    · rw [hsupport i, hgi, hci]
      exact hv
    · simpa only [hci] using hvz
  have hboundaryidx : ∀ i, grp i ∈ boundary → ∃ j, grp j = grp i ∧
      ∃ u ∈ orIn n C (root j), s(center j, u) ∈ PEqualNP.TopForm.starEdges G C := by
    intro i hi
    obtain ⟨c, hc, u, hu, hown⟩ := hboundary (grp i) hi
    let j : Fin (Fintype.card I) := e ⟨grp i, ⟨c, hc⟩⟩
    have hgj : grp j = grp i := by simp [grp, idx, j]
    have hcj : center j = c := by
      exact congrArg (fun k : I => k.2.val) (e.symm_apply_apply ⟨grp i, ⟨c, hc⟩⟩)
    refine ⟨j, hgj, u, ?_, ?_⟩
    · simpa only [hsupport j, hgj, hcj] using hu
    · simpa only [hcj] using hown
  have hsmall : ∀ i, (orIn n C filterRoot ∩ orIn n C (root i)).card ≤ 1 := by
    intro i
    rw [hsupport i]
    exact MaskFilterCommon.mask_inter_neighbors_small G hG _ _ _ (hA _) (hB _) (hcommon _) _
  have hcount := CommonFilterBudget.common_filter_budget_general G hG color hcolor C hL center root
    hbound hpure hclean grp hgroup boundary hboundaryidx filterRoot hfilter hsmall R hRsub hactive
  have hdiff : allStars G A B \ PEqualNP.TopForm.starEdges G C ⊆ edges C center root \ PEqualNP.TopForm.starEdges G C := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩
  have hcard := Finset.card_le_card hdiff
  dsimp only [boundary, R] at hcount
  omega

end PEqualNP.Outside.L_meta_1477.CommonFamilyBudget
namespace PEqualNP.Outside.L_meta_1477.EligibleBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

def Certificate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (owned : Finset (Sym2 (Fin n))) : Prop :=
  (∃ c ∈ cleanCenters G A B, ∃ v ∈ neighbors A B c, s(c, v) ∈ owned) ∧
    ∃ d : Fin n, ∀ c ∈ cleanCenters G A B, ∀ e ∈ MaskGrouping.starEdges A B c, e ∉ owned → d ∈ e

lemma centers_comm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) : cleanCenters G A B = cleanCenters G B A := by
  ext c
  rw [mem_centers_iff, mem_centers_iff]
  simp only [Finset.union_comm, CleanMask, productValue, Bool.and_comm]

lemma neighbors_comm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (hdis : Disjoint A B) (c : Fin n)
    (hc : c ∈ cleanCenters G A B) : neighbors A B c = neighbors B A c := by
  have hcAB := ((mem_centers_iff G A B c).mp hc).1
  by_cases hcA : c ∈ A
  · have hcB : c ∉ B := fun h => Finset.disjoint_left.mp hdis hcA h
    simp only [neighbors, if_pos hcA, if_neg hcB]
  · have hcB : c ∈ B := (Finset.mem_union.mp hcAB).resolve_left hcA
    simp only [neighbors, if_neg hcA, if_pos hcB]

lemma certificate_swap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (hdis : Disjoint A B) (owned : Finset (Sym2 (Fin n)))
    (h : Certificate G A B owned) : Certificate G B A owned := by
  obtain ⟨⟨c, hc, v, hv, hown⟩, d, hd⟩ := h
  have hc' : c ∈ cleanCenters G B A := by simpa only [← centers_comm G A B] using hc
  refine ⟨⟨c, hc', v, ?_, hown⟩, d, ?_⟩
  · simpa only [← neighbors_comm G A B hdis c hc] using hv
  · intro q hq e he hn
    have hq' : q ∈ cleanCenters G A B := by simpa only [centers_comm G A B] using hq
    apply hd q hq' e _ hn
    simpa only [MaskGrouping.starEdges, ← neighbors_comm G A B hdis q hq'] using he

lemma lambda_certificate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (filterRoot : ℕ)
    (hroot : filterRoot < n + C.gates.length)
    (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (c b : Fin n) (hc : c ∈ A) (hb : b ∈ B)
    (hcm : CleanMask G A B c) (hbm : CleanMask G A B b)
    (hmask : ∀ q ∈ orIn n C filterRoot, CleanMask G A B q)
    (k : ℕ) (hk : k ∈ lam G C) (hr : P2.OrR n C filterRoot (n + k))
    (hck : c ∈ orIn n C (n + k)) (hlarge : 2 ≤ (orIn n C (n + k)).card) :
    Certificate G A B (PEqualNP.TopForm.starEdges G C) := by
  classical
  have hAO := P2.ao_of n C hL.1
  have hkl : k < C.gates.length := by
    have hle := P2.orR_le n C hAO _ _ hr
    omega
  have hsub := orIn_subset_of_orR C hAO _ _ hroot (by omega) hr
  have hex : ∃ q ∈ orIn n C (n + k), q ≠ c := by
    by_contra hh
    push_neg at hh
    have hs : orIn n C (n + k) ⊆ {c} := fun q hq => Finset.mem_singleton.mpr (hh q hq)
    have hh := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hh
    omega
  obtain ⟨q, hq, hqc⟩ := hex
  obtain ⟨p, hpAdj, hpOwned⟩ := LambdaMaskBoundary.lambda_center G hG C hL k hk
  have hbound := BoundaryProduct.opposite_support_boundary_bipartite G hG color hcolor
    A B hA hB c b p q hc hb hcm hbm (fun he => hqc he.symm)
    (hpAdj c hck).symm (hpAdj q hq).symm (hmask q (hsub hq))
  have howned : s(c, p) ∈ PEqualNP.TopForm.starEdges G C := by
    simpa only [Sym2.eq_swap] using hpOwned c hck
  refine ⟨⟨c, (mem_centers_iff G A B c).mpr ⟨Finset.mem_union_left _ hc, hcm⟩,
    p, ?_, howned⟩, b, ?_⟩
  · simpa only [neighbors, if_pos hc] using hbound.1
  · exact BoundaryProduct.boundary_mask_cover G hG A B hA hB c b p hc hb hcm hbm hbound.2 _ howned

end PEqualNP.Outside.L_meta_1477.EligibleBoundary
namespace PEqualNP.Outside.L_meta_1477.EligibleFilterCount

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping MaskGraphSupport MaskGraphNetwork CommonFilterBudget

lemma eligible_centers_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (filterRoot : ℕ)
    (hroot : filterRoot < n + C.gates.length)
    (R : Finset (Fin n)) (hR : R ⊆ orIn n C filterRoot)
    (hactive : ∀ c ∈ R, ∃ A B : Finset (Fin n), ∃ b : Fin n,
      2 ≤ A.card ∧ 2 ≤ B.card ∧ c ∈ A ∧ b ∈ B ∧
      CleanMask G A B c ∧ CleanMask G A B b ∧
      (∀ q ∈ orIn n C filterRoot, CleanMask G A B q) ∧
      ¬ EligibleBoundary.Certificate G A B (PEqualNP.TopForm.starEdges G C)) :
    ∃ D : Finset ℕ, D ⊆ orN G C \ lam G C ∧ D ⊆ OrConeCredit.gates (n := n) C {filterRoot} ∧
      R.card ≤ D.card + 1 := by
  classical
  by_cases hne : R.Nonempty
  · obtain ⟨c₀, hc₀⟩ := hne
    have hstop : ∀ k ∈ lam G C, P2.OrR n C filterRoot (n + k) →
        (orIn n C (n + k) ∩ R).card ≤ 1 := by
      intro k hk hr
      by_cases hs : (orIn n C (n + k) ∩ R).card ≤ 1
      · exact hs
      · have hlarge : 2 ≤ (orIn n C (n + k)).card :=
          (show 2 ≤ (orIn n C (n + k) ∩ R).card by omega).trans (Finset.card_le_card Finset.inter_subset_left)
        obtain ⟨c, hc⟩ := Finset.card_pos.mp (show 0 < (orIn n C (n + k) ∩ R).card by omega)
        obtain ⟨hck, hcR⟩ := Finset.mem_inter.mp hc
        obtain ⟨A, B, b, hA, hB, hcA, hbB, hcm, hbm, hmask, hnot⟩ := hactive c hcR
        have hcert := EligibleBoundary.lambda_certificate
          G hG color hcolor C hL filterRoot hroot A B hA hB c b hcA hbB hcm hbm hmask k hk hr hck hlarge
        exact (hnot hcert).elim
    obtain ⟨D, hD, hcone, hcard⟩ := FilterConeCount.filtered_root G C hL filterRoot hroot c₀ R hstop
    exact ⟨D, hD, hcone, by simpa only [Finset.inter_eq_right.mpr hR] using hcard⟩
  · refine ⟨∅, Finset.empty_subset _, Finset.empty_subset _, ?_⟩
    have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he]

end PEqualNP.Outside.L_meta_1477.EligibleFilterCount

namespace PEqualNP.Outside.L_meta_1477.EligibleFilterBudget

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping MaskGraphSupport MaskGraphNetwork CommonFilterBudget

lemma eligible_filter_budget {n m t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k))
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
    (grp : Fin m → Fin t)
    (hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v))
    (boundary : Finset (Fin t))
    (hboundary : ∀ i, grp i ∈ boundary → ∃ j, grp j = grp i ∧
      ∃ u ∈ orIn n C (root j), s(center j, u) ∈ PEqualNP.TopForm.starEdges G C)
    (filterRoot : ℕ) (hfilter : filterRoot < n + C.gates.length)
    (hsmall : ∀ i, (orIn n C filterRoot ∩ orIn n C (root i)).card ≤ 1)
    (R : Finset (Fin n)) (hR : R ⊆ orIn n C filterRoot)
    (hactive : ∀ c ∈ R, ∃ A B : Finset (Fin n), ∃ b : Fin n,
      2 ≤ A.card ∧ 2 ≤ B.card ∧ c ∈ A ∧ b ∈ B ∧
      CleanMask G A B c ∧ CleanMask G A B b ∧
      (∀ q ∈ orIn n C filterRoot, CleanMask G A B q) ∧
      ¬ EligibleBoundary.Certificate G A B (PEqualNP.TopForm.starEdges G C)) :
    (edges C center root \ PEqualNP.TopForm.starEdges G C).card + boundary.card + R.card ≤
      (orN G C \ lam G C).card + t + 1 := by
  classical
  obtain ⟨D, hD, hDcone, hRcard⟩ := EligibleFilterCount.eligible_centers_count
    G hG color hcolor C hL filterRoot hfilter R hR hactive
  have hdis : Disjoint D (liveIndices G C center root) := by
    apply Finset.disjoint_left.mpr
    intro k hkD hkL
    obtain ⟨kk, _, hkk⟩ := Finset.mem_image.mp hkL
    have hkMask : k ∈ MaskGraphSupport.gates C center root := hkk ▸ kk.property
    exact Finset.disjoint_left.mp
      (MaskFilterCommon.filter_cone_disjoint C (P2.ao_of n C hL.1) center root hbound filterRoot hfilter hsmall)
      (hDcone hkD) hkMask
  have hsum := Finset.card_le_card
    (Finset.union_subset hD (live_indices_subset G hG C hL center root hbound hpure hclean))
  rw [Finset.card_union_of_disjoint hdis, live_indices_card] at hsum
  have hcount := MaskGraphBoundary.pruned_grouped_credit G hG C hL center root
    hbound hpure hclean (PEqualNP.TopForm.starEdges G C) grp hgroup boundary hboundary
  omega

end PEqualNP.Outside.L_meta_1477.EligibleFilterBudget

namespace PEqualNP.Outside.L_meta_1477.EligibleFamilyBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport Structural StructuralMasks MaskGrouping MaskAllCenters

noncomputable def boundaryProducts {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (A B : Fin t → Finset (Fin n)) : Finset (Fin t) := by
  classical
  exact Finset.univ.filter fun i => EligibleBoundary.Certificate G (A i) (B i) (PEqualNP.TopForm.starEdges G C)

noncomputable def activeCenters {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (A B : Fin t → Finset (Fin n)) (filterRoot : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.biUnion fun i : Fin t =>
    if i ∈ boundaryProducts G C A B then ∅ else cleanCenters G (A i) (B i) ∩ orIn n C filterRoot

lemma opposite_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B : Finset (Fin n)) (hdis : Disjoint A B)
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (htwo : (cleanCenters G A B).card = 2)
    (c : Fin n) (hc : c ∈ cleanCenters G A B) :
    (c ∈ A → ∃ b ∈ B, CleanMask G A B b) ∧
      (c ∈ B → ∃ a ∈ A, CleanMask G A B a) := by
  have hex : ∃ d ∈ cleanCenters G A B, d ≠ c := by
    by_contra hh
    push_neg at hh
    have hs : cleanCenters G A B ⊆ {c} := fun d hd => Finset.mem_singleton.mpr (hh d hd)
    have hh := Finset.card_le_card hs
    simp only [htwo, Finset.card_singleton] at hh
    omega
  obtain ⟨d, hd, hdc⟩ := hex
  have hcross := different_centers_cross G hG A B hA hB c d hc hd (fun he => hdc he.symm)
  have hdm := ((mem_centers_iff G A B d).mp hd).2
  constructor
  · intro hcA
    rcases hcross with ⟨_, hdB⟩ | ⟨hcB, _⟩
    · exact ⟨d, hdB, hdm⟩
    · exact (Finset.disjoint_left.mp hdis hcA hcB).elim
  · intro hcB
    rcases hcross with ⟨hcA, _⟩ | ⟨_, hdA⟩
    · exact (Finset.disjoint_left.mp hdis hcA hcB).elim
    · exact ⟨d, hdA, hdm⟩
lemma eligible_family_budget {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C)
    (A B : Fin t → Finset (Fin n))
    (hdis : ∀ a, Disjoint (A a) (B a))
    (hA : ∀ a, 2 ≤ (A a).card) (hB : ∀ a, 2 ≤ (B a).card)
    (left right : Fin t → ℕ)
    (hleft : ∀ a, left a < n + C.gates.length)
    (hright : ∀ a, right a < n + C.gates.length)
    (hpureL : ∀ a, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (left a) (n + k))
    (hpureR : ∀ a, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (right a) (n + k))
    (hsupportL : ∀ a, orIn n C (left a) = A a)
    (hsupportR : ∀ a, orIn n C (right a) = B a)
    (htwo : ∀ a, (cleanCenters G (A a) (B a)).card = 2)
    (filterRoot : ℕ) (hfilter : filterRoot < n + C.gates.length)
    (hcommon : ∀ a, ∀ q ∈ orIn n C filterRoot, CleanMask G (A a) (B a) q) :
    (allStars G A B \ PEqualNP.TopForm.starEdges G C).card + (boundaryProducts G C A B).card +
      (activeCenters G C A B filterRoot).card ≤ (orN G C \ lam G C).card + t + 1 := by
  classical
  let boundary := boundaryProducts G C A B
  let R := activeCenters G C A B filterRoot
  have hboundary : ∀ a ∈ boundary, ∃ c ∈ cleanCenters G (A a) (B a),
      ∃ u ∈ neighbors (A a) (B a) c, s(c, u) ∈ PEqualNP.TopForm.starEdges G C :=
    fun a ha => (Finset.mem_filter.mp ha).2.1
  have hRsub : R ⊆ orIn n C filterRoot := by
    intro c hc
    obtain ⟨a, _, hc⟩ := Finset.mem_biUnion.mp hc
    by_cases ha : a ∈ boundaryProducts G C A B
    · simp only [if_pos ha, Finset.notMem_empty] at hc
    · rw [if_neg ha] at hc
      exact (Finset.mem_inter.mp hc).2
  have hactive : ∀ c ∈ R, ∃ A' B' : Finset (Fin n), ∃ b : Fin n,
      2 ≤ A'.card ∧ 2 ≤ B'.card ∧ c ∈ A' ∧ b ∈ B' ∧
      CleanMask G A' B' c ∧ CleanMask G A' B' b ∧
      (∀ q ∈ orIn n C filterRoot, CleanMask G A' B' q) ∧
      ¬ EligibleBoundary.Certificate G A' B' (PEqualNP.TopForm.starEdges G C) := by
    intro c hcR
    obtain ⟨a, _, hc⟩ := Finset.mem_biUnion.mp hcR
    have ha : a ∉ boundaryProducts G C A B := by
      intro ha
      simp only [if_pos ha, Finset.notMem_empty] at hc
    rw [if_neg ha] at hc
    have hcc := (Finset.mem_inter.mp hc).1
    obtain ⟨hcAB, hcm⟩ := (mem_centers_iff G (A a) (B a) c).mp hcc
    have hnot : ¬ EligibleBoundary.Certificate G (A a) (B a) (PEqualNP.TopForm.starEdges G C) := by
      intro hcert
      exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcert⟩)
    have hop := opposite_center G hG (A a) (B a) (hdis a) (hA a) (hB a) (htwo a) c hcc
    by_cases hcA : c ∈ A a
    · obtain ⟨b, hb, hbm⟩ := hop.1 hcA
      exact ⟨A a, B a, b, hA a, hB a, hcA, hb, hcm, hbm, hcommon a, hnot⟩
    · have hcB : c ∈ B a := (Finset.mem_union.mp hcAB).resolve_left hcA
      obtain ⟨b, hb, hbm⟩ := hop.2 hcB
      refine ⟨B a, A a, b, hB a, hA a, hcB, hb, ?_, ?_, ?_, ?_⟩
      · simpa only [CleanMask, productValue, Bool.and_comm] using hcm
      · simpa only [CleanMask, productValue, Bool.and_comm] using hbm
      · intro q hq
        simpa only [CleanMask, productValue, Bool.and_comm] using hcommon a q hq
      · intro hcert
        exact hnot (EligibleBoundary.certificate_swap G (B a) (A a) (hdis a).symm _ hcert)
  let I := Σ a : Fin t, ↥(Structural.cleanCenters G (A a) (B a))
  let e := Fintype.equivFin I
  let idx : Fin (Fintype.card I) → I := e.symm
  let grp : Fin (Fintype.card I) → Fin t := fun i => (idx i).1
  let center : Fin (Fintype.card I) → Fin n := fun i => (idx i).2.val
  let root : Fin (Fintype.card I) → ℕ := fun i =>
    if center i ∈ A (grp i) then right (grp i) else left (grp i)
  have hcenter : ∀ i, center i ∈ Structural.cleanCenters G (A (grp i)) (B (grp i)) :=
    fun i => (idx i).2.property
  have hsupport : ∀ i, orIn n C (root i) =
      MaskGrouping.neighbors (A (grp i)) (B (grp i)) (center i) := by
    intro i
    by_cases hi : center i ∈ A (grp i)
    · simp only [root, if_pos hi, hsupportR, MaskGrouping.neighbors, if_pos hi]
    · simp only [root, if_neg hi, hsupportL, MaskGrouping.neighbors, if_neg hi]
  have hbound : ∀ i, root i < n + C.gates.length := by
    intro i
    dsimp only [root]
    split
    · exact hright _
    · exact hleft _
  have hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k) := by
    intro i k hk hop
    dsimp only [root]
    split
    · exact hpureR _ k hk hop
    · exact hpureL _ k hk hop
  have hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v := by
    intro i v hv
    rw [hsupport i] at hv
    exact MaskGrouping.center_neighbors_clean G _ _ _ (hcenter i) v hv
  have hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v) := by
    intro i j hij
    have hj : center j ∈ Structural.cleanCenters G (A (grp i)) (B (grp i)) := by
      simpa only [hij] using hcenter j
    obtain ⟨z, hz⟩ := MaskGrouping.centers_stars_intersect G hG
      (A (grp i)) (B (grp i)) (hdis _) (hA _) (hB _) (center i) (center j)
      (hcenter i) hj
    obtain ⟨hzi, hzj⟩ := Finset.mem_inter.mp hz
    obtain ⟨u, hu, hue⟩ := Finset.mem_image.mp hzi
    obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp hzj
    refine ⟨u, ?_, v, ?_, hue.trans hve.symm⟩
    · simpa only [hsupport i] using hu
    · simpa only [hsupport j, ← hij] using hv
  have hsub : allStars G A B ⊆ edges C center root := by
    intro z hz
    obtain ⟨a, _, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨c, hc, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hz
    let i : Fin (Fintype.card I) := e ⟨a, ⟨c, hc⟩⟩
    have hgi : grp i = a := by simp [grp, idx, i]
    have hci : center i = c := by
      exact congrArg (fun j : I => j.2.val) (e.symm_apply_apply ⟨a, ⟨c, hc⟩⟩)
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨v, ?_, ?_⟩⟩
    · rw [hsupport i, hgi, hci]
      exact hv
    · simpa only [hci] using hvz
  have hboundaryidx : ∀ i, grp i ∈ boundary → ∃ j, grp j = grp i ∧
      ∃ u ∈ orIn n C (root j), s(center j, u) ∈ PEqualNP.TopForm.starEdges G C := by
    intro i hi
    obtain ⟨c, hc, u, hu, hown⟩ := hboundary (grp i) hi
    let j : Fin (Fintype.card I) := e ⟨grp i, ⟨c, hc⟩⟩
    have hgj : grp j = grp i := by simp [grp, idx, j]
    have hcj : center j = c := by
      exact congrArg (fun k : I => k.2.val) (e.symm_apply_apply ⟨grp i, ⟨c, hc⟩⟩)
    refine ⟨j, hgj, u, ?_, ?_⟩
    · simpa only [hsupport j, hgj, hcj] using hu
    · simpa only [hcj] using hown
  have hsmall : ∀ i, (orIn n C filterRoot ∩ orIn n C (root i)).card ≤ 1 := by
    intro i
    rw [hsupport i]
    exact MaskFilterCommon.mask_inter_neighbors_small G hG _ _ _ (hA _) (hB _) (hcommon _) _
  have hcount := EligibleFilterBudget.eligible_filter_budget G hG color hcolor C hL center root
    hbound hpure hclean grp hgroup boundary hboundaryidx filterRoot hfilter hsmall R hRsub hactive
  have hdiff : allStars G A B \ PEqualNP.TopForm.starEdges G C ⊆ edges C center root \ PEqualNP.TopForm.starEdges G C := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩
  have hcard := Finset.card_le_card hdiff
  dsimp only [boundary, R] at hcount
  omega

end PEqualNP.Outside.L_meta_1477.EligibleFamilyBudget
namespace PEqualNP.Outside.L_meta_1477.EligibleFamilyBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport Structural StructuralMasks MaskGrouping MaskAllCenters

noncomputable def filteredStars {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (A B : Fin t → Finset (Fin n)) (filterRoot : ℕ) : Finset (Sym2 (Fin n)) := by
  classical
  exact Finset.univ.biUnion fun i : Fin t =>
    (cleanCenters G (A i) (B i) ∩ orIn n C filterRoot).biUnion fun c => MaskGrouping.starEdges (A i) (B i) c

lemma eligible_filter_cover {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (A B : Fin t → Finset (Fin n)) (filterRoot : ℕ) :
    ∃ T : Finset (Fin n), T.card ≤ (boundaryProducts G C A B).card + (activeCenters G C A B filterRoot).card ∧
      ∀ e ∈ filteredStars G C A B filterRoot \ PEqualNP.TopForm.starEdges G C, ∃ v ∈ T, v ∈ e := by
  classical
  let J := boundaryProducts G C A B
  let d : J → Fin n := fun i => Classical.choose ((Finset.mem_filter.mp i.property).2.2)
  have hd (i : J) : ∀ c ∈ cleanCenters G (A i.val) (B i.val),
      ∀ e ∈ MaskGrouping.starEdges (A i.val) (B i.val) c,
      e ∉ PEqualNP.TopForm.starEdges G C → d i ∈ e :=
    Classical.choose_spec ((Finset.mem_filter.mp i.property).2.2)
  let D : Finset (Fin n) := Finset.univ.image d
  let R := activeCenters G C A B filterRoot
  have hDcard : D.card ≤ J.card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using (Finset.card_image_le (s := Finset.univ) (f := d))
  refine ⟨D ∪ R, ?_, ?_⟩
  · have h := Finset.card_union_le D R
    change (D ∪ R).card ≤ J.card + R.card
    omega
  · intro e he
    obtain ⟨he, hnot⟩ := Finset.mem_sdiff.mp he
    obtain ⟨i, _, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨c, hc, he⟩ := Finset.mem_biUnion.mp he
    by_cases hi : i ∈ J
    · let j : J := ⟨i, hi⟩
      refine ⟨d j, Finset.mem_union_left _ ?_, hd j c (Finset.mem_inter.mp hc).1 e he hnot⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · have hcR : c ∈ R := by
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_univ _, ?_⟩
        simpa only [show i ∉ boundaryProducts G C A B from hi, ite_false] using hc
      refine ⟨c, Finset.mem_union_right _ hcR, ?_⟩
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he
      simp

lemma filtered_stars_subset {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (A B : Fin t → Finset (Fin n)) (filterRoot : ℕ) :
    filteredStars G C A B filterRoot ⊆ allStars G A B := by
  intro e he
  obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨c, hc, he⟩ := Finset.mem_biUnion.mp he
  exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_biUnion.mpr ⟨c, (Finset.mem_inter.mp hc).1, he⟩⟩

end PEqualNP.Outside.L_meta_1477.EligibleFamilyBudget

namespace PEqualNP.Outside.L_meta_1477.MaskGrouping

open Structural StructuralMasks PEqualNP.EdgeOwnership

lemma center_not_neighbors {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ cleanCenters G A B) :
    c ∉ neighbors A B c := by
  intro hv
  exact G.loopless.irrefl c (center_neighbors_clean G A B c hc c hv)

lemma masked_pair_in_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ cleanCenters G A B)
    (u v : Fin n) (hprod : productValue A B (pairInput u v) = true)
    (hmask : pairInput u v c = true) : s(u, v) ∈ starEdges A B c := by
  simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq] at hprod
  have he : ∃ w ∈ neighbors A B c, pairInput u v w = true := by
    by_cases hca : c ∈ A
    · simpa only [neighbors, if_pos hca] using hprod.2
    · simpa only [neighbors, if_neg hca] using hprod.1
  obtain ⟨w, hw, hpw⟩ := he
  have hcw : c ≠ w := fun h => center_not_neighbors G A B c hc (h ▸ hw)
  apply Finset.mem_image.mpr
  refine ⟨w, hw, ?_⟩
  simp only [pairInput, decide_eq_true_eq] at hmask hpw
  rcases hmask with rfl | rfl <;> rcases hpw with rfl | rfl
  · exact (hcw rfl).elim
  · rfl
  · exact Sym2.eq_swap
  · exact (hcw rfl).elim

lemma star_pair_masked {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ cleanCenters G A B)
    (u v : Fin n) (he : s(u, v) ∈ starEdges A B c) :
    productValue A B (pairInput u v) = true ∧ pairInput u v c = true := by
  obtain ⟨w, hw, he⟩ := Finset.mem_image.mp he
  have hcm := (mem_centers_iff G A B c).mp hc
  have hv : productValue A B (pairInput c w) = true := by
    simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
    by_cases hca : c ∈ A
    · have hwb : w ∈ B := by simpa only [neighbors, if_pos hca] using hw
      exact ⟨⟨c, hca, by simp [pairInput]⟩, ⟨w, hwb, by simp [pairInput]⟩⟩
    · have hcb : c ∈ B := (Finset.mem_union.mp hcm.1).resolve_left hca
      have hwa : w ∈ A := by simpa only [neighbors, if_neg hca] using hw
      exact ⟨⟨w, hwa, by simp [pairInput]⟩, ⟨c, hcb, by simp [pairInput]⟩⟩
  have hpair : pairInput c w = pairInput u v := by
    funext z
    apply Bool.eq_iff_iff.mpr
    have hz := Iff.of_eq (congrArg (fun e : Sym2 (Fin n) => z ∈ e) he)
    simpa only [pairInput, decide_eq_true_eq, Sym2.mem_iff] using hz
  rw [← hpair]
  exact ⟨hv, by simp [pairInput]⟩

lemma effective_mask_pair_covered {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (hdis : Disjoint A B) (u v c : Fin n)
    (huv : G.Adj u v) (hprod : productValue A B (pairInput u v) = true)
    (hmask : pairInput u v c = true) (hclean : CleanMask G A B c) :
    c ∈ cleanCenters G A B ∧ s(u, v) ∈ starEdges A B c := by
  have hm : c ∈ cleanCenters G A B := (mem_centers_iff G A B c).mpr
    ⟨effectiveMask_mem_union G A B hdis c ⟨u, v, huv, hprod, hmask⟩, hclean⟩
  exact ⟨hm, masked_pair_in_star G A B c hm u v hprod hmask⟩

end PEqualNP.Outside.L_meta_1477.MaskGrouping

namespace PEqualNP.Outside.L_meta_1477.CommonFamilyAccounting

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk

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


lemma accounting_paid_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    (hne : G.edgeFinset.Nonempty) (tau t : ℕ)
    (hmin : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) → tau ≤ K.card)
    (T : Finset (Fin n)) (hT : ∀ e ∈ Ustar G C, ∃ v ∈ T, v ∈ e)
    (hpaid : (Ustar G C).card + T.card ≤ (orN G C \ lam G C).card + t + 1) :
    G.edgeFinset.card + tau + 2 * (centreless G C).card + (junk G C).card ≤
      C.size + t + 2 := by
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

lemma filtered_pair_covered {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (A B : Fin t → Finset (Fin n)) (filterRoot : ℕ)
    (hdis : ∀ i, Disjoint (A i) (B i))
    (hcommon : ∀ i, ∀ c ∈ orIn n C filterRoot, StructuralMasks.CleanMask G (A i) (B i) c)
    (i : Fin t) (u v c : Fin n) (huv : G.Adj u v)
    (hp : StructuralMasks.productValue (A i) (B i) (pairInput u v) = true)
    (hc : c ∈ orIn n C filterRoot) (hcv : pairInput u v c = true) :
    s(u, v) ∈ EligibleFamilyBudget.filteredStars G C A B filterRoot := by
  obtain ⟨hcent, he⟩ := MaskGrouping.effective_mask_pair_covered G (A i) (B i)
    (hdis i) u v c huv hp hcv (hcommon i c hc)
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr
    ⟨c, Finset.mem_inter.mpr ⟨hcent, hc⟩, he⟩⟩

lemma common_family_lower_bound {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    (hne : G.edgeFinset.Nonempty) (tau : ℕ)
    (hmin : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) → tau ≤ K.card)
    (A B : Fin t → Finset (Fin n))
    (hdis : ∀ a, Disjoint (A a) (B a))
    (hA : ∀ a, 2 ≤ (A a).card) (hB : ∀ a, 2 ≤ (B a).card)
    (left right : Fin t → ℕ)
    (hleft : ∀ a, left a < n + C.gates.length)
    (hright : ∀ a, right a < n + C.gates.length)
    (hpureL : ∀ a, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (left a) (n + k))
    (hpureR : ∀ a, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (right a) (n + k))
    (hsupportL : ∀ a, orIn n C (left a) = A a)
    (hsupportR : ∀ a, orIn n C (right a) = B a)
    (htwo : ∀ a, (Structural.cleanCenters G (A a) (B a)).card = 2)
    (filterRoot : ℕ) (hfilter : filterRoot < n + C.gates.length)
    (hcommon : ∀ a, ∀ q ∈ orIn n C filterRoot, StructuralMasks.CleanMask G (A a) (B a) q)
    (hcoverage : Ustar G C ⊆ EligibleFamilyBudget.filteredStars G C A B filterRoot)
    (hjunk : t ≤ (junk G C).card) (hcentre : 1 ≤ (centreless G C).card) :
    G.edgeFinset.card + tau ≤ C.size := by
  classical
  have hbudget := EligibleFamilyBudget.eligible_family_budget G hG color hcolor C hL
    A B hdis hA hB left right hleft hright hpureL hpureR hsupportL hsupportR htwo
    filterRoot hfilter hcommon
  obtain ⟨T, hTcard, hT⟩ := EligibleFamilyBudget.eligible_filter_cover G C A B filterRoot
  have hUnot : ∀ e ∈ Ustar G C, e ∉ starEdges G C := fun e he => (Finset.mem_sdiff.mp he).2
  have hcover : ∀ e ∈ Ustar G C, ∃ v ∈ T, v ∈ e := by
    intro e he
    exact hT e (Finset.mem_sdiff.mpr ⟨hcoverage he, hUnot e he⟩)
  have hUsub : Ustar G C ⊆ MaskAllCenters.allStars G A B \ starEdges G C := by
    intro e he
    exact Finset.mem_sdiff.mpr
      ⟨EligibleFamilyBudget.filtered_stars_subset G C A B filterRoot (hcoverage he), hUnot e he⟩
  have hUcard := Finset.card_le_card hUsub
  have hpaid : (Ustar G C).card + T.card ≤ (orN G C \ lam G C).card + t + 1 := by omega
  have hcount := accounting_paid_cover G hG C hL hTF hne tau t hmin T hcover hpaid
  omega

end PEqualNP.Outside.L_meta_1477.CommonFamilyAccounting

namespace PEqualNP.Outside.L_meta_1477.OneJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

lemma mixing_on_junk_path_witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (g : ℕ) (hg : g ∈ junk G C)
    (w : ℕ) (hw : w < n + C.gates.length) (hr : P2.OrR n C w (n + g))
    (hne : (orIn n C w).Nonempty) :
    ∃ m ∈ mixing G C, P2.OrR n C w (n + m) ∧ P2.OrR n C (n + m) (n + g) := by
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
      refine ⟨k, Finset.mem_filter.mpr ⟨?_, hxor⟩,
        Relation.ReflTransGen.refl,
        Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hcin⟩ hr⟩
      simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨hk, hop, hkn⟩
    · obtain ⟨m, hm, hwm, hmg⟩ := ih (hcw.trans hw) (Finset.nonempty_iff_ne_empty.mpr hc)
      exact ⟨m, hm, Relation.ReflTransGen.head hs hwm, hmg⟩

lemma mixing_subset_outside_lambda {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : mixing G C ⊆ orN G C \ lam G C := by
  intro m hm
  simp only [mixing, Finset.mem_filter] at hm
  refine Finset.mem_sdiff.mpr ⟨hm.1, fun hl => ?_⟩
  simp only [lam, Finset.mem_filter] at hl
  apply hm.2
  rw [Finset.nonempty_iff_ne_empty, Finset.nonempty_iff_ne_empty] at hl
  simp only [hl.2.1, hl.2.2.1]

lemma paired_dirty_reader_overhead {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C)
    (a : ℕ) (ha : a ∈ tops G C) (g h : ℕ) (hg : g ∈ junk G C) (hh : h ∈ junk G C)
    (hr0 : P2.OrR n C (opnd C a 0) (n + g))
    (hr1 : P2.OrR n C (opnd C a 1) (n + h))
    (O : Finset ℕ)
    (hO : ∀ k ∈ O, ∀ d ∈ junk G C, ¬ P2.OrR n C (n + k) (n + d)) :
    2 ≤ ((orN G C \ lam G C) \ O).card + 2 * (centreless G C).card := by
  classical
  by_cases he : side (n := n) C a 0 = ∅ ∨ side (n := n) C a 1 = ∅
  · have hac : a ∈ centreless G C := Finset.mem_filter.mpr ⟨ha, he⟩
    have hc := Finset.card_pos.mpr (show (centreless G C).Nonempty from ⟨a, hac⟩)
    omega
  · have hs := not_or.mp he
    have halen : a < C.gates.length := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp ha).1
    have hbig : ∀ b : Fin 2, opnd C a b < n + C.gates.length := by
      intro b
      have hb := P2.opnd_lt n C hA a halen (opnd C a) (P2.opnd_eq n C hA a halen) b
      omega
    obtain ⟨m0, hm0, hw0, hg0⟩ := mixing_on_junk_path_witness G C hA g hg _ (hbig 0) hr0
      (Finset.nonempty_iff_ne_empty.mpr hs.1)
    obtain ⟨m1, hm1, hw1, hg1⟩ := mixing_on_junk_path_witness G C hA h hh _ (hbig 1) hr1
      (Finset.nonempty_iff_ne_empty.mpr hs.2)
    have hneq : m0 ≠ m1 := by
      intro heq
      subst m1
      have hother : P2.OrR n C (opnd C a 1) (n + g) := hw1.trans hg0
      exact top_not_both_junk G C hA g hg a ha 0 hr0 (by simpa using hother)
    have hm0O : m0 ∉ O := fun hk => hO m0 hk g hg hg0
    have hm1O : m1 ∉ O := fun hk => hO m1 hk h hh hg1
    have hsub : ({m0, m1} : Finset ℕ) ⊆ (orN G C \ lam G C) \ O := by
      intro m hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl
      · exact Finset.mem_sdiff.mpr ⟨mixing_subset_outside_lambda G C hm0, hm0O⟩
      · exact Finset.mem_sdiff.mpr ⟨mixing_subset_outside_lambda G C hm1, hm1O⟩
    have hcard := Finset.card_le_card hsub
    have hp : ({m0, m1} : Finset ℕ).card = 2 := by simp [hneq]
    omega

end PEqualNP.Outside.L_meta_1477.OneJunk

namespace PEqualNP.Outside.L_meta_1477.OrdinaryMaskReaders

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk

lemma mixing_support_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (m : ℕ) (hm : m ∈ mixing G C) :
    (orIn n C (n + m)).Nonempty := by
  classical
  have hm0 := (Finset.mem_filter.mp hm).1
  have hxor := (Finset.mem_filter.mp hm).2
  have hf : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using hm0
  have hin := P2.opnd_eq n C hA m hf.1
  have hlt := P2.opnd_lt n C hA m hf.1 (opnd C m) hin
  have hx : ∃ b : Fin 2, (orIn n C (opnd C m b)).Nonempty := by
    by_cases h0 : orIn n C (opnd C m 0) = ∅
    · refine ⟨1, Finset.nonempty_iff_ne_empty.mpr ?_⟩
      intro h1
      exact hxor (propext ⟨fun _ => h1, fun _ => h0⟩)
    · exact ⟨0, Finset.nonempty_iff_ne_empty.mpr h0⟩
  obtain ⟨b, v, hv⟩ := hx
  refine ⟨v, (P1.orIn_gate C m v).mpr ⟨hf.1, hf.2.1, opnd C m b, ?_, hlt b, hv⟩⟩
  rw [hin]
  fin_cases b <;> simp

lemma shared_reader_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2) (c : Fin n)
    (hc : c ∈ side (n := n) C a (1 - b))
    (m : ℕ) (hm : m < C.gates.length)
    (hpath : P2.OrR n C (opnd C a b) (n + m)) :
    ∀ p ∈ orIn n C (n + m), G.Adj c p := by
  have hA := P2.ao_of n C hL.1
  have hal := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp ha).1
  have hb := P2.opnd_lt n C hA a hal (opnd C a) (P2.opnd_eq n C hA a hal) b
  have hsub := orIn_subset_of_orR C hA _ _ (hb.trans (by omega)) (by omega) hpath
  have hcross := (P1.S90.top_facts G C hG hL a ha).2.1
  intro p hp
  have hp := hsub hp
  rcases P2.fin2_sub b with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0] at hp
    rw [h1] at hc
    exact (hcross p hp c hc).symm
  · rw [h0] at hp
    rw [h1] at hc
    exact hcross c hc p hp

lemma adjacent_readers_two_credits {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C)
    (g₀ g₁ : ℕ) (hg₀ : g₀ ∈ junk G C) (hg₁ : g₁ ∈ junk G C)
    (a₀ a₁ : ℕ) (ha₀ : a₀ ∈ tops G C) (ha₁ : a₁ ∈ tops G C)
    (b₀ b₁ : Fin 2) (c₀ c₁ : Fin n) (hc₀₁ : G.Adj c₀ c₁)
    (hc₀ : c₀ ∈ side (n := n) C a₀ (1 - b₀))
    (hc₁ : c₁ ∈ side (n := n) C a₁ (1 - b₁))
    (hpath₀ : P2.OrR n C (opnd C a₀ b₀) (n + g₀))
    (hpath₁ : P2.OrR n C (opnd C a₁ b₁) (n + g₁))
    (hne₀ : (side (n := n) C a₀ b₀).Nonempty)
    (hne₁ : (side (n := n) C a₁ b₁).Nonempty)
    (O : Finset ℕ)
    (hO : ∀ k ∈ O, ∀ d ∈ junk G C, ¬ P2.OrR n C (n + k) (n + d)) :
    2 ≤ ((orN G C \ lam G C) \ O).card := by
  classical
  have hA := P2.ao_of n C hL.1
  have hbig (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2) :
      opnd C a b < n + C.gates.length := by
    have hal := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp ha).1
    have hb := P2.opnd_lt n C hA a hal (opnd C a) (P2.opnd_eq n C hA a hal) b
    omega
  obtain ⟨m₀, hm₀, hp₀, hmg₀⟩ := mixing_on_junk_path_witness G C hA g₀ hg₀ _
    (hbig a₀ ha₀ b₀) hpath₀ hne₀
  obtain ⟨m₁, hm₁, hp₁, hmg₁⟩ := mixing_on_junk_path_witness G C hA g₁ hg₁ _
    (hbig a₁ ha₁ b₁) hpath₁ hne₁
  have hmlen (m : ℕ) (hm : m ∈ mixing G C) : m < C.gates.length := by
    have h := (Finset.mem_filter.mp hm).1
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at h
    exact h.1
  have hneq : m₀ ≠ m₁ := by
    intro he
    subst m₁
    obtain ⟨p, hp⟩ := mixing_support_nonempty G C hA m₀ hm₀
    have h0 := shared_reader_adj G hG C hL a₀ ha₀ b₀ c₀ hc₀ m₀ (hmlen _ hm₀) hp₀ p hp
    have h1 := shared_reader_adj G hG C hL a₁ ha₁ b₁ c₁ hc₁ m₀ (hmlen _ hm₁) hp₁ p hp
    have hcp := hcolor c₀ p h0
    have hdp := hcolor c₁ p h1
    have hcd := hcolor c₀ c₁ hc₀₁
    have hc0 := (color c₀).isLt
    have hc1 := (color c₁).isLt
    have hpp := (color p).isLt
    simp only [ne_eq, Fin.ext_iff] at hcp hdp hcd
    omega
  have hsub : ({m₀, m₁} : Finset ℕ) ⊆ (orN G C \ lam G C) \ O := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact Finset.mem_sdiff.mpr ⟨mixing_subset_outside_lambda G C hm₀,
        fun hk => hO _ hk g₀ hg₀ hmg₀⟩
    · exact Finset.mem_sdiff.mpr ⟨mixing_subset_outside_lambda G C hm₁,
        fun hk => hO _ hk g₁ hg₁ hmg₁⟩
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_pair hneq] using hcard

end PEqualNP.Outside.L_meta_1477.OrdinaryMaskReaders

namespace PEqualNP.Outside.L_meta_1477.OrdinaryMaskReaders

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma common_neighbor_certificate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (c b p q : Fin n) (hc : c ∈ A) (hb : b ∈ B)
    (hcm : CleanMask G A B c) (hbm : CleanMask G A B b)
    (hcq : c ≠ q) (hcp : G.Adj c p) (hqp : G.Adj q p)
    (hqm : CleanMask G A B q) (owned : Finset (Sym2 (Fin n)))
    (howned : s(c, p) ∈ owned) : EligibleBoundary.Certificate G A B owned := by
  have hbound := BoundaryProduct.opposite_support_boundary_bipartite G hG color hcolor
    A B hA hB c b p q hc hb hcm hbm hcq hcp hqp hqm
  refine ⟨⟨c, (mem_centers_iff G A B c).mpr ⟨Finset.mem_union_left _ hc, hcm⟩,
    p, ?_, howned⟩, b, ?_⟩
  · simpa only [neighbors, ite_eq_left hc] using hbound.1
  · exact BoundaryProduct.boundary_mask_cover G hG A B hA hB c b p hc hb hcm hbm hbound.2 _ howned

lemma shared_reader_owned {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C)
    (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2) (c : Fin n)
    (hc : c ∈ side (n := n) C a (1 - b))
    (m : ℕ) (hm : m < C.gates.length)
    (hpath : P2.OrR n C (opnd C a b) (n + m)) :
    ∀ p ∈ orIn n C (n + m), s(c, p) ∈ PEqualNP.TopForm.starEdges G C := by
  have hal := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp ha).1
  have hb := P2.opnd_lt n C hA a hal (opnd C a) (P2.opnd_eq n C hA a hal) b
  have hsub := orIn_subset_of_orR C hA _ _ (hb.trans (by omega)) (by omega) hpath
  intro p hp
  have hp := hsub hp
  apply Finset.mem_biUnion.mpr
  refine ⟨a, ha, ?_⟩
  rcases P2.fin2_sub b with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0] at hp
    rw [h1] at hc
    exact Finset.mem_image.mpr ⟨(p, c), Finset.mem_product.mpr ⟨hp, hc⟩, Sym2.eq_swap⟩
  · rw [h0] at hp
    rw [h1] at hc
    exact Finset.mem_image.mpr ⟨(c, p), Finset.mem_product.mpr ⟨hc, hp⟩, rfl⟩

lemma product_path_mask {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C)
    (A B : Finset (Fin n)) (g : ℕ)
    (hprod : ∀ x : Fin n → Bool, gateVal n C g x = productValue A B x)
    (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2)
    (hr : P2.OrR n C (opnd C a b) (n + g)) :
    ∀ c ∈ side (n := n) C a (1 - b), CleanMask G A B c := by
  intro c hc x hx hxc
  have ha0 := (P2.mem_filter' _ _ _ _).mp ha
  have hal := Finset.mem_range.mp ha0.1
  have hin := P2.opnd_eq n C hA a hal
  have hlt := P2.opnd_lt n C hA a hal (opnd C a) hin
  have hp := (P2.mem_orIn n C hA _ ((hlt (1 - b)).trans (by omega)) c).mp hc
  have hgf : P2.W n C x (n + g) = true := (hprod x).trans hx
  have hout := ha0.2.2 x (P2.sem_mixed n C hA a hal ha0.2.1 (opnd C a) hin g b c hr hp x hgf hxc)
  simpa only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] using hout

lemma shared_mixing_certificate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C)
    (A B : Finset (Fin n)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (c b d : Fin n) (hc : c ∈ A) (hb : b ∈ B)
    (hcm : CleanMask G A B c) (hbm : CleanMask G A B b) (hcd : c ≠ d)
    (g : ℕ) (hprod : ∀ x : Fin n → Bool, gateVal n C g x = productValue A B x)
    (a₀ a₁ : ℕ) (ha₀ : a₀ ∈ tops G C) (ha₁ : a₁ ∈ tops G C)
    (b₀ b₁ : Fin 2) (hc₀ : c ∈ side (n := n) C a₀ (1 - b₀))
    (hc₁ : d ∈ side (n := n) C a₁ (1 - b₁))
    (m : ℕ) (hm : m ∈ mixing G C)
    (hp₀ : P2.OrR n C (opnd C a₀ b₀) (n + m))
    (hp₁ : P2.OrR n C (opnd C a₁ b₁) (n + m))
    (hmg : P2.OrR n C (n + m) (n + g)) :
    EligibleBoundary.Certificate G A B (PEqualNP.TopForm.starEdges G C) := by
  have hAO := P2.ao_of n C hL.1
  have hmlen : m < C.gates.length := by
    have h := (Finset.mem_filter.mp hm).1
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at h
    exact h.1
  obtain ⟨p, hp⟩ := mixing_support_nonempty G C hAO m hm
  have hcp := shared_reader_adj G hG C hL a₀ ha₀ b₀ c hc₀ m hmlen hp₀ p hp
  have hdp := shared_reader_adj G hG C hL a₁ ha₁ b₁ d hc₁ m hmlen hp₁ p hp
  have hown := shared_reader_owned G C hAO a₀ ha₀ b₀ c hc₀ m hmlen hp₀ p hp
  have hdm := product_path_mask G C hAO A B g hprod a₁ ha₁ b₁ (hp₁.trans hmg) d hc₁
  exact common_neighbor_certificate G hG color hcolor A B hA hB c b p d hc hb hcm hbm
    hcd hcp hdp hdm _ hown

lemma uncredited_ordinary_centers_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (R : Finset (Fin n))
    (hreader : ∀ c ∈ R, ∃ A B : Finset (Fin n), ∃ d : Fin n, ∃ g a : ℕ, ∃ b : Fin 2,
      2 ≤ A.card ∧ 2 ≤ B.card ∧ c ∈ A ∧ d ∈ B ∧ CleanMask G A B c ∧ CleanMask G A B d ∧
      ¬ EligibleBoundary.Certificate G A B (PEqualNP.TopForm.starEdges G C) ∧
      g ∈ junk G C ∧ (∀ x : Fin n → Bool, gateVal n C g x = productValue A B x) ∧
      a ∈ tops G C ∧ c ∈ side (n := n) C a (1 - b) ∧
      P2.OrR n C (opnd C a b) (n + g) ∧ (side (n := n) C a b).Nonempty)
    (O : Finset ℕ)
    (hO : ∀ k ∈ O, ∀ d ∈ junk G C, ¬ P2.OrR n C (n + k) (n + d)) :
    R.card ≤ ((orN G C \ lam G C) \ O).card := by
  classical
  have hAO := P2.ao_of n C hL.1
  choose A B d g a b hA hB hc hd hcm hdm hnot hg hprod ha hside hpath hne using hreader
  have hw (c : Fin n) (hc : c ∈ R) : opnd C (a c hc) (b c hc) < n + C.gates.length := by
    have hal := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp (ha c hc)).1
    have hb := P2.opnd_lt n C hAO (a c hc) hal (opnd C (a c hc))
      (P2.opnd_eq n C hAO (a c hc) hal) (b c hc)
    omega
  have hex : ∀ c, (hc : c ∈ R) → ∃ m ∈ mixing G C,
      P2.OrR n C (opnd C (a c hc) (b c hc)) (n + m) ∧
      P2.OrR n C (n + m) (n + g c hc) := by
    intro c hc
    exact mixing_on_junk_path_witness G C hAO (g c hc) (hg c hc) _ (hw c hc)
      (hpath c hc) (hne c hc)
  choose m hm hp hmg using hex
  let f : R → ℕ := fun c => m c.val c.property
  have hfmem (c : R) : f c ∈ (orN G C \ lam G C) \ O :=
    Finset.mem_sdiff.mpr ⟨mixing_subset_outside_lambda G C (hm c.val c.property),
      fun hk => hO _ hk _ (hg c.val c.property) (hmg c.val c.property)⟩
  have hinj : Function.Injective f := by
    intro c q heq
    apply Subtype.ext
    by_contra hneq
    apply hnot c.val c.property
    apply shared_mixing_certificate G hG color hcolor C hL
      (A c.val c.property) (B c.val c.property) (hA c.val c.property) (hB c.val c.property)
      c.val (d c.val c.property) q.val (hc c.val c.property) (hd c.val c.property)
      (hcm c.val c.property) (hdm c.val c.property) hneq (g c.val c.property)
      (hprod c.val c.property) (a c.val c.property) (a q.val q.property)
      (ha c.val c.property) (ha q.val q.property) (b c.val c.property) (b q.val q.property)
      (hside c.val c.property) (hside q.val q.property)
      (f c) (hm c.val c.property) (hp c.val c.property) ?_ (hmg c.val c.property)
    simpa only [f, heq] using hp q.val q.property
  have hcard : Fintype.card R ≤ ((orN G C \ lam G C) \ O).card :=
    Finset.card_le_card_of_injOn f (fun c _ => hfmem c)
      (fun c _ q _ heq => hinj heq)
  simpa only [Fintype.card_coe] using hcard

end PEqualNP.Outside.L_meta_1477.OrdinaryMaskReaders

namespace PEqualNP.Outside.L_meta_1477.OrdinaryMaskReaders

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma uncredited_ordinary_mixing_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (R : Finset (Fin n))
    (hreader : ∀ c ∈ R, ∃ A B : Finset (Fin n), ∃ d : Fin n, ∃ g a : ℕ, ∃ b : Fin 2,
      2 ≤ A.card ∧ 2 ≤ B.card ∧ c ∈ A ∧ d ∈ B ∧ CleanMask G A B c ∧ CleanMask G A B d ∧
      ¬ EligibleBoundary.Certificate G A B (PEqualNP.TopForm.starEdges G C) ∧
      g ∈ junk G C ∧ (∀ x : Fin n → Bool, gateVal n C g x = productValue A B x) ∧
      a ∈ tops G C ∧ c ∈ side (n := n) C a (1 - b) ∧
      P2.OrR n C (opnd C a b) (n + g) ∧ (side (n := n) C a b).Nonempty)
    (O : Finset ℕ)
    (hO : ∀ k ∈ O, ∀ d ∈ junk G C, ¬ P2.OrR n C (n + k) (n + d)) :
    R.card ≤ (mixing G C \ O).card := by
  classical
  have hAO := P2.ao_of n C hL.1
  choose A B d g a b hA hB hc hd hcm hdm hnot hg hprod ha hside hpath hne using hreader
  have hw (c : Fin n) (hc : c ∈ R) : opnd C (a c hc) (b c hc) < n + C.gates.length := by
    have hal := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp (ha c hc)).1
    have hb := P2.opnd_lt n C hAO (a c hc) hal (opnd C (a c hc))
      (P2.opnd_eq n C hAO (a c hc) hal) (b c hc)
    omega
  have hex : ∀ c, (hc : c ∈ R) → ∃ m ∈ mixing G C,
      P2.OrR n C (opnd C (a c hc) (b c hc)) (n + m) ∧
      P2.OrR n C (n + m) (n + g c hc) := by
    intro c hc
    exact mixing_on_junk_path_witness G C hAO (g c hc) (hg c hc) _ (hw c hc)
      (hpath c hc) (hne c hc)
  choose m hm hp hmg using hex
  let f : R → ℕ := fun c => m c.val c.property
  have hfmem (c : R) : f c ∈ mixing G C \ O :=
    Finset.mem_sdiff.mpr ⟨hm c.val c.property,
      fun hk => hO _ hk _ (hg c.val c.property) (hmg c.val c.property)⟩
  have hinj : Function.Injective f := by
    intro c q heq
    apply Subtype.ext
    by_contra hneq
    apply hnot c.val c.property
    apply shared_mixing_certificate G hG color hcolor C hL
      (A c.val c.property) (B c.val c.property) (hA c.val c.property) (hB c.val c.property)
      c.val (d c.val c.property) q.val (hc c.val c.property) (hd c.val c.property)
      (hcm c.val c.property) (hdm c.val c.property) hneq (g c.val c.property)
      (hprod c.val c.property) (a c.val c.property) (a q.val q.property)
      (ha c.val c.property) (ha q.val q.property) (b c.val c.property) (b q.val q.property)
      (hside c.val c.property) (hside q.val q.property)
      (f c) (hm c.val c.property) (hp c.val c.property) ?_ (hmg c.val c.property)
    simpa only [f, heq] using hp q.val q.property
  have hcard : Fintype.card R ≤ (mixing G C \ O).card :=
    Finset.card_le_card_of_injOn f (fun c _ => hfmem c)
      (fun c _ q _ heq => hinj heq)
  simpa only [Fintype.card_coe] using hcard


lemma two_ne_not_mixing {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (m : ℕ) (hm : m < C.gates.length)
    (htwo : P1.TwoNe (gateAt C) (orIn n C) m) : m ∉ mixing G C := by
  intro hmixed
  have hx := (Finset.mem_filter.mp hmixed).2
  have hin := P2.opnd_eq n C hA m hm
  obtain ⟨w, hw, z, hz, hne, hwne, hzne⟩ := htwo
  have hw01 : w = opnd C m 0 ∨ w = opnd C m 1 := by
    simpa only [hin, List.mem_cons, List.not_mem_nil, or_false] using hw
  have hz01 : z = opnd C m 0 ∨ z = opnd C m 1 := by
    simpa only [hin, List.mem_cons, List.not_mem_nil, or_false] using hz
  have hnon : (orIn n C (opnd C m 0)).Nonempty ∧ (orIn n C (opnd C m 1)).Nonempty := by
    rcases hw01 with rfl | rfl <;> rcases hz01 with rfl | rfl
    · exact (hne rfl).elim
    · exact ⟨hwne, hzne⟩
    · exact ⟨hzne, hwne⟩
    · exact (hne rfl).elim
  apply hx
  apply propext
  constructor
  · intro h
    exact (hnon.1.ne_empty h).elim
  · intro h
    exact (hnon.2.ne_empty h).elim

end PEqualNP.Outside.L_meta_1477.OrdinaryMaskReaders

namespace PEqualNP.Outside.L_meta_1477.FilterConeCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge OneJunk

lemma filtered_rt_nonmixing {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C)
    (root : ℕ) (hroot : root < n + C.gates.length) (c : Fin n) (R : Finset (Fin n))
    (hstop : ∀ k ∈ lam G C, P2.OrR n C root (n + k) → (orIn n C (n + k) ∩ R).card ≤ 1) :
    ∃ B : Finset ℕ, B ⊆ orN G C \ lam G C ∧ B ⊆ OrConeCredit.gates (n := n) C {root} ∧
      Disjoint B (mixing G C) ∧ (orIn n C root ∩ R).card ≤ B.card + 1 := by
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
  let Z := (lam G C).filter fun k => P2.OrR n C root (n + k)
  have hZ : ∀ k ∈ Z, f (n + k) ⊆ f root →
      (∀ v ∈ f (n + k), s(c, v) ∈ (∅ : Finset (Sym2 (Fin n)))) ∨ (f (n + k)).card ≤ 1 := by
    intro k hk _
    exact Or.inr (hstop k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2)
  obtain ⟨B, hBstop, hB, hcount⟩ := P1.top_step2 n (gateAt C) hlen hback f hf1 hf2 hf3
    Z root c ∅ hZ
  have hBfacts : ∀ k ∈ B, k ∈ orN G C \ lam G C ∧ k ∈ OrConeCredit.gates (n := n) C {root} := by
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
    have hnl : k ∉ lam G C := by
      intro hl
      exact Finset.disjoint_left.mp hBstop (Finset.mem_filter.mpr ⟨hl, hpath2⟩) hk
    refine ⟨Finset.mem_sdiff.mpr ⟨hkN, hnl⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklen, hop, root, by simp, hpath2⟩
  have hnm : Disjoint B (mixing G C) := by
    apply Finset.disjoint_left.mpr
    intro k hk hkm
    obtain ⟨hop, htwo, _, _, _⟩ := hB k hk
    have hklen : k < C.gates.length := by
      have hf := (Finset.mem_filter.mp hkm).1
      simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hf
      exact hf.1
    obtain ⟨w, hw, z, hz, hne, hwne, hzne⟩ := htwo
    have htwo' : P1.TwoNe (gateAt C) (orIn n C) k :=
      ⟨w, hw, z, hz, hne, hwne.mono Finset.inter_subset_left, hzne.mono Finset.inter_subset_left⟩
    exact OrdinaryMaskReaders.two_ne_not_mixing G C hA k hklen htwo' hkm
  refine ⟨B, fun k hk => (hBfacts k hk).1, fun k hk => (hBfacts k hk).2, hnm, ?_⟩
  have hinj : Function.Injective (fun v : Fin n => s(c, v)) := by
    intro u v he
    rcases Sym2.eq_iff.mp he with ⟨_, huv⟩ | ⟨hcv, huc⟩
    · exact huv
    · exact huc.trans hcv
  simpa only [Finset.sdiff_empty, Finset.card_image_of_injective _ hinj] using hcount

end PEqualNP.Outside.L_meta_1477.FilterConeCount

namespace PEqualNP.Outside.L_meta_1477.EligibleFilterCount

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping MaskGraphSupport MaskGraphNetwork CommonFilterBudget

lemma eligible_centers_count_nonmixing {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (filterRoot : ℕ)
    (hroot : filterRoot < n + C.gates.length)
    (R : Finset (Fin n)) (hR : R ⊆ orIn n C filterRoot)
    (hactive : ∀ c ∈ R, ∃ A B : Finset (Fin n), ∃ b : Fin n,
      2 ≤ A.card ∧ 2 ≤ B.card ∧ c ∈ A ∧ b ∈ B ∧
      CleanMask G A B c ∧ CleanMask G A B b ∧
      (∀ q ∈ orIn n C filterRoot, CleanMask G A B q) ∧
      ¬ EligibleBoundary.Certificate G A B (PEqualNP.TopForm.starEdges G C)) :
    ∃ D : Finset ℕ, D ⊆ orN G C \ lam G C ∧ D ⊆ OrConeCredit.gates (n := n) C {filterRoot} ∧
      Disjoint D (mixing G C) ∧ R.card ≤ D.card + 1 := by
  classical
  by_cases hne : R.Nonempty
  · obtain ⟨c₀, hc₀⟩ := hne
    have hstop : ∀ k ∈ lam G C, P2.OrR n C filterRoot (n + k) →
        (orIn n C (n + k) ∩ R).card ≤ 1 := by
      intro k hk hr
      by_cases hs : (orIn n C (n + k) ∩ R).card ≤ 1
      · exact hs
      · have hlarge : 2 ≤ (orIn n C (n + k)).card :=
          (show 2 ≤ (orIn n C (n + k) ∩ R).card by omega).trans (Finset.card_le_card Finset.inter_subset_left)
        obtain ⟨c, hc⟩ := Finset.card_pos.mp (show 0 < (orIn n C (n + k) ∩ R).card by omega)
        obtain ⟨hck, hcR⟩ := Finset.mem_inter.mp hc
        obtain ⟨A, B, b, hA, hB, hcA, hbB, hcm, hbm, hmask, hnot⟩ := hactive c hcR
        have hcert := EligibleBoundary.lambda_certificate
          G hG color hcolor C hL filterRoot hroot A B hA hB c b hcA hbB hcm hbm hmask k hk hr hck hlarge
        exact (hnot hcert).elim
    obtain ⟨D, hD, hcone, hnm, hcard⟩ := FilterConeCount.filtered_rt_nonmixing G C hL filterRoot hroot c₀ R hstop
    exact ⟨D, hD, hcone, hnm, by simpa only [Finset.inter_eq_right.mpr hR] using hcard⟩
  · refine ⟨∅, Finset.empty_subset _, Finset.empty_subset _, by simp, ?_⟩
    have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he]

end PEqualNP.Outside.L_meta_1477.EligibleFilterCount

namespace PEqualNP.Outside.L_meta_1477.OrdinaryFilterBudget

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping MaskGraphSupport MaskGraphNetwork CommonFilterBudget

 def OrdinaryActive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (c : Fin n) : Prop :=
    ∃ A B : Finset (Fin n), ∃ d : Fin n, ∃ g a : ℕ, ∃ b : Fin 2,
      2 ≤ A.card ∧ 2 ≤ B.card ∧ c ∈ A ∧ d ∈ B ∧ CleanMask G A B c ∧ CleanMask G A B d ∧
      ¬ EligibleBoundary.Certificate G A B (PEqualNP.TopForm.starEdges G C) ∧
      g ∈ junk G C ∧ (∀ x : Fin n → Bool, gateVal n C g x = productValue A B x) ∧
      a ∈ tops G C ∧ c ∈ side (n := n) C a (1 - b) ∧
      P2.OrR n C (opnd C a b) (n + g) ∧ (side (n := n) C a b).Nonempty

lemma live_no_junk {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k)) :
    ∀ k ∈ liveIndices G C center root, ∀ d ∈ junk G C, ¬ P2.OrR n C (n + k) (n + d) := by
  classical
  intro k hk d hd
  obtain ⟨kk, _, hkk⟩ := Finset.mem_image.mp hk
  have hkMask : k ∈ MaskGraphSupport.gates C center root := hkk ▸ kk.property
  obtain ⟨c, hc⟩ := (Finset.mem_filter.mp hkMask).2.2
  obtain ⟨hdlen, hdop, _⟩ := (P1.junk_iff G C d).mp hd
  exact assoc_no_and C center root hpure c _ hc d hdlen hdop

lemma ordinary_mask_budget {n m t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k))
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
    (grp : Fin m → Fin t)
    (hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v))
    (boundary : Finset (Fin t))
    (hboundary : ∀ i, grp i ∈ boundary → ∃ j, grp j = grp i ∧
      ∃ u ∈ orIn n C (root j), s(center j, u) ∈ PEqualNP.TopForm.starEdges G C)
    (S : Finset (Fin n)) (hreader : ∀ c ∈ S, OrdinaryActive G C c) :
    (edges C center root \ PEqualNP.TopForm.starEdges G C).card + boundary.card + S.card ≤
      (orN G C \ lam G C).card + t := by
  classical
  let L := liveIndices G C center root
  let M := mixing G C \ L
  have hScard : S.card ≤ M.card := OrdinaryMaskReaders.uncredited_ordinary_mixing_count
    G hG color hcolor C hL S hreader L (live_no_junk G C center root hpure)
  have hLsub := live_indices_subset G hG C hL center root hbound hpure hclean
  have hMsub : M ⊆ orN G C \ lam G C :=
    fun _ h => OneJunk.mixing_subset_outside_lambda G C (Finset.mem_sdiff.mp h).1
  have hdis : Disjoint L M := Finset.disjoint_left.mpr (fun _ hL hM => (Finset.mem_sdiff.mp hM).2 hL)
  have hsum := Finset.card_le_card (Finset.union_subset hLsub hMsub)
  rw [Finset.card_union_of_disjoint hdis] at hsum
  have hcount := MaskGraphBoundary.pruned_grouped_credit G hG C hL center root
    hbound hpure hclean (PEqualNP.TopForm.starEdges G C) grp hgroup boundary hboundary
  have hLcard := live_indices_card G C center root
  change L.card = _ at hLcard
  omega

lemma common_filter_ordinary_budget {n m t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C)
    (center : Fin m → Fin n) (root : Fin m → ℕ)
    (hbound : ∀ i, root i < n + C.gates.length)
    (hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k))
    (hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v)
    (grp : Fin m → Fin t)
    (hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v))
    (boundary : Finset (Fin t))
    (hboundary : ∀ i, grp i ∈ boundary → ∃ j, grp j = grp i ∧
      ∃ u ∈ orIn n C (root j), s(center j, u) ∈ PEqualNP.TopForm.starEdges G C)
    (filterRoot : ℕ) (hfilter : filterRoot < n + C.gates.length)
    (hsmall : ∀ i, (orIn n C filterRoot ∩ orIn n C (root i)).card ≤ 1)
    (R : Finset (Fin n)) (hR : R ⊆ orIn n C filterRoot)
    (hactive : ∀ c ∈ R, ∃ A B : Finset (Fin n), ∃ b : Fin n,
      2 ≤ A.card ∧ 2 ≤ B.card ∧ c ∈ A ∧ b ∈ B ∧
      CleanMask G A B c ∧ CleanMask G A B b ∧
      (∀ q ∈ orIn n C filterRoot, CleanMask G A B q) ∧
      ¬ EligibleBoundary.Certificate G A B (PEqualNP.TopForm.starEdges G C))
    (S : Finset (Fin n)) (hreader : ∀ c ∈ S, OrdinaryActive G C c) :
    (edges C center root \ PEqualNP.TopForm.starEdges G C).card + boundary.card + R.card + S.card ≤
      (orN G C \ lam G C).card + t + 1 := by
  classical
  obtain ⟨D, hD, hDcone, hDmix, hRcard⟩ := EligibleFilterCount.eligible_centers_count_nonmixing
    G hG color hcolor C hL filterRoot hfilter R hR hactive
  let L := liveIndices G C center root
  let M := mixing G C \ L
  have hScard : S.card ≤ M.card := OrdinaryMaskReaders.uncredited_ordinary_mixing_count
    G hG color hcolor C hL S hreader L (live_no_junk G C center root hpure)
  have hLsub := live_indices_subset G hG C hL center root hbound hpure hclean
  have hMsub : M ⊆ orN G C \ lam G C :=
    fun _ h => OneJunk.mixing_subset_outside_lambda G C (Finset.mem_sdiff.mp h).1
  have hLD : Disjoint L D := by
    apply Finset.disjoint_left.mpr
    intro k hkL hkD
    obtain ⟨kk, _, hkk⟩ := Finset.mem_image.mp hkL
    have hkMask : k ∈ MaskGraphSupport.gates C center root := hkk ▸ kk.property
    exact Finset.disjoint_left.mp
      (MaskFilterCommon.filter_cone_disjoint C (P2.ao_of n C hL.1) center root hbound filterRoot hfilter hsmall)
      (hDcone hkD) hkMask
  have hLM : Disjoint L M := Finset.disjoint_left.mpr (fun _ hL hM => (Finset.mem_sdiff.mp hM).2 hL)
  have hDM : Disjoint D M := hDmix.mono_right Finset.sdiff_subset
  have hdis : Disjoint (L ∪ D) M := Finset.disjoint_union_left.mpr ⟨hLM, hDM⟩
  have hsum := Finset.card_le_card (Finset.union_subset (Finset.union_subset hLsub hD) hMsub)
  rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint hLD] at hsum
  have hcount := MaskGraphBoundary.pruned_grouped_credit G hG C hL center root
    hbound hpure hclean (PEqualNP.TopForm.starEdges G C) grp hgroup boundary hboundary
  have hLcard := live_indices_card G C center root
  change L.card = _ at hLcard
  omega

end PEqualNP.Outside.L_meta_1477.OrdinaryFilterBudget

namespace PEqualNP.Outside.L_meta_1477.GeneralDirtyPairs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge OneJunk

def JointClean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g h : ℕ) : Prop :=
  ∀ x : Fin n → Bool, gateVal n C g x = true → gateVal n C h x = true → graphFun G ∅ x = true

end PEqualNP.Outside.L_meta_1477.GeneralDirtyPairs

namespace PEqualNP.Outside.L_meta_1477.FirstLayerEffective

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

noncomputable def effectiveCenters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) : Finset (Fin n) := by
  classical
  exact (wmax G C j).filter fun c => ∃ u v : Fin n, G.Adj u v ∧ (c = u ∨ c = v) ∧
    gateVal n C j (pairInput u v) = true

end PEqualNP.Outside.L_meta_1477.FirstLayerEffective

namespace PEqualNP.Outside.L_meta_1477.ActualFilterCoverage

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge OneJunk GeneralDirtyPairs

lemma top_pair_raw_mask_or_joint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (hT : TopForm G C)
    (g : ℕ) (hg : g ∈ junk G C) (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2)
    (hreach : OrReaches n C (opnd C a b) g) (u v : Fin n)
    (hfire : gateVal n C a (pairInput u v) = true)
    (hgf : gateVal n C g (pairInput u v) = true) :
    (∃ c : Fin n, c ∈ side (n := n) C a (1 - b) ∧ c ∈ wmax G C g ∧ (c = u ∨ c = v)) ∨
      (∃ h : ℕ, h ∈ junk G C ∧ g ≠ h ∧
        gateVal n C h (pairInput u v) = true ∧ JointClean G C g h) := by
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
    rcases P2.fin2_sub b with ⟨_, hb⟩ | ⟨_, hb⟩
    · simpa only [hb] using hvals.2
    · simpa only [hb] using hvals.1
  obtain ⟨w, hpath, hleaf, hw⟩ :=
    P2.orR_leaf_true n C hA (pairInput u v) _ (hbig (1 - b)) hoppt
  rcases hleaf with hwlt | ⟨h, rfl, hhlen, hhop⟩
  · let c : Fin n := ⟨w, hwlt⟩
    left
    refine ⟨c, (P2.mem_orIn n C hA _ (hbig (1 - b)) c).mpr hpath, ?_, ?_⟩
    · apply (P2.mem_filter' _ _ _ _).mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro x hx hxc
      exact ha0.2.2 x (P2.sem_mixed n C hA a halen ha0.2.1 (opnd C a)
        hin g b c hr hpath x hx hxc)
    · rw [P2.W_input n C (pairInput u v) w hwlt] at hw
      simpa only [pairInput, decide_eq_true_eq] using hw
  · have hcone := operand_orR_inCone C hA a halen (1 - b) h hpath
    have hh : h ∈ junk G C := (P1.junk_iff G C h).mpr
      ⟨hhlen, hhop, fun hb => hT h hhlen a halen hhop hb ha0.2.1 hcone⟩
    have hne : g ≠ h := by
      intro he
      subst h
      exact top_not_both_junk G C hA g hg a ha b hr hpath
    right
    refine ⟨h, hh, hne, hw, ?_⟩
    intro x hxg hxh
    have hleft := P2.orR_mono n C hA x _ _ hr hxg
    have hright := P2.orR_mono n C hA x _ _ hpath hxh
    have hboth := P2.fin2_both (fun c => P2.W n C x (opnd C a c) = true) b hleft hright
    apply ha0.2.2 x
    change P2.W n C x (n + a) = true
    rw [P2.W_and n C x a halen ha0.2.1 _ _ hin (hlt 0) (hlt 1), hboth.1, hboth.2]
    rfl

lemma top_path_common_wmax {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hA : P2.AO n C) (a : ℕ) (ha : a ∈ tops G C)
    (b : Fin 2) (g : ℕ) (hr : P2.OrR n C (opnd C a b) (n + g)) :
    ∀ c ∈ side (n := n) C a (1 - b), c ∈ wmax G C g := by
  intro c hc
  have ha0 := (P2.mem_filter' _ _ _ _).mp ha
  have hal := Finset.mem_range.mp ha0.1
  have hin := P2.opnd_eq n C hA a hal
  have hlt := P2.opnd_lt n C hA a hal (opnd C a) hin
  have hp := (P2.mem_orIn n C hA _ ((hlt (1 - b)).trans (by omega)) c).mp hc
  apply (P2.mem_filter' _ _ _ _).mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro x hx hxc
  exact ha0.2.2 x (P2.sem_mixed n C hA a hal ha0.2.1 (opnd C a) hin g b c hr hp x hx hxc)

lemma off_star_common_filter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hnojoint : ∀ g ∈ junk G C, ∀ h ∈ junk G C, g ≠ h → ∀ u v : Fin n,
      gateVal n C g (pairInput u v) = true → gateVal n C h (pairInput u v) = true →
      ¬ JointClean G C g h)
    (u v : Fin n) (huv : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C,
      P2.OrR n C (opnd C a b) (n + g) ∧ gateVal n C g (pairInput u v) = true ∧
      ∃ c ∈ side (n := n) C a (1 - b), c ∈ FirstLayerEffective.effectiveCenters G C g ∧
        (c = u ∨ c = v) ∧
        (∀ d ∈ side (n := n) C a (1 - b), d ∈ wmax G C g) := by
  classical
  obtain ⟨a, ha, b, g, hg, hfire, hreach, hgf⟩ := P1.S90.off_star G C hL hT u v huv
  have hA := P2.ao_of n C hL.1
  have hal := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp ha).1
  have hlt := P2.opnd_lt n C hA a hal (opnd C a) (P2.opnd_eq n C hA a hal) b
  have hr := P2.orReaches_orR n C _ (hlt.trans (by omega)) g hreach
  rcases top_pair_raw_mask_or_joint G C hA hT g hg a ha b hreach u v hfire hgf with hm | hj
  · obtain ⟨c, hc, hcm, hcv⟩ := hm
    have hadj : G.Adj u v := (G.mem_edgeSet).mp
      ((SimpleGraph.mem_edgeFinset).mp (Finset.mem_sdiff.mp huv).1)
    have heff : c ∈ FirstLayerEffective.effectiveCenters G C g :=
      Finset.mem_filter.mpr ⟨hcm, u, v, hadj, hcv, hgf⟩
    exact ⟨a, ha, b, g, hg, hr, hgf, c, hc, heff, hcv, top_path_common_wmax G C hA a ha b g hr⟩
  · obtain ⟨h, hh, hgh, hhf, hj⟩ := hj
    exact (hnojoint g hg h hh hgh u v hgf hhf hj).elim

lemma two_junk_common_filter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (g h : ℕ) (hjunk : junk G C = {g, h})
    (hnojoint : ∀ u v : Fin n, gateVal n C g (pairInput u v) = true →
      gateVal n C h (pairInput u v) = true → ¬ JointClean G C g h)
    (u v : Fin n) (huv : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ i : Fin 2,
      P2.OrR n C (opnd C a b) (n + (![g, h] i)) ∧
      gateVal n C (![g, h] i) (pairInput u v) = true ∧
      ∃ c ∈ side (n := n) C a (1 - b),
        c ∈ FirstLayerEffective.effectiveCenters G C (![g, h] i) ∧ (c = u ∨ c = v) ∧
        (∀ d ∈ side (n := n) C a (1 - b), d ∈ wmax G C (![g, h] i)) := by
  have hn : ∀ j ∈ junk G C, ∀ k ∈ junk G C, j ≠ k → ∀ u v : Fin n,
      gateVal n C j (pairInput u v) = true → gateVal n C k (pairInput u v) = true →
      ¬ JointClean G C j k := by
    intro j hj k hk hjk u v hjf hkf hclean
    rw [hjunk] at hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hk
    rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
    · exact hjk rfl
    · exact hnojoint u v hjf hkf hclean
    · exact hnojoint u v hkf hjf (fun x hxg hxh => hclean x hxh hxg)
    · exact hjk rfl
  obtain ⟨a, ha, b, j, hj, hr, hjf, c, hc, hce, hcv, hcommon⟩ :=
    off_star_common_filter G C hL hT hn u v huv
  rw [hjunk] at hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact ⟨a, ha, b, 0, hr, hjf, c, hc, hce, hcv, hcommon⟩
  · have he := Finset.mem_singleton.mp hj
    subst j
    exact ⟨a, ha, b, 1, hr, hjf, c, hc, hce, hcv, hcommon⟩

end PEqualNP.Outside.L_meta_1477.ActualFilterCoverage

namespace PEqualNP.Outside.L_meta_1477.OrdinaryFamilyCoverage

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma no_centreless_mask_cover {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    (hcent : centreless G C = ∅)
    (g : Fin t → ℕ) (hgj : ∀ i, g i ∈ junk G C) (honto : ∀ j ∈ junk G C, ∃ i, g i = j)
    (hpure : ∀ i, ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C (g i) b) (n + k))
    (hdis : ∀ i, Disjoint (side (n := n) C (g i) 0) (side C (g i) 1))
    (hA : ∀ i, 2 ≤ (side (n := n) C (g i) 0).card)
    (hB : ∀ i, 2 ≤ (side (n := n) C (g i) 1).card)
    (htwo : ∀ i, (cleanCenters G (side (n := n) C (g i) 0) (side C (g i) 1)).card = 2)
    (hnojoint : ∀ j ∈ junk G C, ∀ k ∈ junk G C, j ≠ k → ∀ u v : Fin n,
      gateVal n C j (pairInput u v) = true → gateVal n C k (pairInput u v) = true →
      ¬ GeneralDirtyPairs.JointClean G C j k) :
    ∃ S : Finset (Fin n), (∀ c ∈ S, OrdinaryFilterBudget.OrdinaryActive G C c) ∧
      ∀ e ∈ Ustar G C, e ∉ PEqualNP.TopForm.starEdges G C ∧
        ∃ i : Fin t, ∃ c ∈ cleanCenters G (side (n := n) C (g i) 0) (side C (g i) 1),
          e ∈ MaskGrouping.starEdges (side (n := n) C (g i) 0) (side C (g i) 1) c ∧
          (i ∈ EligibleFamilyBudget.boundaryProducts G C
            (fun i => side (n := n) C (g i) 0) (fun i => side C (g i) 1) ∨ c ∈ S) := by
  classical
  let A := fun i => side (n := n) C (g i) 0
  let B := fun i => side (n := n) C (g i) 1
  let S := Finset.univ.filter (OrdinaryFilterBudget.OrdinaryActive G C)
  refine ⟨S, fun c hc => (Finset.mem_filter.mp hc).2, ?_⟩
  intro e he
  have hnot := (Finset.mem_sdiff.mp he).2
  induction e using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨a, ha, b, j, hj, hr, hjfire, c, hc, _, hcv, _⟩ :=
      ActualFilterCoverage.off_star_common_filter G C hL hTF hnojoint u v he
    obtain ⟨i, hgi⟩ := honto j hj
    subst j
    have hg := (P1.junk_iff G C (g i)).mp (hgj i)
    have hAO := P2.ao_of n C hL.1
    have hprod := ActualCommonMasks.pure_product_value C hAO (g i) hg.1 hg.2.1 (hpure i)
    have hcm := ActualCommonMasks.top_common_masks G C hAO (g i) hg.1 hg.2.1 (hpure i)
      a ha b hr c hc
    have hpair : pairInput u v c = true := by
      simp only [pairInput, decide_eq_true_eq]
      exact hcv
    have huv : G.Adj u v := (G.mem_edgeSet).mp
      ((SimpleGraph.mem_edgeFinset).mp (Finset.mem_sdiff.mp he).1)
    have hp : productValue (A i) (B i) (pairInput u v) = true := (hprod _).symm.trans hjfire
    obtain ⟨hcc, heStar⟩ := MaskGrouping.effective_mask_pair_covered G (A i) (B i)
      (hdis i) u v c huv hp hpair hcm
    refine ⟨hnot, i, c, hcc, heStar, ?_⟩
    by_cases hbound : EligibleBoundary.Certificate G (A i) (B i) (PEqualNP.TopForm.starEdges G C)
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbound⟩)
    · right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hne : (side (n := n) C a b).Nonempty := by
        apply Finset.nonempty_iff_ne_empty.mpr
        intro hemp
        have hac : a ∈ centreless G C := by
          apply Finset.mem_filter.mpr
          refine ⟨ha, ?_⟩
          rcases P2.fin2_sub b with ⟨hb, _⟩ | ⟨hb, _⟩
          · exact Or.inl (by simpa only [hb] using hemp)
          · exact Or.inr (by simpa only [hb] using hemp)
        rw [hcent] at hac
        exact Finset.notMem_empty _ hac
      obtain ⟨hcAB, _⟩ := (mem_centers_iff G (A i) (B i) c).mp hcc
      have hop := EligibleFamilyBudget.opposite_center G hG (A i) (B i)
        (hdis i) (hA i) (hB i) (htwo i) c hcc
      by_cases hcA : c ∈ A i
      · obtain ⟨d, hd, hdm⟩ := hop.1 hcA
        exact ⟨A i, B i, d, g i, a, b, hA i, hB i, hcA, hd, hcm, hdm, hbound,
          hgj i, hprod, ha, hc, hr, hne⟩
      · have hcB : c ∈ B i := (Finset.mem_union.mp hcAB).resolve_left hcA
        obtain ⟨d, hd, hdm⟩ := hop.2 hcB
        refine ⟨B i, A i, d, g i, a, b, hB i, hA i, hcB, hd, ?_, ?_, ?_, hgj i, ?_, ha, hc, hr, hne⟩
        · simpa only [CleanMask, productValue, Bool.and_comm] using hcm
        · simpa only [CleanMask, productValue, Bool.and_comm] using hdm
        · intro hcert
          exact hbound (EligibleBoundary.certificate_swap G (B i) (A i) (hdis i).symm _ hcert)
        · intro x
          simpa only [productValue, Bool.and_comm] using hprod x

end PEqualNP.Outside.L_meta_1477.OrdinaryFamilyCoverage


namespace PEqualNP.Outside.L_meta_1477.EligibleFamilyBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OneJunk MaskGraphSupport Structural StructuralMasks MaskGrouping MaskAllCenters

lemma ordinary_all_centers_budget {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C)
    (A B : Fin t → Finset (Fin n))
    (hdis : ∀ a, Disjoint (A a) (B a))
    (hA : ∀ a, 2 ≤ (A a).card) (hB : ∀ a, 2 ≤ (B a).card)
    (left right : Fin t → ℕ)
    (hleft : ∀ a, left a < n + C.gates.length)
    (hright : ∀ a, right a < n + C.gates.length)
    (hpureL : ∀ a, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (left a) (n + k))
    (hpureR : ∀ a, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (right a) (n + k))
    (hsupportL : ∀ a, orIn n C (left a) = A a)
    (hsupportR : ∀ a, orIn n C (right a) = B a)
    (S : Finset (Fin n)) (hreader : ∀ c ∈ S, OrdinaryFilterBudget.OrdinaryActive G C c) :
    (allStars G A B \ PEqualNP.TopForm.starEdges G C).card + (boundaryProducts G C A B).card +
      S.card ≤ (orN G C \ lam G C).card + t := by
  classical
  let boundary := boundaryProducts G C A B
  have hboundary : ∀ a ∈ boundary, ∃ c ∈ cleanCenters G (A a) (B a),
      ∃ u ∈ neighbors (A a) (B a) c, s(c, u) ∈ PEqualNP.TopForm.starEdges G C :=
    fun a ha => (Finset.mem_filter.mp ha).2.1
  let I := Σ a : Fin t, ↥(Structural.cleanCenters G (A a) (B a))
  let e := Fintype.equivFin I
  let idx : Fin (Fintype.card I) → I := e.symm
  let grp : Fin (Fintype.card I) → Fin t := fun i => (idx i).1
  let center : Fin (Fintype.card I) → Fin n := fun i => (idx i).2.val
  let root : Fin (Fintype.card I) → ℕ := fun i =>
    if center i ∈ A (grp i) then right (grp i) else left (grp i)
  have hcenter : ∀ i, center i ∈ Structural.cleanCenters G (A (grp i)) (B (grp i)) :=
    fun i => (idx i).2.property
  have hsupport : ∀ i, orIn n C (root i) =
      MaskGrouping.neighbors (A (grp i)) (B (grp i)) (center i) := by
    intro i
    by_cases hi : center i ∈ A (grp i)
    · simp only [root, if_pos hi, hsupportR, MaskGrouping.neighbors, if_pos hi]
    · simp only [root, if_neg hi, hsupportL, MaskGrouping.neighbors, if_neg hi]
  have hbound : ∀ i, root i < n + C.gates.length := by
    intro i
    dsimp only [root]
    split
    · exact hright _
    · exact hleft _
  have hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k) := by
    intro i k hk hop
    dsimp only [root]
    split
    · exact hpureR _ k hk hop
    · exact hpureL _ k hk hop
  have hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v := by
    intro i v hv
    rw [hsupport i] at hv
    exact MaskGrouping.center_neighbors_clean G _ _ _ (hcenter i) v hv
  have hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v) := by
    intro i j hij
    have hj : center j ∈ Structural.cleanCenters G (A (grp i)) (B (grp i)) := by
      simpa only [hij] using hcenter j
    obtain ⟨z, hz⟩ := MaskGrouping.centers_stars_intersect G hG
      (A (grp i)) (B (grp i)) (hdis _) (hA _) (hB _) (center i) (center j)
      (hcenter i) hj
    obtain ⟨hzi, hzj⟩ := Finset.mem_inter.mp hz
    obtain ⟨u, hu, hue⟩ := Finset.mem_image.mp hzi
    obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp hzj
    refine ⟨u, ?_, v, ?_, hue.trans hve.symm⟩
    · simpa only [hsupport i] using hu
    · simpa only [hsupport j, ← hij] using hv
  have hsub : allStars G A B ⊆ edges C center root := by
    intro z hz
    obtain ⟨a, _, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨c, hc, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hz
    let i : Fin (Fintype.card I) := e ⟨a, ⟨c, hc⟩⟩
    have hgi : grp i = a := by simp [grp, idx, i]
    have hci : center i = c := by
      exact congrArg (fun j : I => j.2.val) (e.symm_apply_apply ⟨a, ⟨c, hc⟩⟩)
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨v, ?_, ?_⟩⟩
    · rw [hsupport i, hgi, hci]
      exact hv
    · simpa only [hci] using hvz
  have hboundaryidx : ∀ i, grp i ∈ boundary → ∃ j, grp j = grp i ∧
      ∃ u ∈ orIn n C (root j), s(center j, u) ∈ PEqualNP.TopForm.starEdges G C := by
    intro i hi
    obtain ⟨c, hc, u, hu, hown⟩ := hboundary (grp i) hi
    let j : Fin (Fintype.card I) := e ⟨grp i, ⟨c, hc⟩⟩
    have hgj : grp j = grp i := by simp [grp, idx, j]
    have hcj : center j = c := by
      exact congrArg (fun k : I => k.2.val) (e.symm_apply_apply ⟨grp i, ⟨c, hc⟩⟩)
    refine ⟨j, hgj, u, ?_, ?_⟩
    · simpa only [hsupport j, hgj, hcj] using hu
    · simpa only [hcj] using hown
  have hcount := OrdinaryFilterBudget.ordinary_mask_budget G hG color hcolor C hL center root
    hbound hpure hclean grp hgroup boundary hboundaryidx S hreader
  have hdiff : allStars G A B \ PEqualNP.TopForm.starEdges G C ⊆ edges C center root \ PEqualNP.TopForm.starEdges G C := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩
  have hcard := Finset.card_le_card hdiff
  dsimp only [boundary] at hcount
  omega


lemma common_all_centers_ordinary_budget {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C)
    (A B : Fin t → Finset (Fin n))
    (hdis : ∀ a, Disjoint (A a) (B a))
    (hA : ∀ a, 2 ≤ (A a).card) (hB : ∀ a, 2 ≤ (B a).card)
    (left right : Fin t → ℕ)
    (hleft : ∀ a, left a < n + C.gates.length)
    (hright : ∀ a, right a < n + C.gates.length)
    (hpureL : ∀ a, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (left a) (n + k))
    (hpureR : ∀ a, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (right a) (n + k))
    (hsupportL : ∀ a, orIn n C (left a) = A a)
    (hsupportR : ∀ a, orIn n C (right a) = B a)
    (htwo : ∀ a, (cleanCenters G (A a) (B a)).card = 2)
    (filterRoot : ℕ) (hfilter : filterRoot < n + C.gates.length)
    (hcommon : ∀ a, ∀ q ∈ orIn n C filterRoot, CleanMask G (A a) (B a) q)
    (S : Finset (Fin n)) (hreader : ∀ c ∈ S, OrdinaryFilterBudget.OrdinaryActive G C c) :
    (allStars G A B \ PEqualNP.TopForm.starEdges G C).card + (boundaryProducts G C A B).card +
      (activeCenters G C A B filterRoot).card + S.card ≤ (orN G C \ lam G C).card + t + 1 := by
  classical
  let boundary := boundaryProducts G C A B
  let R := activeCenters G C A B filterRoot
  have hboundary : ∀ a ∈ boundary, ∃ c ∈ cleanCenters G (A a) (B a),
      ∃ u ∈ neighbors (A a) (B a) c, s(c, u) ∈ PEqualNP.TopForm.starEdges G C :=
    fun a ha => (Finset.mem_filter.mp ha).2.1
  have hRsub : R ⊆ orIn n C filterRoot := by
    intro c hc
    obtain ⟨a, _, hc⟩ := Finset.mem_biUnion.mp hc
    by_cases ha : a ∈ boundaryProducts G C A B
    · simp only [if_pos ha, Finset.notMem_empty] at hc
    · rw [if_neg ha] at hc
      exact (Finset.mem_inter.mp hc).2
  have hactive : ∀ c ∈ R, ∃ A' B' : Finset (Fin n), ∃ b : Fin n,
      2 ≤ A'.card ∧ 2 ≤ B'.card ∧ c ∈ A' ∧ b ∈ B' ∧
      CleanMask G A' B' c ∧ CleanMask G A' B' b ∧
      (∀ q ∈ orIn n C filterRoot, CleanMask G A' B' q) ∧
      ¬ EligibleBoundary.Certificate G A' B' (PEqualNP.TopForm.starEdges G C) := by
    intro c hcR
    obtain ⟨a, _, hc⟩ := Finset.mem_biUnion.mp hcR
    have ha : a ∉ boundaryProducts G C A B := by
      intro ha
      simp only [if_pos ha, Finset.notMem_empty] at hc
    rw [if_neg ha] at hc
    have hcc := (Finset.mem_inter.mp hc).1
    obtain ⟨hcAB, hcm⟩ := (mem_centers_iff G (A a) (B a) c).mp hcc
    have hnot : ¬ EligibleBoundary.Certificate G (A a) (B a) (PEqualNP.TopForm.starEdges G C) := by
      intro hcert
      exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcert⟩)
    have hop := opposite_center G hG (A a) (B a) (hdis a) (hA a) (hB a) (htwo a) c hcc
    by_cases hcA : c ∈ A a
    · obtain ⟨b, hb, hbm⟩ := hop.1 hcA
      exact ⟨A a, B a, b, hA a, hB a, hcA, hb, hcm, hbm, hcommon a, hnot⟩
    · have hcB : c ∈ B a := (Finset.mem_union.mp hcAB).resolve_left hcA
      obtain ⟨b, hb, hbm⟩ := hop.2 hcB
      refine ⟨B a, A a, b, hB a, hA a, hcB, hb, ?_, ?_, ?_, ?_⟩
      · simpa only [CleanMask, productValue, Bool.and_comm] using hcm
      · simpa only [CleanMask, productValue, Bool.and_comm] using hbm
      · intro q hq
        simpa only [CleanMask, productValue, Bool.and_comm] using hcommon a q hq
      · intro hcert
        exact hnot (EligibleBoundary.certificate_swap G (B a) (A a) (hdis a).symm _ hcert)
  let I := Σ a : Fin t, ↥(Structural.cleanCenters G (A a) (B a))
  let e := Fintype.equivFin I
  let idx : Fin (Fintype.card I) → I := e.symm
  let grp : Fin (Fintype.card I) → Fin t := fun i => (idx i).1
  let center : Fin (Fintype.card I) → Fin n := fun i => (idx i).2.val
  let root : Fin (Fintype.card I) → ℕ := fun i =>
    if center i ∈ A (grp i) then right (grp i) else left (grp i)
  have hcenter : ∀ i, center i ∈ Structural.cleanCenters G (A (grp i)) (B (grp i)) :=
    fun i => (idx i).2.property
  have hsupport : ∀ i, orIn n C (root i) =
      MaskGrouping.neighbors (A (grp i)) (B (grp i)) (center i) := by
    intro i
    by_cases hi : center i ∈ A (grp i)
    · simp only [root, if_pos hi, hsupportR, MaskGrouping.neighbors, if_pos hi]
    · simp only [root, if_neg hi, hsupportL, MaskGrouping.neighbors, if_neg hi]
  have hbound : ∀ i, root i < n + C.gates.length := by
    intro i
    dsimp only [root]
    split
    · exact hright _
    · exact hleft _
  have hpure : ∀ i, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (root i) (n + k) := by
    intro i k hk hop
    dsimp only [root]
    split
    · exact hpureR _ k hk hop
    · exact hpureL _ k hk hop
  have hclean : ∀ i, ∀ v ∈ orIn n C (root i), G.Adj (center i) v := by
    intro i v hv
    rw [hsupport i] at hv
    exact MaskGrouping.center_neighbors_clean G _ _ _ (hcenter i) v hv
  have hgroup : ∀ i j, grp i = grp j → ∃ u ∈ orIn n C (root i),
      ∃ v ∈ orIn n C (root j), s(center i, u) = s(center j, v) := by
    intro i j hij
    have hj : center j ∈ Structural.cleanCenters G (A (grp i)) (B (grp i)) := by
      simpa only [hij] using hcenter j
    obtain ⟨z, hz⟩ := MaskGrouping.centers_stars_intersect G hG
      (A (grp i)) (B (grp i)) (hdis _) (hA _) (hB _) (center i) (center j)
      (hcenter i) hj
    obtain ⟨hzi, hzj⟩ := Finset.mem_inter.mp hz
    obtain ⟨u, hu, hue⟩ := Finset.mem_image.mp hzi
    obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp hzj
    refine ⟨u, ?_, v, ?_, hue.trans hve.symm⟩
    · simpa only [hsupport i] using hu
    · simpa only [hsupport j, ← hij] using hv
  have hsub : allStars G A B ⊆ edges C center root := by
    intro z hz
    obtain ⟨a, _, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨c, hc, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hz
    let i : Fin (Fintype.card I) := e ⟨a, ⟨c, hc⟩⟩
    have hgi : grp i = a := by simp [grp, idx, i]
    have hci : center i = c := by
      exact congrArg (fun j : I => j.2.val) (e.symm_apply_apply ⟨a, ⟨c, hc⟩⟩)
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨v, ?_, ?_⟩⟩
    · rw [hsupport i, hgi, hci]
      exact hv
    · simpa only [hci] using hvz
  have hboundaryidx : ∀ i, grp i ∈ boundary → ∃ j, grp j = grp i ∧
      ∃ u ∈ orIn n C (root j), s(center j, u) ∈ PEqualNP.TopForm.starEdges G C := by
    intro i hi
    obtain ⟨c, hc, u, hu, hown⟩ := hboundary (grp i) hi
    let j : Fin (Fintype.card I) := e ⟨grp i, ⟨c, hc⟩⟩
    have hgj : grp j = grp i := by simp [grp, idx, j]
    have hcj : center j = c := by
      exact congrArg (fun k : I => k.2.val) (e.symm_apply_apply ⟨grp i, ⟨c, hc⟩⟩)
    refine ⟨j, hgj, u, ?_, ?_⟩
    · simpa only [hsupport j, hgj, hcj] using hu
    · simpa only [hcj] using hown
  have hsmall : ∀ i, (orIn n C filterRoot ∩ orIn n C (root i)).card ≤ 1 := by
    intro i
    rw [hsupport i]
    exact MaskFilterCommon.mask_inter_neighbors_small G hG _ _ _ (hA _) (hB _) (hcommon _) _
  have hcount := OrdinaryFilterBudget.common_filter_ordinary_budget G hG color hcolor C hL center root
    hbound hpure hclean grp hgroup boundary hboundaryidx filterRoot hfilter hsmall R hRsub hactive S hreader
  have hdiff : allStars G A B \ PEqualNP.TopForm.starEdges G C ⊆ edges C center root \ PEqualNP.TopForm.starEdges G C := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_sdiff.mp hz).1, (Finset.mem_sdiff.mp hz).2⟩
  have hcard := Finset.card_le_card hdiff
  dsimp only [boundary, R] at hcount
  omega


end PEqualNP.Outside.L_meta_1477.EligibleFamilyBudget


namespace PEqualNP.Outside.L_meta_1477.CommonFamilyAccounting

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk

lemma accounting_paid_cover_general {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    (hne : G.edgeFinset.Nonempty) (tau d : ℕ)
    (hmin : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) → tau ≤ K.card)
    (T : Finset (Fin n)) (hT : ∀ e ∈ Ustar G C, ∃ v ∈ T, v ∈ e)
    (hpaid : (Ustar G C).card + T.card ≤ (orN G C \ lam G C).card + d) :
    G.edgeFinset.card + tau + 2 * (centreless G C).card + (junk G C).card ≤
      C.size + d + 1 := by
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

end PEqualNP.Outside.L_meta_1477.CommonFamilyAccounting

namespace PEqualNP.Outside.L_meta_1477.EligibleFamilyBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping MaskAllCenters

lemma eligible_cover_from_centers {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (A B : Fin t → Finset (Fin n)) (S : Finset (Fin n))
    (F : Finset (Sym2 (Fin n)))
    (hF : ∀ e ∈ F, e ∉ PEqualNP.TopForm.starEdges G C ∧
      ∃ i : Fin t, ∃ c ∈ cleanCenters G (A i) (B i),
        e ∈ MaskGrouping.starEdges (A i) (B i) c ∧ (i ∈ boundaryProducts G C A B ∨ c ∈ S)) :
    ∃ T : Finset (Fin n), T.card ≤ (boundaryProducts G C A B).card + S.card ∧
      ∀ e ∈ F, ∃ v ∈ T, v ∈ e := by
  classical
  let J := boundaryProducts G C A B
  let d : J → Fin n := fun i => Classical.choose ((Finset.mem_filter.mp i.property).2.2)
  have hd (i : J) : ∀ c ∈ cleanCenters G (A i.val) (B i.val),
      ∀ e ∈ MaskGrouping.starEdges (A i.val) (B i.val) c,
      e ∉ PEqualNP.TopForm.starEdges G C → d i ∈ e :=
    Classical.choose_spec ((Finset.mem_filter.mp i.property).2.2)
  let D : Finset (Fin n) := Finset.univ.image d
  have hDcard : D.card ≤ J.card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using (Finset.card_image_le (s := Finset.univ) (f := d))
  refine ⟨D ∪ S, ?_, ?_⟩
  · exact (Finset.card_union_le D S).trans (Nat.add_le_add_right hDcard _)
  · intro e he
    obtain ⟨hnot, i, c, hc, he, hi | hcS⟩ := hF e he
    · let j : J := ⟨i, hi⟩
      refine ⟨d j, Finset.mem_union_left _ ?_, hd j c hc e he hnot⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · refine ⟨c, Finset.mem_union_right _ hcS, ?_⟩
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp he
      simp

lemma lower_bound_from_center_budget {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    (hne : G.edgeFinset.Nonempty) (tau d : ℕ)
    (hmin : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) → tau ≤ K.card)
    (A B : Fin t → Finset (Fin n)) (S : Finset (Fin n))
    (hF : ∀ e ∈ Ustar G C, e ∉ PEqualNP.TopForm.starEdges G C ∧
      ∃ i : Fin t, ∃ c ∈ cleanCenters G (A i) (B i),
        e ∈ MaskGrouping.starEdges (A i) (B i) c ∧ (i ∈ boundaryProducts G C A B ∨ c ∈ S))
    (hbudget : (Ustar G C).card + (boundaryProducts G C A B).card + S.card ≤
      (orN G C \ lam G C).card + d) :
    G.edgeFinset.card + tau + 2 * (centreless G C).card + (junk G C).card ≤ C.size + d + 1 := by
  obtain ⟨T, hTcard, hT⟩ := eligible_cover_from_centers G C A B S (Ustar G C) hF
  apply CommonFamilyAccounting.accounting_paid_cover_general G hG C hL hTF hne tau d hmin T hT
  omega

end PEqualNP.Outside.L_meta_1477.EligibleFamilyBudget

namespace PEqualNP.Outside.L_meta_1477.OrdinaryFamilyLowerBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma no_centreless_lower_bound {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    (hne : G.edgeFinset.Nonempty) (tau : ℕ)
    (hmin : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) → tau ≤ K.card)
    (hcent : centreless G C = ∅)
    (g : Fin t → ℕ) (hgj : ∀ i, g i ∈ junk G C) (honto : ∀ j ∈ junk G C, ∃ i, g i = j)
    (hcount : t ≤ (junk G C).card)
    (hpure : ∀ i, ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C (g i) b) (n + k))
    (hdis : ∀ i, Disjoint (side (n := n) C (g i) 0) (side C (g i) 1))
    (hA : ∀ i, 2 ≤ (side (n := n) C (g i) 0).card)
    (hB : ∀ i, 2 ≤ (side (n := n) C (g i) 1).card)
    (htwo : ∀ i, (cleanCenters G (side (n := n) C (g i) 0) (side C (g i) 1)).card = 2)
    (hnojoint : ∀ j ∈ junk G C, ∀ k ∈ junk G C, j ≠ k → ∀ u v : Fin n,
      gateVal n C j (pairInput u v) = true → gateVal n C k (pairInput u v) = true →
      ¬ GeneralDirtyPairs.JointClean G C j k) :
    G.edgeFinset.card + tau ≤ C.size + 1 := by
  classical
  let A := fun i => side (n := n) C (g i) 0
  let B := fun i => side (n := n) C (g i) 1
  obtain ⟨S, hreader, hcover⟩ := OrdinaryFamilyCoverage.no_centreless_mask_cover
    G hG C hL hTF hcent g hgj honto hpure hdis hA hB htwo hnojoint
  have hAO := P2.ao_of n C hL.1
  have hroots (i : Fin t) (b : Fin 2) : opnd C (g i) b < n + C.gates.length := by
    have hg := (P1.junk_iff G C (g i)).mp (hgj i)
    have hb := P2.opnd_lt n C hAO (g i) hg.1 (opnd C (g i))
      (P2.opnd_eq n C hAO (g i) hg.1) b
    omega
  have hbudget := EligibleFamilyBudget.ordinary_all_centers_budget G hG color hcolor C hL
    A B hdis hA hB (fun i => opnd C (g i) 0) (fun i => opnd C (g i) 1)
    (fun i => hroots i 0) (fun i => hroots i 1) (fun i => hpure i 0) (fun i => hpure i 1)
    (fun _ => rfl) (fun _ => rfl) S hreader
  have hsub : Ustar G C ⊆ MaskAllCenters.allStars G A B \ PEqualNP.TopForm.starEdges G C := by
    intro e he
    obtain ⟨hnot, i, c, hc, hstar, _⟩ := hcover e he
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨c, hc, hstar⟩⟩, hnot⟩
  have hUcard := Finset.card_le_card hsub
  have hpaid : (Ustar G C).card + (EligibleFamilyBudget.boundaryProducts G C A B).card + S.card ≤
      (orN G C \ lam G C).card + t := by omega
  have hfinal := EligibleFamilyBudget.lower_bound_from_center_budget G hG C hL hTF hne tau t hmin
    A B S hcover hpaid
  rw [hcent, Finset.card_empty] at hfinal
  omega

end PEqualNP.Outside.L_meta_1477.OrdinaryFamilyLowerBound

namespace PEqualNP.Outside.L_meta_1477.OrdinaryFamilyCoverage

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma mask_cover_or_centreless {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    (g : Fin t → ℕ) (hgj : ∀ i, g i ∈ junk G C) (honto : ∀ j ∈ junk G C, ∃ i, g i = j)
    (hpure : ∀ i, ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C (g i) b) (n + k))
    (hdis : ∀ i, Disjoint (side (n := n) C (g i) 0) (side C (g i) 1))
    (hA : ∀ i, 2 ≤ (side (n := n) C (g i) 0).card)
    (hB : ∀ i, 2 ≤ (side (n := n) C (g i) 1).card)
    (htwo : ∀ i, (cleanCenters G (side (n := n) C (g i) 0) (side C (g i) 1)).card = 2)
    (hnojoint : ∀ j ∈ junk G C, ∀ k ∈ junk G C, j ≠ k → ∀ u v : Fin n,
      gateVal n C j (pairInput u v) = true → gateVal n C k (pairInput u v) = true →
      ¬ GeneralDirtyPairs.JointClean G C j k) :
    ∃ S : Finset (Fin n), (∀ c ∈ S, OrdinaryFilterBudget.OrdinaryActive G C c) ∧
      ∀ e ∈ Ustar G C, e ∉ PEqualNP.TopForm.starEdges G C ∧
        ∃ i : Fin t, ∃ c ∈ cleanCenters G (side (n := n) C (g i) 0) (side C (g i) 1),
          e ∈ MaskGrouping.starEdges (side (n := n) C (g i) 0) (side C (g i) 1) c ∧
          (i ∈ EligibleFamilyBudget.boundaryProducts G C
            (fun i => side (n := n) C (g i) 0) (fun i => side C (g i) 1) ∨ c ∈ S ∨
            ∃ a ∈ centreless G C, ∃ b : Fin 2, c ∈ side (n := n) C a (1-b) ∧
              P2.OrR n C (opnd C a b) (n + g i)) := by
  classical
  let A := fun i => side (n := n) C (g i) 0
  let B := fun i => side (n := n) C (g i) 1
  let S := Finset.univ.filter (OrdinaryFilterBudget.OrdinaryActive G C)
  refine ⟨S, fun c hc => (Finset.mem_filter.mp hc).2, ?_⟩
  intro e he
  have hnot := (Finset.mem_sdiff.mp he).2
  induction e using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨a, ha, b, j, hj, hr, hjfire, c, hc, _, hcv, _⟩ :=
      ActualFilterCoverage.off_star_common_filter G C hL hTF hnojoint u v he
    obtain ⟨i, hgi⟩ := honto j hj
    subst j
    have hg := (P1.junk_iff G C (g i)).mp (hgj i)
    have hAO := P2.ao_of n C hL.1
    have hprod := ActualCommonMasks.pure_product_value C hAO (g i) hg.1 hg.2.1 (hpure i)
    have hcm := ActualCommonMasks.top_common_masks G C hAO (g i) hg.1 hg.2.1 (hpure i)
      a ha b hr c hc
    have hpair : pairInput u v c = true := by
      simp only [pairInput, decide_eq_true_eq]
      exact hcv
    have huv : G.Adj u v := (G.mem_edgeSet).mp
      ((SimpleGraph.mem_edgeFinset).mp (Finset.mem_sdiff.mp he).1)
    have hp : productValue (A i) (B i) (pairInput u v) = true := (hprod _).symm.trans hjfire
    obtain ⟨hcc, heStar⟩ := MaskGrouping.effective_mask_pair_covered G (A i) (B i)
      (hdis i) u v c huv hp hpair hcm
    refine ⟨hnot, i, c, hcc, heStar, ?_⟩
    by_cases hbound : EligibleBoundary.Certificate G (A i) (B i) (PEqualNP.TopForm.starEdges G C)
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbound⟩)
    · right
      by_cases hemp : side (n := n) C a b = ∅
      · right
        have hac : a ∈ centreless G C := by
          apply Finset.mem_filter.mpr
          refine ⟨ha, ?_⟩
          rcases P2.fin2_sub b with ⟨hb, _⟩ | ⟨hb, _⟩
          · exact Or.inl (by simpa only [hb] using hemp)
          · exact Or.inr (by simpa only [hb] using hemp)
        exact ⟨a, hac, b, hc, hr⟩
      · left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have hne : (side (n := n) C a b).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
        obtain ⟨hcAB, _⟩ := (mem_centers_iff G (A i) (B i) c).mp hcc
        have hop := EligibleFamilyBudget.opposite_center G hG (A i) (B i)
          (hdis i) (hA i) (hB i) (htwo i) c hcc
        by_cases hcA : c ∈ A i
        · obtain ⟨d, hd, hdm⟩ := hop.1 hcA
          exact ⟨A i, B i, d, g i, a, b, hA i, hB i, hcA, hd, hcm, hdm, hbound,
            hgj i, hprod, ha, hc, hr, hne⟩
        · have hcB : c ∈ B i := (Finset.mem_union.mp hcAB).resolve_left hcA
          obtain ⟨d, hd, hdm⟩ := hop.2 hcB
          refine ⟨B i, A i, d, g i, a, b, hB i, hA i, hcB, hd, ?_, ?_, ?_, hgj i, ?_, ha, hc, hr, hne⟩
          · simpa only [CleanMask, productValue, Bool.and_comm] using hcm
          · simpa only [CleanMask, productValue, Bool.and_comm] using hdm
          · intro hcert
            exact hbound (EligibleBoundary.certificate_swap G (B i) (A i) (hdis i).symm _ hcert)
          · intro x
            simpa only [productValue, Bool.and_comm] using hprod x

end PEqualNP.Outside.L_meta_1477.OrdinaryFamilyCoverage


namespace PEqualNP.Outside.L_meta_1477.TwoProductCentreless

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma two_centreless_lower_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    (hne : G.edgeFinset.Nonempty) (tau : ℕ)
    (hmin : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) → tau ≤ K.card)
    (hcent : 2 ≤ (centreless G C).card) (hjcard : 2 ≤ (junk G C).card)
    (g : Fin 2 → ℕ) (hgj : ∀ i, g i ∈ junk G C) (honto : ∀ j ∈ junk G C, ∃ i, g i = j)
    (hpure : ∀ i, ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C (g i) b) (n + k))
    (hdis : ∀ i, Disjoint (side (n := n) C (g i) 0) (side C (g i) 1))
    (hA : ∀ i, 2 ≤ (side (n := n) C (g i) 0).card)
    (hB : ∀ i, 2 ≤ (side (n := n) C (g i) 1).card)
    (htwo : ∀ i, (cleanCenters G (side (n := n) C (g i) 0) (side C (g i) 1)).card = 2)
    (hnojoint : ∀ j ∈ junk G C, ∀ k ∈ junk G C, j ≠ k → ∀ u v : Fin n,
      gateVal n C j (pairInput u v) = true → gateVal n C k (pairInput u v) = true →
      ¬ GeneralDirtyPairs.JointClean G C j k) :
    G.edgeFinset.card + tau ≤ C.size + 1 := by
  classical
  let A := fun i => side (n := n) C (g i) 0
  let B := fun i => side (n := n) C (g i) 1
  obtain ⟨S, hreader, hcover⟩ := OrdinaryFamilyCoverage.mask_cover_or_centreless
    G hG C hL hTF g hgj honto hpure hdis hA hB htwo hnojoint
  have hAO := P2.ao_of n C hL.1
  have hroots (i : Fin 2) (b : Fin 2) : opnd C (g i) b < n + C.gates.length := by
    have hg := (P1.junk_iff G C (g i)).mp (hgj i)
    have hb := P2.opnd_lt n C hAO (g i) hg.1 (opnd C (g i))
      (P2.opnd_eq n C hAO (g i) hg.1) b
    omega
  have hbudget := EligibleFamilyBudget.ordinary_all_centers_budget G hG color hcolor C hL
    A B hdis hA hB (fun i => opnd C (g i) 0) (fun i => opnd C (g i) 1)
    (fun i => hroots i 0) (fun i => hroots i 1) (fun i => hpure i 0) (fun i => hpure i 1)
    (fun _ => rfl) (fun _ => rfl) S hreader
  have hsub : Ustar G C ⊆ MaskAllCenters.allStars G A B \ PEqualNP.TopForm.starEdges G C := by
    intro e he
    obtain ⟨hnot, i, c, hc, hstar, _⟩ := hcover e he
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨c, hc, hstar⟩⟩, hnot⟩
  let T := cleanCenters G (A 0) (B 0) ∪ cleanCenters G (A 1) (B 1)
  have hTcard : T.card ≤ 4 := by
    have hc := Finset.card_union_le (cleanCenters G (A 0) (B 0)) (cleanCenters G (A 1) (B 1))
    simpa only [T,A,B,htwo 0,htwo 1,Nat.reduceAdd] using hc
  have hT : ∀ e ∈ Ustar G C, ∃ v ∈ T, v ∈ e := by
    intro e he
    obtain ⟨_, i, c, hc, hstar, _⟩ := hcover e he
    refine ⟨c, ?_, ?_⟩
    · fin_cases i
      · exact Finset.mem_union_left _ hc
      · exact Finset.mem_union_right _ hc
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hstar
      simp
  have hUcard := Finset.card_le_card hsub
  have hpaid : (Ustar G C).card + T.card ≤ (orN G C \ lam G C).card + 6 := by omega
  have hfinal := CommonFamilyAccounting.accounting_paid_cover_general G hG C hL hTF hne tau 6
    hmin T hT hpaid
  omega

end PEqualNP.Outside.L_meta_1477.TwoProductCentreless

namespace PEqualNP.Outside.L_meta_1477.TwoProductCentreless

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma one_centreless_lower_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    (hne : G.edgeFinset.Nonempty) (tau : ℕ)
    (hmin : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) → tau ≤ K.card)
    (hcent : (centreless G C).card = 1) (hjcard : 2 ≤ (junk G C).card)
    (g : Fin 2 → ℕ) (hgj : ∀ i, g i ∈ junk G C) (honto : ∀ j ∈ junk G C, ∃ i, g i = j)
    (hpure : ∀ i, ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C (g i) b) (n + k))
    (hdis : ∀ i, Disjoint (side (n := n) C (g i) 0) (side C (g i) 1))
    (hA : ∀ i, 2 ≤ (side (n := n) C (g i) 0).card)
    (hB : ∀ i, 2 ≤ (side (n := n) C (g i) 1).card)
    (htwo : ∀ i, (cleanCenters G (side (n := n) C (g i) 0) (side C (g i) 1)).card = 2)
    (hnojoint : ∀ j ∈ junk G C, ∀ k ∈ junk G C, j ≠ k → ∀ u v : Fin n,
      gateVal n C j (pairInput u v) = true → gateVal n C k (pairInput u v) = true →
      ¬ GeneralDirtyPairs.JointClean G C j k) :
    G.edgeFinset.card + tau ≤ C.size + 1 := by
  classical
  let A := fun i => side (n := n) C (g i) 0
  let B := fun i => side (n := n) C (g i) 1
  obtain ⟨S, hreader, hcover⟩ := OrdinaryFamilyCoverage.mask_cover_or_centreless
    G hG C hL hTF g hgj honto hpure hdis hA hB htwo hnojoint
  have hAO := P2.ao_of n C hL.1
  have hroots (i : Fin 2) (b : Fin 2) : opnd C (g i) b < n + C.gates.length := by
    have hg := (P1.junk_iff G C (g i)).mp (hgj i)
    have hb := P2.opnd_lt n C hAO (g i) hg.1 (opnd C (g i))
      (P2.opnd_eq n C hAO (g i) hg.1) b
    omega
  have hsub : Ustar G C ⊆ MaskAllCenters.allStars G A B \ PEqualNP.TopForm.starEdges G C := by
    intro e he
    obtain ⟨hnot, i, c, hc, hstar, _⟩ := hcover e he
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨c, hc, hstar⟩⟩, hnot⟩
  have hUcard := Finset.card_le_card hsub
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcent
  have hamem : a ∈ centreless G C := by rw [ha]; simp
  have hatop : a ∈ tops G C := (Finset.mem_filter.mp hamem).1
  obtain ⟨b,hb⟩ : ∃ b : Fin 2, side (n := n) C a b = ∅ := by
    rcases (Finset.mem_filter.mp hamem).2 with h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  have hside : ∀ d : Fin 2, ∀ c : Fin n, c ∈ side (n := n) C a (1-d) → d=b := by
    intro d c hc
    fin_cases b <;> fin_cases d
    · rfl
    · have hh : c ∈ side (n := n) C a 0 := by simpa using hc
      have hb' : side (n := n) C a 0 = ∅ := by simpa using hb
      rw [hb'] at hh
      exact (Finset.notMem_empty c hh).elim
    · have hh : c ∈ side (n := n) C a 1 := by simpa using hc
      have hb' : side (n := n) C a 1 = ∅ := by simpa using hb
      rw [hb'] at hh
      exact (Finset.notMem_empty c hh).elim
    · rfl
  have hcentre : ∀ e ∈ Ustar G C, e ∉ PEqualNP.TopForm.starEdges G C ∧
      ∃ i : Fin 2, ∃ c ∈ cleanCenters G (A i) (B i),
        e ∈ MaskGrouping.starEdges (A i) (B i) c ∧
        (i ∈ EligibleFamilyBudget.boundaryProducts G C A B ∨ c ∈ S ∨
          c ∈ side (n := n) C a (1-b) ∧ P2.OrR n C (opnd C a b) (n+g i)) := by
    intro e he
    obtain ⟨hnot,i,c,hc,hstar,hcase⟩ := hcover e he
    rcases hcase with hi | hcS | ⟨ac,hac,d,hcd,hr⟩
    · exact ⟨hnot,i,c,hc,hstar,Or.inl hi⟩
    · exact ⟨hnot,i,c,hc,hstar,Or.inr (Or.inl hcS)⟩
    · have heq : ac=a := by simpa only [ha,Finset.mem_singleton] using hac
      subst ac
      have hdb := hside d c hcd
      subst d
      exact ⟨hnot,i,c,hc,hstar,Or.inr (Or.inr ⟨hcd,hr⟩)⟩
  by_cases hall : ∀ i : Fin 2, P2.OrR n C (opnd C a b) (n+g i)
  · let f := opnd C a (1-b)
    have hfilter : f < n+C.gates.length := by
      have halen := Finset.mem_range.mp ((P2.mem_filter' _ _ _ _).mp hatop).1
      have hlt := P2.opnd_lt n C hAO a halen (opnd C a) (P2.opnd_eq n C hAO a halen) (1-b)
      dsimp [f]
      omega
    have hcommon : ∀ i, ∀ q ∈ orIn n C f, CleanMask G (A i) (B i) q := by
      intro i q hq
      have hg := (P1.junk_iff G C (g i)).mp (hgj i)
      exact ActualCommonMasks.top_common_masks G C hAO (g i) hg.1 hg.2.1 (hpure i)
        a hatop b (hall i) q hq
    let R := EligibleFamilyBudget.activeCenters G C A B f
    have hbudget := EligibleFamilyBudget.common_all_centers_ordinary_budget G hG color hcolor C hL
      A B hdis hA hB (fun i => opnd C (g i) 0) (fun i => opnd C (g i) 1)
      (fun i => hroots i 0) (fun i => hroots i 1) (fun i => hpure i 0) (fun i => hpure i 1)
      (fun _ => rfl) (fun _ => rfl) htwo f hfilter hcommon S hreader
    have hcov : ∀ e ∈ Ustar G C, e ∉ PEqualNP.TopForm.starEdges G C ∧
      ∃ i : Fin 2, ∃ c ∈ cleanCenters G (A i) (B i),
        e ∈ MaskGrouping.starEdges (A i) (B i) c ∧
        (i ∈ EligibleFamilyBudget.boundaryProducts G C A B ∨ c ∈ S ∪ R) := by
      intro e he
      obtain ⟨hnot,i,c,hc,hstar,hcase⟩ := hcentre e he
      rcases hcase with hi | hcS | ⟨hcf,hr⟩
      · exact ⟨hnot,i,c,hc,hstar,Or.inl hi⟩
      · exact ⟨hnot,i,c,hc,hstar,Or.inr (Finset.mem_union_left _ hcS)⟩
      · refine ⟨hnot,i,c,hc,hstar,?_⟩
        by_cases hi : i ∈ EligibleFamilyBudget.boundaryProducts G C A B
        · exact Or.inl hi
        · right
          apply Finset.mem_union_right
          change c ∈ Finset.univ.biUnion (fun j : Fin 2 =>
            if j ∈ EligibleFamilyBudget.boundaryProducts G C A B then ∅
            else cleanCenters G (A j) (B j) ∩ orIn n C f)
          apply Finset.mem_biUnion.mpr
          refine ⟨i,Finset.mem_univ _,?_⟩
          rw [if_neg hi]
          exact Finset.mem_inter.mpr ⟨hc,hcf⟩
    have hUnion := Finset.card_union_le S R
    have hpaid : (Ustar G C).card + (EligibleFamilyBudget.boundaryProducts G C A B).card +
        (S ∪ R).card ≤ (orN G C \ lam G C).card + 3 := by
      change (MaskAllCenters.allStars G A B \ PEqualNP.TopForm.starEdges G C).card +
        (EligibleFamilyBudget.boundaryProducts G C A B).card + R.card + S.card ≤
        (orN G C \ lam G C).card + 2 + 1 at hbudget
      omega
    have hfinal := EligibleFamilyBudget.lower_bound_from_center_budget G hG C hL hTF hne tau 3 hmin
      A B (S ∪ R) hcov hpaid
    omega
  · push_neg at hall
    obtain ⟨k,hk⟩ := hall
    let F := cleanCenters G (A (1-k)) (B (1-k))
    have hFcard : F.card = 2 := htwo (1-k)
    have hbudget := EligibleFamilyBudget.ordinary_all_centers_budget G hG color hcolor C hL
      A B hdis hA hB (fun i => opnd C (g i) 0) (fun i => opnd C (g i) 1)
      (fun i => hroots i 0) (fun i => hroots i 1) (fun i => hpure i 0) (fun i => hpure i 1)
      (fun _ => rfl) (fun _ => rfl) S hreader
    have hcov : ∀ e ∈ Ustar G C, e ∉ PEqualNP.TopForm.starEdges G C ∧
      ∃ i : Fin 2, ∃ c ∈ cleanCenters G (A i) (B i),
        e ∈ MaskGrouping.starEdges (A i) (B i) c ∧
        (i ∈ EligibleFamilyBudget.boundaryProducts G C A B ∨ c ∈ S ∪ F) := by
      intro e he
      obtain ⟨hnot,i,c,hc,hstar,hcase⟩ := hcentre e he
      rcases hcase with hi | hcS | ⟨hcf,hr⟩
      · exact ⟨hnot,i,c,hc,hstar,Or.inl hi⟩
      · exact ⟨hnot,i,c,hc,hstar,Or.inr (Finset.mem_union_left _ hcS)⟩
      · refine ⟨hnot,i,c,hc,hstar,Or.inr (Finset.mem_union_right _ ?_)⟩
        have hik : i ≠ k := by intro heq; subst i; exact hk hr
        have heq : i = 1-k := by fin_cases i <;> fin_cases k <;> simp_all
        simpa only [F,heq] using hc
    have hUnion := Finset.card_union_le S F
    have hpaid : (Ustar G C).card + (EligibleFamilyBudget.boundaryProducts G C A B).card +
        (S ∪ F).card ≤ (orN G C \ lam G C).card + 4 := by omega
    have hfinal := EligibleFamilyBudget.lower_bound_from_center_budget G hG C hL hTF hne tau 4 hmin
      A B (S ∪ F) hcov hpaid
    omega

end PEqualNP.Outside.L_meta_1477.TwoProductCentreless

namespace PEqualNP.Outside.L_meta_1477.TwoProductCentreless

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma two_product_lower_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (C : Circuit) (hL : IsLeastAO G C) (hTF : TopForm G C)
    (hne : G.edgeFinset.Nonempty) (tau : ℕ)
    (hmin : ∀ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) → tau ≤ K.card)
    (hjcard : 2 ≤ (junk G C).card)
    (g : Fin 2 → ℕ) (hgj : ∀ i, g i ∈ junk G C) (honto : ∀ j ∈ junk G C, ∃ i, g i = j)
    (hpure : ∀ i, ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C (g i) b) (n + k))
    (hdis : ∀ i, Disjoint (side (n := n) C (g i) 0) (side C (g i) 1))
    (hA : ∀ i, 2 ≤ (side (n := n) C (g i) 0).card)
    (hB : ∀ i, 2 ≤ (side (n := n) C (g i) 1).card)
    (htwo : ∀ i, (cleanCenters G (side (n := n) C (g i) 0) (side C (g i) 1)).card = 2)
    (hnojoint : ∀ j ∈ junk G C, ∀ k ∈ junk G C, j ≠ k → ∀ u v : Fin n,
      gateVal n C j (pairInput u v) = true → gateVal n C k (pairInput u v) = true →
      ¬ GeneralDirtyPairs.JointClean G C j k) :
    G.edgeFinset.card + tau ≤ C.size + 1 := by
  by_cases hzero : (centreless G C).card = 0
  · exact OrdinaryFamilyLowerBound.no_centreless_lower_bound G hG color hcolor C hL hTF
      hne tau hmin (Finset.card_eq_zero.mp hzero) g hgj honto hjcard hpure hdis hA hB htwo hnojoint
  · by_cases hone : (centreless G C).card = 1
    · exact one_centreless_lower_bound G hG color hcolor C hL hTF hne tau hmin hone hjcard
        g hgj honto hpure hdis hA hB htwo hnojoint
    · exact two_centreless_lower_bound G hG color hcolor C hL hTF hne tau hmin (by omega) hjcard
        g hgj honto hpure hdis hA hB htwo hnojoint

end PEqualNP.Outside.L_meta_1477.TwoProductCentreless

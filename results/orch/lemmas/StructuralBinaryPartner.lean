import Mathlib.Data.Fin.Basic
import PEqualNP.Defs
import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_2592_aux

def edgeValue (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def singleInput (u : Fin 10) : Fin 10 → Bool := fun i => decide (i = u)

def pairInput (u v : Fin 10) : Fin 10 → Bool := fun i => decide (i = u ∨ i = v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma two_false_witness : ∀ v a b : Fin 10, v ≠ a → v ≠ b →
    ∃ u : Fin 10, u ≠ a ∧ u ≠ b ∧ u ≠ v ∧
      edgeValue (singleInput u) = false ∧ edgeValue (pairInput v u) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma one_true_witness : ∀ v a : Fin 10, v ≠ a →
    ∃ u : Fin 10, u ≠ v ∧
      edgeValue (pairInput a u) = false ∧
      edgeValue (fun i => decide (i = v ∨ i = a ∨ i = u)) = true := by
  decide +kernel

def Critical (v : Fin 10) (x : Fin 10 → Bool) : Prop :=
  x v = false ∧ edgeValue x = false ∧ edgeValue (Function.update x v true) = true

lemma single_update (u v : Fin 10) :
    Function.update (singleInput u) v true = pairInput v u := by
  funext i
  by_cases hi : i = v
  · subst i
    simp [singleInput, pairInput]
  · simp [Function.update_of_ne hi, singleInput, pairInput, hi]

lemma pair_update (v a u : Fin 10) :
    Function.update (pairInput a u) v true =
      (fun i => decide (i = v ∨ i = a ∨ i = u)) := by
  funext i
  by_cases hi : i = v
  · subst i
    simp [pairInput]
  · simp [Function.update_of_ne hi, pairInput, hi]

lemma no_binary_partner (v a b : Fin 10) (isAnd : Bool) (ha : v ≠ a) (hb : v ≠ b) :
    ¬ ∀ x : Fin 10 → Bool, Critical v x →
      (if isAnd then x a && x b else x a || x b) = true := by
  intro partner
  obtain ⟨u, hua, hub, huv, hzero, hedge⟩ := two_false_witness v a b ha hb
  have hcrit : Critical v (singleInput u) := by
    refine ⟨?_, hzero, ?_⟩
    · simp [singleInput, Ne.symm huv]
    · rw [single_update]
      exact hedge
  have bad := partner (singleInput u) hcrit
  simp [singleInput, Ne.symm hua, Ne.symm hub] at bad

lemma no_negated_partner (v a : Fin 10) (ha : v ≠ a) :
    ¬ ∀ x : Fin 10 → Bool, Critical v x → (!x a) = true := by
  intro partner
  obtain ⟨u, huv, hzero, hedge⟩ := one_true_witness v a ha
  have hcrit : Critical v (pairInput a u) := by
    refine ⟨?_, hzero, ?_⟩
    · simp [pairInput, ha, Ne.symm huv]
    · rw [pair_update]
      exact hedge
  have bad := partner (pairInput a u) hcrit
  simp [pairInput] at bad

lemma critical_partner_of_factor (v : Fin 10) (h : (Fin 10 → Bool) → Bool)
    (H : (Fin 10 → Bool) → Bool → Bool)
    (independent : ∀ x, h (Function.update x v true) = h x)
    (factor : ∀ x, edgeValue x = H (Function.update x v false) (x v && h x)) :
    ∀ x, Critical v x → h x = true := by
  intro x hx
  obtain ⟨hxv, hxzero, hxone⟩ := hx
  cases hvalue : h x with
  | true => rfl
  | false =>
    have hzero := factor x
    have hone := factor (Function.update x v true)
    simp only [hxv, Bool.false_and, hxzero] at hzero
    simp only [Function.update_self, Function.update_idem, Bool.true_and,
      independent x, hvalue, hxone] at hone
    have bad : false = true := hzero.trans hone.symm
    cases bad

lemma no_binary_and_factor (v a b : Fin 10) (isAnd : Bool)
    (ha : v ≠ a) (hb : v ≠ b) (H : (Fin 10 → Bool) → Bool → Bool) :
    ¬ ∀ x, edgeValue x = H (Function.update x v false)
      (x v && (if isAnd then x a && x b else x a || x b)) := by
  intro factor
  exact no_binary_partner v a b isAnd ha hb
    (critical_partner_of_factor v _ H (by
      intro x
      simp [Function.update_of_ne (Ne.symm ha), Function.update_of_ne (Ne.symm hb)]) factor)

lemma no_negated_and_factor (v a : Fin 10) (ha : v ≠ a)
    (H : (Fin 10 → Bool) → Bool → Bool) :
    ¬ ∀ x, edgeValue x = H (Function.update x v false) (x v && !x a) := by
  intro factor
  exact no_negated_partner v a ha
    (critical_partner_of_factor v _ H (by
      intro x
      simp [Function.update_of_ne (Ne.symm ha)]) factor)

open PEqualNP.CircuitLowerBounds

def runGates (gs : List Gate) (ws : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws

def AgreeAway (v : Nat) (ws zs : List Bool) : Prop :=
  ws.length = zs.length ∧ ∀ i : Nat, i ≠ v → ws.getD i false = zs.getD i false

lemma agreeAway_append {v : Nat} {ws zs : List Bool} (h : AgreeAway v ws zs)
    (tail : List Bool) : AgreeAway v (ws ++ tail) (zs ++ tail) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hiv
  by_cases hi : i < ws.length
  · rw [List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ (by simpa [h.1] using hi)]
    exact h.2 i hiv
  · have hwi : ws.length ≤ i := Nat.le_of_not_gt hi
    have hzi : zs.length ≤ i := by simpa [h.1] using hwi
    rw [List.getD_append_right _ _ _ _ hwi, List.getD_append_right _ _ _ _ hzi, h.1]

lemma runGates_agreeAway (gs : List Gate) {v : Nat} {ws zs : List Bool}
    (hgs : ∀ g ∈ gs, v ∉ g.inputs) (h : AgreeAway v ws zs) :
    AgreeAway v (runGates gs ws) (runGates gs zs) := by
  induction gs generalizing ws zs with
  | nil => exact h
  | cons g gs ih =>
    have hgate : g.op.eval (g.inputs.map fun i => ws.getD i false) =
        g.op.eval (g.inputs.map fun i => zs.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h.2 i (fun eq => hgs g (by simp) (eq ▸ hi))
    simp only [runGates, List.foldl_cons]
    rw [hgate]
    exact ih (fun q hq => hgs q (by simp [hq])) (agreeAway_append h _)

lemma runGates_getD_input (gs : List Gate) (ws : List Bool) (i : Nat) (hi : i < ws.length) :
    (runGates gs ws).getD i false = ws.getD i false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change (runGates gs (ws ++ [g.op.eval (g.inputs.map fun j => ws.getD j false)])).getD i false = _
    rw [ih _ (by simp only [List.length_append, List.length_singleton]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma agreeAway_update {n : Nat} (x : Fin n → Bool) (v : Fin n) (b : Bool) :
    AgreeAway v.val (List.ofFn x) (List.ofFn (Function.update x v b)) := by
  refine ⟨by simp, ?_⟩
  intro i hiv
  by_cases hi : i < n
  · have hfin : (⟨i, hi⟩ : Fin n) ≠ v := by
      intro eq
      exact hiv (congrArg Fin.val eq)
    simp [List.getD_eq_getElem?_getD, hi, Function.update_of_ne hfin]
  · simp [List.getD_eq_getElem?_getD, hi]

lemma eval_and_split (pre post : List Gate) (o v w : Nat) (xs : List Bool) :
    (Circuit.mk (pre ++ ⟨GateOp.and, [v, w]⟩ :: post) o).eval xs =
      (runGates post (runGates pre xs ++
        [(runGates pre xs).getD v false && (runGates pre xs).getD w false])).getD o false := by
  simp [Circuit.eval, Circuit.wires, runGates, List.foldl_append, GateOp.eval]

lemma sole_and_reader_factor {n : Nat} (pre post : List Gate) (o w : Nat) (v : Fin n)
    (hnoread : ∀ g ∈ pre ++ post, v.val ∉ g.inputs) (ho : o ≠ v.val) :
    ∀ x : Fin n → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.and, [v.val, w]⟩ :: post) o).eval (List.ofFn x) =
        (runGates post (runGates pre (List.ofFn (Function.update x v false)) ++
          [x v && (runGates pre (List.ofFn x)).getD w false])).getD o false := by
  intro x
  have preAway := runGates_agreeAway pre
    (fun g hg => hnoread g (by simp [hg])) (agreeAway_update x v false)
  have postAway := runGates_agreeAway post
    (fun g hg => hnoread g (by simp [hg]))
    (agreeAway_append preAway [x v && (runGates pre (List.ofFn x)).getD w false])
  rw [eval_and_split]
  have hv : (runGates pre (List.ofFn x)).getD v.val false = x v := by
    rw [runGates_getD_input _ _ _ (by simpa using v.isLt)]
    simp [List.getD_eq_getElem?_getD]
  rw [hv]
  exact postAway.2 o ho

lemma sole_and_reader_binary_impossible (pre post : List Gate) (o w : Nat)
    (v a b : Fin 10) (isAnd : Bool)
    (hnoread : ∀ g ∈ pre ++ post, v.val ∉ g.inputs) (ho : o ≠ v.val)
    (ha : v ≠ a) (hb : v ≠ b)
    (hpartner : ∀ x : Fin 10 → Bool,
      (runGates pre (List.ofFn x)).getD w false =
        (if isAnd then x a && x b else x a || x b)) :
    ¬ ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.and, [v.val, w]⟩ :: post) o).eval (List.ofFn x) =
        edgeValue x := by
  intro computes
  apply no_binary_and_factor v a b isAnd ha hb
    (fun y z => (runGates post (runGates pre (List.ofFn y) ++ [z])).getD o false)
  intro x
  rw [← computes x, sole_and_reader_factor pre post o w v hnoread ho x, hpartner x]

lemma critical_or_partner_of_factor (v : Fin 10) (h : (Fin 10 → Bool) → Bool)
    (H : (Fin 10 → Bool) → Bool → Bool)
    (independent : ∀ x, h (Function.update x v true) = h x)
    (factor : ∀ x, edgeValue x = H (Function.update x v false) (x v || h x)) :
    ∀ x, Critical v x → h x = false := by
  intro x hx
  obtain ⟨hxv, hxzero, hxone⟩ := hx
  cases hvalue : h x with
  | false => rfl
  | true =>
    have hzero := factor x
    have hone := factor (Function.update x v true)
    simp only [hxv, Bool.false_or, hvalue, hxzero] at hzero
    simp only [Function.update_self, Function.update_idem, Bool.true_or, hxone] at hone
    have bad : false = true := hzero.trans hone.symm
    cases bad

lemma no_raw_or_factor (v a : Fin 10) (ha : v ≠ a)
    (H : (Fin 10 → Bool) → Bool → Bool) :
    ¬ ∀ x, edgeValue x = H (Function.update x v false) (x v || x a) := by
  intro factor
  have allzero := critical_or_partner_of_factor v (fun x => x a) H
    (fun x => Function.update_of_ne (Ne.symm ha) true x) factor
  obtain ⟨u, huv, hzero, hedge⟩ := one_true_witness v a ha
  have hcrit : Critical v (pairInput a u) := by
    refine ⟨?_, hzero, ?_⟩
    · simp [pairInput, ha, Ne.symm huv]
    · rw [pair_update]
      exact hedge
  have bad := allzero (pairInput a u) hcrit
  simp [pairInput] at bad

lemma eval_or_split (pre post : List Gate) (o v w : Nat) (xs : List Bool) :
    (Circuit.mk (pre ++ ⟨GateOp.or, [v, w]⟩ :: post) o).eval xs =
      (runGates post (runGates pre xs ++
        [(runGates pre xs).getD v false || (runGates pre xs).getD w false])).getD o false := by
  simp [Circuit.eval, Circuit.wires, runGates, List.foldl_append, GateOp.eval]

lemma sole_or_reader_factor {n : Nat} (pre post : List Gate) (o w : Nat) (v : Fin n)
    (hnoread : ∀ g ∈ pre ++ post, v.val ∉ g.inputs) (ho : o ≠ v.val) :
    ∀ x : Fin n → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.or, [v.val, w]⟩ :: post) o).eval (List.ofFn x) =
        (runGates post (runGates pre (List.ofFn (Function.update x v false)) ++
          [x v || (runGates pre (List.ofFn x)).getD w false])).getD o false := by
  intro x
  have preAway := runGates_agreeAway pre
    (fun g hg => hnoread g (by simp [hg])) (agreeAway_update x v false)
  have postAway := runGates_agreeAway post
    (fun g hg => hnoread g (by simp [hg]))
    (agreeAway_append preAway [x v || (runGates pre (List.ofFn x)).getD w false])
  rw [eval_or_split]
  have hv : (runGates pre (List.ofFn x)).getD v.val false = x v := by
    rw [runGates_getD_input _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  rw [hv]
  exact postAway.2 o ho

lemma sole_or_reader_raw_impossible (pre post : List Gate) (o : Nat)
    (v a : Fin 10) (hnoread : ∀ g ∈ pre ++ post, v.val ∉ g.inputs)
    (ho : o ≠ v.val) (ha : v ≠ a) :
    ¬ ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.or, [v.val, a.val]⟩ :: post) o).eval (List.ofFn x) =
        edgeValue x := by
  intro computes
  apply no_raw_or_factor v a ha
    (fun y z => (runGates post (runGates pre (List.ofFn y) ++ [z])).getD o false)
  intro x
  rw [← computes x, sole_or_reader_factor pre post o a.val v hnoread ho x]
  have hraw : (runGates pre (List.ofFn x)).getD a.val false = x a := by
    rw [runGates_getD_input _ _ _ (by simp)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos a.isLt, Option.getD_some]
  rw [hraw]

lemma sole_and_reader_raw_impossible (pre post : List Gate) (o : Nat)
    (v a : Fin 10) (hnoread : ∀ g ∈ pre ++ post, v.val ∉ g.inputs)
    (ho : o ≠ v.val) (ha : v ≠ a) :
    ¬ ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.and, [v.val, a.val]⟩ :: post) o).eval (List.ofFn x) =
        edgeValue x := by
  apply sole_and_reader_binary_impossible pre post o a.val v a a true hnoread ho ha ha
  intro x
  change (runGates pre (List.ofFn x)).getD a.val false = (x a && x a)
  rw [runGates_getD_input _ _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos a.isLt, Option.getD_some, Bool.and_self]


lemma sole_and_reader_partner_critical (pre post : List Gate) (o w : Nat)
    (v : Fin 10) (hnoread : ∀ g ∈ pre ++ post, v.val ∉ g.inputs)
    (ho : o ≠ v.val) (hw : w ≠ v.val)
    (computes : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.and, [v.val, w]⟩ :: post) o).eval (List.ofFn x) =
        edgeValue x) :
    ∀ x, Critical v x → (runGates pre (List.ofFn x)).getD w false = true := by
  apply critical_partner_of_factor v
    (fun x => (runGates pre (List.ofFn x)).getD w false)
    (fun y z => (runGates post (runGates pre (List.ofFn y) ++ [z])).getD o false)
  · intro x
    exact ((runGates_agreeAway pre (fun g hg => hnoread g (by simp [hg]))
      (agreeAway_update x v true)).2 w hw).symm
  · intro x
    rw [← computes x, sole_and_reader_factor pre post o w v hnoread ho x]

lemma sole_or_reader_partner_critical (pre post : List Gate) (o w : Nat)
    (v : Fin 10) (hnoread : ∀ g ∈ pre ++ post, v.val ∉ g.inputs)
    (ho : o ≠ v.val) (hw : w ≠ v.val)
    (computes : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.or, [v.val, w]⟩ :: post) o).eval (List.ofFn x) =
        edgeValue x) :
    ∀ x, Critical v x → (runGates pre (List.ofFn x)).getD w false = false := by
  apply critical_or_partner_of_factor v
    (fun x => (runGates pre (List.ofFn x)).getD w false)
    (fun y z => (runGates post (runGates pre (List.ofFn y) ++ [z])).getD o false)
  · intro x
    exact ((runGates_agreeAway pre (fun g hg => hnoread g (by simp [hg]))
      (agreeAway_update x v true)).2 w hw).symm
  · intro x
    rw [← computes x, sole_or_reader_factor pre post o w v hnoread ho x]

lemma sole_and_reader_negated_impossible (pre post : List Gate) (o w : Nat)
    (v a : Fin 10) (hnoread : ∀ g ∈ pre ++ post, v.val ∉ g.inputs)
    (ho : o ≠ v.val) (ha : v ≠ a)
    (hpartner : ∀ x : Fin 10 → Bool,
      (runGates pre (List.ofFn x)).getD w false = !x a) :
    ¬ ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.and, [v.val, w]⟩ :: post) o).eval (List.ofFn x) =
        edgeValue x := by
  intro computes
  apply no_negated_and_factor v a ha
    (fun y z => (runGates post (runGates pre (List.ofFn y) ++ [z])).getD o false)
  intro x
  rw [← computes x, sole_and_reader_factor pre post o w v hnoread ho x, hpartner x]

lemma sole_or_reader_negated_impossible (pre post : List Gate) (o w : Nat)
    (v a : Fin 10) (hnoread : ∀ g ∈ pre ++ post, v.val ∉ g.inputs)
    (ho : o ≠ v.val) (hw : w ≠ v.val) (ha : v ≠ a)
    (hpartner : ∀ x : Fin 10 → Bool,
      (runGates pre (List.ofFn x)).getD w false = !x a) :
    ¬ ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.or, [v.val, w]⟩ :: post) o).eval (List.ofFn x) =
        edgeValue x := by
  intro computes
  obtain ⟨u, hua, _, huv, hzero, hedge⟩ := two_false_witness v a a ha ha
  have hcrit : Critical v (singleInput u) := by
    refine ⟨?_, hzero, ?_⟩
    · simp [singleInput, Ne.symm huv]
    · rw [single_update]
      exact hedge
  have h := sole_or_reader_partner_critical pre post o w v hnoread ho hw computes
    (singleInput u) hcrit
  rw [hpartner] at h
  simp [singleInput, Ne.symm hua] at h


lemma no_read_of_count_zero (gs : List Gate) (v : Nat)
    (hzero : (gs.flatMap Gate.inputs).count v = 0) :
    ∀ g ∈ gs, v ∉ g.inputs := by
  intro g hg hv
  have hmem : v ∈ gs.flatMap Gate.inputs := List.mem_flatMap.mpr ⟨g, hg, hv⟩
  have hnmem := List.count_eq_zero.mp hzero
  exact hnmem hmem

lemma one_reader_split (gs : List Gate) (v : Nat)
    (hcount : (gs.flatMap Gate.inputs).count v = 1) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate),
      gs = pre ++ g :: post ∧ g.inputs.count v = 1 ∧
        ∀ h ∈ pre ++ post, v ∉ h.inputs := by
  induction gs with
  | nil => simp at hcount
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.count_append] at hcount
    by_cases hz : g.inputs.count v = 0
    · have ht : (gs.flatMap Gate.inputs).count v = 1 := by omega
      obtain ⟨pre, h, post, heq, hh, hnoread⟩ := ih ht
      refine ⟨g :: pre, h, post, ?_, hh, ?_⟩
      · simp [heq]
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact List.count_eq_zero.mp hz
        · exact hnoread k hk
    · have hg : g.inputs.count v = 1 := by omega
      have ht : (gs.flatMap Gate.inputs).count v = 0 := by omega
      exact ⟨[], g, gs, rfl, hg, no_read_of_count_zero gs v ht⟩

lemma strict_gate_reader_forms (g : Gate) (w v : Nat)
    (strict : PEqualNP.MinimumComplex.StrictGate w g)
    (hcount : g.inputs.count v = 1) :
    (g.op = GateOp.not ∧ g.inputs = [v]) ∨
      ∃ u, u ≠ v ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        (g.inputs = [v, u] ∨ g.inputs = [u, v]) := by
  rcases strict with ⟨hop, hlen, hnodup, hvalid⟩ | ⟨hop, hlen, hvalid⟩
  · obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    have hc : ([a, b] : List Nat).count v = 1 := hab ▸ hcount
    by_cases ha : a = v
    · subst a
      have hb : b ≠ v := by intro he; subst b; simp at hc
      exact Or.inr ⟨b, hb, hop, Or.inl hab⟩
    · have hb : b = v := by by_contra hn; simp [ha, hn, Ne.symm ha, Ne.symm hn] at hc
      subst b
      exact Or.inr ⟨a, ha, hop, Or.inr hab⟩
  · have hs : ∃ a, g.inputs = [a] := by
      cases hi : g.inputs with
      | nil => simp [hi] at hlen
      | cons a as =>
        cases as with
        | nil => exact ⟨a, rfl⟩
        | cons b bs => simp [hi] at hlen
    obtain ⟨a, ha⟩ := hs
    have hav : a = v := by
      have hc : ([a] : List Nat).count v = 1 := ha ▸ hcount
      by_contra hn
      simp [hn, Ne.symm hn] at hc
    subst a
    exact Or.inl ⟨hop, ha⟩


lemma eval_swap_binary (pre post : List Gate) (o v w : Nat) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (xs : List Bool) :
    (Circuit.mk (pre ++ ⟨op, [v, w]⟩ :: post) o).eval xs =
      (Circuit.mk (pre ++ ⟨op, [w, v]⟩ :: post) o).eval xs := by
  rcases hop with rfl | rfl
  · rw [eval_and_split, eval_and_split, Bool.and_comm]
  · rw [eval_or_split, eval_or_split, Bool.or_comm]

lemma output_not_input (C : Circuit) (v : Fin 10)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edgeValue x) :
    C.output ≠ v.val := by
  intro hout
  have hs : ∀ a : Fin 10, edgeValue (singleInput a) = false := by decide +kernel
  have hc := computes (singleInput v)
  change (runGates C.gates (List.ofFn (singleInput v))).getD C.output false = _ at hc
  rw [hout, runGates_getD_input _ _ _ (by simp)] at hc
  rw [hs] at hc
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dite_eq_left v.isLt, Option.getD_some, singleInput, decide_true] at hc
  cases hc

lemma single_reader_has_gate_partner (C : Circuit) (v : Fin 10)
    (strict : PEqualNP.MinimumComplex.Strict 10 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edgeValue x)
    (hcount : (C.gates.flatMap Gate.inputs).count v.val = 1) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate),
      C.gates = pre ++ g :: post ∧
      (∀ h ∈ pre ++ post, v.val ∉ h.inputs) ∧
      ((g.op = GateOp.not ∧ g.inputs = [v.val]) ∨
        ∃ w, 10 ≤ w ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          (g.inputs = [v.val, w] ∨ g.inputs = [w, v.val])) := by
  obtain ⟨pre, g, post, hgs, hgcount, hnoread⟩ := one_reader_split C.gates v.val hcount
  refine ⟨pre, g, post, hgs, hnoread, ?_⟩
  have hidx : pre.length < C.gates.length := by simp [hgs]
  have hstrict := strict pre.length hidx
  have hgate : PEqualNP.MinimumComplex.StrictGate (10 + pre.length) g := by
    simpa [hgs] using hstrict
  rcases strict_gate_reader_forms g (10 + pre.length) v.val hgate hgcount with hnot | hbinary
  · exact Or.inl hnot
  · obtain ⟨w, hw, hop, hins⟩ := hbinary
    refine Or.inr ⟨w, ?_, hop, hins⟩
    by_contra hsmall
    have hwlt : w < 10 := by omega
    let a : Fin 10 := ⟨w, hwlt⟩
    have ha : v ≠ a := by intro heq; apply hw; exact congrArg Fin.val heq.symm
    have ho := output_not_input C v computes
    have heval : ∀ x : Fin 10 → Bool,
        (Circuit.mk (pre ++ g :: post) C.output).eval (List.ofFn x) = edgeValue x := by
      intro x
      have heq : Circuit.mk (pre ++ g :: post) C.output = C := by
        cases C
        simp_all
      rw [heq]
      exact computes x
    rcases hop with hand | hor
    · apply sole_and_reader_raw_impossible pre post C.output v a hnoread ho ha
      intro x
      rcases hins with hleft | hright
      · have hg : g = ⟨GateOp.and, [v.val, w]⟩ := by cases g; simp_all
        simpa only [hg] using heval x
      · have hg : g = ⟨GateOp.and, [w, v.val]⟩ := by cases g; simp_all
        rw [eval_swap_binary pre post C.output v.val a.val GateOp.and (Or.inl rfl)]
        simpa only [hg] using heval x
    · apply sole_or_reader_raw_impossible pre post C.output v a hnoread ho ha
      intro x
      rcases hins with hleft | hright
      · have hg : g = ⟨GateOp.or, [v.val, w]⟩ := by cases g; simp_all
        simpa only [hg] using heval x
      · have hg : g = ⟨GateOp.or, [w, v.val]⟩ := by cases g; simp_all
        rw [eval_swap_binary pre post C.output v.val a.val GateOp.or (Or.inr rfl)]
        simpa only [hg] using heval x


lemma critical_input_pattern (v a : Fin 10) (ha : v ≠ a) (b : Bool) :
    ∃ x, Critical v x ∧ x a = b := by
  cases b with
  | false =>
    obtain ⟨u, hua, _, huv, hzero, hedge⟩ := two_false_witness v a a ha ha
    refine ⟨singleInput u, ⟨?_, hzero, ?_⟩, ?_⟩
    · simp [singleInput, Ne.symm huv]
    · rw [single_update]
      exact hedge
    · simp [singleInput, Ne.symm hua]
  | true =>
    obtain ⟨u, huv, hzero, hedge⟩ := one_true_witness v a ha
    refine ⟨pairInput a u, ⟨?_, hzero, ?_⟩, ?_⟩
    · simp [pairInput, ha, Ne.symm huv]
    · rw [pair_update]
      exact hedge
    · simp [pairInput]

lemma no_binary_funnel (v a : Fin 10) (ha : v ≠ a)
    (p : Bool → Bool → Bool) (blocked : ∃ b, p false b = p true b)
    (H : (Fin 10 → Bool) → Bool → Bool) :
    ¬ ∀ x, edgeValue x = H (Function.update x v false) (p (x v) (x a)) := by
  intro factor
  obtain ⟨b, hb⟩ := blocked
  obtain ⟨x, ⟨hxv, hxzero, hxone⟩, hxa⟩ := critical_input_pattern v a ha b
  have hz := factor x
  have ho := factor (Function.update x v true)
  simp only [hxzero, hxv, hxa] at hz
  simp only [hxone, Function.update_self, Function.update_idem,
    Function.update_of_ne (Ne.symm ha), hxa] at ho
  rw [hb] at hz
  have bad : false = true := hz.trans ho.symm
  cases bad

lemma signed_gate_blocked (d : Nat) (hd : d < 4) :
    ∃ b : Bool,
      (if d = 0 then false && b else if d = 1 then false || b else
        if d = 2 then false && !b else !false && b) =
      (if d = 0 then true && b else if d = 1 then true || b else
        if d = 2 then true && !b else !true && b) := by
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

lemma no_signed_gate_funnel (v a : Fin 10) (ha : v ≠ a)
    (d : Nat) (hd : d < 4) (H : (Fin 10 → Bool) → Bool → Bool) :
    ¬ ∀ x, edgeValue x = H (Function.update x v false)
      (if d = 0 then x v && x a else if d = 1 then x v || x a else
        if d = 2 then x v && !x a else !x v && x a) := by
  exact no_binary_funnel v a ha
    (fun x y => if d = 0 then x && y else if d = 1 then x || y else
      if d = 2 then x && !y else !x && y) (signed_gate_blocked d hd) H


lemma every_input_read (C : Circuit)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edgeValue x)
    (v : Fin 10) : 1 ≤ (C.gates.flatMap Gate.inputs).count v.val := by
  by_contra hn
  have hz : (C.gates.flatMap Gate.inputs).count v.val = 0 := by omega
  have hnoread := no_read_of_count_zero C.gates v.val hz
  have next_ne : ∀ a : Fin 10, a ≠ a + 1 := by decide +kernel
  obtain ⟨x, ⟨hxv, hxzero, hxone⟩, hxa⟩ := critical_input_pattern v (v + 1) (next_ne v) false
  have haway := runGates_agreeAway C.gates hnoread (agreeAway_update x v true)
  have heq := haway.2 C.output (output_not_input C v computes)
  change C.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v true)) at heq
  rw [computes, computes, hxzero, hxone] at heq
  cases heq

lemma every_input_read_nat (C : Circuit)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edgeValue x) :
    ∀ i < 10, 1 ≤ (C.gates.flatMap Gate.inputs).count i := by
  intro i hi
  exact every_input_read C computes ⟨i, hi⟩

end PEqualNP.Outside.L_meta_2592_aux

namespace PEqualNP.Outside.L_meta_2592_aux
open PEqualNP.CircuitLowerBounds
lemma getD_snoc_eq_solo (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono_solo (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
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

lemma runGates_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (runGates gs w₁).getD i false = true → (runGates gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : runGates (g :: gs) w₁ =
        runGates gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : runGates (g :: gs) w₂ =
        runGates gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
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
        rw [getD_snoc_eq_solo] at hj
        rw [hlen, getD_snoc_eq_solo]
        exact gateOp_eval_mono_solo g.op (hmono g List.mem_cons_self)
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

lemma eval_not_split (pre post : List Gate) (o v : Nat) (xs : List Bool) :
    (Circuit.mk (pre ++ ⟨GateOp.not, [v]⟩ :: post) o).eval xs =
      (runGates post (runGates pre xs ++ [!(runGates pre xs).getD v false])).getD o false := by
  simp [Circuit.eval, Circuit.wires, runGates, List.foldl_append, GateOp.eval]

lemma sole_not_reader_factor {n : Nat} (pre post : List Gate) (o : Nat) (v : Fin n)
    (hnoread : ∀ g ∈ pre ++ post, v.val ∉ g.inputs) (ho : o ≠ v.val) :
    ∀ x : Fin n → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.not, [v.val]⟩ :: post) o).eval (List.ofFn x) =
        (runGates post (runGates pre (List.ofFn (Function.update x v false)) ++
          [!x v])).getD o false := by
  intro x
  have preAway := runGates_agreeAway pre
    (fun g hg => hnoread g (by simp [hg])) (agreeAway_update x v false)
  have postAway := runGates_agreeAway post
    (fun g hg => hnoread g (by simp [hg])) (agreeAway_append preAway [!x v])
  rw [eval_not_split]
  have hv : (runGates pre (List.ofFn x)).getD v.val false = x v := by
    rw [runGates_getD_input _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  rw [hv]
  exact postAway.2 o ho

lemma critical_exists (v : Fin 10) : ∃ x : Fin 10 → Bool, Critical v x := by
  have next_ne : ∀ u : Fin 10, u ≠ u + 1 := by decide +kernel
  obtain ⟨u, _, _, huv, hzero, hone⟩ :=
    two_false_witness v (v + 1) (v + 1) (next_ne v) (next_ne v)
  refine ⟨singleInput u, ?_, hzero, ?_⟩
  · simp [singleInput, Ne.symm huv]
  · rw [single_update]
    exact hone

lemma sole_not_reader_impossible (pre post : List Gate) (o : Nat) (v : Fin 10)
    (hnoread : ∀ g ∈ pre ++ post, v.val ∉ g.inputs) (ho : o ≠ v.val)
    (hmono : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ¬ ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.not, [v.val]⟩ :: post) o).eval (List.ofFn x) =
        edgeValue x := by
  intro computes
  obtain ⟨x, hxv, hxzero, hxone⟩ := critical_exists v
  let ws := runGates pre (List.ofFn (Function.update x v false))
  have low : (runGates post (ws ++ [true])).getD o false = false := by
    have h := (sole_not_reader_factor pre post o v hnoread ho x).symm.trans (computes x)
    simpa only [hxv, Bool.not_false, hxzero] using h
  have high : (runGates post (ws ++ [false])).getD o false = true := by
    have h := (sole_not_reader_factor pre post o v hnoread ho
      (Function.update x v true)).symm.trans (computes (Function.update x v true))
    simpa only [Function.update_idem, Function.update_self, Bool.not_true, hxone] using h
  have lowTrue := runGates_mono post hmono (ws ++ [false]) (ws ++ [true])
    (by simp) (by
      intro i hi
      by_cases hlt : i < ws.length
      · rw [List.getD_append _ _ _ _ hlt] at hi ⊢
        exact hi
      · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hlt)] at hi
        simp at hi) o high
  rw [low] at lowTrue
  cases lowTrue


lemma sole_not_reader_has_later_not (pre post : List Gate) (o : Nat) (v : Fin 10)
    (hnoread : ∀ g ∈ pre ++ post, v.val ∉ g.inputs) (ho : o ≠ v.val)
    (hfan : PEqualNP.MetaComplexity.FanInTwo
      (Circuit.mk (pre ++ ⟨GateOp.not, [v.val]⟩ :: post) o))
    (computes : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.not, [v.val]⟩ :: post) o).eval (List.ofFn x) =
        edgeValue x) :
    ∃ g ∈ post, g.op = GateOp.not := by
  by_contra hn
  push_neg at hn
  apply sole_not_reader_impossible pre post o v hnoread ho _ computes
  intro g hg
  have hop := (hfan g (by simp [hg])).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with ha | ho | hn'
  · exact Or.inl ha
  · exact Or.inr ho
  · exact False.elim (hn g hg hn')

end PEqualNP.Outside.L_meta_2592_aux


namespace PEqualNP.Outside.L_meta_2592.ReadCount

open PEqualNP.CircuitLowerBounds
open scoped BigOperators

def slots (gs : List Gate) : List ℕ := gs.flatMap Gate.inputs

lemma slots_le_twice (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (slots gs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp [slots]
  | cons g gs ih =>
    have hg := arity g (by simp)
    have ht := ih (fun h hh => arity h (by simp [hh]))
    simp only [slots, List.flatMap_cons, List.length_append, List.length_cons] at ht ⊢
    omega

lemma slots_with_unary (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (unary : ∃ g ∈ gs, g.inputs.length ≤ 1) :
    (slots gs).length + 1 ≤ 2 * gs.length := by
  induction gs with
  | nil => simpa using unary
  | cons g gs ih =>
    have hg := arity g (by simp)
    have ha : ∀ h ∈ gs, h.inputs.length ≤ 2 := fun h hh => arity h (by simp [hh])
    obtain ⟨h, hh, hu⟩ := unary
    rcases List.mem_cons.mp hh with rfl | hh
    · have ht := slots_le_twice gs ha
      simp only [slots, List.flatMap_cons, List.length_append, List.length_cons] at ht ⊢
      omega
    · have ht := ih ha ⟨h, hh, hu⟩
      simp only [slots, List.flatMap_cons, List.length_append, List.length_cons] at ht ⊢
      omega

lemma sum_counts_le (s : Finset ℕ) (l : List ℕ) :
    ∑ i ∈ s, l.count i ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hc (i : ℕ) : (a :: l).count i = l.count i + if i = a then 1 else 0 := by
      by_cases h : i = a
      · subst i
        simp
      · simp [h, Ne.symm h]
    simp_rw [hc]
    rw [Finset.sum_add_distrib]
    have he : (∑ i ∈ s, if i = a then (1 : ℕ) else 0) ≤ 1 := by
      by_cases ha : a ∈ s <;> simp [ha]
    simp only [List.length_cons]
    omega

lemma has_single_reader (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (unary : ∃ g ∈ gs, g.inputs.length ≤ 1)
    (budget : gs.length ≤ 19)
    (inputs : ∀ i < 10, 1 ≤ (slots gs).count i)
    (live : ∀ j < gs.length - 1, 1 ≤ (slots gs).count (10 + j)) :
    ∃ i < 10, (slots gs).count i = 1 := by
  by_contra h
  push_neg at h
  have input_two : ∀ i < 10, 2 ≤ (slots gs).count i := by
    intro i hi
    have := inputs i hi
    have := h i hi
    omega
  have first := Finset.sum_le_sum (s := Finset.range 10)
    (f := fun _ => (2 : ℕ)) (g := fun i => (slots gs).count i)
    (fun i hi => input_two i (Finset.mem_range.mp hi))
  have second := Finset.sum_le_sum (s := Finset.range (gs.length - 1))
    (f := fun _ => (1 : ℕ)) (g := fun j => (slots gs).count (10 + j))
    (fun j hj => live j (Finset.mem_range.mp hj))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at first second
  have total := sum_counts_le (Finset.range (10 + (gs.length - 1))) (slots gs)
  rw [Finset.sum_range_add] at total
  have capacity := slots_with_unary gs arity unary
  omega

lemma strict_has_single_reader (C : Circuit)
    (strict : PEqualNP.MinimumComplex.Strict 10 C)
    (has_not : ∃ g ∈ C.gates, g.op = GateOp.not)
    (budget : C.size ≤ 19)
    (inputs : ∀ i < 10, 1 ≤ (slots C.gates).count i)
    (live : ∀ j < C.size - 1, 1 ≤ (slots C.gates).count (10 + j)) :
    ∃ i < 10, (slots C.gates).count i = 1 := by
  have gate_strict (g : Gate) (hg : g ∈ C.gates) :
      ∃ w, PEqualNP.MinimumComplex.StrictGate w g := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    exact ⟨10 + i, strict i hi⟩
  have arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨w, hw⟩ := gate_strict g hg
    rcases hw with ⟨_, hlen, _, _⟩ | ⟨_, hlen, _⟩ <;> omega
  have unary : ∃ g ∈ C.gates, g.inputs.length ≤ 1 := by
    obtain ⟨g, hg, hn⟩ := has_not
    refine ⟨g, hg, ?_⟩
    obtain ⟨w, hw⟩ := gate_strict g hg
    rcases hw with ⟨ho, _, _, _⟩ | ⟨_, hlen, _⟩
    · rcases ho with ho | ho <;> rw [hn] at ho <;> cases ho
    · omega
  exact has_single_reader C.gates arity unary budget inputs live

open scoped Classical

lemma slots_plus_nots (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length + (if g.op = GateOp.not then 1 else 0) ≤ 2) :
    (slots gs).length + (gs.filter fun g => decide (g.op = GateOp.not)).length ≤
      2 * gs.length := by
  induction gs with
  | nil => simp [slots]
  | cons g gs ih =>
    have hg := arity g (by simp)
    have ht := ih (fun h hh => arity h (by simp [hh]))
    by_cases hn : g.op = GateOp.not
    · simp only [hn, if_true] at hg
      simp only [slots, List.flatMap_cons, List.length_append, List.filter_cons,
        hn, decide_true, Bool.true_eq, if_true, List.length_cons] at ht ⊢
      omega
    · simp only [hn, if_false, Nat.add_zero] at hg
      simp only [slots, List.flatMap_cons, List.length_append, List.filter_cons,
        hn, decide_false, Bool.false_eq_true, if_false, List.length_cons] at ht ⊢
      omega

lemma strict_leaf_count (C : Circuit)
    (strict : PEqualNP.MinimumComplex.Strict 10 C)
    (budget : C.size ≤ 19)
    (inputs : ∀ i < 10, 1 ≤ (slots C.gates).count i)
    (live : ∀ j < C.size - 1, 1 ≤ (slots C.gates).count (10 + j)) :
    PEqualNP.NotBracket.notCount C ≤
      ((Finset.range 10).filter fun i => (slots C.gates).count i = 1).card := by
  have arity : ∀ g ∈ C.gates,
      g.inputs.length + (if g.op = GateOp.not then 1 else 0) ≤ 2 := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    rcases strict i hi with ⟨ho, hl, _, _⟩ | ⟨ho, hl, _⟩
    · rcases ho with ho | ho <;> simp [ho, hl]
    · simp [ho, hl]
  have capacity := slots_plus_nots C.gates arity
  have count_eq : (C.gates.filter fun g => decide (g.op = GateOp.not)).length =
      PEqualNP.NotBracket.notCount C := by
    unfold PEqualNP.NotBracket.notCount
    apply congrArg List.length
    apply List.filter_congr
    intro g hg
    apply Bool.eq_iff_iff.mpr
    simp
  rw [count_eq] at capacity
  change (slots C.gates).length + PEqualNP.NotBracket.notCount C ≤ 2 * C.size at capacity
  have primary := Finset.sum_le_sum (s := Finset.range 10)
    (f := fun _ => (2 : ℕ))
    (g := fun i => (slots C.gates).count i + if (slots C.gates).count i = 1 then 1 else 0)
    (by
      intro i hi
      have positive := inputs i (Finset.mem_range.mp hi)
      split_ifs <;> omega)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul,
    Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at primary
  have internal := Finset.sum_le_sum (s := Finset.range (C.size - 1))
    (f := fun _ => (1 : ℕ)) (g := fun j => (slots C.gates).count (10 + j))
    (fun j hj => live j (Finset.mem_range.mp hj))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at internal
  have total := sum_counts_le (Finset.range (10 + (C.size - 1))) (slots C.gates)
  rw [Finset.sum_range_add] at total
  omega

end PEqualNP.Outside.L_meta_2592.ReadCount

namespace PEqualNP.Outside.L_meta_2592_aux
open PEqualNP.CircuitLowerBounds
open scoped BigOperators Classical

lemma gate_leaf_uses_le (S : Finset Nat) (g : Gate)
    (notarity : g.op = GateOp.not → g.inputs.length ≤ 1)
    (onlyNot : ∀ i ∈ S, i ∈ g.inputs → g.op = GateOp.not) :
    (∑ i ∈ S, g.inputs.count i) ≤ if g.op = GateOp.not then 1 else 0 := by
  by_cases hop : g.op = GateOp.not
  · rw [if_pos hop]
    exact (PEqualNP.Outside.L_meta_2592.ReadCount.sum_counts_le S g.inputs).trans (notarity hop)
  · rw [if_neg hop]
    have hz : ∀ i ∈ S, g.inputs.count i = 0 := by
      intro i hi
      exact List.count_eq_zero.mpr (fun hm => hop (onlyNot i hi hm))
    simp [Finset.sum_eq_zero hz]

lemma leaf_uses_le_nots (S : Finset Nat) (gs : List Gate)
    (notarity : ∀ g ∈ gs, g.op = GateOp.not → g.inputs.length ≤ 1)
    (onlyNot : ∀ g ∈ gs, ∀ i ∈ S, i ∈ g.inputs → g.op = GateOp.not) :
    (∑ i ∈ S, (gs.flatMap Gate.inputs).count i) ≤
      (gs.filter fun g => decide (g.op = GateOp.not)).length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hh := gate_leaf_uses_le S g (notarity g (by simp)) (onlyNot g (by simp))
    have ht := ih (fun h hm => notarity h (by simp [hm]))
      (fun h hm => onlyNot h (by simp [hm]))
    simp only [List.flatMap_cons, List.count_append, Finset.sum_add_distrib]
    by_cases hop : g.op = GateOp.not
    · simp only [if_pos hop] at hh
      simp [hop]
      omega
    · simp only [if_neg hop] at hh
      simp [hop]
      omega

lemma leaf_uses_lt_nots (S : Finset Nat) (gs : List Gate)
    (notarity : ∀ g ∈ gs, g.op = GateOp.not → g.inputs.length ≤ 1)
    (onlyNot : ∀ g ∈ gs, ∀ i ∈ S, i ∈ g.inputs → g.op = GateOp.not)
    (unused : ∃ g ∈ gs, g.op = GateOp.not ∧ ∀ i ∈ S, i ∉ g.inputs) :
    (∑ i ∈ S, (gs.flatMap Gate.inputs).count i) + 1 ≤
      (gs.filter fun g => decide (g.op = GateOp.not)).length := by
  induction gs with
  | nil => simp at unused
  | cons g gs ih =>
    have ha : ∀ h ∈ gs, h.op = GateOp.not → h.inputs.length ≤ 1 :=
      fun h hm => notarity h (by simp [hm])
    have ho : ∀ h ∈ gs, ∀ i ∈ S, i ∈ h.inputs → h.op = GateOp.not :=
      fun h hm => onlyNot h (by simp [hm])
    obtain ⟨h, hm, hn, hu⟩ := unused
    rcases List.mem_cons.mp hm with heq | hm
    · subst h
      have hzero : (∑ i ∈ S, g.inputs.count i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact List.count_eq_zero.mpr (hu i hi)
      have ht := leaf_uses_le_nots S gs ha ho
      simp only [List.flatMap_cons, List.count_append, Finset.sum_add_distrib]
      simp [hzero, hn]
      exact ht
    · have ht := ih ha ho ⟨h, hm, hn, hu⟩
      have hh := gate_leaf_uses_le S g (notarity g (by simp)) (onlyNot g (by simp))
      simp only [List.flatMap_cons, List.count_append, Finset.sum_add_distrib]
      by_cases hop : g.op = GateOp.not
      · simp only [if_pos hop] at hh
        simp [hop]
        omega
      · simp only [if_neg hop] at hh
        simp [hop]
        omega

end PEqualNP.Outside.L_meta_2592_aux

namespace PEqualNP.Outside.L_meta_2592_aux
open PEqualNP.CircuitLowerBounds
open scoped BigOperators Classical

lemma strict_member (C : Circuit) (strict : PEqualNP.MinimumComplex.Strict 10 C)
    (g : Gate) (hg : g ∈ C.gates) : ∃ w, PEqualNP.MinimumComplex.StrictGate w g := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  exact ⟨10 + i, strict i hi⟩

lemma last_not_split (gs : List Gate) (hasNot : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate), gs = pre ++ g :: post ∧
      g.op = GateOp.not ∧ ∀ h ∈ post, h.op ≠ GateOp.not := by
  induction gs with
  | nil => simp at hasNot
  | cons g gs ih =>
    by_cases ht : ∃ h ∈ gs, h.op = GateOp.not
    · obtain ⟨pre, h, post, heq, hn, hlast⟩ := ih ht
      exact ⟨g :: pre, h, post, by simp [heq], hn, hlast⟩
    · obtain ⟨h, hm, hn⟩ := hasNot
      have hsame : h = g := by
        rcases List.mem_cons.mp hm with heq | hm
        · exact heq
        · exact False.elim (ht ⟨h, hm, hn⟩)
      subst h
      refine ⟨[], g, gs, rfl, hn, ?_⟩
      intro h hm heq
      exact ht ⟨h, hm, heq⟩

lemma last_not_avoids_leaves (C : Circuit)
    (strict : PEqualNP.MinimumComplex.Strict 10 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edgeValue x)
    (pre post : List Gate) (g : Gate) (hgs : C.gates = pre ++ g :: post)
    (hn : g.op = GateOp.not) (hlast : ∀ h ∈ post, h.op ≠ GateOp.not) :
    ∀ i ∈ (Finset.range 10).filter (fun i => (C.gates.flatMap Gate.inputs).count i = 1),
      i ∉ g.inputs := by
  intro i hi hmem
  obtain ⟨hirange, hicount⟩ := Finset.mem_filter.mp hi
  have hi10 : i < 10 := Finset.mem_range.mp hirange
  let v : Fin 10 := ⟨i, hi10⟩
  have hgmem : g ∈ C.gates := by simp [hgs]
  obtain ⟨w, hstrict⟩ := strict_member C strict g hgmem
  have hlen : g.inputs.length = 1 := by
    rcases hstrict with ⟨ha, _, _, _⟩ | ⟨_, hl, _⟩
    · rcases ha with ha | ha <;> rw [hn] at ha <;> cases ha
    · exact hl
  have hins : g.inputs = [i] := by
    cases heq : g.inputs with
    | nil => simp [heq] at hlen
    | cons a as =>
      cases as with
      | nil =>
        have hia : i = a := by simpa [heq] using hmem
        exact congrArg (fun z => [z]) hia.symm
      | cons b bs => simp [heq] at hlen
  have hg : g = ⟨GateOp.not, [i]⟩ := by cases g; simp_all
  have hsum : (pre.flatMap Gate.inputs).count i + 1 +
      (post.flatMap Gate.inputs).count i = 1 := by
    simpa [hgs, hins, List.flatMap_append, List.count_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hicount
  have hzero : ((pre ++ post).flatMap Gate.inputs).count i = 0 := by
    simp only [List.flatMap_append, List.count_append]
    omega
  have hnoread : ∀ h ∈ pre ++ post, v.val ∉ h.inputs := no_read_of_count_zero _ i hzero
  have ho := output_not_input C v computes
  have hmono : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := by
    intro h hm
    obtain ⟨w, hh⟩ := strict_member C strict h (by simp [hgs, hm])
    rcases hh with ⟨ha, _, _, _⟩ | ⟨hn, _, _⟩
    · exact ha
    · exact False.elim (hlast h hm hn)
  apply sole_not_reader_impossible pre post C.output v hnoread ho hmono
  intro x
  have heq : Circuit.mk (pre ++ ⟨GateOp.not, [v.val]⟩ :: post) C.output = C := by
    cases C
    simp_all [v]
  rw [heq]
  exact computes x

lemma strict_live_has_binary_leaf (C : Circuit)
    (strict : PEqualNP.MinimumComplex.Strict 10 C)
    (budget : C.size ≤ 19)
    (live : ∀ j < C.size - 1, 1 ≤ (C.gates.flatMap Gate.inputs).count (10 + j))
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edgeValue x) :
    ∃ v : Fin 10, (C.gates.flatMap Gate.inputs).count v.val = 1 ∧
      ∃ g ∈ C.gates, v.val ∈ g.inputs ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) := by
  by_contra hn
  let S := (Finset.range 10).filter fun i => (C.gates.flatMap Gate.inputs).count i = 1
  have onlyNot : ∀ g ∈ C.gates, ∀ i ∈ S, i ∈ g.inputs → g.op = GateOp.not := by
    intro g hg i hi hmem
    obtain ⟨hirange, hicount⟩ := Finset.mem_filter.mp hi
    have hi10 : i < 10 := Finset.mem_range.mp hirange
    obtain ⟨w, hstrict⟩ := strict_member C strict g hg
    rcases hstrict with ⟨hop, _, _, _⟩ | ⟨hop, _, _⟩
    · exact False.elim (hn ⟨⟨i, hi10⟩, hicount, g, hg, hmem, hop⟩)
    · exact hop
  have notarity : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
    intro g hg hop
    obtain ⟨w, hstrict⟩ := strict_member C strict g hg
    rcases hstrict with ⟨ha, _, _, _⟩ | ⟨_, hl, _⟩
    · rcases ha with ha | ha <;> rw [hop] at ha <;> cases ha
    · omega
  obtain ⟨pre, g, post, hgs, hnot, hlast⟩ := last_not_split C.gates hasNot
  have unused : ∃ g ∈ C.gates, g.op = GateOp.not ∧ ∀ i ∈ S, i ∉ g.inputs :=
    ⟨g, by simp [hgs], hnot, last_not_avoids_leaves C strict computes pre post g hgs hnot hlast⟩
  have loss := leaf_uses_lt_nots S C.gates notarity onlyNot unused
  have hsum : (∑ i ∈ S, (C.gates.flatMap Gate.inputs).count i) = S.card := by
    calc
      _ = ∑ _i ∈ S, 1 := Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)
      _ = S.card := by simp
  have count_eq : (C.gates.filter fun g => decide (g.op = GateOp.not)).length =
      PEqualNP.NotBracket.notCount C := by
    unfold PEqualNP.NotBracket.notCount
    apply congrArg List.length
    apply List.filter_congr
    intro g hg
    apply Bool.eq_iff_iff.mpr
    simp
  rw [hsum, count_eq] at loss
  have lower := PEqualNP.Outside.L_meta_2592.ReadCount.strict_leaf_count C strict budget
    (every_input_read_nat C computes) live
  change PEqualNP.NotBracket.notCount C ≤ S.card at lower
  omega


lemma strict_live_binary_leaf_partner (C : Circuit)
    (strict : PEqualNP.MinimumComplex.Strict 10 C)
    (budget : C.size ≤ 19)
    (live : ∀ j < C.size - 1, 1 ≤ (C.gates.flatMap Gate.inputs).count (10 + j))
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edgeValue x) :
    ∃ (v : Fin 10) (pre : List Gate) (g : Gate) (post : List Gate) (w : Nat),
      (C.gates.flatMap Gate.inputs).count v.val = 1 ∧
      C.gates = pre ++ g :: post ∧
      (∀ h ∈ pre ++ post, v.val ∉ h.inputs) ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (g.inputs = [v.val, w] ∨ g.inputs = [w, v.val]) ∧
      10 ≤ w ∧ w < 10 + pre.length := by
  obtain ⟨v, hcount, h, hm, hvm, hop⟩ :=
    strict_live_has_binary_leaf C strict budget live hasNot computes
  obtain ⟨pre, g, post, hgs, hnoread, hform⟩ :=
    single_reader_has_gate_partner C v strict computes hcount
  have hsame : h = g := by
    rw [hgs] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact False.elim (hnoread h (by simp [hm]) hvm)
    · rcases List.mem_cons.mp hm with heq | hm
      · exact heq
      · exact False.elim (hnoread h (by simp [hm]) hvm)
  subst h
  rcases hform with ⟨hn, _⟩ | ⟨w, hw, ho, hins⟩
  · rcases hop with ha | ha <;> rw [hn] at ha <;> cases ha
  · have hidx : pre.length < C.gates.length := by simp [hgs]
    have hgate : PEqualNP.MinimumComplex.StrictGate (10 + pre.length) g := by
      simpa [hgs] using strict pre.length hidx
    have hvalid : ∀ i ∈ g.inputs, i < 10 + pre.length := by
      rcases hgate with ⟨_, _, _, hv⟩ | ⟨_, _, hv⟩ <;> exact hv
    have hmem : w ∈ g.inputs := by rcases hins with hins | hins <;> simp [hins]
    exact ⟨v, pre, g, post, w, hcount, hgs, hnoread, ho, hins, hw, hvalid w hmem⟩

end PEqualNP.Outside.L_meta_2592_aux

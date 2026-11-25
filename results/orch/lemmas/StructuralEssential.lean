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

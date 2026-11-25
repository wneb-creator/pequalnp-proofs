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

end PEqualNP.Outside.L_meta_2592_aux

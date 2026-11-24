import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.Alternative6Certificate

def localPairs : List (Fin 19 × Fin 19) :=
  [(0, 6), (1, 6), (1, 7), (2, 7), (5, 7), (2, 8), (3, 8), (3, 9), (4, 10), (0, 11), (1, 12), (0, 13), (2, 13), (4, 13), (1, 14), (3, 14), (4, 14), (2, 15), (5, 16), (4, 17), (5, 17), (0, 18), (3, 18), (5, 18)]

def leftIdx (i : Fin 6) : Fin 19 := ⟨i.val, by omega⟩

def rightIdx (j : Fin 13) : Fin 19 := ⟨j.val + 6, by omega⟩

def incident (i : Fin 6) (j : Fin 13) : Prop := (leftIdx i, rightIdx j) ∈ localPairs

def target (x : Fin 19 → Bool) : Prop :=
  ∃ i : Fin 6, ∃ j : Fin 13, incident i j ∧ x (leftIdx i) = true ∧ x (rightIdx j) = true

def positive (i : Fin 6) (j : Fin 13) (v : Fin 19) : Bool :=
  decide (v = leftIdx i ∨ v = rightIdx j)

def negative (A : Fin 6 → Bool) (v : Fin 19) : Bool :=
  if h : v.val < 6 then A ⟨v.val, h⟩ else
    let j : Fin 13 := ⟨v.val - 6, by omega⟩
    decide (∀ i : Fin 6, (leftIdx i, rightIdx j) ∈ localPairs → A i = false)

lemma negative_left (A : Fin 6 → Bool) (i : Fin 6) : negative A (leftIdx i) = A i := by
  simp [negative, leftIdx, i.isLt]

lemma negative_right (A : Fin 6 → Bool) (j : Fin 13) :
    negative A (rightIdx j) =
      decide (∀ i : Fin 6, (leftIdx i, rightIdx j) ∈ localPairs → A i = false) := by
  have h : ¬ j.val + 6 < 6 := by omega
  simp [negative, rightIdx, h]
  rfl

lemma positive_target (i : Fin 6) (j : Fin 13) (hij : incident i j) :
    target (positive i j) := by
  exact ⟨i, j, hij, by simp [positive], by simp [positive]⟩

lemma negative_not_target (A : Fin 6 → Bool) : ¬ target (negative A) := by
  rintro ⟨i, j, hij, hi, hj⟩
  rw [negative_left] at hi
  rw [negative_right] at hj
  have hz := of_decide_eq_true hj i hij
  exact Bool.false_ne_true (hz.symm.trans hi)

lemma independent_le_negative (x : Fin 19 → Bool) (hx : ¬ target x) :
    x ≤ negative (fun i => x (leftIdx i)) := by
  intro v
  apply Bool.le_iff_imp.mpr
  intro hv
  by_cases h : v.val < 6
  · let i : Fin 6 := ⟨v.val, h⟩
    have he : v = leftIdx i := by apply Fin.ext; rfl
    rw [he, negative_left]
    simpa only [he] using hv
  · let j : Fin 13 := ⟨v.val - 6, by omega⟩
    have he : v = rightIdx j := by apply Fin.ext; dsimp [rightIdx, j]; omega
    rw [he, negative_right]
    apply decide_eq_true
    intro i hij
    apply Bool.eq_false_of_not_eq_true
    intro hi
    exact hx ⟨i, j, hij, hi, by simpa only [he] using hv⟩

lemma positive_le_of_target (x : Fin 19 → Bool) (hx : target x) :
    ∃ i : Fin 6, ∃ j : Fin 13, incident i j ∧ positive i j ≤ x := by
  rcases hx with ⟨i, j, hij, hi, hj⟩
  refine ⟨i, j, hij, ?_⟩
  intro v
  apply Bool.le_iff_imp.mpr
  intro hv
  simp only [positive, decide_eq_true_eq] at hv
  rcases hv with rfl | rfl
  · exact hi
  · exact hj

lemma certificate (h : (Fin 19 → Bool) → Bool) (hmono : Monotone h) :
    (∀ x, h x = true ↔ target x) ↔
      (∀ i j, incident i j → h (positive i j) = true) ∧
      (∀ A, h (negative A) = false) := by
  constructor
  · intro heq
    constructor
    · intro i j hij
      exact (heq _).mpr (positive_target i j hij)
    · intro A
      exact Bool.eq_false_of_not_eq_true (fun hA => negative_not_target A ((heq _).mp hA))
  · rintro ⟨hpos, hneg⟩ x
    constructor
    · intro hx
      by_contra hfalse
      have ht := Bool.le_iff_imp.mp (hmono (independent_le_negative x hfalse)) hx
      rw [hneg] at ht
      exact Bool.false_ne_true ht
    · intro hx
      obtain ⟨i, j, hij, hle⟩ := positive_le_of_target x hx
      exact Bool.le_iff_imp.mp (hmono hle) (hpos i j hij)

set_option maxRecDepth 100000 in
lemma localPairs_bounds : ∀ e ∈ localPairs, e.1.val < 6 ∧ 6 ≤ e.2.val := by decide

lemma target_iff_pairs (x : Fin 19 → Bool) : target x ↔
    ∃ u v : Fin 19, (u, v) ∈ localPairs ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨leftIdx i, rightIdx j, hij, hi, hj⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    have hb := localPairs_bounds (u, v) huv
    change u.val < 6 ∧ 6 ≤ v.val at hb
    let i : Fin 6 := ⟨u.val, hb.1⟩
    let j : Fin 13 := ⟨v.val - 6, by omega⟩
    have hi : leftIdx i = u := by apply Fin.ext; rfl
    have hj : rightIdx j = v := by apply Fin.ext; dsimp [rightIdx, j]; omega
    refine ⟨i, j, ?_, ?_, ?_⟩
    · simpa only [incident, hi, hj] using huv
    · simpa only [hi] using hu
    · simpa only [hj] using hv

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w


lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp


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



lemma circuit_mono (n : ℕ) (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C) :
    Monotone (fun x : Fin n → Bool => C.eval (List.ofFn x)) := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  change (wiresFrom C.gates (List.ofFn x)).getD C.output false = true →
    (wiresFrom C.gates (List.ofFn y)).getD C.output false = true
  apply wiresFrom_mono C.gates ?_ _ _ (by simp) ?_ C.output
  · intro g hg
    simpa using (hM g hg).1
  · intro i hi
    by_cases hlt : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn] at hi ⊢
      exact Bool.le_iff_imp.mp (hxy ⟨i, hlt⟩) hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact Bool.noConfusion hi

lemma circuit_certificate (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C) :
    (∀ x : Fin 19 → Bool, C.eval (List.ofFn x) = true ↔ target x) ↔
      (∀ i j, incident i j → C.eval (List.ofFn (positive i j)) = true) ∧
      (∀ A, C.eval (List.ofFn (negative A)) = false) :=
  certificate _ (circuit_mono 19 C hM)

lemma verified_computes (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hpos : ∀ i j, incident i j → C.eval (List.ofFn (positive i j)) = true)
    (hneg : ∀ A, C.eval (List.ofFn (negative A)) = false) :
    ∀ x : Fin 19 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 19, (u, v) ∈ localPairs ∧ x u = true ∧ x v = true := by
  intro x
  exact ((circuit_certificate C hM).mpr ⟨hpos, hneg⟩ x).trans (target_iff_pairs x)

lemma positive_test_count : localPairs.length = 24 := by decide

lemma negative_test_count : Fintype.card (Fin 6 → Bool) = 64 := by decide


def baseline29 : Circuit :=
  ⟨[
    ⟨GateOp.or, [6, 11]⟩,
    ⟨GateOp.or, [19, 13]⟩,
    ⟨GateOp.or, [20, 18]⟩,
    ⟨GateOp.and, [0, 21]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [23, 12]⟩,
    ⟨GateOp.or, [24, 14]⟩,
    ⟨GateOp.and, [1, 25]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [27, 13]⟩,
    ⟨GateOp.or, [28, 15]⟩,
    ⟨GateOp.and, [2, 29]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [31, 14]⟩,
    ⟨GateOp.or, [32, 18]⟩,
    ⟨GateOp.and, [3, 33]⟩,
    ⟨GateOp.or, [10, 13]⟩,
    ⟨GateOp.or, [35, 14]⟩,
    ⟨GateOp.or, [36, 17]⟩,
    ⟨GateOp.and, [4, 37]⟩,
    ⟨GateOp.or, [7, 16]⟩,
    ⟨GateOp.or, [39, 17]⟩,
    ⟨GateOp.or, [40, 18]⟩,
    ⟨GateOp.and, [5, 41]⟩,
    ⟨GateOp.or, [22, 26]⟩,
    ⟨GateOp.or, [43, 30]⟩,
    ⟨GateOp.or, [44, 34]⟩,
    ⟨GateOp.or, [45, 38]⟩,
    ⟨GateOp.or, [46, 42]⟩
  ], 47⟩

lemma baseline29_monotone : PEqualNP.MetaComplexity.Monotone2 baseline29 := by
  simp [PEqualNP.MetaComplexity.Monotone2, baseline29]

lemma baseline29_size : baseline29.size = 29 := by decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
lemma baseline29_positive : ∀ i j, incident i j →
    baseline29.eval (List.ofFn (positive i j)) = true := by
  unfold incident
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
lemma baseline29_negative : ∀ A,
    baseline29.eval (List.ofFn (negative A)) = false := by
  decide

lemma baseline29_computes : ∀ x : Fin 19 → Bool,
    baseline29.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 19, (u, v) ∈ localPairs ∧ x u = true ∧ x v = true :=
  verified_computes baseline29 baseline29_monotone baseline29_positive baseline29_negative

end PEqualNP.Outside.L_meta_1477.Alternative6Certificate

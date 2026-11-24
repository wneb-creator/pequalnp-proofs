import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.Triangle9Certificate

def localPairs : List (Fin 27 × Fin 27) :=
  [(0, 9), (1, 9), (4, 9), (1, 10), (2, 10), (5, 10), (2, 11), (3, 11), (3, 12), (4, 12), (8, 12), (4, 13), (5, 13), (0, 14), (5, 14), (8, 14), (1, 15), (6, 15), (0, 16), (2, 16), (1, 17), (3, 17), (7, 17), (2, 18), (4, 18), (6, 18), (3, 19), (5, 19), (6, 19), (4, 20), (7, 20), (5, 21), (7, 21), (6, 22), (8, 22), (0, 23), (6, 23), (7, 23), (1, 24), (8, 24), (2, 25), (7, 25), (8, 25), (0, 26), (3, 26)]

def leftIdx (i : Fin 9) : Fin 27 := ⟨i.val, by omega⟩

def rightIdx (j : Fin 18) : Fin 27 := ⟨j.val + 9, by omega⟩

def incident (i : Fin 9) (j : Fin 18) : Prop := (leftIdx i, rightIdx j) ∈ localPairs

def target (x : Fin 27 → Bool) : Prop :=
  ∃ i : Fin 9, ∃ j : Fin 18, incident i j ∧ x (leftIdx i) = true ∧ x (rightIdx j) = true

def positive (i : Fin 9) (j : Fin 18) (v : Fin 27) : Bool :=
  decide (v = leftIdx i ∨ v = rightIdx j)

def negative (A : Fin 9 → Bool) (v : Fin 27) : Bool :=
  if h : v.val < 9 then A ⟨v.val, h⟩ else
    let j : Fin 18 := ⟨v.val - 9, by omega⟩
    decide (∀ i : Fin 9, (leftIdx i, rightIdx j) ∈ localPairs → A i = false)

lemma negative_left (A : Fin 9 → Bool) (i : Fin 9) : negative A (leftIdx i) = A i := by
  simp [negative, leftIdx, i.isLt]

lemma negative_right (A : Fin 9 → Bool) (j : Fin 18) :
    negative A (rightIdx j) =
      decide (∀ i : Fin 9, (leftIdx i, rightIdx j) ∈ localPairs → A i = false) := by
  have h : ¬ j.val + 9 < 9 := by omega
  simp [negative, rightIdx, h]
  rfl

lemma positive_target (i : Fin 9) (j : Fin 18) (hij : incident i j) :
    target (positive i j) := by
  exact ⟨i, j, hij, by simp [positive], by simp [positive]⟩

lemma negative_not_target (A : Fin 9 → Bool) : ¬ target (negative A) := by
  rintro ⟨i, j, hij, hi, hj⟩
  rw [negative_left] at hi
  rw [negative_right] at hj
  have hz := of_decide_eq_true hj i hij
  exact Bool.false_ne_true (hz.symm.trans hi)

lemma independent_le_negative (x : Fin 27 → Bool) (hx : ¬ target x) :
    x ≤ negative (fun i => x (leftIdx i)) := by
  intro v
  apply Bool.le_iff_imp.mpr
  intro hv
  by_cases h : v.val < 9
  · let i : Fin 9 := ⟨v.val, h⟩
    have he : v = leftIdx i := by apply Fin.ext; rfl
    rw [he, negative_left]
    simpa only [he] using hv
  · let j : Fin 18 := ⟨v.val - 9, by omega⟩
    have he : v = rightIdx j := by apply Fin.ext; dsimp [rightIdx, j]; omega
    rw [he, negative_right]
    apply decide_eq_true
    intro i hij
    apply Bool.eq_false_of_not_eq_true
    intro hi
    exact hx ⟨i, j, hij, hi, by simpa only [he] using hv⟩

lemma positive_le_of_target (x : Fin 27 → Bool) (hx : target x) :
    ∃ i : Fin 9, ∃ j : Fin 18, incident i j ∧ positive i j ≤ x := by
  rcases hx with ⟨i, j, hij, hi, hj⟩
  refine ⟨i, j, hij, ?_⟩
  intro v
  apply Bool.le_iff_imp.mpr
  intro hv
  simp only [positive, decide_eq_true_eq] at hv
  rcases hv with rfl | rfl
  · exact hi
  · exact hj

lemma certificate (h : (Fin 27 → Bool) → Bool) (hmono : Monotone h) :
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
lemma localPairs_bounds : ∀ e ∈ localPairs, e.1.val < 9 ∧ 9 ≤ e.2.val := by decide

lemma target_iff_pairs (x : Fin 27 → Bool) : target x ↔
    ∃ u v : Fin 27, (u, v) ∈ localPairs ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨leftIdx i, rightIdx j, hij, hi, hj⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    have hb := localPairs_bounds (u, v) huv
    change u.val < 9 ∧ 9 ≤ v.val at hb
    let i : Fin 9 := ⟨u.val, hb.1⟩
    let j : Fin 18 := ⟨v.val - 9, by omega⟩
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
    (∀ x : Fin 27 → Bool, C.eval (List.ofFn x) = true ↔ target x) ↔
      (∀ i j, incident i j → C.eval (List.ofFn (positive i j)) = true) ∧
      (∀ A, C.eval (List.ofFn (negative A)) = false) :=
  certificate _ (circuit_mono 27 C hM)

lemma verified_computes (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hpos : ∀ i j, incident i j → C.eval (List.ofFn (positive i j)) = true)
    (hneg : ∀ A, C.eval (List.ofFn (negative A)) = false) :
    ∀ x : Fin 27 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 27, (u, v) ∈ localPairs ∧ x u = true ∧ x v = true := by
  intro x
  exact ((circuit_certificate C hM).mpr ⟨hpos, hneg⟩ x).trans (target_iff_pairs x)

lemma positive_test_count : localPairs.length = 45 := by decide

set_option maxRecDepth 10000 in
lemma negative_test_count : Fintype.card (Fin 9 → Bool) = 512 := by decide

end PEqualNP.Outside.L_meta_1477.Triangle9Certificate

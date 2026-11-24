import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.HyperovalCertificate

def pairEnds : Fin 15 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4),
    (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

def leftIdx (i : Fin 6) : Fin 21 := ⟨i.val, by omega⟩

def rightIdx (j : Fin 15) : Fin 21 := ⟨j.val + 6, by omega⟩

def target (x : Fin 21 → Bool) : Prop :=
  ∃ j : Fin 15, x (rightIdx j) = true ∧
    (x (leftIdx (pairEnds j).1) = true ∨ x (leftIdx (pairEnds j).2) = true)

def endpoint (j : Fin 15) (b : Bool) : Fin 6 :=
  if b then (pairEnds j).1 else (pairEnds j).2

def positive (j : Fin 15) (b : Bool) (v : Fin 21) : Bool :=
  decide (v = leftIdx (endpoint j b) ∨ v = rightIdx j)

def negative (A : Fin 6 → Bool) (v : Fin 21) : Bool :=
  if h : v.val < 6 then A ⟨v.val, h⟩ else
    let j : Fin 15 := ⟨v.val - 6, by omega⟩
    !(A (pairEnds j).1 || A (pairEnds j).2)

lemma negative_left (A : Fin 6 → Bool) (i : Fin 6) : negative A (leftIdx i) = A i := by
  simp [negative, leftIdx, i.isLt]

lemma negative_right (A : Fin 6 → Bool) (j : Fin 15) :
    negative A (rightIdx j) = !(A (pairEnds j).1 || A (pairEnds j).2) := by
  have h : ¬ j.val + 6 < 6 := by omega
  simp [negative, rightIdx, h]

lemma positive_target (j : Fin 15) (b : Bool) : target (positive j b) := by
  refine ⟨j, ?_, ?_⟩
  · simp [positive]
  · cases b <;> simp [positive, endpoint]

lemma negative_not_target (A : Fin 6 → Bool) : ¬ target (negative A) := by
  rintro ⟨j, hj, hi | hi⟩
  · rw [negative_right] at hj
    rw [negative_left] at hi
    simp [hi] at hj
  · rw [negative_right] at hj
    rw [negative_left] at hi
    simp [hi] at hj

lemma independent_le_negative (x : Fin 21 → Bool) (hx : ¬ target x) :
    x ≤ negative (fun i => x (leftIdx i)) := by
  intro v
  apply Bool.le_iff_imp.mpr
  intro hv
  by_cases h : v.val < 6
  · let i : Fin 6 := ⟨v.val, h⟩
    have he : v = leftIdx i := by apply Fin.ext; rfl
    rw [he, negative_left]
    simpa only [he] using hv
  · let j : Fin 15 := ⟨v.val - 6, by omega⟩
    have he : v = rightIdx j := by apply Fin.ext; dsimp [rightIdx, j]; omega
    rw [he, negative_right]
    have hvj : x (rightIdx j) = true := by simpa only [he] using hv
    have h1 : x (leftIdx (pairEnds j).1) = false :=
      Bool.eq_false_of_not_eq_true (fun h1 => hx ⟨j, hvj, Or.inl h1⟩)
    have h2 : x (leftIdx (pairEnds j).2) = false :=
      Bool.eq_false_of_not_eq_true (fun h2 => hx ⟨j, hvj, Or.inr h2⟩)
    simp [h1, h2]

lemma positive_le_of_target (x : Fin 21 → Bool) (hx : target x) :
    ∃ j : Fin 15, ∃ b : Bool, positive j b ≤ x := by
  rcases hx with ⟨j, hj, hleft | hright⟩
  · refine ⟨j, true, ?_⟩
    intro v
    apply Bool.le_iff_imp.mpr
    intro hv
    simp only [positive, decide_eq_true_eq] at hv
    rcases hv with rfl | rfl
    · simpa [endpoint] using hleft
    · exact hj
  · refine ⟨j, false, ?_⟩
    intro v
    apply Bool.le_iff_imp.mpr
    intro hv
    simp only [positive, decide_eq_true_eq] at hv
    rcases hv with rfl | rfl
    · simpa [endpoint] using hright
    · exact hj

lemma certificate (h : (Fin 21 → Bool) → Bool) (hmono : Monotone h) :
    (∀ x, h x = true ↔ target x) ↔
      (∀ j b, h (positive j b) = true) ∧ (∀ A, h (negative A) = false) := by
  constructor
  · intro heq
    constructor
    · intro j b
      exact (heq _).mpr (positive_target j b)
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
      obtain ⟨j, b, hle⟩ := positive_le_of_target x hx
      exact Bool.le_iff_imp.mp (hmono hle) (hpos j b)


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
    (∀ x : Fin 21 → Bool, C.eval (List.ofFn x) = true ↔ target x) ↔
      (∀ j b, C.eval (List.ofFn (positive j b)) = true) ∧
      (∀ A, C.eval (List.ofFn (negative A)) = false) :=
  certificate _ (circuit_mono 21 C hM)

lemma positive_test_count : Fintype.card (Fin 15 × Bool) = 30 := by decide

lemma negative_test_count : Fintype.card (Fin 6 → Bool) = 64 := by decide

end PEqualNP.Outside.L_meta_1477.HyperovalCertificate

import Mathlib.Data.Finset.Basic

namespace PEqualNP.Outside.L_meta_2602_aux.ClausePrune

def BitMonotone {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def singleton {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def linearPart {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Bool :=
  decide (∃ i, f (singleton i) = true ∧ x i = true)

lemma clause_singleton {n : ℕ} (A : Finset (Fin n)) (i : Fin n) :
    (∃ j ∈ A, singleton i j = true) ↔ i ∈ A := by
  simp [singleton]

lemma below_clause {n : ℕ} (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
    (hf : BitMonotone f) (hz : f (fun i => decide (i ∉ A)) = false) :
    ∀ x, f x = true → ∃ i ∈ A, x i = true := by
  intro x hx
  by_contra hno
  have hle : ∀ i, x i = true → decide (i ∉ A) = true := by
    intro i hi
    simp only [decide_eq_true_eq]
    exact fun hiA => hno ⟨i, hiA, hi⟩
  have ht := hf x _ hle hx
  rw [hz] at ht
  contradiction

lemma and_below_clause {n : ℕ} (A : Finset (Fin n)) (f g : (Fin n → Bool) → Bool)
    (hf : BitMonotone f) (hg : BitMonotone g)
    (hspec : ∀ x, (f x && g x) = true → ∃ i ∈ A, x i = true) :
    (∀ x, f x = true → ∃ i ∈ A, x i = true) ∨
      (∀ x, g x = true → ∃ i ∈ A, x i = true) := by
  let z : Fin n → Bool := fun i => decide (i ∉ A)
  have hzero : (f z && g z) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have := hspec z h
    simpa [z] using this
  cases hF : f z
  · exact Or.inl (below_clause A f hf hF)
  · have hG : g z = false := by simpa [hF] using hzero
    exact Or.inr (below_clause A g hg hG)

lemma and_or_clause {n : ℕ} (A : Finset (Fin n)) (f g r : (Fin n → Bool) → Bool)
    (hf : BitMonotone f) (hg : BitMonotone g)
    (hspec : ∀ x, ((f x && g x) || r x) = true ↔ ∃ i ∈ A, x i = true) :
    (∀ x, (f x || r x) = true ↔ ∃ i ∈ A, x i = true) ∨
      (∀ x, (g x || r x) = true ↔ ∃ i ∈ A, x i = true) := by
  have hbound : ∀ x, (f x && g x) = true → ∃ i ∈ A, x i = true := by
    intro x hx
    exact (hspec x).1 (by simp [hx])
  have replace (h : (Fin n → Bool) → Bool)
      (hb : ∀ x, h x = true → ∃ i ∈ A, x i = true)
      (hw : ∀ x, (f x && g x) = true → h x = true) :
      ∀ x, (h x || r x) = true ↔ ∃ i ∈ A, x i = true := by
    intro x
    constructor
    · intro hx
      rcases Bool.or_eq_true_iff.mp hx with hh | hr
      · exact hb x hh
      · exact (hspec x).1 (by simp [hr])
    · intro hx
      rcases Bool.or_eq_true_iff.mp ((hspec x).2 hx) with hh | hr
      · simp [hw x hh]
      · simp [hr]
  rcases and_below_clause A f g hf hg hbound with h | h
  · exact Or.inl (replace f h (fun _ hx => (Bool.and_eq_true_iff.mp hx).1))
  · exact Or.inr (replace g h (fun _ hx => (Bool.and_eq_true_iff.mp hx).2))

lemma singleton_mem {n : ℕ} (A : Finset (Fin n)) (f r : (Fin n → Bool) → Bool)
    (hspec : ∀ x, (f x || r x) = true ↔ ∃ i ∈ A, x i = true)
    (i : Fin n) (hi : f (singleton i) = true) : i ∈ A := by
  apply (clause_singleton A i).mp
  exact (hspec (singleton i)).1 (by simp [hi])

lemma linear_or_clause {n : ℕ} (A : Finset (Fin n)) (f r : (Fin n → Bool) → Bool)
    (hr : BitMonotone r)
    (hspec : ∀ x, (f x || r x) = true ↔ ∃ i ∈ A, x i = true) :
    ∀ x, (linearPart f x || r x) = true ↔ ∃ i ∈ A, x i = true := by
  intro x
  constructor
  · intro hx
    rcases Bool.or_eq_true_iff.mp hx with hl | hrx
    · obtain ⟨i, hi, hxi⟩ := of_decide_eq_true hl
      exact ⟨i, singleton_mem A f r hspec i hi, hxi⟩
    · exact (hspec x).1 (by simp [hrx])
  · rintro ⟨i, hi, hxi⟩
    have hs : (f (singleton i) || r (singleton i)) = true :=
      (hspec (singleton i)).2 ⟨i, hi, by simp [singleton]⟩
    rcases Bool.or_eq_true_iff.mp hs with hf | hs
    · apply Bool.or_eq_true_iff.mpr
      left
      exact decide_eq_true ⟨i, hf, hxi⟩
    · apply Bool.or_eq_true_iff.mpr
      right
      apply hr (singleton i) x ?_ hs
      intro j hj
      simp only [singleton, decide_eq_true_eq] at hj
      simpa [hj] using hxi

lemma linearPart_small {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hsmall : ∀ i j, f (singleton i) = true → f (singleton j) = true → i = j) :
    (∀ x, linearPart f x = false) ∨ ∃ i, ∀ x, linearPart f x = x i := by
  by_cases h : ∃ i, f (singleton i) = true
  · obtain ⟨i, hi⟩ := h
    right
    refine ⟨i, fun x => ?_⟩
    apply Bool.eq_iff_iff.mpr
    simp only [linearPart, decide_eq_true_eq]
    constructor
    · rintro ⟨j, hj, hx⟩
      simpa [hsmall j i hj hi] using hx
    · exact fun hx => ⟨i, hi, hx⟩
  · left
    intro x
    apply Bool.eq_false_iff.mpr
    intro hx
    obtain ⟨i, hi, _⟩ := of_decide_eq_true hx
    exact h ⟨i, hi⟩

lemma shared_linearPart_small {n : ℕ} (A B : Finset (Fin n))
    (f r s : (Fin n → Bool) → Bool)
    (hA : ∀ x, (f x || r x) = true ↔ ∃ i ∈ A, x i = true)
    (hB : ∀ x, (f x || s x) = true ↔ ∃ i ∈ B, x i = true)
    (hsmall : ∀ i j, i ∈ A → i ∈ B → j ∈ A → j ∈ B → i = j) :
    (∀ x, linearPart f x = false) ∨ ∃ i, ∀ x, linearPart f x = x i := by
  apply linearPart_small
  intro i j hi hj
  exact hsmall i j (singleton_mem A f r hA i hi) (singleton_mem B f s hB i hi)
    (singleton_mem A f r hA j hj) (singleton_mem B f s hB j hj)

end PEqualNP.Outside.L_meta_2602_aux.ClausePrune

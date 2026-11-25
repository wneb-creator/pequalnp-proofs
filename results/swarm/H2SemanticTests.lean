import Mathlib

namespace PEqualNP.Outside.L_meta_4970

def starDisjunction {α : Type*} [DecidableEq α] (Q : Finset α) (x : α → Bool) : Bool :=
  decide (∃ i ∈ Q, x i = true)

lemma monotone_factor_eq_star {α : Type*} [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool) (hf : Monotone f)
    (hz : f (fun i => decide (i ∉ Q)) = false)
    (hcontains : ∀ x, starDisjunction Q x = true → f x = true) :
    ∀ x, f x = starDisjunction Q x := by
  intro x
  cases hx : starDisjunction Q x with
  | false =>
      have hzero : ∀ i ∈ Q, x i = false := by
        intro i hi
        cases hxi : x i with
        | false => rfl
        | true =>
            have : starDisjunction Q x = true := by
              simp only [starDisjunction, decide_eq_true_eq]
              exact ⟨i, hi, hxi⟩
            simp [hx] at this
      have hle : x ≤ fun i => decide (i ∉ Q) := by
        intro i
        by_cases hi : i ∈ Q
        · simp [hi, hzero i hi]
        · simp [hi]
      have hfx := hf hle
      rw [hz] at hfx
      exact le_antisymm hfx (by cases f x <;> decide)
  | true => exact hcontains x hx

lemma monotone_and_eq_star {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x && g x) = starDisjunction Q x) :
    (∀ x, f x = starDisjunction Q x) ∨
      (∀ x, g x = starDisjunction Q x) := by
  have hcontains : ∀ x, starDisjunction Q x = true → f x = true ∧ g x = true := by
    intro x hx
    have hh := h x
    rw [hx] at hh
    simpa only [Bool.and_eq_true] using hh
  have hz : starDisjunction Q (fun i => decide (i ∉ Q)) = false := by
    simp [starDisjunction]
  have hzfg : f (fun i => decide (i ∉ Q)) = false ∨
      g (fun i => decide (i ∉ Q)) = false := by
    have hh := h (fun i => decide (i ∉ Q))
    rw [hz] at hh
    simpa only [Bool.and_eq_false_iff] using hh
  rcases hzfg with hzf | hzg
  · exact Or.inl (monotone_factor_eq_star Q f hf hzf fun x hx => (hcontains x hx).1)
  · exact Or.inr (monotone_factor_eq_star Q g hg hzg fun x hx => (hcontains x hx).2)

end PEqualNP.Outside.L_meta_4970


namespace PEqualNP.Outside.L_meta_4970.SparseTests

def singletonInput {α : Type*} [DecidableEq α] (i : α) : α → Bool :=
  fun j => decide (j = i)

def starFun {α : Type*} [DecidableEq α] (Q : Finset α) (x : α → Bool) : Bool :=
  decide (∃ i ∈ Q, x i = true)

lemma star_eq_of_sparse_tests {α : Type*} [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool) (hf : Monotone f)
    (hpos : ∀ i ∈ Q, f (singletonInput i) = true)
    (hneg : f (fun i => decide (i ∉ Q)) = false) :
    ∀ x, f x = starFun Q x := by
  intro x
  cases hx : starFun Q x with
  | false =>
      have hn : ¬ ∃ i ∈ Q, x i = true := by
        simpa only [starFun, decide_eq_false_iff_not] using hx
      have hle : x ≤ fun i => decide (i ∉ Q) := by
        intro i
        by_cases hi : i ∈ Q
        · have hxi : x i = false := by
            cases hxi : x i with
            | false => rfl
            | true => exact False.elim (hn ⟨i, hi, hxi⟩)
          simp [hi, hxi]
        · simp [hi]
      have hfx := hf hle
      rw [hneg] at hfx
      exact le_antisymm hfx (by cases f x <;> decide)
  | true =>
      have hp : ∃ i ∈ Q, x i = true := by
        simpa only [starFun, decide_eq_true_eq] using hx
      obtain ⟨i, hi, hxi⟩ := hp
      have hle : singletonInput i ≤ x := by
        intro j
        by_cases hji : j = i
        · subst j
          simp [singletonInput, hxi]
        · simp [singletonInput, hji]
      have hfx := hf hle
      rw [hpos i hi] at hfx
      exact le_antisymm (by cases f x <;> decide) hfx

def edgeInput {p l : ℕ} (a : Fin p) (b : Fin l) : Fin p ⊕ Fin l → Bool
  | Sum.inl a' => decide (a' = a)
  | Sum.inr b' => decide (b' = b)

def edgeFun {p l : ℕ} (E : Finset (Fin p × Fin l)) (x : Fin p ⊕ Fin l → Bool) : Bool :=
  decide (∃ a b, (a, b) ∈ E ∧ x (Sum.inl a) = true ∧ x (Sum.inr b) = true)

def saturatedIndependentInput {p l : ℕ} (E : Finset (Fin p × Fin l))
    (A : Finset (Fin p)) : Fin p ⊕ Fin l → Bool
  | Sum.inl a => decide (a ∈ A)
  | Sum.inr b => decide (∀ a ∈ A, (a, b) ∉ E)

lemma graph_eq_of_sparse_tests {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : (Fin p ⊕ Fin l → Bool) → Bool) (hf : Monotone f)
    (hpos : ∀ a b, (a, b) ∈ E → f (edgeInput a b) = true)
    (hneg : ∀ A, f (saturatedIndependentInput E A) = false) :
    ∀ x, f x = edgeFun E x := by
  intro x
  cases hx : edgeFun E x with
  | false =>
      have hn : ¬ ∃ a b, (a, b) ∈ E ∧ x (Sum.inl a) = true ∧ x (Sum.inr b) = true := by
        simpa only [edgeFun, decide_eq_false_iff_not] using hx
      let A : Finset (Fin p) := Finset.univ.filter fun a => x (Sum.inl a) = true
      have hle : x ≤ saturatedIndependentInput E A := by
        intro i
        cases i with
        | inl a =>
            cases ha : x (Sum.inl a) <;> simp [saturatedIndependentInput, A, ha]
        | inr b =>
            cases hb : x (Sum.inr b) with
            | false => simp
            | true =>
                have hcompat : ∀ a ∈ A, (a, b) ∉ E := by
                  intro a ha hab
                  have hax : x (Sum.inl a) = true := (Finset.mem_filter.mp ha).2
                  exact hn ⟨a, b, hab, hax, hb⟩
                change true ≤ decide (∀ a ∈ A, (a, b) ∉ E)
                rw [decide_eq_true hcompat]
      have hfx := hf hle
      rw [hneg A] at hfx
      exact le_antisymm hfx (by cases f x <;> decide)
  | true =>
      have hp : ∃ a b, (a, b) ∈ E ∧ x (Sum.inl a) = true ∧ x (Sum.inr b) = true := by
        simpa only [edgeFun, decide_eq_true_eq] using hx
      obtain ⟨a, b, hab, ha, hb⟩ := hp
      have hle : edgeInput a b ≤ x := by
        intro i
        cases i with
        | inl a' =>
            by_cases haa : a' = a
            · subst a'
              simp [edgeInput, ha]
            · simp [edgeInput, haa]
        | inr b' =>
            by_cases hbb : b' = b
            · subst b'
              simp [edgeInput, hb]
            · simp [edgeInput, hbb]
      have hfx := hf hle
      rw [hpos a b hab] at hfx
      exact le_antisymm (by cases f x <;> decide) hfx

end PEqualNP.Outside.L_meta_4970.SparseTests

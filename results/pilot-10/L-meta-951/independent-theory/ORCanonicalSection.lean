import Mathlib

namespace PEqualNP.Outside.L_meta_951.ORCanonical

def familyOR {n m : ℕ} (S : Fin m → Finset (Fin n))
    (x : Fin n → Bool) : Fin m → Bool :=
  fun i => decide (∃ v ∈ S i, x v = true)

def maximalInput {n m : ℕ} (S : Fin m → Finset (Fin n))
    (y : Fin m → Bool) : Fin n → Bool :=
  fun v => decide (∀ i, v ∈ S i → y i = true)

lemma bool_le_of_true_imp {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b <;> simp_all

lemma true_of_bool_le {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  cases a <;> cases b <;> simp_all
  exact (by decide : ¬ (true : Bool) ≤ false) h

lemma bool_eq_of_true_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem maximalInput_monotone {n m : ℕ} (S : Fin m → Finset (Fin n)) :
    Monotone (maximalInput S) := by
  intro y y' hyy v
  apply bool_le_of_true_imp
  intro hv
  have hv' : ∀ i, v ∈ S i → y i = true := of_decide_eq_true hv
  apply decide_eq_true
  intro i hi
  exact true_of_bool_le (hyy i) (hv' i hi)

theorem familyOR_le_iff {n m : ℕ} (S : Fin m → Finset (Fin n))
    (x : Fin n → Bool) (y : Fin m → Bool) :
    familyOR S x ≤ y ↔ x ≤ maximalInput S y := by
  constructor
  · intro h v
    apply bool_le_of_true_imp
    intro hxv
    apply decide_eq_true
    intro i hvi
    have hi : familyOR S x i = true := decide_eq_true ⟨v, hvi, hxv⟩
    exact true_of_bool_le (h i) hi
  · intro h i
    apply bool_le_of_true_imp
    intro hi
    obtain ⟨v, hvi, hxv⟩ := of_decide_eq_true hi
    have hm : maximalInput S y v = true := true_of_bool_le (h v) hxv
    exact (of_decide_eq_true hm) i hvi

theorem canonical_section {n m : ℕ} (S : Fin m → Finset (Fin n))
    (y : Fin m → Bool) (hy : y ∈ Set.range (familyOR S)) :
    familyOR S (maximalInput S y) = y := by
  obtain ⟨x, rfl⟩ := hy
  funext i
  apply bool_eq_of_true_iff
  constructor
  · intro hi
    obtain ⟨v, hvi, hmv⟩ := of_decide_eq_true hi
    exact (of_decide_eq_true hmv) i hvi
  · intro hi
    obtain ⟨v, hvi, hxv⟩ := of_decide_eq_true hi
    apply decide_eq_true
    refine ⟨v, hvi, ?_⟩
    apply decide_eq_true
    intro j hvj
    exact decide_eq_true ⟨v, hvj, hxv⟩

end PEqualNP.Outside.L_meta_951.ORCanonical

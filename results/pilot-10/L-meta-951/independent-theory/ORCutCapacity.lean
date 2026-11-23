import Mathlib

namespace PEqualNP.Outside.L_meta_951.CanonicalCut

theorem canonical_code_injective
    {Input Output Code Selector : Type*}
    [Preorder Input] [PartialOrder Output] [LinearOrder Selector]
    (F : Input → Output) (M : Output → Input) (hM : Monotone M)
    (hsection : ∀ y ∈ Set.range F, F (M y) = y)
    (z : Input → Selector) (hz : Antitone z)
    (code : Input → Code) (decode : Code → Selector → Output)
    (hdecode : ∀ c, Monotone (decode c))
    (hcompute : ∀ x, F x = decode (code x) (z x)) :
    Function.Injective (fun y : Set.range F => code (M y.val)) := by
  intro v w hcode
  change code (M v.val) = code (M w.val) at hcode
  have hv : v.val = decode (code (M v.val)) (z (M v.val)) := by
    exact (hsection v.val v.property).symm.trans (hcompute _)
  have hw : w.val = decode (code (M w.val)) (z (M w.val)) := by
    exact (hsection w.val w.property).symm.trans (hcompute _)
  apply Subtype.ext
  rcases le_total (z (M v.val)) (z (M w.val)) with h | h
  · have hvw : v.val ≤ w.val := by
      rw [hv, hw, hcode]
      exact hdecode _ h
    have heq : z (M v.val) = z (M w.val) :=
      le_antisymm h (hz (hM hvw))
    rw [hv, hw, hcode, heq]
  · have hwv : w.val ≤ v.val := by
      rw [hv, hw, hcode]
      exact hdecode _ h
    have heq : z (M v.val) = z (M w.val) :=
      le_antisymm (hz (hM hwv)) h
    rw [hv, hw, hcode, heq]

theorem range_card_le_code_card
    {Input Output Code Selector : Type*}
    [Preorder Input] [PartialOrder Output] [LinearOrder Selector]
    (F : Input → Output) [Fintype (Set.range F)] [Fintype Code]
    (M : Output → Input) (hM : Monotone M)
    (hsection : ∀ y ∈ Set.range F, F (M y) = y)
    (z : Input → Selector) (hz : Antitone z)
    (code : Input → Code) (decode : Code → Selector → Output)
    (hdecode : ∀ c, Monotone (decode c))
    (hcompute : ∀ x, F x = decode (code x) (z x)) :
    Fintype.card (Set.range F) ≤ Fintype.card Code := by
  exact Fintype.card_le_of_injective _
    (canonical_code_injective F M hM hsection z hz code decode hdecode hcompute)

end PEqualNP.Outside.L_meta_951.CanonicalCut


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


namespace PEqualNP.Outside.L_meta_951.ORCanonical

theorem cut_capacity {n m : ℕ} (S : Fin m → Finset (Fin n))
    {Code : Type*} [Finite Code]
    (z : (Fin n → Bool) → Bool) (hz : Antitone z)
    (code : (Fin n → Bool) → Code)
    (decode : Code → Bool → (Fin m → Bool))
    (hdecode : ∀ c, Monotone (decode c))
    (hcompute : ∀ x, familyOR S x = decode (code x) (z x)) :
    Nat.card (Set.range (familyOR S)) ≤ Nat.card Code := by
  exact Nat.card_le_card_of_injective _
    (CanonicalCut.canonical_code_injective (familyOR S) (maximalInput S)
      (maximalInput_monotone S) (canonical_section S) z hz code decode hdecode hcompute)

theorem bit_cut_capacity {n m k : ℕ} (S : Fin m → Finset (Fin n))
    (z : (Fin n → Bool) → Bool) (hz : Antitone z)
    (code : (Fin n → Bool) → (Fin k → Bool))
    (decode : (Fin k → Bool) → Bool → (Fin m → Bool))
    (hdecode : ∀ c, Monotone (decode c))
    (hcompute : ∀ x, familyOR S x = decode (code x) (z x)) :
    Nat.card (Set.range (familyOR S)) ≤ 2 ^ k := by
  simpa [Nat.card_eq_fintype_card] using
    cut_capacity S z hz code decode hdecode hcompute

end PEqualNP.Outside.L_meta_951.ORCanonical

import Mathlib

namespace PEqualNP.Outside.L_meta_4970

def pureOr {α : Type*} [Fintype α] [DecidableEq α] (Q : Finset α)
    (x : α → Bool) : Bool := decide (∃ q ∈ Q, x q = true)

def complementInput {α : Type*} [DecidableEq α] (Q : Finset α) (i : α) : Bool :=
  decide (i ∉ Q)

lemma below_pureOr_iff_complement_false {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool) (hf : Monotone f) :
    (∀ x, f x = true → pureOr Q x = true) ↔ f (complementInput Q) = false := by
  constructor
  · intro h
    by_contra hfalse
    have htrue : f (complementInput Q) = true := Bool.eq_true_of_not_eq_false hfalse
    have hp := h (complementInput Q) htrue
    unfold pureOr complementInput at hp
    simp at hp
  · intro hfalse x hx
    by_contra hnot
    have hn : ¬ ∃ q ∈ Q, x q = true := by
      simpa only [pureOr, decide_eq_true_eq] using hnot
    have hxle : x ≤ complementInput Q := by
      intro i
      by_cases hi : i ∈ Q
      · have hix : x i = false := by
          cases h : x i
          · rfl
          · exact False.elim (hn ⟨i, hi, h⟩)
        simp [complementInput, hi, hix]
      · simp [complementInput, hi]
    have hle := hf hxle
    rw [hx, hfalse] at hle
    exact (by decide : ¬ (true ≤ false)) hle

lemma and_below_pureOr_choose {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool) (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x && g x) = true → pureOr Q x = true) :
    (∀ x, f x = true → pureOr Q x = true) ∨
      (∀ x, g x = true → pureOr Q x = true) := by
  have hfalse : (f (complementInput Q) && g (complementInput Q)) = false := by
    by_contra hn
    have ht := h (complementInput Q) (Bool.eq_true_of_not_eq_false hn)
    simp [pureOr, complementInput] at ht
  rcases Bool.and_eq_false_iff.mp hfalse with hf0 | hg0
  · exact Or.inl ((below_pureOr_iff_complement_false Q f hf).mpr hf0)
  · exact Or.inr ((below_pureOr_iff_complement_false Q g hg).mpr hg0)

lemma singleton_below_pureOr {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool)
    (h : ∀ x, f x = true → pureOr Q x = true)
    (i : α) (hi : f (fun j => decide (j = i)) = true) : i ∈ Q := by
  have hp := h _ hi
  simpa [pureOr] using hp

lemma demand_split_union {α : Type*} [DecidableEq α] (D A B : Finset α)
    (hD : D ⊆ A ∪ B) :
    ∃ DA DB : Finset α,
      DA ⊆ A ∧ DB ⊆ B ∧ Disjoint DA DB ∧ DA ∪ DB = D := by
  refine ⟨D ∩ A, D \ A, Finset.inter_subset_right, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hiD, hiA⟩ := Finset.mem_sdiff.mp hi
    exact (Finset.mem_union.mp (hD hiD)).resolve_left hiA
  · exact Finset.disjoint_left.mpr (by
      intro i hi hi'
      exact (Finset.mem_sdiff.mp hi').2 (Finset.mem_inter.mp hi).2)
  · ext i
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto

end PEqualNP.Outside.L_meta_4970

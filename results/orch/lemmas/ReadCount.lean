import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.ReadCount

open PEqualNP.CircuitLowerBounds
open scoped BigOperators

def slots (gs : List Gate) : List ℕ := gs.flatMap Gate.inputs

lemma slots_le_twice (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (slots gs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp [slots]
  | cons g gs ih =>
    have hg := arity g (by simp)
    have ht := ih (fun h hh => arity h (by simp [hh]))
    simp only [slots, List.flatMap_cons, List.length_append, List.length_cons] at ht ⊢
    omega

lemma slots_with_unary (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (unary : ∃ g ∈ gs, g.inputs.length ≤ 1) :
    (slots gs).length + 1 ≤ 2 * gs.length := by
  induction gs with
  | nil => simpa using unary
  | cons g gs ih =>
    have hg := arity g (by simp)
    have ha : ∀ h ∈ gs, h.inputs.length ≤ 2 := fun h hh => arity h (by simp [hh])
    obtain ⟨h, hh, hu⟩ := unary
    rcases List.mem_cons.mp hh with rfl | hh
    · have ht := slots_le_twice gs ha
      simp only [slots, List.flatMap_cons, List.length_append, List.length_cons] at ht ⊢
      omega
    · have ht := ih ha ⟨h, hh, hu⟩
      simp only [slots, List.flatMap_cons, List.length_append, List.length_cons] at ht ⊢
      omega

lemma sum_counts_le (s : Finset ℕ) (l : List ℕ) :
    ∑ i ∈ s, l.count i ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hc (i : ℕ) : (a :: l).count i = l.count i + if i = a then 1 else 0 := by
      by_cases h : i = a
      · subst i
        simp
      · simp [h, Ne.symm h]
    simp_rw [hc]
    rw [Finset.sum_add_distrib]
    have he : (∑ i ∈ s, if i = a then (1 : ℕ) else 0) ≤ 1 := by
      by_cases ha : a ∈ s <;> simp [ha]
    simp only [List.length_cons]
    omega

lemma has_single_reader (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (unary : ∃ g ∈ gs, g.inputs.length ≤ 1)
    (budget : gs.length ≤ 19)
    (inputs : ∀ i < 10, 1 ≤ (slots gs).count i)
    (live : ∀ j < gs.length - 1, 1 ≤ (slots gs).count (10 + j)) :
    ∃ i < 10, (slots gs).count i = 1 := by
  by_contra h
  push_neg at h
  have input_two : ∀ i < 10, 2 ≤ (slots gs).count i := by
    intro i hi
    have := inputs i hi
    have := h i hi
    omega
  have first := Finset.sum_le_sum (s := Finset.range 10)
    (f := fun _ => (2 : ℕ)) (g := fun i => (slots gs).count i)
    (fun i hi => input_two i (Finset.mem_range.mp hi))
  have second := Finset.sum_le_sum (s := Finset.range (gs.length - 1))
    (f := fun _ => (1 : ℕ)) (g := fun j => (slots gs).count (10 + j))
    (fun j hj => live j (Finset.mem_range.mp hj))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at first second
  have total := sum_counts_le (Finset.range (10 + (gs.length - 1))) (slots gs)
  rw [Finset.sum_range_add] at total
  have capacity := slots_with_unary gs arity unary
  omega

end PEqualNP.Outside.L_meta_2592.ReadCount

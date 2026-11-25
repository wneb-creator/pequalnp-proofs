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

lemma strict_has_single_reader (C : Circuit)
    (strict : PEqualNP.MinimumComplex.Strict 10 C)
    (has_not : ∃ g ∈ C.gates, g.op = GateOp.not)
    (budget : C.size ≤ 19)
    (inputs : ∀ i < 10, 1 ≤ (slots C.gates).count i)
    (live : ∀ j < C.size - 1, 1 ≤ (slots C.gates).count (10 + j)) :
    ∃ i < 10, (slots C.gates).count i = 1 := by
  have gate_strict (g : Gate) (hg : g ∈ C.gates) :
      ∃ w, PEqualNP.MinimumComplex.StrictGate w g := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    exact ⟨10 + i, strict i hi⟩
  have arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨w, hw⟩ := gate_strict g hg
    rcases hw with ⟨_, hlen, _, _⟩ | ⟨_, hlen, _⟩ <;> omega
  have unary : ∃ g ∈ C.gates, g.inputs.length ≤ 1 := by
    obtain ⟨g, hg, hn⟩ := has_not
    refine ⟨g, hg, ?_⟩
    obtain ⟨w, hw⟩ := gate_strict g hg
    rcases hw with ⟨ho, _, _, _⟩ | ⟨_, hlen, _⟩
    · rcases ho with ho | ho <;> rw [hn] at ho <;> cases ho
    · omega
  exact has_single_reader C.gates arity unary budget inputs live

open scoped Classical

lemma slots_plus_nots (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length + (if g.op = GateOp.not then 1 else 0) ≤ 2) :
    (slots gs).length + (gs.filter fun g => decide (g.op = GateOp.not)).length ≤
      2 * gs.length := by
  induction gs with
  | nil => simp [slots]
  | cons g gs ih =>
    have hg := arity g (by simp)
    have ht := ih (fun h hh => arity h (by simp [hh]))
    by_cases hn : g.op = GateOp.not
    · simp only [hn, if_true] at hg
      simp only [slots, List.flatMap_cons, List.length_append, List.filter_cons,
        hn, decide_true, Bool.true_eq, if_true, List.length_cons] at ht ⊢
      omega
    · simp only [hn, if_false, Nat.add_zero] at hg
      simp only [slots, List.flatMap_cons, List.length_append, List.filter_cons,
        hn, decide_false, Bool.false_eq_true, if_false, List.length_cons] at ht ⊢
      omega

lemma strict_leaf_count (C : Circuit)
    (strict : PEqualNP.MinimumComplex.Strict 10 C)
    (budget : C.size ≤ 19)
    (inputs : ∀ i < 10, 1 ≤ (slots C.gates).count i)
    (live : ∀ j < C.size - 1, 1 ≤ (slots C.gates).count (10 + j)) :
    PEqualNP.NotBracket.notCount C ≤
      ((Finset.range 10).filter fun i => (slots C.gates).count i = 1).card := by
  have arity : ∀ g ∈ C.gates,
      g.inputs.length + (if g.op = GateOp.not then 1 else 0) ≤ 2 := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    rcases strict i hi with ⟨ho, hl, _, _⟩ | ⟨ho, hl, _⟩
    · rcases ho with ho | ho <;> simp [ho, hl]
    · simp [ho, hl]
  have capacity := slots_plus_nots C.gates arity
  have count_eq : (C.gates.filter fun g => decide (g.op = GateOp.not)).length =
      PEqualNP.NotBracket.notCount C := by
    unfold PEqualNP.NotBracket.notCount
    apply congrArg List.length
    apply List.filter_congr
    intro g hg
    apply Bool.eq_iff_iff.mpr
    simp
  rw [count_eq] at capacity
  change (slots C.gates).length + PEqualNP.NotBracket.notCount C ≤ 2 * C.size at capacity
  have primary := Finset.sum_le_sum (s := Finset.range 10)
    (f := fun _ => (2 : ℕ))
    (g := fun i => (slots C.gates).count i + if (slots C.gates).count i = 1 then 1 else 0)
    (by
      intro i hi
      have positive := inputs i (Finset.mem_range.mp hi)
      split_ifs <;> omega)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul,
    Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at primary
  have internal := Finset.sum_le_sum (s := Finset.range (C.size - 1))
    (f := fun _ => (1 : ℕ)) (g := fun j => (slots C.gates).count (10 + j))
    (fun j hj => live j (Finset.mem_range.mp hj))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at internal
  have total := sum_counts_le (Finset.range (10 + (C.size - 1))) (slots C.gates)
  rw [Finset.sum_range_add] at total
  omega

end PEqualNP.Outside.L_meta_2592.ReadCount

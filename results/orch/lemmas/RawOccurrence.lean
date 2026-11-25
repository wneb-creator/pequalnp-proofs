import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.RawOccurrence

open PEqualNP.CircuitLowerBounds

lemma sum_count_le_length (s : Finset ℕ) (l : List ℕ) :
    (∑ i ∈ s, l.count i) ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib]
      have h : (∑ i ∈ s, if a == i then 1 else 0) ≤ 1 := by
        simp only [beq_iff_eq, Finset.sum_ite_eq]
        split <;> omega
      omega

lemma reference_length_le (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      have hg := hfan g (by simp)
      have ht := ih (fun h hh => hfan h (by simp [hh]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

lemma raw_occurrence_bound (C : Circuit) (n : ℕ)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hlive : ∀ i < C.size - 1, n + i ∈ C.gates.flatMap Gate.inputs) :
    (∑ i ∈ Finset.range n, (C.gates.flatMap Gate.inputs).count i) ≤ C.size + 1 := by
  let refs := C.gates.flatMap Gate.inputs
  have htotal := sum_count_le_length (Finset.range (n + (C.size - 1))) refs
  rw [Finset.sum_range_add] at htotal
  have hinternal : C.size - 1 ≤
      ∑ i ∈ Finset.range (C.size - 1), refs.count (n + i) := by
    calc
      C.size - 1 = ∑ i ∈ Finset.range (C.size - 1), (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => by
        exact List.count_pos_iff.mpr (hlive i (Finset.mem_range.mp hi))
  have hlen := reference_length_le C.gates hfan
  change refs.length ≤ 2 * C.size at hlen
  change (∑ i ∈ Finset.range n, refs.count i) ≤ C.size + 1
  omega

lemma unique_raw_input (C : Circuit) (n : ℕ)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hlive : ∀ i < C.size - 1, n + i ∈ C.gates.flatMap Gate.inputs)
    (hused : ∀ i < n, i ∈ C.gates.flatMap Gate.inputs)
    (hsmall : C.size + 1 < 2 * n) :
    ∃ i < n, (C.gates.flatMap Gate.inputs).count i = 1 := by
  have hbound := raw_occurrence_bound C n hfan hlive
  by_contra h
  push Not at h
  have htwo : ∀ i ∈ Finset.range n, 2 ≤ (C.gates.flatMap Gate.inputs).count i := by
    intro i hi
    have hp := List.count_pos_iff.mpr (hused i (Finset.mem_range.mp hi))
    have hn := h i (Finset.mem_range.mp hi)
    omega
  have hs := Finset.sum_le_sum htwo
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hs
  omega

lemma unique_input_of_size26 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hlive : ∀ i < C.size - 1, 14 + i ∈ C.gates.flatMap Gate.inputs)
    (hused : ∀ i < 14, i ∈ C.gates.flatMap Gate.inputs)
    (hsmall : C.size ≤ 26) :
    ∃ i < 14, (C.gates.flatMap Gate.inputs).count i = 1 := by
  exact unique_raw_input C 14 hfan hlive hused (by omega)

lemma padding_preserves_raw_count (C : Circuit) (n i : ℕ)
    (hi : i < n) (hout : n ≤ C.output) :
    ((C.gates ++ [Gate.mk GateOp.or [C.output, C.output]]).flatMap Gate.inputs).count i =
      (C.gates.flatMap Gate.inputs).count i := by
  have hne : C.output ≠ i := by omega
  simp [List.flatMap_append, List.count_append, hne, Ne.symm hne]

end PEqualNP.Outside.L_meta_2732_aux.RawOccurrence

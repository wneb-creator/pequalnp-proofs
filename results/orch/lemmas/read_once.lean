import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds

lemma readCount_sum_le_length (L : List ℕ) (S : Finset ℕ) (hS : S ⊆ L.toFinset) :
    ∑ i ∈ S, L.count i ≤ L.length := by
  have total : (∑ i ∈ L.toFinset, L.count i) = L.length := by
    simpa using Multiset.toFinset_sum_count_eq (L : Multiset ℕ)
  rw [← total]
  exact Finset.sum_le_sum_of_subset_of_nonneg hS (by intros; exact Nat.zero_le _)

lemma readCount_exists_once (n g : ℕ) (L : List ℕ)
    (hports : L.length + 1 ≤ 2 * g) (hsize : g < 2 * n)
    (hinput : ∀ i < n, i ∈ L)
    (hinternal : ∀ j < g - 1, n + j ∈ L) :
    ∃ i < n, L.count i = 1 := by
  by_contra h
  have inputTwo : ∀ i < n, 2 ≤ L.count i := by
    intro i hi
    have positive : 0 < L.count i := List.count_pos_iff.mpr (hinput i hi)
    have ne : L.count i ≠ 1 := by
      intro hc
      exact h ⟨i, hi, hc⟩
    omega
  have internalOne : ∀ j < g - 1, 1 ≤ L.count (n + j) := by
    intro j hj
    exact List.count_pos_iff.mpr (hinternal j hj)
  have inputSum : 2 * n ≤ ∑ i ∈ Finset.range n, L.count i := by
    calc
      2 * n = ∑ _i ∈ Finset.range n, 2 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i hi => inputTwo i (Finset.mem_range.mp hi))
  have internalSum : g - 1 ≤ ∑ j ∈ Finset.range (g - 1), L.count (n + j) := by
    calc
      g - 1 = ∑ _j ∈ Finset.range (g - 1), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j hj => internalOne j (Finset.mem_range.mp hj))
  have allSum : (∑ i ∈ Finset.range n, L.count i) +
      (∑ j ∈ Finset.range (g - 1), L.count (n + j)) ≤ L.length := by
    rw [← Finset.sum_range_add]
    apply readCount_sum_le_length
    intro i hi
    have hi' : i < n + (g - 1) := Finset.mem_range.mp hi
    apply List.mem_toFinset.mpr
    by_cases hn : i < n
    · exact hinput i hn
    · have heq : n + (i - n) = i := by omega
      rw [← heq]
      exact hinternal (i - n) (by omega)
  omega

lemma readCount_slots_bound (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := hfan g (by simp)
    have hrest := ih (fun a ha => hfan a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

lemma readCount_slots_strict (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hsmall : ∃ g ∈ gs, g.inputs.length ≤ 1) :
    (gs.flatMap Gate.inputs).length + 1 ≤ 2 * gs.length := by
  induction gs with
  | nil => simpa using hsmall
  | cons g gs ih =>
    have hg := hfan g (by simp)
    have htail : ∀ a ∈ gs, a.inputs.length ≤ 2 := fun a ha => hfan a (by simp [ha])
    obtain ⟨a, ha, hlen⟩ := hsmall
    rcases List.mem_cons.mp ha with rfl | ha
    · have hrest := readCount_slots_bound gs htail
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
    · have hrest := ih htail ⟨a, ha, hlen⟩
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega

lemma readCount_petersen_budget (C : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hnormal : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (hnot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (hsize : C.size ≤ 19)
    (hinput : ∀ i < 10, i ∈ C.gates.flatMap Gate.inputs)
    (hinternal : ∀ j < C.size - 1, 10 + j ∈ C.gates.flatMap Gate.inputs) :
    ∃ i < 10, (C.gates.flatMap Gate.inputs).count i = 1 := by
  apply readCount_exists_once 10 C.size (C.gates.flatMap Gate.inputs)
  · apply readCount_slots_strict
    · exact fun g hg => (hfan g hg).2
    · obtain ⟨g, hg, hn⟩ := hnot
      exact ⟨g, hg, hnormal g hg hn⟩
  · omega
  · exact hinput
  · exact hinternal

end PEqualNP.Outside.L_meta_2592

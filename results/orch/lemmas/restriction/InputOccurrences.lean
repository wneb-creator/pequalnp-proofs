namespace PEqualNP.Outside.L_meta_2592_aux

theorem length_le_of_count_le (xs ys : List Nat)
    (counts : ∀ i, xs.count i ≤ ys.count i) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have mem : a ∈ ys := List.count_pos_iff.mp (by
      have h := counts a
      simp only [List.count_cons_self] at h
      omega)
    have reduced : ∀ i, xs.count i ≤ (ys.erase a).count i := by
      intro i
      have h := counts i
      by_cases eq : a = i
      · subst i
        rw [List.count_erase_self]
        simp only [List.count_cons_self] at h
        omega
      · simpa [List.count_cons, List.count_erase, eq] using h
    have bound := ih (ys.erase a) reduced
    have len := List.length_erase_of_mem mem
    have pos : 0 < ys.length := by
      have h := List.count_pos_iff.mpr mem
      have h' : ys.count a ≤ ys.length := List.count_le_length
      omega
    simp only [List.length_cons]
    omega

theorem two_reads_cost (reads : List Nat) (n s : Nat) (hs : 0 < s)
    (inputs : ∀ i < n, 2 ≤ reads.count i)
    (internal : ∀ i, n ≤ i → i < n + s - 1 → i ∈ reads) :
    2 * n + s - 1 ≤ reads.length := by
  have bound : (List.range n ++ List.range (n + s - 1)).length ≤ reads.length := by
    apply length_le_of_count_le
    intro i
    by_cases hi : i < n
    · have hi' : i < n + s - 1 := by omega
      simpa [List.count_append, List.count_range, hi, hi'] using inputs i hi
    · by_cases hi' : i < n + s - 1
      · have pos := List.count_pos_iff.mpr (internal i (by omega) hi')
        simpa [List.count_append, List.count_range, hi, hi'] using pos
      · simp [List.count_append, List.count_range, hi, hi']
  simp only [List.length_append, List.length_range] at bound
  omega

theorem exists_rare_input (reads : List Nat) (s : Nat) (hs : 0 < s)
    (budget : s ≤ 19)
    (fanin : reads.length < 2 * s)
    (internal : ∀ i, 10 ≤ i → i < 10 + s - 1 → i ∈ reads) :
    ∃ i < 10, reads.count i ≤ 1 := by
  apply Classical.byContradiction
  intro absent
  have twice : ∀ i < 10, 2 ≤ reads.count i := by
    intro i hi
    apply Nat.le_of_not_lt
    intro small
    exact absent ⟨i, hi, by omega⟩
  have bound := two_reads_cost reads 10 s hs twice internal
  omega

theorem exists_unique_input (reads : List Nat) (s : Nat) (hs : 0 < s)
    (budget : s ≤ 19)
    (fanin : reads.length < 2 * s)
    (internal : ∀ i, 10 ≤ i → i < 10 + s - 1 → i ∈ reads)
    (essential : ∀ i < 10, i ∈ reads) :
    ∃ i < 10, reads.count i = 1 := by
  obtain ⟨i, hi, count⟩ := exists_rare_input reads s hs budget fanin internal
  have pos := List.count_pos_iff.mpr (essential i hi)
  exact ⟨i, hi, by omega⟩

end PEqualNP.Outside.L_meta_2592_aux

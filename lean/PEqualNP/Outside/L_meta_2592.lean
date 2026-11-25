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


theorem flatten_length_le_twice (gs : List (List Nat))
    (fan : ∀ g ∈ gs, g.length ≤ 2) : gs.flatten.length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have head := fan g (by simp)
    have tail := ih (fun h mem => fan h (by simp [mem]))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem flatten_length_lt_twice (gs : List (List Nat))
    (fan : ∀ g ∈ gs, g.length ≤ 2)
    (unary : ∃ g ∈ gs, g.length ≤ 1) : gs.flatten.length < 2 * gs.length := by
  induction gs with
  | nil => simp at unary
  | cons g gs ih =>
    have head := fan g (by simp)
    have tailFan : ∀ h ∈ gs, h.length ≤ 2 := fun h mem => fan h (by simp [mem])
    obtain ⟨h, mem, short⟩ := unary
    rcases List.mem_cons.mp mem with eq | mem
    · subst h
      have tail := flatten_length_le_twice gs tailFan
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      omega
    · have tail := ih tailFan ⟨h, mem, short⟩
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      omega

theorem live_gate_trace_unique_input (gs : List (List Nat))
    (budget : gs.length ≤ 19)
    (fan : ∀ g ∈ gs, g.length ≤ 2)
    (unary : ∃ g ∈ gs, g.length ≤ 1)
    (internal : ∀ i, 10 ≤ i → i < 10 + gs.length - 1 → i ∈ gs.flatten)
    (essential : ∀ i < 10, i ∈ gs.flatten) :
    ∃ i < 10, gs.flatten.count i = 1 := by
  have hs : 0 < gs.length := by
    obtain ⟨g, mem, _⟩ := unary
    cases gs with
    | nil => simp at mem
    | cons h hs => simp
  exact exists_unique_input gs.flatten gs.length hs budget
    (flatten_length_lt_twice gs fan unary) internal essential

end PEqualNP.Outside.L_meta_2592_aux

namespace PEqualNP.Outside.L_meta_2592_aux.ReadOnce

def deletedEdges : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (2, 3), (0, 5), (1, 6), (2, 7),
   (3, 8), (4, 6), (6, 8), (8, 5), (5, 7), (7, 4)]

def deletedFun (x : Fin 9 → Bool) : Bool :=
  deletedEdges.any (fun e => x e.1 && x e.2)

def neighbors (x : Fin 9 → Bool) : Bool := x 0 || x 3 || x 4

def cofactor (b : Bool) (x : Fin 9 → Bool) : Bool :=
  deletedFun x || (b && neighbors x)

def pairInput (i j : Fin 9) : Fin 9 → Bool :=
  fun v => decide (v = i ∨ v = j)

def tripleInput (i j k : Fin 9) : Fin 9 → Bool :=
  fun v => decide (v = i ∨ v = j ∨ v = k)

def adjacentZero (k : Fin 9) : Prop := k = 0 ∨ k = 3 ∨ k = 4

set_option maxRecDepth 4000 in
theorem pair_extension : ∀ i j : Fin 9,
    deletedFun (pairInput i j) = false →
      ∃ k : Fin 9, adjacentZero k ∧ deletedFun (tripleInput i j k) = false := by
  unfold adjacentZero
  decide

theorem triple_neighbors (i j k : Fin 9) (hk : adjacentZero k) :
    neighbors (tripleInput i j k) = true := by
  rcases hk with rfl | rfl | rfl <;> simp [neighbors, tripleInput]

theorem single_independent (i : Fin 9) : deletedFun (pairInput i i) = false := by
  revert i
  decide

theorem or_operand_false_on_boundary
    (h : (Fin 9 → Bool) → Bool) (F : (Fin 9 → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b || h x) = cofactor b x)
    (x : Fin 9 → Bool) (independent : deletedFun x = false)
    (touches : neighbors x = true) : h x = false := by
  cases operand : h x
  · rfl
  · have off := computes false x
    have on := computes true x
    simp [operand, cofactor, independent, touches] at off on
    exact Bool.noConfusion (off.symm.trans on)

theorem and_operand_true_on_boundary
    (h : (Fin 9 → Bool) → Bool) (F : (Fin 9 → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b && h x) = cofactor b x)
    (x : Fin 9 → Bool) (independent : deletedFun x = false)
    (touches : neighbors x = true) : h x = true := by
  cases operand : h x
  · have off := computes false x
    have on := computes true x
    simp [operand, cofactor, independent, touches] at off on
    exact Bool.noConfusion (off.symm.trans on)
  · rfl

theorem or_operand_small_minterm_is_edge
    (h : (Fin 9 → Bool) → Bool) (F : (Fin 9 → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b || h x) = cofactor b x)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → h x = true → h y = true)
    (i j : Fin 9) (active : h (pairInput i j) = true) :
    deletedFun (pairInput i j) = true := by
  cases edge : deletedFun (pairInput i j)
  · obtain ⟨k, hk, independent⟩ := pair_extension i j edge
    have below : ∀ v, pairInput i j v = true → tripleInput i j k v = true := by
      intro v hv
      simp only [pairInput, decide_eq_true_eq] at hv
      simp only [tripleInput, decide_eq_true_eq]
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (Or.inl hv)
    have active' := mono _ _ below active
    have inactive := or_operand_false_on_boundary h F computes _ independent
      (triple_neighbors i j k hk)
    exact Bool.noConfusion (inactive.symm.trans active')
  · rfl

theorem or_read_and_operand_is_edge (i j : Fin 9)
    (F : (Fin 9 → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b || (x i && x j)) = cofactor b x) :
    deletedFun (pairInput i j) = true := by
  apply or_operand_small_minterm_is_edge (fun x => x i && x j) F computes
  · intro x y below active
    have h := Bool.and_eq_true_iff.mp active
    exact Bool.and_eq_true_iff.mpr ⟨below i h.1, below j h.2⟩
  · simp [pairInput]

theorem or_read_or_operand_impossible (i j : Fin 9)
    (F : (Fin 9 → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b || (x i || x j)) = cofactor b x) : False := by
  have edge := or_operand_small_minterm_is_edge (fun x => x i || x j) F computes
    (by
      intro x y below active
      rcases Bool.or_eq_true_iff.mp active with active | active
      · exact Bool.or_eq_true_iff.mpr (Or.inl (below i active))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (below j active)))
    i i (by simp [pairInput])
  have nonedge := single_independent i
  exact Bool.noConfusion (nonedge.symm.trans edge)


theorem neighbor_avoids_pair : ∀ i j : Fin 9,
    ∃ k : Fin 9, adjacentZero k ∧ k ≠ i ∧ k ≠ j := by
  unfold adjacentZero
  decide

theorem singleton_touches (k : Fin 9) (hk : adjacentZero k) :
    neighbors (pairInput k k) = true := by
  rcases hk with rfl | rfl | rfl <;> simp [neighbors, pairInput]

theorem or_read_not_operand_impossible (i : Fin 9)
    (F : (Fin 9 → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b || !x i) = cofactor b x) : False := by
  obtain ⟨k, hk, hki, _⟩ := neighbor_avoids_pair i i
  have boundary := or_operand_false_on_boundary (fun x => !x i) F computes
    (pairInput k k) (single_independent k) (singleton_touches k hk)
  have h : i ≠ k := Ne.symm hki
  simp [pairInput, h] at boundary

theorem and_read_or_operand_impossible (i j : Fin 9)
    (F : (Fin 9 → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b && (x i || x j)) = cofactor b x) : False := by
  obtain ⟨k, hk, hki, hkj⟩ := neighbor_avoids_pair i j
  have boundary := and_operand_true_on_boundary (fun x => x i || x j) F computes
    (pairInput k k) (single_independent k) (singleton_touches k hk)
  have hi : i ≠ k := Ne.symm hki
  have hj : j ≠ k := Ne.symm hkj
  simp [pairInput, hi, hj] at boundary

theorem and_read_and_operand_impossible (i j : Fin 9)
    (F : (Fin 9 → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b && (x i && x j)) = cofactor b x) : False := by
  obtain ⟨k, hk, hki, _⟩ := neighbor_avoids_pair i i
  have boundary := and_operand_true_on_boundary (fun x => x i && x j) F computes
    (pairInput k k) (single_independent k) (singleton_touches k hk)
  have hi : i ≠ k := Ne.symm hki
  simp [pairInput, hi] at boundary

theorem and_read_not_operand_impossible (i : Fin 9)
    (F : (Fin 9 → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b && !x i) = cofactor b x) : False := by
  obtain ⟨k, hk, independent⟩ := pair_extension i i (single_independent i)
  have boundary := and_operand_true_on_boundary (fun x => !x i) F computes
    (tripleInput i i k) independent (triple_neighbors i i k hk)
  simp [tripleInput] at boundary

def elementary (h : (Fin 9 → Bool) → Bool) : Prop :=
  h = (fun _ => false) ∨ h = (fun _ => true) ∨
  (∃ i : Fin 9, h = (fun x => x i)) ∨
  (∃ i j : Fin 9, h = (fun x => x i && x j)) ∨
  (∃ i j : Fin 9, h = (fun x => x i || x j)) ∨
  (∃ i : Fin 9, h = (fun x => !x i))

theorem and_read_elementary_operand_trivial
    (h : (Fin 9 → Bool) → Bool) (F : (Fin 9 → Bool) → Bool → Bool)
    (simple : elementary h)
    (computes : ∀ b x, F x (b && h x) = cofactor b x) : h = (fun _ => true) := by
  rcases simple with eq | eq | ⟨i, eq⟩ | ⟨i, j, eq⟩ | ⟨i, j, eq⟩ | ⟨i, eq⟩
  · subst h
    have boundary := and_operand_true_on_boundary (fun _ => false) F computes
      (pairInput 0 0) (single_independent 0) (singleton_touches 0 (Or.inl rfl))
    exact Bool.noConfusion boundary
  · exact eq
  · subst h
    exact False.elim (and_read_or_operand_impossible i i F (by simpa using computes))
  · subst h
    exact False.elim (and_read_and_operand_impossible i j F computes)
  · subst h
    exact False.elim (and_read_or_operand_impossible i j F computes)
  · subst h
    exact False.elim (and_read_not_operand_impossible i F computes)

theorem or_read_elementary_operand_classification
    (h : (Fin 9 → Bool) → Bool) (F : (Fin 9 → Bool) → Bool → Bool)
    (simple : elementary h)
    (computes : ∀ b x, F x (b || h x) = cofactor b x) :
    h = (fun _ => false) ∨
      ∃ i j : Fin 9, deletedFun (pairInput i j) = true ∧ h = (fun x => x i && x j) := by
  rcases simple with eq | eq | ⟨i, eq⟩ | ⟨i, j, eq⟩ | ⟨i, j, eq⟩ | ⟨i, eq⟩
  · exact Or.inl eq
  · subst h
    have boundary := or_operand_false_on_boundary (fun _ => true) F computes
      (pairInput 0 0) (single_independent 0) (singleton_touches 0 (Or.inl rfl))
    exact Bool.noConfusion boundary
  · subst h
    exact False.elim (or_read_or_operand_impossible i i F (by simpa using computes))
  · subst h
    exact Or.inr ⟨i, j, or_read_and_operand_is_edge i j F computes, rfl⟩
  · subst h
    exact False.elim (or_read_or_operand_impossible i j F computes)
  · subst h
    exact False.elim (or_read_not_operand_impossible i F computes)

end PEqualNP.Outside.L_meta_2592_aux.ReadOnce

namespace PEqualNP.Outside.L_meta_2592_aux

theorem or_read_cofactors_equal {α : Type}
    (f : Bool → α → Bool) (h : α → Bool) (F : α → Bool → Bool)
    (computes : ∀ b x, F x (b || h x) = f b x)
    (x : α) (hx : h x = true) : f false x = f true x := by
  rw [← computes false x, ← computes true x]
  simp [hx]

theorem and_read_cofactors_equal {α : Type}
    (f : Bool → α → Bool) (h : α → Bool) (F : α → Bool → Bool)
    (computes : ∀ b x, F x (b && h x) = f b x)
    (x : α) (hx : h x = false) : f false x = f true x := by
  rw [← computes false x, ← computes true x]
  simp [hx]

theorem or_read_false_below_separation {n : Nat}
    (f : Bool → (Fin n → Bool) → Bool) (h : (Fin n → Bool) → Bool)
    (F : (Fin n → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b || h x) = f b x)
    (operandMono : ∀ x y, (∀ i, x i = true → y i = true) → h x = true → h y = true)
    (x y : Fin n → Bool) (below : ∀ i, x i = true → y i = true)
    (separates : f false y ≠ f true y) : h x = false := by
  cases hx : h x
  · rfl
  · have hy := operandMono x y below hx
    exact False.elim (separates (or_read_cofactors_equal f h F computes y hy))

theorem and_read_true_above_separation {n : Nat}
    (f : Bool → (Fin n → Bool) → Bool) (h : (Fin n → Bool) → Bool)
    (F : (Fin n → Bool) → Bool → Bool)
    (computes : ∀ b x, F x (b && h x) = f b x)
    (operandMono : ∀ x y, (∀ i, x i = true → y i = true) → h x = true → h y = true)
    (x y : Fin n → Bool) (above : ∀ i, y i = true → x i = true)
    (separates : f false y ≠ f true y) : h x = true := by
  have hy : h y = true := by
    cases hy : h y
    · exact False.elim (separates (and_read_cofactors_equal f h F computes y hy))
    · rfl
  exact operandMono y x above hy

theorem not_read_cofactors_antitone {α : Type}
    (f : Bool → α → Bool) (F : α → Bool → Bool)
    (computes : ∀ b x, F x (!b) = f b x)
    (suffixMono : ∀ x, F x false = true → F x true = true) :
    ∀ x, f true x = true → f false x = true := by
  intro x hx
  have hzero : F x false = true := by simpa using (computes true x).trans hx
  have hone := suffixMono x hzero
  simpa using (computes false x).symm.trans hone

theorem not_read_no_positive_separation {α : Type}
    (f : Bool → α → Bool) (F : α → Bool → Bool)
    (computes : ∀ b x, F x (!b) = f b x)
    (suffixMono : ∀ x, F x false = true → F x true = true)
    (x : α) (off : f false x = false) (on : f true x = true) : False := by
  have h := not_read_cofactors_antitone f F computes suffixMono x on
  simp_all

end PEqualNP.Outside.L_meta_2592_aux

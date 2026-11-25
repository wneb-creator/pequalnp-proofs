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

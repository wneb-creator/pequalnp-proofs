import Mathlib

namespace PEqualNP.Outside.L_meta_3678.PrivateUnion

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def UnionProgram (initial xs : List (Finset α)) : Prop :=
  ∀ i < xs.length, ∃ A ∈ initial ++ xs.take i,
    ∃ B ∈ initial ++ xs.take i, xs.getD i ∅ = A ∪ B

lemma program_nil (initial : List (Finset α)) : UnionProgram initial [] := by
  simp [UnionProgram]

lemma program_cons (initial : List (Finset α)) (s : Finset α) (xs : List (Finset α)) :
    UnionProgram initial (s :: xs) ↔
      (∃ A ∈ initial, ∃ B ∈ initial, s = A ∪ B) ∧
        UnionProgram (initial ++ [s]) xs := by
  constructor
  · intro h
    constructor
    · simpa using h 0 (by simp)
    · intro i hi
      have hh := h (i + 1) (by simpa using hi)
      simpa [List.take_succ_cons, List.append_assoc] using hh
  · rintro ⟨h, hh⟩ i hi
    cases i with
    | zero => simpa using h
    | succ i =>
      have hi' : i < xs.length := by simpa using hi
      simpa [List.take_succ_cons, List.append_assoc] using hh i hi'

def projectedCost (φ : Finset α → Finset β) (initial : List (Finset α)) :
    List (Finset α) → ℕ
  | [] => 0
  | s :: xs => (if φ s ∈ initial.map φ then 0 else 1) +
      projectedCost φ (initial ++ [s]) xs

lemma compress (φ : Finset α → Finset β)
    (hunion : ∀ A B, φ (A ∪ B) = φ A ∪ φ B)
    (initial xs : List (Finset α)) (target : List (Finset β))
    (hprog : UnionProgram initial xs)
    (hinit : ∀ A ∈ initial, φ A ∈ target) :
    ∃ ys : List (Finset β), UnionProgram target ys ∧
      (∀ A ∈ initial ++ xs, φ A ∈ target ++ ys) ∧
      ys.length ≤ projectedCost φ initial xs := by
  induction xs generalizing initial target with
  | nil =>
    refine ⟨[], program_nil _, ?_, by simp [projectedCost]⟩
    simpa using hinit
  | cons s xs ih =>
    obtain ⟨⟨A, hA, B, hB, hs⟩, htail⟩ := (program_cons initial s xs).mp hprog
    by_cases hm : φ s ∈ target
    · have hinit' : ∀ X ∈ initial ++ [s], φ X ∈ target := by
        intro X hX
        rcases List.mem_append.mp hX with hX | hX
        · exact hinit X hX
        · have : X = s := List.mem_singleton.mp hX
          subst X
          exact hm
      obtain ⟨ys, hys, hout, hlen⟩ := ih (initial ++ [s]) target htail hinit'
      refine ⟨ys, hys, ?_, ?_⟩
      · intro X hX
        apply hout
        simpa [List.append_assoc] using hX
      · simp only [projectedCost]
        omega
    · have hnew : φ s ∉ initial.map φ := by
        rintro h
        obtain ⟨X, hX, hXs⟩ := List.mem_map.mp h
        exact hm (hXs ▸ hinit X hX)
      have hinit' : ∀ X ∈ initial ++ [s], φ X ∈ target ++ [φ s] := by
        intro X hX
        rcases List.mem_append.mp hX with hX | hX
        · exact List.mem_append_left _ (hinit X hX)
        · have : X = s := List.mem_singleton.mp hX
          subst X
          simp
      obtain ⟨ys, hys, hout, hlen⟩ :=
        ih (initial ++ [s]) (target ++ [φ s]) htail hinit'
      refine ⟨φ s :: ys, ?_, ?_, ?_⟩
      · apply (program_cons target (φ s) ys).mpr
        refine ⟨⟨φ A, hinit A hA, φ B, hinit B hB, ?_⟩, hys⟩
        rw [hs, hunion]
      · intro X hX
        have hx' : X ∈ (initial ++ [s]) ++ xs := by
          simpa [List.append_assoc] using hX
        simpa [List.append_assoc] using hout X hx'
      · simp only [List.length_cons, projectedCost, ite_eq_right hnew]
        omega

lemma fresh_atom_redundant (φ : Finset α → Finset β)
    (hunion : ∀ A B, φ (A ∪ B) = φ A ∪ φ B)
    (initial xs : List (Finset α)) (hprog : UnionProgram initial xs)
    (i : ℕ) (hi : i < xs.length) (p : α) (hp : p ∈ xs.getD i ∅)
    (hprior : ∀ A ∈ xs.take i, p ∉ A)
    (hinit : ∀ A ∈ initial, p ∈ A → φ A = ∅) :
    φ (xs.getD i ∅) ∈ (initial ++ xs.take i).map φ := by
  obtain ⟨A, hA, B, hB, hs⟩ := hprog i hi
  have hp' : p ∈ A ∪ B := hs ▸ hp
  rcases Finset.mem_union.mp hp' with hpA | hpB
  · have hzero : φ A = ∅ := by
      rcases List.mem_append.mp hA with hA | hA
      · exact hinit A hA hpA
      · exact False.elim (hprior A hA hpA)
    have heq : φ (xs.getD i ∅) = φ B := by rw [hs, hunion, hzero, Finset.empty_union]
    rw [heq]
    exact List.mem_map.mpr ⟨B, hB, rfl⟩
  · have hzero : φ B = ∅ := by
      rcases List.mem_append.mp hB with hB | hB
      · exact hinit B hB hpB
      · exact False.elim (hprior B hB hpB)
    have heq : φ (xs.getD i ∅) = φ A := by rw [hs, hunion, hzero, Finset.union_empty]
    rw [heq]
    exact List.mem_map.mpr ⟨A, hA, rfl⟩

end PEqualNP.Outside.L_meta_3678.PrivateUnion

namespace PEqualNP.Outside.L_meta_3678.PrivateUnion

variable {α : Type*} [DecidableEq α]

lemma program_filter (P : Finset α → Prop) [DecidablePred P]
    (hclosed : ∀ A B, P (A ∪ B) → P A ∧ P B)
    (initial xs : List (Finset α)) (hprog : UnionProgram initial xs) :
    UnionProgram (initial.filter fun A => decide (P A))
      (xs.filter fun A => decide (P A)) := by
  induction xs generalizing initial with
  | nil => exact program_nil _
  | cons s xs ih =>
    obtain ⟨⟨A, hA, B, hB, hs⟩, htail⟩ := (program_cons initial s xs).mp hprog
    have hh := ih (initial ++ [s]) htail
    by_cases hPs : P s
    · have hAB : P A ∧ P B := hclosed A B (hs ▸ hPs)
      simp only [List.filter_cons, decide_eq_true hPs, ↓reduceIte]
      apply (program_cons _ _ _).mpr
      constructor
      · refine ⟨A, ?_, B, ?_, hs⟩
        · simpa only [List.mem_filter, decide_eq_true_eq] using And.intro hA hAB.1
        · simpa only [List.mem_filter, decide_eq_true_eq] using And.intro hB hAB.2
      · simpa [List.filter_append, hPs] using hh
    · simpa [List.filter_append, hPs] using hh

lemma program_filter_preserving_initial (P : Finset α → Prop) [DecidablePred P]
    (hclosed : ∀ A B, P (A ∪ B) → P A ∧ P B)
    (initial xs : List (Finset α)) (hprog : UnionProgram initial xs)
    (hinit : ∀ A ∈ initial, P A) :
    UnionProgram initial (xs.filter fun A => decide (P A)) := by
  have hh := program_filter P hclosed initial xs hprog
  have heq : initial.filter (fun A => decide (P A)) = initial := by
    apply List.filter_eq_self.mpr
    intro A hA
    simpa using hinit A hA
  simpa [heq] using hh


lemma program_initial_mono (initial target xs : List (Finset α))
    (hinit : ∀ A ∈ initial, A ∈ target) (hprog : UnionProgram initial xs) :
    UnionProgram target xs := by
  intro i hi
  obtain ⟨A, hA, B, hB, hAB⟩ := hprog i hi
  refine ⟨A, ?_, B, ?_, hAB⟩
  · rcases List.mem_append.mp hA with hA | hA
    · exact List.mem_append_left _ (hinit A hA)
    · exact List.mem_append_right _ hA
  · rcases List.mem_append.mp hB with hB | hB
    · exact List.mem_append_left _ (hinit B hB)
    · exact List.mem_append_right _ hB

lemma program_filter_retain_initial (P : Finset α → Prop) [DecidablePred P]
    (hclosed : ∀ A B, P (A ∪ B) → P A ∧ P B)
    (initial xs : List (Finset α)) (hprog : UnionProgram initial xs) :
    UnionProgram initial (xs.filter fun A => decide (P A)) := by
  apply program_initial_mono (initial.filter fun A => decide (P A)) initial
    (xs.filter fun A => decide (P A))
  · intro A hA
    exact (List.mem_filter.mp hA).1
  · exact program_filter P hclosed initial xs hprog

lemma program_filter_row_subsets (rows initial xs : List (Finset α))
    (hprog : UnionProgram initial xs) :
    UnionProgram initial
      (xs.filter fun A => decide (∃ R ∈ rows, A ⊆ R)) := by
  apply program_filter_retain_initial (fun A => ∃ R ∈ rows, A ⊆ R) _ initial xs hprog
  intro A B hAB
  obtain ⟨R, hR, hsub⟩ := hAB
  exact ⟨⟨R, hR, subset_trans Finset.subset_union_left hsub⟩,
    ⟨R, hR, subset_trans Finset.subset_union_right hsub⟩⟩

lemma rows_mem_after_pruning (rows initial xs : List (Finset α))
    (hrows : ∀ R ∈ rows, R ∈ initial ++ xs) :
    ∀ R ∈ rows, R ∈ initial ++
      xs.filter (fun A => decide (∃ T ∈ rows, A ⊆ T)) := by
  intro R hR
  rcases List.mem_append.mp (hrows R hR) with hinit | hxs
  · exact List.mem_append_left _ hinit
  · apply List.mem_append_right
    apply List.mem_filter.mpr
    exact ⟨hxs, by simpa only [decide_eq_true_eq] using
      (show ∃ T ∈ rows, R ⊆ T from ⟨R, hR, Finset.Subset.refl R⟩)⟩

end PEqualNP.Outside.L_meta_3678.PrivateUnion

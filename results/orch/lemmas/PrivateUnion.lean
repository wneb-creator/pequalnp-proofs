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

end PEqualNP.Outside.L_meta_3678.PrivateUnion

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

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma projectedCost_eq_sum (φ : Finset α → Finset β)
    (initial xs : List (Finset α)) :
    projectedCost φ initial xs =
      ∑ i ∈ Finset.range xs.length,
        if φ (xs.getD i ∅) ∈ (initial ++ xs.take i).map φ then 0 else 1 := by
  induction xs generalizing initial with
  | nil => simp [projectedCost]
  | cons s xs ih =>
    rw [projectedCost, ih]
    rw [List.length_cons, Finset.sum_range_succ']
    simp [List.take_succ_cons, List.append_assoc, Nat.add_comm]

lemma projectedCost_add_skipped_eq (φ : Finset α → Finset β)
    (initial xs : List (Finset α)) :
    projectedCost φ initial xs +
      ((Finset.range xs.length).filter fun i =>
        φ (xs.getD i ∅) ∈ (initial ++ xs.take i).map φ).card = xs.length := by
  rw [projectedCost_eq_sum, Finset.card_eq_sum_ones, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  have hh : ∀ i : ℕ,
      (if φ (xs.getD i ∅) ∈ (initial ++ xs.take i).map φ then 0 else 1) +
        (if φ (xs.getD i ∅) ∈ (initial ++ xs.take i).map φ then 1 else 0) = 1 := by
    intro i
    split <;> simp_all
  simp_rw [hh]
  simp


lemma projectedCost_add_card_le (φ : Finset α → Finset β)
    (initial xs : List (Finset α)) (S : Finset ℕ)
    (hbound : ∀ i ∈ S, i < xs.length)
    (hskip : ∀ i ∈ S, φ (xs.getD i ∅) ∈ (initial ++ xs.take i).map φ) :
    projectedCost φ initial xs + S.card ≤ xs.length := by
  have hcard : S.card ≤ ((Finset.range xs.length).filter fun i =>
      φ (xs.getD i ∅) ∈ (initial ++ xs.take i).map φ).card := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hbound i hi), hskip i hi⟩
  have hsum := projectedCost_add_skipped_eq φ initial xs
  omega

lemma projectedCost_add_le_of_injective (φ : Finset α → Finset β)
    (initial xs : List (Finset α)) {m : ℕ}
    (f : Fin m → Fin xs.length) (hf : Function.Injective f)
    (hskip : ∀ p, φ (xs.getD (f p).val ∅) ∈
      (initial ++ xs.take (f p).val).map φ) :
    projectedCost φ initial xs + m ≤ xs.length := by
  have hinj : Function.Injective (fun p => (f p).val) := by
    intro p q hpq
    exact hf (Fin.ext hpq)
  have hh := projectedCost_add_card_le φ initial xs
    (Finset.univ.image fun p => (f p).val)
    (by
      intro i hi
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hi
      exact (f p).isLt)
    (by
      intro i hi
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hi
      exact hskip p)
  simpa [Finset.card_image_of_injective _ hinj] using hh

lemma projectedCost_add_le_of_first_occurrences
    (φ : Finset α → Finset β) (initial xs : List (Finset α)) {m : ℕ}
    (seen : Fin m → ℕ → Prop) [∀ p, DecidablePred (seen p)]
    (hseen : ∀ p, ∃ i < xs.length, seen p i)
    (hunique : ∀ i < xs.length, ∀ p q, seen p i → seen q i → p = q)
    (hfirst : ∀ p i, i < xs.length → seen p i → (∀ j < i, ¬ seen p j) →
      φ (xs.getD i ∅) ∈ (initial ++ xs.take i).map φ) :
    projectedCost φ initial xs + m ≤ xs.length := by
  let f : Fin m → Fin xs.length := fun p =>
    ⟨Nat.find (hseen p), (Nat.find_spec (hseen p)).1⟩
  have hfseen (p : Fin m) : seen p (f p).val :=
    (Nat.find_spec (hseen p)).2
  apply projectedCost_add_le_of_injective φ initial xs f
  · intro p q hpq
    apply hunique (f p).val (f p).isLt p q (hfseen p)
    simpa [hpq] using hfseen q
  · intro p
    apply hfirst p (f p).val (f p).isLt (hfseen p)
    intro j hj hsj
    have hjbound : j < xs.length := lt_trans hj (f p).isLt
    have hmin := Nat.find_min' (hseen p) ⟨hjbound, hsj⟩
    change Nat.find (hseen p) ≤ j at hmin
    change j < Nat.find (hseen p) at hj
    omega

end PEqualNP.Outside.L_meta_3678.PrivateUnion

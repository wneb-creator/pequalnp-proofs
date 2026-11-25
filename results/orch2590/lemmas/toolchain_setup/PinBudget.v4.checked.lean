import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.PinBudget

open scoped BigOperators

lemma tight_nineteen_budget
    (inputs : Fin 10 → ℕ) (uses : Fin 19 → ℕ) (output : Fin 19)
    (input_lb : ∀ i, 2 ≤ inputs i)
    (gate_lb : ∀ j, j ≠ output → 1 ≤ uses j)
    (total : (∑ i, inputs i) + (∑ j, uses j) ≤ 38) :
    (∀ i, inputs i = 2) ∧
      (∀ j, uses j = if j = output then 0 else 1) := by
  classical
  let base : Fin 19 → ℕ := fun j => if j = output then 0 else 1
  have base_le : ∀ j, base j ≤ uses j := by
    intro j
    by_cases h : j = output
    · simp [base, h]
    · simpa [base, h] using gate_lb j h
  have base_sum : (∑ j, base j) = 18 := by
    have split : (∑ _j : Fin 19, 1) =
        (∑ j : Fin 19, if j = output then 1 else 0) + ∑ j, base j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = output <;> simp [base, h]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at split
    omega
  have input_sum : 20 ≤ ∑ i, inputs i := by
    calc
      20 = ∑ _i : Fin 10, 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => input_lb i
  have gate_sum : 18 ≤ ∑ j, uses j := by
    calc
      18 = ∑ j, base j := base_sum.symm
      _ ≤ _ := Finset.sum_le_sum fun j _ => base_le j
  constructor
  · intro i
    by_contra h
    have strict : 2 < inputs i := by have := input_lb i; omega
    have hs : (∑ _j : Fin 10, 2) < ∑ j, inputs j :=
      Finset.sum_lt_sum (fun j _ => input_lb j) ⟨i, Finset.mem_univ i, strict⟩
    have : 20 < ∑ j, inputs j := by simpa using hs
    omega
  · intro j
    change uses j = base j
    by_contra h
    have strict : base j < uses j := by have := base_le j; omega
    have hs : (∑ k, base k) < ∑ k, uses k :=
      Finset.sum_lt_sum (fun k _ => base_le k) ⟨j, Finset.mem_univ j, strict⟩
    rw [base_sum] at hs
    omega

lemma sum_count_le_length (xs : List ℕ) (S : Finset ℕ) :
    (∑ i ∈ S, xs.count i) ≤ xs.length := by
  have restricted : (∑ i ∈ S, xs.count i) = ∑ i ∈ S ∩ xs.toFinset, xs.count i := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro i hi hn
    have no : i ∉ xs := by
      intro hm
      exact hn (Finset.mem_inter.mpr ⟨hi, List.mem_toFinset.mpr hm⟩)
    exact List.count_eq_zero.mpr no
  rw [restricted]
  calc
    (∑ i ∈ S ∩ xs.toFinset, xs.count i) ≤ ∑ i ∈ xs.toFinset, xs.count i :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => Nat.zero_le _)
    _ = xs.length := List.sum_toFinset_count_eq_length xs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pins (C : Circuit) : List ℕ := C.gates.flatMap Gate.inputs

lemma pins_length_bound (C : Circuit) (h : Monotone2 C) :
    (pins C).length ≤ 2 * C.size := by
  have aux : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
      (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro arity
      have hg := arity g (by simp)
      have hs := ih (fun a ha => arity a (List.mem_cons_of_mem g ha))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  exact aux C.gates (fun g hg => (h g hg).2)

lemma circuit_nineteen_no_sharing (C : Circuit) (h : Monotone2 C)
    (size : C.size = 19) (output : Fin 19)
    (inputs : ∀ i : Fin 10, 2 ≤ (pins C).count i.val)
    (live : ∀ j : Fin 19, j ≠ output → 1 ≤ (pins C).count (10 + j.val)) :
    (∀ i : Fin 10, (pins C).count i.val = 2) ∧
      (∀ j : Fin 19, (pins C).count (10 + j.val) =
        if j = output then 0 else 1) := by
  apply tight_nineteen_budget (fun i => (pins C).count i.val)
    (fun j => (pins C).count (10 + j.val)) output inputs live
  have bound : (∑ i : Fin 10, (pins C).count i.val) +
      (∑ j : Fin 19, (pins C).count (10 + j.val)) ≤ (pins C).length := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (pins C).count i) 10,
      Fin.sum_univ_eq_sum_range (fun j => (pins C).count (10 + j)) 19,
      ← Finset.sum_range_add]
    exact sum_count_le_length (pins C) (Finset.range 29)
  have len := pins_length_bound C h
  rw [size] at len
  omega

lemma nineteen_primary_once_or_no_sharing (C : Circuit) (h : Monotone2 C)
    (size : C.size = 19) (output : Fin 19)
    (essential : ∀ i : Fin 10, 1 ≤ (pins C).count i.val)
    (live : ∀ j : Fin 19, j ≠ output → 1 ≤ (pins C).count (10 + j.val)) :
    (∃ i : Fin 10, (pins C).count i.val = 1) ∨
      ((∀ i : Fin 10, (pins C).count i.val = 2) ∧
        (∀ j : Fin 19, (pins C).count (10 + j.val) =
          if j = output then 0 else 1)) := by
  classical
  by_cases twice : ∀ i : Fin 10, 2 ≤ (pins C).count i.val
  · exact Or.inr (circuit_nineteen_no_sharing C h size output twice live)
  · push_neg at twice
    obtain ⟨i, hi⟩ := twice
    left
    refine ⟨i, ?_⟩
    have := essential i
    omega

lemma small_nineteen_budget {s : ℕ}
    (inputs : Fin 10 → ℕ) (uses : Fin s → ℕ) (output : Fin s)
    (size : s ≤ 19)
    (input_lb : ∀ i, 2 ≤ inputs i)
    (gate_lb : ∀ j, j ≠ output → 1 ≤ uses j)
    (total : (∑ i, inputs i) + (∑ j, uses j) ≤ 2 * s) :
    s = 19 ∧ (∀ i, inputs i = 2) ∧
      (∀ j, uses j = if j = output then 0 else 1) := by
  classical
  let base : Fin s → ℕ := fun j => if j = output then 0 else 1
  have base_le : ∀ j, base j ≤ uses j := by
    intro j
    by_cases h : j = output
    · simp [base, h]
    · simpa [base, h] using gate_lb j h
  have base_sum : 1 + (∑ j, base j) = s := by
    have split : (∑ _j : Fin s, 1) =
        (∑ j : Fin s, if j = output then 1 else 0) + ∑ j, base j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : j = output <;> simp [base, h]
    simpa using split.symm
  have input_sum : 20 ≤ ∑ i, inputs i := by
    calc
      20 = ∑ _i : Fin 10, 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => input_lb i
  have gate_sum : (∑ j, base j) ≤ ∑ j, uses j :=
    Finset.sum_le_sum fun j _ => base_le j
  have exact_size : s = 19 := by omega
  refine ⟨exact_size, ?_, ?_⟩
  · intro i
    by_contra h
    have strict : 2 < inputs i := by have := input_lb i; omega
    have hs : (∑ _j : Fin 10, 2) < ∑ j, inputs j :=
      Finset.sum_lt_sum (fun j _ => input_lb j) ⟨i, Finset.mem_univ i, strict⟩
    have : 20 < ∑ j, inputs j := by simpa using hs
    omega
  · intro j
    change uses j = base j
    by_contra h
    have strict : base j < uses j := by have := base_le j; omega
    have hs : (∑ k, base k) < ∑ k, uses k :=
      Finset.sum_lt_sum (fun k _ => base_le k) ⟨j, Finset.mem_univ j, strict⟩
    omega

lemma at_most_nineteen_primary_once_or_no_sharing (C : Circuit) (h : Monotone2 C)
    (size : C.size ≤ 19) (output : Fin C.size)
    (essential : ∀ i : Fin 10, 1 ≤ (pins C).count i.val)
    (live : ∀ j : Fin C.size, j ≠ output →
      1 ≤ (pins C).count (10 + j.val)) :
    (∃ i : Fin 10, (pins C).count i.val = 1) ∨
      (C.size = 19 ∧ (∀ i : Fin 10, (pins C).count i.val = 2) ∧
        (∀ j : Fin C.size, (pins C).count (10 + j.val) =
          if j = output then 0 else 1)) := by
  classical
  by_cases twice : ∀ i : Fin 10, 2 ≤ (pins C).count i.val
  · right
    apply small_nineteen_budget (fun i => (pins C).count i.val)
      (fun j => (pins C).count (10 + j.val)) output size twice live
    have bound : (∑ i : Fin 10, (pins C).count i.val) +
        (∑ j : Fin C.size, (pins C).count (10 + j.val)) ≤ (pins C).length := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (pins C).count i) 10,
        Fin.sum_univ_eq_sum_range (fun j => (pins C).count (10 + j)) C.size,
        ← Finset.sum_range_add]
      exact sum_count_le_length (pins C) (Finset.range (10 + C.size))
    exact bound.trans (pins_length_bound C h)
  · push Not at twice
    obtain ⟨i, hi⟩ := twice
    left
    refine ⟨i, ?_⟩
    have := essential i
    omega

end PEqualNP.Outside.L_meta_2590_aux.PinBudget

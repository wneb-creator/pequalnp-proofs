import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590

lemma count_dichotomy (s : ℕ) (o : Fin s) (r : Fin 10 → ℕ) (u : Fin s → ℕ)
    (budget : s ≤ 19) (balance : (∑ i, r i) + (∑ j, u j) = 2 * s)
    (live : ∀ j, j ≠ o → 1 ≤ u j) (twice : ∀ i, 2 ≤ r i) :
    s = 19 ∧ (∀ i, r i = 2) ∧ u o = 0 ∧ ∀ j, j ≠ o → u j = 1 := by
  classical
  let base : Fin s → ℕ := fun j => if j = o then 0 else 1
  have base_sum : (∑ j, base j) = s - 1 := by
    simp [base, Finset.sum_ite, Finset.filter_ne']
  have base_le : ∀ j, base j ≤ u j := by
    intro j
    by_cases hj : j = o
    · simp [base, hj]
    · simpa [base, hj] using live j hj
  have rmin : 20 ≤ ∑ i, r i := by
    calc
      20 = ∑ _ : Fin 10, 2 := by norm_num
      _ ≤ ∑ i, r i := Finset.sum_le_sum (fun i _ => twice i)
  have umin : s - 1 ≤ ∑ j, u j := by
    rw [← base_sum]
    exact Finset.sum_le_sum (fun j _ => base_le j)
  have spos : 0 < s := by have := o.isLt; omega
  have size : s = 19 := by omega
  have rsum : (∑ i, r i) = 20 := by omega
  have usum : (∑ j, u j) = s - 1 := by omega
  have requal : ∀ i, r i = 2 := by
    have eq : (∑ _ : Fin 10, 2) = ∑ i, r i := by simpa using rsum.symm
    have each := (Finset.sum_eq_sum_iff_of_le (fun i _ => twice i)).mp eq
    exact fun i => (each i (Finset.mem_univ i)).symm
  have uequal : ∀ j, u j = base j := by
    have eq : (∑ j, base j) = ∑ j, u j := base_sum.trans usum.symm
    have each := (Finset.sum_eq_sum_iff_of_le (fun j _ => base_le j)).mp eq
    exact fun j => (each j (Finset.mem_univ j)).symm
  exact ⟨size, requal, by simp [uequal, base], fun j hj => by simp [uequal, base, hj]⟩

lemma count_fin (L : List ℕ) (m : ℕ) (h : ∀ i ∈ L, i < m) :
    (∑ i : Fin m, L.count i.val) = L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : a < m := h a (by simp)
    have ht : ∀ i ∈ L, i < m := fun i hi => h i (by simp [hi])
    simp only [List.count_cons, List.length_cons]
    rw [Finset.sum_add_distrib, ih ht]
    have one : (∑ i : Fin m, if a == i.val then 1 else 0) = 1 := by
      have same : (fun i : Fin m => if a == i.val then 1 else 0) =
          (fun i => if i = (⟨a, ha⟩ : Fin m) then 1 else 0) := by
        funext i
        by_cases hi : i = (⟨a, ha⟩ : Fin m)
        · subst i
          simp
        · have ne : a ≠ i.val := fun eq => hi (Fin.ext eq.symm)
          simp [hi, ne, beq_iff_eq]
      rw [same]
      simp
    omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma inputs_length (gs : List Gate) :
    (∀ g ∈ gs, g.inputs.length = 2) → (gs.flatMap Gate.inputs).length = 2 * gs.length := by
  induction gs with
  | nil => intro _; simp
  | cons g gs ih =>
    intro h
    have hg := h g (by simp)
    have ht : ∀ g ∈ gs, g.inputs.length = 2 := fun g hg => h g (by simp [hg])
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [hg, ih ht]
    omega

lemma inputs_range (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 10 C) :
    ∀ i ∈ C.gates.flatMap Gate.inputs, i < 10 + C.size := by
  intro i hi
  obtain ⟨g, hg, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have gate : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] :=
    List.getD_eq_getElem _ _ hj
  have earlier := ao.2.1 j hj i (by simpa [gate] using hi)
  change i < 10 + C.gates.length
  omega

lemma circuit_balance (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 10 C) :
    (∑ i : Fin 10, (C.gates.flatMap Gate.inputs).count i.val) +
      (∑ j : Fin C.size, (C.gates.flatMap Gate.inputs).count (10 + j.val)) = 2 * C.size := by
  have h := count_fin (C.gates.flatMap Gate.inputs) (10 + C.size) (inputs_range C ao)
  rw [Fin.sum_univ_add] at h
  exact h.trans (inputs_length C.gates ao.2.2)

lemma tree_of_twice (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 10 C)
    (budget : C.size ≤ 19) (o : Fin C.size) (hout : C.output = 10 + o.val)
    (live : ∀ j : Fin C.size, j ≠ o →
      1 ≤ (C.gates.flatMap Gate.inputs).count (10 + j.val))
    (twice : ∀ i : Fin 10, 2 ≤ (C.gates.flatMap Gate.inputs).count i.val) :
    ((C.output :: C.gates.flatMap Gate.inputs).filter (fun i => decide (10 ≤ i))).Nodup := by
  have dich := count_dichotomy C.size o
    (fun i => (C.gates.flatMap Gate.inputs).count i.val)
    (fun j => (C.gates.flatMap Gate.inputs).count (10 + j.val))
    budget (circuit_balance C ao) live twice
  apply List.nodup_iff_count_le_one.mpr
  intro i
  by_cases hi : 10 ≤ i
  · rw [List.count_filter (by simp [hi])]
    by_cases bound : i < 10 + C.size
    · let j : Fin C.size := ⟨i - 10, by omega⟩
      have eq : i = 10 + j.val := by dsimp [j]; omega
      by_cases jo : j = o
      · rw [eq, jo]
        simp [hout, dich.2.2.1]
      · have ne : C.output ≠ i := by
          rw [hout, eq]
          exact fun h => jo (Fin.ext (by omega))
        rw [eq, List.count_cons, dich.2.2.2 j jo]
        simp [beq_iff_eq, ← eq, ne]
    · have absent : i ∉ C.gates.flatMap Gate.inputs := fun hm => bound (inputs_range C ao i hm)
      have ne : C.output ≠ i := by rw [hout]; have := o.isLt; omega
      simp [List.count_eq_zero.mpr absent, ne]
  · have absent : i ∉ ((C.output :: C.gates.flatMap Gate.inputs).filter
        (fun i => decide (10 ≤ i))) := by simp [hi]
    rw [List.count_eq_zero.mpr absent]
    omega

end PEqualNP.Outside.L_meta_2590

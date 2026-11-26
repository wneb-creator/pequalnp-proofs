import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2456_1
    (search :
      let f := fun x : Fin 10 → Bool =>
        ([(0, 2), (2, 3), (3, 1), (0, 4), (4, 5), (5, 6), (6, 1),
          (0, 7), (7, 8), (8, 9), (9, 1)] : List (Fin 10 × Fin 10)).any
          (fun e => x e.1 && x e.2)
      ∃ (i : Fin 10) (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 13 ∧
        ∀ x : Fin 10 → Bool,
          (Minimal (fun y => f y = true ∧ y i = x i) x ∨
           Maximal (fun y => f y = false ∧ y i = x i) x) →
          D.eval (List.ofFn x ++ [!(x i)]) = f x)
    (mono : ∀ (n : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 D → ∀ b : Bool,
      Monotone (fun x : Fin n → Bool => D.eval (List.ofFn x ++ [b]))) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧
      (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) =
        ([(0, 2), (2, 3), (3, 1), (0, 4), (4, 5), (5, 6), (6, 1),
          (0, 7), (7, 8), (8, 9), (9, 1)] : List (Fin 10 × Fin 10)).any
          (fun e => x e.1 && x e.2)) ∧
      ∃ g : PEqualNP.CircuitLowerBounds.Gate,
        C.gates.head? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not := by
  let f := fun x : Fin 10 → Bool =>
    ([(0, 2), (2, 3), (3, 1), (0, 4), (4, 5), (5, 6), (6, 1),
      (0, 7), (7, 8), (8, 9), (9, 1)] : List (Fin 10 × Fin 10)).any
      (fun e => x e.1 && x e.2)
  obtain ⟨i, D, hD, hsize, hcheck⟩ := search
  change ∀ x, (Minimal (fun y => f y = true ∧ y i = x i) x ∨
      Maximal (fun y => f y = false ∧ y i = x i) x) →
      D.eval (List.ofFn x ++ [!(x i)]) = f x at hcheck
  let g : PEqualNP.CircuitLowerBounds.Gate := ⟨.not, [i.val]⟩
  refine ⟨⟨g :: D.gates, D.output⟩, ?_, ?_, ?_, g, rfl, rfl⟩
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [g]
    · obtain ⟨hop, hlen⟩ := hD a ha
      exact ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢; tauto, hlen⟩
  · change D.gates.length + 1 ≤ 14
    change D.gates.length ≤ 13 at hsize
    omega
  · intro x
    have hget : (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp only [List.getElem_ofFn]
    change D.eval (List.ofFn x ++ [!((List.ofFn x).getD i.val false)]) = f x
    rw [hget]
    cases hx : f x with
    | false =>
      obtain ⟨y, hxy, hy⟩ := exists_maximal_ge_of_wellFoundedGT
        (fun y => f y = false ∧ y i = x i) x ⟨hx, rfl⟩
      have hi := hy.prop.2
      have hv := hcheck y (Or.inr (by simpa only [hi] using hy))
      rw [hi, hy.prop.1] at hv
      exact le_antisymm ((mono 10 D hD (!(x i)) hxy).trans_eq hv) (by simp)
    | true =>
      obtain ⟨y, hyx, hy⟩ := exists_minimal_le_of_wellFoundedLT
        (fun y => f y = true ∧ y i = x i) x ⟨hx, rfl⟩
      have hi := hy.prop.2
      have hv := hcheck y (Or.inl (by simpa only [hi] using hy))
      rw [hi, hy.prop.1] at hv
      exact le_antisymm (by simp) (hv.symm.trans_le (mono 10 D hD (!(x i)) hyx))

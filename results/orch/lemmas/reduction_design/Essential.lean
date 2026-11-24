import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_670_aux_essential (C : Circuit)
    (hC : circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ i : Fin 9, ∃ x y : Fin 9 → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ circuitFun 9 C x ≠ circuitFun 9 C y := by
  intro i
  let nb : Fin 9 → Fin 9 := ![1, 0, 1, 2, 3, 0, 1, 2, 3]
  let x : Fin 9 → Bool := fun j => decide (j = nb i)
  let y : Fin 9 → Bool := fun j => decide (j = nb i ∨ j = i)
  refine ⟨x, y, ?_, ?_⟩
  · intro j hj
    simp [x, y, hj]
  · rw [hC]
    have hv : ∀ i : Fin 9,
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j => decide (j = nb i)) = false ∧
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j => decide (j = nb i ∨ j = i)) = true := by
      decide +kernel
    change (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j => decide (j = nb i)) ≠
      (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) (fun j => decide (j = nb i ∨ j = i))
    rw [(hv i).1, (hv i).2]
    decide

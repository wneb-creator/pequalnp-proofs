import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_2592_aux

def petersen (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma petersen_independence : ∀ x : Fin 10 → Bool,
    petersen x = false → (List.ofFn x).count true ≤ 4 := by
  decide

lemma petersen_independence_attained :
    petersen (fun i => decide (i = 0 ∨ i = 2 ∨ i = 8 ∨ i = 9)) = false ∧
    (List.ofFn (fun i : Fin 10 => decide (i = 0 ∨ i = 2 ∨ i = 8 ∨ i = 9))).count true = 4 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma petersen_cofactor_witness : ∀ i j : Fin 10, i ≠ j → ∀ b : Bool,
    ∃ k : Fin 10, k ≠ i ∧ k ≠ j ∧
      petersen (fun v => if v = j then true else if v = i then b else decide (v = k)) = true ∧
      petersen (fun v => if v = j then false else if v = i then b else decide (v = k)) = false := by
  decide

lemma petersen_cofactor_dep (i j : Fin 10) (h : i ≠ j) (b : Bool) :
    ∃ x : Fin 10 → Bool, x i = b ∧
      petersen (Function.update x j true) ≠ petersen (Function.update x j false) := by
  obtain ⟨k, hki, hkj, htrue, hfalse⟩ := petersen_cofactor_witness i j h b
  let x := fun v => if v = i then b else decide (v = k)
  refine ⟨x, by simp [x], ?_⟩
  have ht : Function.update x j true =
      (fun v => if v = j then true else if v = i then b else decide (v = k)) := by
    funext v
    by_cases hv : v = j
    · subst v; simp
    · simp [Function.update_of_ne hv, hv, x]
  have hf : Function.update x j false =
      (fun v => if v = j then false else if v = i then b else decide (v = k)) := by
    funext v
    by_cases hv : v = j
    · subst v; simp
    · simp [Function.update_of_ne hv, hv, x]
  rw [ht, hf, htrue, hfalse]
  decide

end PEqualNP.Outside.L_meta_2592_aux

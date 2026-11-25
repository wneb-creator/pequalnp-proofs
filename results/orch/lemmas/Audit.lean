import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma petersen_zero : petersen (fun _ => false) = false := rfl

lemma petersen_one : petersen (fun _ => true) = true := rfl

lemma petersen_singleton (i : Fin 10) :
    petersen (fun j => decide (j = i)) = false := by
  fin_cases i <;> decide

lemma petersen_essential (i : Fin 10) :
    ∃ x y : Fin 10 → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ x i = false ∧ y i = true ∧
      petersen x = false ∧ petersen y = true := by
  refine ⟨(fun j => decide (j.val = (i.val + 5) % 10)),
    (fun j => decide (j.val = (i.val + 5) % 10 ∨ j = i)), ?_⟩
  fin_cases i <;> decide

lemma bool_and_mono : ∀ {a b c d : Bool}, a ≤ c → b ≤ d → (a && b) ≤ (c && d) := by
  decide

lemma bool_or_mono : ∀ {a b c d : Bool}, a ≤ c → b ≤ d → (a || b) ≤ (c || d) := by
  decide

lemma petersen_monotone : Monotone petersen := by
  intro x y h
  unfold petersen
  repeat' first | apply bool_or_mono | apply bool_and_mono | exact h _

lemma wire_fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
      x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size :=
  wire_fold_length C.gates x

lemma wire_fold_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) x).getD i false =
      x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp only [List.length_append, List.length_singleton]
        omega

lemma circuit_input (C : Circuit) (x : List Bool) (hi : C.output < x.length) :
    C.eval x = x.getD C.output false :=
  wire_fold_input C.gates x C.output hi

lemma petersen_output_lt (C : Circuit)
    (hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    C.output < 10 + C.size := by
  by_contra hn
  have hl : (C.wires (List.ofFn (fun _ : Fin 10 => true))).length ≤ C.output := by
    rw [wires_length, List.length_ofFn]
    omega
  have he := hc (fun _ => true)
  rw [Circuit.eval, List.getD_eq_default _ _ hl, petersen_one] at he
  contradiction

lemma petersen_output_ge (C : Circuit)
    (hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    10 ≤ C.output := by
  by_contra hn
  have hi : C.output < 10 := by omega
  let i : Fin 10 := ⟨C.output, hi⟩
  have he := hc (fun j => decide (j = i))
  rw [petersen_singleton] at he
  have hl : C.output < (List.ofFn (fun j => decide (j = i))).length := by
    simpa using hi
  rw [circuit_input C _ hl] at he
  rw [List.getD_eq_getElem _ _ hl, List.getElem_ofFn] at he
  simp [i] at he

end PEqualNP.Outside.L_meta_2592

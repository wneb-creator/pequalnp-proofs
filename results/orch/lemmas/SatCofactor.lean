import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds

def satEdgeFunction (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma sat_dependency_witness :
    ∀ u v : Fin 10, u ≠ v → ∀ b : Bool, ∃ w : Fin 10,
      ∀ a : Bool,
        satEdgeFunction (fun i =>
          if i = u then a else if i = v then b else decide (i = w)) = a := by
  decide

lemma sat_cofactor_essential (u v : Fin 10) (huv : u ≠ v) (b : Bool) :
    ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ u → x i = y i) ∧ x v = b ∧ y v = b ∧
      satEdgeFunction x ≠ satEdgeFunction y := by
  obtain ⟨w, hw⟩ := sat_dependency_witness u v huv b
  refine ⟨(fun i => if i = u then false else if i = v then b else decide (i = w)),
    (fun i => if i = u then true else if i = v then b else decide (i = w)),
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp [hi]
  · simp [Ne.symm huv]
  · simp [Ne.symm huv]
  · rw [hw false, hw true]
    decide

def satStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma sat_fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl satStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons, ih, satStep, Nat.add_comm, Nat.add_left_comm]

lemma sat_fold_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl satStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl satStep (satStep x g)).getD i false = _
    rw [ih _ (by simp [satStep]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma sat_eval_input (C : Circuit) (x : Fin 10 → Bool) (i : Fin 10)
    (output : C.output = i.val) : C.eval (List.ofFn x) = x i := by
  unfold Circuit.eval Circuit.wires
  change (C.gates.foldl satStep (List.ofFn x)).getD C.output false = x i
  rw [output, sat_fold_getD _ _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_eq_left,
    Option.getD_some]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma sat_edge_avoids :
    ∀ i : Fin 10, ∃ u v : Fin 10,
      (fun j : Fin 10 => decide (j = u ∨ j = v)) i = false ∧
      satEdgeFunction (fun j => decide (j = u ∨ j = v)) = true := by
  decide

lemma sat_output_bounds (C : Circuit)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = satEdgeFunction x) :
    10 ≤ C.output ∧ C.output < 10 + C.size := by
  constructor
  · by_contra! small
    let i : Fin 10 := ⟨C.output, small⟩
    obtain ⟨u, v, zero, one⟩ := sat_edge_avoids i
    let x : Fin 10 → Bool := fun j => decide (j = u ∨ j = v)
    have value : C.eval (List.ofFn x) = false := (sat_eval_input C x i rfl).trans zero
    have target : satEdgeFunction x = true := one
    have bad : false = true := value.symm.trans ((computes x).trans target)
    cases bad
  · by_contra! large
    let x : Fin 10 → Bool := fun j => decide (j = 0 ∨ j = 1)
    have target : satEdgeFunction x = true := by decide
    have length : (C.wires (List.ofFn x)).length = 10 + C.size := by
      change (C.gates.foldl satStep (List.ofFn x)).length = 10 + C.gates.length
      rw [sat_fold_length, List.length_ofFn]
    have value : C.eval (List.ofFn x) = false := by
      apply List.getD_eq_default
      omega
    have bad : false = true := value.symm.trans ((computes x).trans target)
    cases bad

end PEqualNP.Outside.L_meta_2592_aux

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_trim

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma gate_fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_singleton, List.length_cons]
    omega

lemma gate_fold_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    simp [List.getD, List.getElem?_append_left hi]

lemma trim_output (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (isGate : n ≤ C.output) (existsOutput : C.output < n + C.size) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧ D.output = C.output ∧
      D.output + 1 = n + D.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let k := C.output + 1 - n
  have hk : k ≤ C.gates.length := by change k ≤ C.size; dsimp [k]; omega
  let D : Circuit := ⟨C.gates.take k, C.output⟩
  have dsize : D.size = k := by
    change (C.gates.take k).length = k
    simp [List.length_take, Nat.min_eq_left hk]
  refine ⟨D, ?_, ?_, rfl, ?_, ?_⟩
  · intro g mem
    apply fan g
    exact List.mem_of_mem_take mem
  · rw [dsize]
    exact hk
  · change C.output + 1 = n + D.size
    rw [dsize]
    dsimp [k]
    omega
  · intro x
    have short : C.output < (D.wires (List.ofFn x)).length := by
      change C.output < ((C.gates.take k).foldl _ (List.ofFn x)).length
      rw [gate_fold_length]
      have eq : (C.gates.take k).length = k := dsize
      rw [eq]
      simp only [List.length_ofFn]
      dsimp [k]
      omega
    change (D.wires (List.ofFn x)).getD C.output false = (C.gates.foldl _ (List.ofFn x)).getD C.output false
    conv_rhs => rw [← List.take_append_drop k C.gates, List.foldl_append]
    exact (gate_fold_read (C.gates.drop k) (D.wires (List.ofFn x)) C.output short).symm

end PEqualNP.Outside.L_meta_2592_trim

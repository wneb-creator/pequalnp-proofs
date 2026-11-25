import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def attachRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def shiftedGate (g : Gate) : Gate := ⟨g.op, g.inputs.map Nat.succ⟩

lemma attachRun_length (gs : List Gate) (x : List Bool) :
    (attachRun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [attachRun, List.foldl_cons] at *
    rw [ih]
    simp
    omega

lemma shiftedGate_run (gs : List Gate) (b : Bool) (x : List Bool) :
    attachRun (gs.map shiftedGate) (b :: x) = b :: attachRun gs x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [attachRun, List.map_cons, List.foldl_cons, shiftedGate,
      List.map_map, Function.comp_def, List.getD_cons_succ]
    exact ih _

def attachedPoint (D : Circuit) (j : ℕ) : Circuit :=
  ⟨D.gates.map shiftedGate ++
    [⟨.and, [0, j + 1]⟩, ⟨.or, [D.output + 1, 26 + D.size]⟩],
    27 + D.size⟩

lemma attachedPoint_size (D : Circuit) (j : ℕ) :
    (attachedPoint D j).size = D.size + 2 := by
  simp [attachedPoint, Circuit.size]

lemma attachedPoint_monotone (D : Circuit) (j : ℕ) (hm : Monotone2 D) :
    Monotone2 (attachedPoint D j) := by
  intro g hg
  change g ∈ D.gates.map shiftedGate ++ _ at hg
  rcases List.mem_append.mp hg with hmap | hlast
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmap
    obtain ⟨op, arity⟩ := hm a ha
    exact ⟨op, by simpa [shiftedGate] using arity⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hlast
    rcases hlast with rfl | rfl <;> simp

lemma attachedPoint_eval (D : Circuit) (j : ℕ)
    (hout : D.output < 25 + D.size) (b : Bool) (y : Fin 25 → Bool) :
    (attachedPoint D j).eval (b :: List.ofFn y) =
      (D.eval (List.ofFn y) || (b && (D.wires (List.ofFn y)).getD j false)) := by
  let w := D.wires (List.ofFn y)
  have len : w.length = 25 + D.size := by
    simpa only [w, Circuit.wires, Circuit.size, attachRun, List.length_ofFn]
      using attachRun_length D.gates (List.ofFn y)
  have shifted : attachRun (D.gates.map shiftedGate) (b :: List.ofFn y) = b :: w :=
    shiftedGate_run _ _ _
  change (attachRun (D.gates.map shiftedGate ++
    [⟨.and, [0, j + 1]⟩, ⟨.or, [D.output + 1, 26 + D.size]⟩])
    (b :: List.ofFn y)).getD (27 + D.size) false = _
  unfold attachRun at shifted ⊢
  rw [List.foldl_append, shifted]
  simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
    List.getD_cons_zero, List.getD_cons_succ, Bool.and_true, Bool.or_false, id_eq]
  have readOutput : ((b :: w) ++ [b && w.getD j false]).getD (D.output + 1) false =
      w.getD D.output false := by
    rw [List.getD_append]
    · rfl
    · simp only [List.length_cons, len]
      omega
  have readNew : ((b :: w) ++ [b && w.getD j false]).getD (26 + D.size) false =
      (b && w.getD j false) := by
    rw [List.getD_append_right]
    · simp only [List.length_cons, len]
      rw [show 26 + D.size - (25 + D.size + 1) = 0 by omega]
      rfl
    · simp only [List.length_cons, len]
      omega
  rw [readOutput, readNew, List.getD_append_right]
  · simp only [List.length_append, List.length_cons, List.length_nil, len]
    rw [show 27 + D.size - (25 + D.size + 1 + (0 + 1)) = 0 by omega]
    rfl
  · simp only [List.length_append, List.length_cons, List.length_nil, len]
    omega

lemma attach_point (D : Circuit) (j : ℕ) (hm : Monotone2 D)
    (hout : D.output < 25 + D.size) (_hj : j < 25 + D.size) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 2 ∧
      ∀ (b : Bool) (y : Fin 25 → Bool),
        C.eval (b :: List.ofFn y) =
          (D.eval (List.ofFn y) || (b && (D.wires (List.ofFn y)).getD j false)) := by
  exact ⟨attachedPoint D j, attachedPoint_monotone D j hm,
    le_of_eq (attachedPoint_size D j), attachedPoint_eval D j hout⟩

end PEqualNP.Outside.L_meta_650


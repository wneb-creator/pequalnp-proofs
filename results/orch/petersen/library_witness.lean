import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.Witness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [10, 6]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [12, 8]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [0, 7]⟩,
    ⟨GateOp.or, [15, 8]⟩,
    ⟨GateOp.and, [10, 12]⟩,
    ⟨GateOp.and, [17, 15]⟩,
    ⟨GateOp.or, [18, 9]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.and, [3, 13]⟩,
    ⟨GateOp.or, [20, 21]⟩,
    ⟨GateOp.and, [5, 16]⟩,
    ⟨GateOp.or, [22, 23]⟩,
    ⟨GateOp.and, [6, 14]⟩,
    ⟨GateOp.or, [24, 25]⟩,
    ⟨GateOp.or, [4, 7]⟩,
    ⟨GateOp.and, [27, 19]⟩,
    ⟨GateOp.or, [26, 28]⟩], 29⟩

lemma isAO2 : PEqualNP.TopForm.IsAO2 10 circuit := by decide

lemma size_eq : circuit.size = 20 := by decide

lemma or_count : circuit.gates.countP (fun g => decide (g.op = GateOp.or)) = 13 := by decide

lemma and_count : circuit.gates.countP (fun g => decide (g.op = GateOp.and)) = 7 := by decide

lemma path_gadget : ∀ a b c d e : Bool,
    ((b || d) && ((((a || e) && (e || b)) && (a || d)) || c)) =
      ((a && b) || (b && c) || (c && d) || (d && e)) := by
  decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
lemma correct : ∀ x : Fin 10 → Bool, circuit.eval (List.ofFn x) =
    (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
     x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
     x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
  intro x
  change (((((x 1 && ((x 0 || x 2) || x 6)) ||
      (x 3 && ((x 2 || x 4) || x 8))) ||
      (x 5 && ((x 0 || x 7) || x 8))) || (x 6 && (x 8 || x 9))) ||
      ((x 4 || x 7) && ((((x 0 || x 2) && (x 2 || x 4)) &&
        (x 0 || x 7)) || x 9))) = _
  rw [path_gadget]
  simp only [Bool.and_or]
  ac_rfl

end PEqualNP.Outside.L_meta_2590_aux.Witness

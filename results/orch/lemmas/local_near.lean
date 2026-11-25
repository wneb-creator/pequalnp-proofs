import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

lemma k4_cover_identity : ∀ a b c d e f : Bool,
    ((a || c || f) && (a || b || e) && (c || d || e) && (b || d || f)) =
      ((a && d) || (b && c) || (e && f) || (a && b && e) ||
        (c && d && e) || (a && c && f) || (b && d && f)) := by
  decide

def nearCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [2, 5]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [6, 0]⟩,
    ⟨.or, [9, 10]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [0, 11]⟩,
    ⟨.or, [5, 14]⟩, ⟨.or, [12, 2]⟩, ⟨.and, [17, 16]⟩,
    ⟨.and, [4, 15]⟩, ⟨.and, [15, 18]⟩, ⟨.or, [7, 20]⟩,
    ⟨.and, [17, 1]⟩, ⟨.or, [19, 22]⟩, ⟨.and, [16, 8]⟩,
    ⟨.and, [21, 13]⟩, ⟨.or, [25, 24]⟩, ⟨.or, [23, 26]⟩], 27⟩

lemma nearCircuit_size : nearCircuit.size = 18 := rfl

lemma nearCircuit_fanInTwo : PEqualNP.MetaComplexity.FanInTwo nearCircuit := by
  simp [PEqualNP.MetaComplexity.FanInTwo, nearCircuit]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma nearCircuit_eval : ∀ x : Fin 10 → Bool,
    nearCircuit.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
        (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
        (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
        (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
        (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5) ||
        (x 0 && x 2 && x 6) || (x 3 && x 5 && x 6) ||
        (x 0 && x 3 && x 9) || (x 2 && x 5 && x 9)) := by
  intro x
  have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := rfl
  rw [h]
  simp only [nearCircuit, PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons,
    List.any_nil, List.all_cons, List.all_nil, id, Bool.and_true, Bool.or_false]
  generalize x 0 = a0
  generalize x 1 = a1
  generalize x 2 = a2
  generalize x 3 = a3
  generalize x 4 = a4
  generalize x 5 = a5
  generalize x 6 = a6
  generalize x 7 = a7
  generalize x 8 = a8
  generalize x 9 = a9
  revert a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  decide

end PEqualNP.Outside.L_meta_2592_aux

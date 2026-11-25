import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

def nonedgeProjectionCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [2, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.not, [1]⟩,
    ⟨.and, [1, 9]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [12, 13]⟩,
    ⟨.or, [2, 4]⟩, ⟨.or, [15, 5]⟩, ⟨.and, [7, 16]⟩,
    ⟨.or, [3, 6]⟩, ⟨.or, [18, 5]⟩, ⟨.and, [8, 19]⟩,
    ⟨.or, [14, 17]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [22, 0]⟩], 23⟩

lemma nonedgeProjectionCircuit_size : nonedgeProjectionCircuit.size = 15 := rfl

lemma nonedgeProjectionCircuit_notCount :
    PEqualNP.NotBracket.notCount nonedgeProjectionCircuit = 1 := by
  decide

lemma nonedgeProjectionCircuit_fanInTwo :
    PEqualNP.MetaComplexity.FanInTwo nonedgeProjectionCircuit := by
  simp [PEqualNP.MetaComplexity.FanInTwo, nonedgeProjectionCircuit]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma nonedgeProjectionCircuit_eval : ∀ x : Fin 9 → Bool,
    nonedgeProjectionCircuit.eval (List.ofFn x) =
      ((!x 1 && x 0) || (x 0 && x 1) || (x 1 && x 2) ||
        (x 2 && x 3) || (x 3 && !x 1) || (!x 1 && x 4) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 4 && x 6) || (x 6 && x 8) ||
        (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 4)) := by
  intro x
  have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := rfl
  rw [h]
  simp only [nonedgeProjectionCircuit, PEqualNP.CircuitLowerBounds.Circuit.eval,
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
  revert a0 a1 a2 a3 a4 a5 a6 a7 a8
  decide

end PEqualNP.Outside.L_meta_2592_aux

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Restriction

open PEqualNP.CircuitLowerBounds

def restricted (x : Fin 9 → Bool) : Bool :=
  (!x 0 && x 1) || (x 1 && x 0) || (x 0 && x 4) ||
  (x 4 && x 2) || (x 2 && !x 0) || (!x 0 && x 3) ||
  (x 1 && x 6) || (x 0 && x 5) || (x 4 && x 7) ||
  (x 2 && x 8) || (x 3 && x 5) || (x 5 && x 8) ||
  (x 8 && x 6) || (x 6 && x 7) || (x 7 && x 3)

def witness : Circuit :=
  ⟨[⟨.not, [0]⟩,
    ⟨.or, [2, 3]⟩, ⟨.and, [9, 10]⟩,
    ⟨.or, [4, 5]⟩, ⟨.and, [0, 12]⟩,
    ⟨.or, [4, 3]⟩, ⟨.or, [14, 6]⟩, ⟨.and, [7, 15]⟩,
    ⟨.or, [2, 5]⟩, ⟨.or, [17, 6]⟩, ⟨.and, [8, 18]⟩,
    ⟨.or, [11, 13]⟩, ⟨.or, [16, 19]⟩,
    ⟨.or, [20, 21]⟩, ⟨.or, [22, 1]⟩], 23⟩

lemma witness_size : witness.size = 15 := rfl

lemma witness_binary_count :
    witness.gates.countP (fun g => !g.op.eval [false]) = 14 := rfl

lemma witness_fan : PEqualNP.MetaComplexity.FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma witness_correct : ∀ x : Fin 9 → Bool,
    witness.eval (List.ofFn x) = restricted x := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.Restriction

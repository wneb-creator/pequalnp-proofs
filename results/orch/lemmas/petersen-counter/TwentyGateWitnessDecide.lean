import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upperCircuit : Circuit :=
  ⟨[
    ⟨.or, [1, 4]⟩,
    ⟨.or, [11, 5]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [16, 8]⟩,
    ⟨.and, [3, 17]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [19, 9]⟩,
    ⟨.and, [7, 20]⟩,
    ⟨.or, [6, 5]⟩,
    ⟨.and, [8, 22]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.and, [9, 24]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [26, 18]⟩,
    ⟨.or, [27, 21]⟩,
    ⟨.or, [28, 23]⟩,
    ⟨.or, [29, 25]⟩],
   30⟩

def upperTarget (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

theorem upper_size : upperCircuit.size = 20 := rfl

theorem upper_legal : FanInTwo upperCircuit := by
  intro g hg
  simp only [upperCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem upper_evaluation : ∀ x : Fin 10 → Bool,
    upperCircuit.eval (List.ofFn x ++ [x 0 && x 2]) = upperTarget x := by
  decide +kernel

end PEqualNP.Outside.L_meta_1890_aux

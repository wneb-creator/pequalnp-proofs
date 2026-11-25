import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.Pilot110Partial

def petersen20 : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [1, 11]⟩,
    ⟨.or, [2, 4]⟩, ⟨.or, [13, 8]⟩, ⟨.and, [3, 14]⟩,
    ⟨.or, [0, 9]⟩, ⟨.and, [4, 16]⟩,
    ⟨.or, [0, 7]⟩, ⟨.or, [18, 8]⟩, ⟨.and, [5, 19]⟩,
    ⟨.or, [9, 8]⟩, ⟨.and, [6, 21]⟩,
    ⟨.or, [2, 9]⟩, ⟨.and, [7, 23]⟩,
    ⟨.or, [12, 15]⟩, ⟨.or, [25, 17]⟩, ⟨.or, [26, 20]⟩,
    ⟨.or, [27, 22]⟩, ⟨.or, [28, 24]⟩], 29⟩

def petersenFunction (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
  x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
  x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 ||
  x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma petersen20_size : petersen20.size = 20 := rfl

lemma petersen20_fan : FanInTwo petersen20 := by
  intro g hg
  simp only [petersen20, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma petersen20_eval : ∀ x : Fin 10 → Bool,
    petersen20.eval (List.ofFn x) = petersenFunction x := by
  decide +kernel

end PEqualNP.Outside.Pilot110Partial

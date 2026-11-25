import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Twenty

def C : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[
    ⟨.or, [0, 2]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [13, 8]⟩,
    ⟨.and, [3, 14]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [4, 16]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [18, 8]⟩,
    ⟨.and, [5, 19]⟩,
    ⟨.or, [9, 8]⟩,
    ⟨.and, [6, 21]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.and, [7, 23]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [25, 17]⟩,
    ⟨.or, [26, 20]⟩,
    ⟨.or, [27, 22]⟩,
    ⟨.or, [28, 24]⟩
  ], 29⟩

def f (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma size : C.size = 20 := rfl

lemma fan : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f x := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.Twenty

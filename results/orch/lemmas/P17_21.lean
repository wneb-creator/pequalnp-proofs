import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def pathCirc : Circuit :=
  ⟨[
    ⟨.or, [0, 13]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.or, [1, 14]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.or, [2, 15]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [3, 16]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [4, 18]⟩,
    ⟨.and, [17, 25]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.and, [19, 27]⟩,
    ⟨.or, [20, 22]⟩,
    ⟨.and, [21, 29]⟩,
    ⟨.or, [22, 24]⟩,
    ⟨.and, [23, 31]⟩,
    ⟨.and, [24, 4]⟩,
    ⟨.or, [26, 28]⟩,
    ⟨.or, [34, 30]⟩,
    ⟨.or, [35, 32]⟩,
    ⟨.or, [36, 33]⟩
  ], 37⟩

lemma path_mono : Monotone2 pathCirc := by
  simp [Monotone2, pathCirc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma path_rep : Represents (fun a : Fin 9 => fun b : Fin 8 => decide (a.val = b.val ∨ a.val = b.val + 1)) pathCirc := by
  decide +kernel

lemma path_upper : RepSizeAtMost (fun a : Fin 9 => fun b : Fin 8 => decide (a.val = b.val ∨ a.val = b.val + 1)) 21 :=
  ⟨pathCirc, path_mono, by decide, path_rep⟩

end PEqualNP.Outside.L_meta_9502

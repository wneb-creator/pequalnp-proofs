import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def rereadMatching : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [0, 1]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [2, 3]⟩,
    ⟨.and, [8, 9]⟩], 10⟩

lemma rereadMatching_ao : PEqualNP.TopForm.IsAO2 4 rereadMatching := by decide

lemma rereadMatching_fun : ∀ z : Fin 4 → Bool,
    circuitFun 4 rereadMatching z = ((z 0 && z 2) || (z 1 && z 3)) := by decide

lemma rereadMatching_pair_one : readsAtMost rereadMatching 4 [0, 2] 1 = false := by decide

lemma rereadMatching_pair_two : readsAtMost rereadMatching 4 [0, 2] 2 = true := by decide

lemma rereadMatching_internal : ∀ j : Fin 6, ∃ z : Fin 4 → Bool,
    Circuit.eval ⟨rereadMatching.gates, 4 + j.val⟩ (List.ofFn z) = true ∧
      circuitFun 4 rereadMatching z = false := by decide

def readOnceMatching : Circuit :=
  ⟨[⟨.and, [0, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [4, 5]⟩], 6⟩

lemma readOnceMatching_ao : PEqualNP.TopForm.IsAO2 4 readOnceMatching := by decide

lemma readOnceMatching_fun : ∀ z : Fin 4 → Bool,
    circuitFun 4 readOnceMatching z = ((z 0 && z 2) || (z 1 && z 3)) := by decide

lemma readOnceMatching_read : IsReadK 4 readOnceMatching 1 := by decide

lemma readOnceMatching_smaller : readOnceMatching.size < rereadMatching.size := by decide

end PEqualNP.Outside.L_meta_2583

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585_aux.DirtyBlockExample

open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [6, 7]⟩,
    ⟨GateOp.and, [8, 9]⟩], 10⟩

lemma valid : PEqualNP.TopForm.IsAO2 4 C := by decide

lemma computes_matching : ∀ z : Fin 4 → Bool,
    PEqualNP.MetaComplexity.circuitFun 4 C z = ((z 0 && z 2) || (z 1 && z 3)) := by decide

lemma all_interior_not_below : ∀ w : Fin 10,
    ¬ PEqualNP.CircuitMoves.WireBelowOutput 4 C w.val := by decide

lemma not_read_one : ¬ PEqualNP.ReadK.IsReadK 4 C 1 := by decide

lemma size_seven : C.size = 7 := rfl

end PEqualNP.Outside.L_meta_2585_aux.DirtyBlockExample

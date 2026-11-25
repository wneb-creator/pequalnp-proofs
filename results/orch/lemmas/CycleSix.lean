import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sixCycle : Circuit :=
  { gates := [⟨.or, [4, 5]⟩, ⟨.and, [0, 6]⟩,
      ⟨.or, [3, 5]⟩, ⟨.and, [1, 8]⟩,
      ⟨.or, [3, 4]⟩, ⟨.and, [2, 10]⟩,
      ⟨.or, [7, 9]⟩, ⟨.or, [12, 11]⟩]
    output := 13 }

lemma sixCycle_size : sixCycle.size = 8 := rfl

lemma sixCycle_model : PEqualNP.TopForm.IsAO2 6 sixCycle := by decide

lemma sixCycle_computes :
    ∀ z : Fin 6 → Bool, circuitFun 6 sixCycle z =
      decide (∃ p : Fin 3, ∃ l : Fin 3,
        p ≠ l ∧ z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true) := by decide

set_option maxRecDepth 100000 in
lemma sixCycle_read1 : PEqualNP.ReadK.IsReadK 6 sixCycle 1 := by decide

lemma sixCycle_no_four :
    ∀ p p' : Fin 3, ∀ l l' : Fin 3,
      p ≠ p' → l ≠ l' → ¬ (p ≠ l ∧ p ≠ l' ∧ p' ≠ l ∧ p' ≠ l') := by decide

end PEqualNP.Outside.L_meta_2585

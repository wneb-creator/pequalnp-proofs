import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_4970.ReadObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def duplicateStar : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [4, 4]⟩], 5⟩

lemma duplicateStar_properties :
    PEqualNP.TopForm.IsAO2 3 duplicateStar ∧
    (∀ x : Fin 3 → Bool, circuitFun 3 duplicateStar x = (x 0 && (x 1 || x 2))) ∧
    PEqualNP.TwoColour.tCount 3 duplicateStar (fun i => decide (1 ≤ i)) = 0 ∧
    ¬ PEqualNP.ReadK.IsReadK 3 duplicateStar 1 := by
  decide +kernel

lemma duplicateStar_service (a : Fin 1) (b : Fin 2) :
    ∃ (j : ℕ) (Q : Finset (Fin 2)), j < duplicateStar.gates.length ∧
      (gateAt duplicateStar j).op = GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧
      (∀ b' ∈ Q, (a, b') ∈ (Finset.univ : Finset (Fin 1 × Fin 2))) ∧
      ∀ x : Fin (1 + 2) → Bool,
        (duplicateStar.wires (List.ofFn x)).getD (1 + 2 + j) false =
          decide (∃ b' ∈ Q, x (Fin.natAdd 1 b') = true) := by
  refine ⟨0, Finset.univ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · rfl
  · decide
  · simp
  · simp
  · decide +kernel

end PEqualNP.Outside.L_meta_4970.ReadObstruction

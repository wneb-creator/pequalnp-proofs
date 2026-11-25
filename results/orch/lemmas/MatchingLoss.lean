import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.MatchingLoss

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour
  PEqualNP.CleanedNonEdge

def edges : Finset (Fin 2 × Fin 2) := {(0, 0), (1, 1)}

abbrev graph : SimpleGraph (Fin 4) := SimpleGraph.fromRel fun u v =>
  (u.val, v.val) ∈ ([(0, 2), (1, 3)] : List (ℕ × ℕ))

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.and, [0, 0]⟩,
    ⟨GateOp.and, [1, 1]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [2, 8]⟩,
    ⟨GateOp.and, [9, 10]⟩,
    ⟨GateOp.and, [6, 11]⟩], 12⟩

lemma size : circuit.size = 9 := rfl

lemma legal : IsAO2 4 circuit := by decide +kernel

lemma computes : ∀ x : Fin 4 → Bool,
    circuitFun 4 circuit x = decide (∃ a : Fin 2, ∃ b : Fin 2,
      (a, b) ∈ edges ∧ x (Fin.castAdd 2 a) = true ∧
      x (Fin.natAdd 2 b) = true) := by decide +kernel

lemma computes_graph : circuitFun 4 circuit = graphFun graph ∅ := by decide +kernel

lemma zero_two_colour : tCount 4 circuit (fun i => decide (2 ≤ i)) = 0 := by decide +kernel

lemma no_four_cycle : NoFourCycle graph := by decide +kernel

lemma top_form : TopForm graph circuit := by decide +kernel

lemma dirty_gates : junk graph circuit = {2, 3, 4, 7} := by decide +kernel

lemma forcing_first_dirty_loses_all : ∀ x : Fin 4 → Bool,
    circuitFun 4 (PEqualNP.Outside.L_meta_4675.Pruning.pruned 4 2 circuit) x = false := by
  decide +kernel

lemma no_single_center : ¬ ∃ z : Fin 4, ∀ (a : Fin 2) (b : Fin 2),
    (a, b) ∈ edges → Fin.castAdd 2 a = z ∨ Fin.natAdd 2 b = z := by decide +kernel

end PEqualNP.Outside.L_meta_4675.MatchingLoss

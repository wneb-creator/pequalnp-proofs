import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.ReaderPath

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour
  PEqualNP.CleanedNonEdge

def edges : Finset (Fin 3 × Fin 2) := {(0, 0), (0, 1), (1, 0), (2, 1)}

abbrev graph : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun u v =>
  (u.val, v.val) ∈ ([(0, 3), (0, 4), (1, 3), (2, 4)] : List (ℕ × ℕ))

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [5, 6]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.and, [8, 9]⟩,
    ⟨GateOp.and, [2, 4]⟩,
    ⟨GateOp.or, [10, 11]⟩], 12⟩

lemma circuit_size : circuit.size = 8 := rfl

lemma legal : IsAO2 5 circuit := by decide +kernel

lemma computes : ∀ x : Fin 5 → Bool,
    circuitFun 5 circuit x =
      decide (∃ a : Fin 3, ∃ b : Fin 2, (a, b) ∈ edges ∧
        x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 3 b) = true) := by decide +kernel

lemma computes_graph : circuitFun 5 circuit = graphFun graph ∅ := by decide +kernel

lemma zero_two_colour : tCount 5 circuit (fun i => decide (3 ≤ i)) = 0 := by decide +kernel

lemma no_four_cycle : NoFourCycle graph := by decide +kernel

lemma top_form : TopForm graph circuit := by decide +kernel

lemma one_dirty_and : junk graph circuit = {2} := by decide +kernel

lemma reader_is_below : BelowF graph circuit 5 := by decide +kernel

lemma reader_pair_values : ∀ (a : Fin 3) (b : Fin 2),
    PEqualNP.EdgeOwnership.gateVal 5 circuit 5
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 2 a) (Fin.natAdd 3 b)) =
    decide ((a, b) ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (Fin 3 × Fin 2))) := by
  decide +kernel

lemma reader_has_no_star_center : ¬ ∃ z : Fin 5, ∀ (a : Fin 3) (b : Fin 2),
    (a, b) ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (Fin 3 × Fin 2)) →
    Fin.castAdd 2 a = z ∨ Fin.natAdd 3 b = z := by decide +kernel

end PEqualNP.Outside.L_meta_4675.ReaderPath

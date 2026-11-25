import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.twoJunkExample

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def C : Circuit := ⟨[
  ⟨GateOp.or, [0, 1]⟩,
  ⟨GateOp.or, [2, 4]⟩,
  ⟨GateOp.or, [7, 3]⟩,
  ⟨GateOp.or, [8, 5]⟩,
  ⟨GateOp.or, [0, 2]⟩,
  ⟨GateOp.or, [10, 3]⟩,
  ⟨GateOp.or, [1, 4]⟩,
  ⟨GateOp.or, [12, 5]⟩,
  ⟨GateOp.and, [6, 9]⟩,
  ⟨GateOp.and, [11, 13]⟩,
  ⟨GateOp.and, [14, 15]⟩], 16⟩

abbrev G : SimpleGraph (Fin 6) := edgeGraph 6 [(0, 4), (0, 5), (1, 2), (1, 3)]

lemma circuit_monotone : Monotone2 C := by simp [Monotone2, C]

lemma circuit_reads_back : ReadsBack 6 C := by decide

lemma no_triangle : ∀ a b c : Fin 6, G.Adj a b → G.Adj b c → ¬ G.Adj c a := by decide

lemma no_four_cycle : NoFourCycle G := by decide

lemma boolean_identity (a b c d : Bool) :
    (((a || b) && (c || d)) && ((a || c) && (b || d))) = ((a && d) || (b && c)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma circuit_computes : ∀ x : Fin 6 → Bool, circuitFun 6 C x = graphFun G ∅ x := by decide

lemma lower_left_owns : Owns 6 C 8 0 4 ∧ Owns 6 C 8 1 2 := by decide

lemma lower_right_owns : Owns 6 C 9 0 4 ∧ Owns 6 C 9 1 2 := by decide

end PEqualNP.Outside.L_meta_2448_aux.twoJunkExample

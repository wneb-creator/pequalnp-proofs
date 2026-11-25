import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_1772.Repair

lemma filter_exchange (a b c d : Bool) :
    (((a || c) && (b || d)) && (a || d)) =
      ((a && (b || d)) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

abbrev pathGraph : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 1), (0, 3), (2, 3)]

def filteredCircuit : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.and, [6, 7]⟩], 8⟩

def exchangedCircuit : Circuit :=
  ⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [0, 4]⟩,
    ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [5, 6]⟩], 7⟩

lemma path_girth :
    (∀ a b c : Fin 4, pathGraph.Adj a b → pathGraph.Adj b c → ¬pathGraph.Adj c a) ∧
      NoFourCycle pathGraph := by
  decide +kernel

lemma filtered_mono : Monotone2 filteredCircuit := by
  simp [Monotone2, filteredCircuit]

lemma exchanged_mono : Monotone2 exchangedCircuit := by
  simp [Monotone2, exchangedCircuit]

lemma filtered_correct : circuitFun 4 filteredCircuit = graphFun pathGraph ∅ := by
  funext x
  revert x
  decide +kernel

lemma exchanged_correct : circuitFun 4 exchangedCircuit = graphFun pathGraph ∅ := by
  funext x
  revert x
  decide +kernel

lemma filtered_last_unowned :
    ∀ u v : Fin 4, pathGraph.Adj u v → ¬Owns 4 filteredCircuit 4 u v := by
  decide +kernel

lemma exchanged_owns :
    ∀ j < exchangedCircuit.gates.length,
      (gateAt exchangedCircuit j).op = GateOp.and →
      ∃ u v : Fin 4, pathGraph.Adj u v ∧ Owns 4 exchangedCircuit j u v := by
  intro j hj hand
  have hj' : j < 4 := hj
  interval_cases j
  · cases hand
  · exact ⟨0, 1, by decide +kernel, by decide +kernel⟩
  · exact ⟨2, 3, by decide +kernel, by decide +kernel⟩
  · cases hand

lemma exchange_saves : exchangedCircuit.size < filteredCircuit.size := by decide +kernel

lemma filtered_not_minimal : ¬IsMinimalMonoCircuit 4 filteredCircuit := by
  intro h
  have lower := h.2 exchangedCircuit exchanged_mono
    (exchanged_correct.trans filtered_correct.symm)
  exact (Nat.not_le_of_lt exchange_saves) lower

lemma filtered_last_pivotal :
    ∀ u v : Fin 4, pathGraph.Adj u v →
      gateVal 4 filteredCircuit 4 (pairInput u v) = true ∧
        circuitFun 4 (PEqualNP.CircuitMoves.eraseGate 4 filteredCircuit 4 9)
          (pairInput u v) = false := by
  decide +kernel

lemma operand_bypasses_fail :
    ∀ i : Fin 2, ∃ x : Fin 4 → Bool,
      circuitFun 4 (PEqualNP.CircuitMoves.eraseGate 4 filteredCircuit 4 (6 + i.val)) x ≠
        circuitFun 4 filteredCircuit x := by
  decide +kernel

end PEqualNP.Outside.L_meta_1772.Repair

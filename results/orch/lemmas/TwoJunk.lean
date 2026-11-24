import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2584.TwoJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def exampleCircuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [5, 6]⟩,
    ⟨.or, [0, 3]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [9, 4]⟩,
    ⟨.and, [1, 4]⟩, ⟨.or, [10, 11]⟩], 12⟩

abbrev exampleGraph : SimpleGraph (Fin 5) :=
  PEqualNP.EdgeOwnership.edgeGraph 5 [(0, 4), (1, 4)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma example_ao : PEqualNP.TopForm.IsAO2 5 exampleCircuit := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma example_function :
    ∀ x : Fin 5 → Bool, circuitFun 5 exampleCircuit x = graphFun exampleGraph ∅ x := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma example_top : PEqualNP.TopForm.TopForm exampleGraph exampleCircuit := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma example_dirty : (PEqualNP.TopForm.junk exampleGraph exampleCircuit).card = 2 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma example_not_read : ¬ PEqualNP.ReadK.IsReadK 5 exampleCircuit 2 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma example_no_four_cycle : PEqualNP.TopForm.NoFourCycle exampleGraph := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma example_distinct_gate_functions :
    ∀ i j : Fin 8, i ≠ j → ∃ x : Fin 5 → Bool,
      PEqualNP.EdgeOwnership.gateVal 5 exampleCircuit i.val x ≠
      PEqualNP.EdgeOwnership.gateVal 5 exampleCircuit j.val x := by decide

def replacementCircuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [5, 4]⟩], 6⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma replacement_properties :
    PEqualNP.TopForm.IsAO2 5 replacementCircuit ∧
    (∀ x : Fin 5 → Bool, circuitFun 5 replacementCircuit x = graphFun exampleGraph ∅ x) ∧
    replacementCircuit.size ≤ exampleCircuit.size ∧
    PEqualNP.ReadK.IsReadK 5 replacementCircuit 2 := by decide

end PEqualNP.Outside.L_meta_2584.TwoJunk

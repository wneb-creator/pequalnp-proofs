import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.NestedReplacementObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

abbrev pathGraph : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 3), (1, 3), (1, 2)]

def nestedCircuit : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.or, [10, 11]⟩], 12⟩

def fourGate : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [5, 6]⟩], 7⟩

def wire (w : ℕ) (x : Fin 4 → Bool) : Bool :=
  (nestedCircuit.wires (List.ofFn x)).getD w false

lemma nested_isAO2 : IsAO2 4 nestedCircuit := by decide
lemma smaller_isAO2 : IsAO2 4 fourGate := by decide
lemma noFourCycle : NoFourCycle pathGraph := by decide
lemma bipartite : ∀ u v : Fin 4, pathGraph.Adj u v →
    decide (u.val < 2) ≠ decide (v.val < 2) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma nested_computes : circuitFun 4 nestedCircuit = graphFun pathGraph ∅ := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma smaller_computes : circuitFun 4 fourGate = graphFun pathGraph ∅ := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma exactly_two_junk : junk pathGraph nestedCircuit = {2, 4} := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma nested_topForm : TopForm pathGraph nestedCircuit := by decide

lemma actual_nested : InCone 4 nestedCircuit 2 4 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma nested_semantics :
    (∀ x : Fin 4 → Bool, gateVal 4 nestedCircuit 2 x =
      ((x 0 || x 1) && (x 0 || x 2))) ∧
    (∀ x : Fin 4 → Bool, gateVal 4 nestedCircuit 4 x =
      (gateVal 4 nestedCircuit 2 x && (x 1 || x 3))) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma cleaners : wmax pathGraph nestedCircuit 2 = {3} ∧
    wmax pathGraph nestedCircuit 4 = {2, 3} := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma unstarred_edges : Ustar pathGraph nestedCircuit = {s(0, 3), s(1, 2)} := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma later_accepts_unstarred :
    gateVal 4 nestedCircuit 4 (pairInput 0 3) = true ∧
    gateVal 4 nestedCircuit 4 (pairInput 1 2) = true := by decide

lemma no_single_center : ∀ z : Fin 4, ¬ ((z = 0 ∨ z = 3) ∧ (z = 1 ∨ z = 2)) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma no_available_clean_AND : ∀ u v : Fin 10, u.val ≠ 8 → v.val ≠ 8 →
    (∀ x : Fin 4 → Bool, (wire u x && wire v x) = true → graphFun pathGraph ∅ x = true) →
    (wire u (pairInput 0 3) && wire v (pairInput 0 3)) = false ∨
    (wire u (pairInput 1 2) && wire v (pairInput 1 2)) = false := by decide

lemma nested_not_least : ¬ IsLeastAO pathGraph nestedCircuit := by
  intro h
  have hs := h.2.2 fourGate smaller_isAO2 smaller_computes
  change 9 ≤ 4 at hs
  omega

end PEqualNP.Outside.L_meta_5012.NestedReplacementObstruction

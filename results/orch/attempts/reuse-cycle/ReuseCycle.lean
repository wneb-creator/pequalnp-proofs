import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.ReuseCycle

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

abbrev graph : SimpleGraph (Fin 10) :=
  edgeGraph 10 [(0, 2), (0, 3), (0, 5), (1, 3), (1, 4), (1, 6), (2, 4), (2, 7), (3, 8), (4, 9)]

def sharedFilters : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [4, 0]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.and, [14, 15]⟩,
    ⟨.and, [17, 10]⟩,
    ⟨.and, [18, 16]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [10, 20]⟩,
    ⟨.and, [22, 11]⟩,
    ⟨.and, [23, 21]⟩,
    ⟨.or, [1, 7]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.and, [11, 25]⟩,
    ⟨.and, [27, 12]⟩,
    ⟨.and, [28, 26]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.and, [12, 30]⟩,
    ⟨.and, [32, 13]⟩,
    ⟨.and, [33, 31]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [13, 35]⟩,
    ⟨.and, [37, 14]⟩,
    ⟨.and, [38, 36]⟩,
    ⟨.or, [19, 24]⟩,
    ⟨.or, [40, 29]⟩,
    ⟨.or, [41, 34]⟩,
    ⟨.or, [42, 39]⟩], 43⟩

def cleanStars : Circuit :=
  ⟨[⟨.or, [2, 3]⟩,
    ⟨.or, [10, 5]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [13, 6]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.and, [2, 16]⟩,
    ⟨.and, [3, 8]⟩,
    ⟨.and, [4, 9]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [20, 17]⟩,
    ⟨.or, [21, 18]⟩,
    ⟨.or, [22, 19]⟩], 23⟩

lemma sharedFilters_mono : Monotone2 sharedFilters := by
  simp [Monotone2, sharedFilters]

lemma cleanStars_mono : Monotone2 cleanStars := by
  simp [Monotone2, cleanStars]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
lemma sharedFilters_correct : circuitFun 10 sharedFilters = graphFun graph ∅ := by decide

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
lemma cleanStars_correct : circuitFun 10 cleanStars = graphFun graph ∅ := by decide

set_option maxHeartbeats 5000000 in
lemma noTriangle : ∀ a b c : Fin 10, graph.Adj a b → graph.Adj b c → ¬ graph.Adj c a := by decide

set_option maxHeartbeats 5000000 in
lemma noFour : PEqualNP.TopForm.NoFourCycle graph := by decide

lemma sizes : sharedFilters.size = 34 ∧ cleanStars.size = 14 := by decide

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
lemma final_filters_unowned : ∀ i : Fin 5,
    (gateAt sharedFilters (9 + 5 * i.val)).op = GateOp.and ∧
    ∀ u v : Fin 10, graph.Adj u v → ¬ Owns 10 sharedFilters (9 + 5 * i.val) u v := by
  letI : DecidableEq GateOp := gateOpDecEq
  decide

def blackout (j : ℕ) : Circuit :=
  ⟨sharedFilters.gates.set j ⟨GateOp.or, []⟩, sharedFilters.output⟩

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 10000 in
lemma every_gate_pivotal : ∀ j < sharedFilters.gates.length,
    ∃ u v : Fin 10, graph.Adj u v ∧
      circuitFun 10 (blackout j) (pairInput u v) = false := by decide

lemma cyclic_sharing : ∀ i : Fin 5,
    10 + i.val ∈ (gateAt sharedFilters (8 + 5 * i.val)).inputs ∧
    10 + i.val ∈ (gateAt sharedFilters (7 + 5 * ((i + 1).val))).inputs := by decide

end PEqualNP.Outside.L_meta_1772_aux.ReuseCycle

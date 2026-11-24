import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3444

abbrev G : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun i j : Fin 4 => i = 0 ∧ j ≠ 0)

def C : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩,
    ⟨.and, [6, 1]⟩, ⟨.or, [6, 7]⟩], 8⟩

set_option maxRecDepth 4096 in
lemma ao : PEqualNP.TopForm.IsAO2 4 C := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma computes : PEqualNP.MetaComplexity.circuitFun 4 C =
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma fixed : PEqualNP.Core.IsLiftFixedPoint G C := by
  decide

set_option maxRecDepth 4096 in
lemma live : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone 4 C k := by
  decide

abbrev D : Finset (Sym2 (Fin 4)) := {s((0 : Fin 4), 1)}

lemma color_valid : ∀ u v : Fin 4, G.Adj u v →
    decide (u ≠ 0) ≠ decide (v ≠ 0) := by
  decide +kernel

lemma no_four_cycle : PEqualNP.TopForm.NoFourCycle G := by
  decide +kernel

lemma residual_min_cover :
    PEqualNP.MetaComplexity.NestedCover.IsMinCover
      (G.deleteEdges (D : Set (Sym2 (Fin 4)))) ({0} : Finset (Fin 4)) := by
  decide +kernel

lemma residual_edges : G.edgeFinset \ D =
    ({s((0 : Fin 4), 2), s((0 : Fin 4), 3)} : Finset (Sym2 (Fin 4))) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma maximalCores_eq : PEqualNP.Core.maximalCores G C = {3} := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma gammaE_eq : PEqualNP.TopForm.gammaE G C 3 = {s((0 : Fin 4), 1)} := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma internal_card :
    ((({3} : Finset ℕ).biUnion (PEqualNP.Core.coneSet 4 C)).filter
      (fun w => w ∈ ({3} : Finset ℕ) ∨
        ((PEqualNP.TopForm.readers 4 C w).filter
          (fun k => PEqualNP.Core.InOutputCone 4 C k)) ⊆
            ({3} : Finset ℕ).biUnion (PEqualNP.Core.coneSet 4 C))).card = 3 := by
  decide

end PEqualNP.Outside.L_meta_3444

open PEqualNP.Outside.L_meta_3444

theorem PEqualNP.Outside.L_meta_3444 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  intro h
  have hm : PEqualNP.MetaComplexity.NestedCover.IsMinCover
      (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion
        (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin 4))) :
          Set (Sym2 (Fin 4)))) ({0} : Finset (Fin 4)) := by
    simpa only [maximalCores_eq, Finset.singleton_biUnion, gammaE_eq] using residual_min_cover
  have hb := h 4 G C (fun i => decide (i ≠ 0)) {0}
    color_valid no_four_cycle ao computes fixed live hm
  rw [maximalCores_eq, internal_card, Finset.singleton_biUnion, gammaE_eq] at hb
  norm_num [D, residual_edges, C, PEqualNP.CircuitLowerBounds.Circuit.size] at hb

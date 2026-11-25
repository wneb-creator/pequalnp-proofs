import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

abbrev restrictionExampleG : SimpleGraph (Fin 4) :=
  PEqualNP.EdgeOwnership.edgeGraph 4 [(0, 1)]

def restrictionExampleC : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [4, 5]⟩,
      ⟨.and, [6, 0]⟩, ⟨.and, [7, 1]⟩]
    output := 8 }

lemma restrictionExample_model : PEqualNP.TopForm.IsAO2 4 restrictionExampleC := by
  decide

lemma restrictionExample_top :
    PEqualNP.TopForm.TopForm restrictionExampleG restrictionExampleC := by
  decide

lemma restrictionExample_junk :
    PEqualNP.TopForm.junk restrictionExampleG restrictionExampleC = {2, 3} := by
  decide

lemma restrictionExample_computes :
    ∀ x : Fin 4 → Bool,
      PEqualNP.MetaComplexity.circuitFun 4 restrictionExampleC x =
        PEqualNP.MetaComplexity.NestedCover.graphFun restrictionExampleG ∅ x := by
  decide

lemma restrictionExample_noFourCycle :
    PEqualNP.TopForm.NoFourCycle restrictionExampleG := by
  decide

lemma restrictionExample_bipartite :
    ∀ u v : Fin 4, restrictionExampleG.Adj u v →
      decide (u = 0) ≠ decide (v = 0) := by
  decide

def restrictionSingleEdgeC : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [⟨.and, [0, 1]⟩]
    output := 4 }

lemma restrictionExample_not_least :
    ¬ PEqualNP.TopForm.IsLeastAO restrictionExampleG restrictionExampleC := by
  intro h
  have hmodel : PEqualNP.TopForm.IsAO2 4 restrictionSingleEdgeC := by decide
  have hcompute : PEqualNP.MetaComplexity.circuitFun 4 restrictionSingleEdgeC =
      PEqualNP.MetaComplexity.NestedCover.graphFun restrictionExampleG ∅ := by decide
  have hsize := h.2.2 restrictionSingleEdgeC hmodel hcompute
  norm_num [PEqualNP.CircuitLowerBounds.Circuit.size, restrictionExampleC,
    restrictionSingleEdgeC] at hsize

def restrictionAbstractC : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [⟨.and, [4, 0]⟩, ⟨.and, [5, 1]⟩]
    output := 6 }

lemma restrictionAbstract_pairs :
    ∀ u v : Fin 5, PEqualNP.MetaComplexity.circuitFun 5 restrictionAbstractC
      (PEqualNP.EdgeOwnership.pairInput u v) = false := by
  decide

lemma restrictionAbstract_not_graph (H : SimpleGraph (Fin 5)) [DecidableRel H.Adj] :
    PEqualNP.MetaComplexity.circuitFun 5 restrictionAbstractC ≠
      PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ := by
  intro heq
  let x : Fin 5 → Bool := fun i => decide (i = 0 ∨ i = 1 ∨ i = 4)
  have hx : PEqualNP.MetaComplexity.circuitFun 5 restrictionAbstractC x = true := by
    decide
  have hxH : PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ x = true :=
    (congrFun heq x).symm.trans hx
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun,
    Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hxH
  obtain ⟨u, v, huv, _, _⟩ := hxH
  have hp : PEqualNP.MetaComplexity.NestedCover.graphFun H ∅
      (PEqualNP.EdgeOwnership.pairInput u v) = true := by
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun,
      Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    refine ⟨u, v, huv, ?_, ?_⟩ <;> simp [PEqualNP.EdgeOwnership.pairInput]
  have hbad : false = true := (restrictionAbstract_pairs u v).symm.trans
    ((congrFun heq (PEqualNP.EdgeOwnership.pairInput u v)).trans hp)
  cases hbad

end PEqualNP.Outside.L_meta_5012

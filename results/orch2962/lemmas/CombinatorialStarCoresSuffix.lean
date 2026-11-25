
namespace PEqualNP.Outside.L_meta_2962_aux.Combinatorial

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Core

theorem star_forest_core_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (S L T R : Finset (Fin n)) (f : Fin n → Fin n)
    (hD : (maximalCores G C).biUnion (gammaE G C) = L.image (fun v => s(f v, v)))
    (hf : ∀ v ∈ L, f v ∈ S) (hS : S ⊆ L.image f) (hdisj : Disjoint S L)
    (hT : IsMinCover G T)
    (hR : IsMinCover
      (G.deleteEdges (((maximalCores G C).biUnion (gammaE G C)) : Set (Sym2 (Fin n)))) R) :
    ((maximalCores G C).biUnion (gammaE G C)).card + T.card ≤
      ((maximalCores G C).biUnion (coneSet n C)).card + (maximalCores G C).card + R.card := by
  have vertices := PEqualNP.Outside.L_meta_2962.Structural.supported_vertices_bound
    (G := G) (C := C) ao (S ∪ L)
    (star_vertices_incident _ S L f hD hS)
  exact star_forest_budget_sufficient G _ S L T R f _ hD hf hdisj vertices hT hR.1

end PEqualNP.Outside.L_meta_2962_aux.Combinatorial

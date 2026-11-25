import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def reviewPathAdj (a b : Fin 4) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
  (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) ∨
  (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)

def reviewPath : SimpleGraph (Fin 4) where
  Adj := reviewPathAdj
  symm := ⟨by unfold reviewPathAdj; decide⟩
  loopless := ⟨by unfold reviewPathAdj; decide⟩

abbrev reviewPathDecidable : DecidableRel reviewPath.Adj := by
  unfold reviewPath reviewPathAdj
  infer_instance

def reviewNested : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [0, 3]⟩,
    ⟨.or, [1, 6]⟩, ⟨.and, [5, 7]⟩], 8⟩

lemma reviewNested_AO2 : IsAO2 4 reviewNested := by decide

lemma reviewNested_size : reviewNested.size = 5 := rfl

lemma reviewNested_lastAnd : (NestedCover.gateAt reviewNested 4).op = .and := rfl

lemma reviewPath_bipartite :
    ∃ c : Fin 4 → Bool, ∀ u v, reviewPath.Adj u v → c u ≠ c v := by
  refine ⟨fun u => decide (u = 1 ∨ u = 3), ?_⟩
  unfold reviewPath reviewPathAdj
  decide

lemma reviewPath_noFourCycle :
    @NoFourCycle 4 reviewPath reviewPathDecidable := by decide

lemma reviewNested_computes :
    circuitFun 4 reviewNested =
      @NestedCover.graphFun 4 reviewPath reviewPathDecidable ∅ := by decide

lemma reviewNested_clean :
    @BelowF 4 reviewPath reviewPathDecidable reviewNested 4 := by decide

lemma reviewNested_notTopForm :
    ¬ @PEqualNP.TopForm.TopForm 4 reviewPath reviewPathDecidable reviewNested := by decide

lemma reviewPath_noSingleCover :
    ∀ z : Fin 4, ¬ CoverPromise.IsVertexCover reviewPath {z} := by
  unfold CoverPromise.IsVertexCover reviewPath reviewPathAdj
  decide

end PEqualNP.Outside.L_meta_3566

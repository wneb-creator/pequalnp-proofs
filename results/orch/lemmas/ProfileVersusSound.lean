import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.ProfileVersusSound

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev starGraph : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 1), (1, 2), (1, 3)]

def dirtyProfile : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [6, 3]⟩, ⟨.and, [7, 1]⟩], 8⟩

def smallStar : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [5, 1]⟩], 6⟩

lemma starGraph_girth :
    (∀ a b c : Fin 4, starGraph.Adj a b → starGraph.Adj b c → ¬ starGraph.Adj c a) ∧
      PEqualNP.TopForm.NoFourCycle starGraph := by
  decide

lemma dirtyProfile_legal : PEqualNP.TopForm.IsAO2 4 dirtyProfile := by decide

lemma dirtyProfile_correct : circuitFun 4 dirtyProfile = graphFun starGraph ∅ := by
  funext x
  revert x
  decide

lemma dirtyProfile_top : PEqualNP.TopForm.TopForm starGraph dirtyProfile := by decide

lemma dirtyProfile_has_junk : PEqualNP.TopForm.junk starGraph dirtyProfile = {2} := by decide

lemma dirtyProfile_nonempty_star_owners : ∀ j < dirtyProfile.gates.length,
    (gateAt dirtyProfile j).op = GateOp.and → ∃ c : Fin 4,
      (∃ u v : Fin 4, starGraph.Adj u v ∧ Owns 4 dirtyProfile j u v) ∧
      ∀ u v : Fin 4, starGraph.Adj u v → Owns 4 dirtyProfile j u v → u = c ∨ v = c := by
  intro j hj hop
  have hj5 : j < 5 := hj
  interval_cases j <;> norm_num [dirtyProfile, gateAt] at hop
  all_goals decide

lemma dirtyProfile_pivotal : ∀ j : Fin 5, ∃ u v : Fin 4, starGraph.Adj u v ∧
    circuitFun 4 ⟨dirtyProfile.gates.set j.val ⟨.or, []⟩, dirtyProfile.output⟩
      (pairInput u v) = false := by
  decide

lemma smallStar_correct : circuitFun 4 smallStar = graphFun starGraph ∅ := by
  funext x
  revert x
  decide

lemma dirtyProfile_not_least : ¬ PEqualNP.TopForm.IsLeastAO starGraph dirtyProfile := by
  intro h
  have hs := h.2.2 smallStar (by decide) smallStar_correct
  norm_num [Circuit.size, dirtyProfile, smallStar] at hs

end PEqualNP.Outside.L_meta_1031.ProfileVersusSound

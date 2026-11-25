import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

abbrev cycleFiveGraph : SimpleGraph (Fin 5) :=
  edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

def cycleFiveCircuit : Circuit :=
  ⟨[⟨.or, [2, 4]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [3, 5]⟩,
    ⟨.or, [6, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [1, 9]⟩,
    ⟨.or, [8, 10]⟩], 11⟩

lemma cycleFive_mono : Monotone2 cycleFiveCircuit := by
  simp [Monotone2, cycleFiveCircuit]

lemma cycleFive_correct :
    circuitFun 5 cycleFiveCircuit = graphFun cycleFiveGraph ∅ := by decide

lemma cycleFive_profile : HasStarProfile 5 cycleFiveGraph cycleFiveCircuit := by decide

lemma cycleFive_size : cycleFiveCircuit.size = 7 := rfl

lemma cycleFive_triangle_free :
    ∀ a b c : Fin 5, cycleFiveGraph.Adj a b → cycleFiveGraph.Adj b c →
      ¬cycleFiveGraph.Adj c a := by decide

lemma cycleFive_four_cycle_free :
    ∀ a b c d : Fin 5, cycleFiveGraph.Adj a b → cycleFiveGraph.Adj b c →
      cycleFiveGraph.Adj c d → cycleFiveGraph.Adj d a → a = c ∨ b = d := by decide

end PEqualNP.Outside.L_meta_2448_aux

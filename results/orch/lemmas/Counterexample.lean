import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def cycleFive : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 3]⟩,
    ⟨.and, [2, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 8]⟩,
    ⟨.or, [10, 9]⟩], 11⟩

abbrev cycleFiveGraph : SimpleGraph (Fin 5) :=
  edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)]

lemma cycleFive_mono : Monotone2 cycleFive := by
  simp [Monotone2, cycleFive]

lemma cycleFive_correct : circuitFun 5 cycleFive = graphFun cycleFiveGraph ∅ := by
  decide

lemma cycleFive_owns :
    ∀ j < cycleFive.gates.length, (gateAt cycleFive j).op = GateOp.and →
      ∃ u v : Fin 5, cycleFiveGraph.Adj u v ∧ Owns 5 cycleFive j u v := by
  letI : DecidableEq GateOp := gateOpDecEq
  decide

lemma cycleFive_size : cycleFive.size = 7 := rfl

end PEqualNP.Outside.L_meta_1772_aux

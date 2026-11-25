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

def subdividedFour : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [0, 9]⟩,
    ⟨.or, [2, 5]⟩, ⟨.or, [6, 11]⟩, ⟨.and, [1, 12]⟩,
    ⟨.or, [4, 7]⟩, ⟨.and, [2, 14]⟩, ⟨.or, [5, 7]⟩,
    ⟨.and, [3, 16]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [15, 17]⟩,
    ⟨.or, [18, 19]⟩], 20⟩

abbrev subdividedFourGraph : SimpleGraph (Fin 8) :=
  edgeGraph 8 [(0, 3), (1, 2), (0, 4), (2, 4), (1, 5),
    (3, 5), (0, 6), (1, 6), (2, 7), (3, 7)]

lemma subdividedFour_mono : Monotone2 subdividedFour := by
  simp [Monotone2, subdividedFour]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in
lemma subdividedFour_correct :
    circuitFun 8 subdividedFour = graphFun subdividedFourGraph ∅ := by
  decide

set_option maxHeartbeats 5000000 in
lemma subdividedFour_owns :
    ∀ j < subdividedFour.gates.length, (gateAt subdividedFour j).op = GateOp.and →
      ∃ u v : Fin 8, subdividedFourGraph.Adj u v ∧ Owns 8 subdividedFour j u v := by
  letI : DecidableEq GateOp := gateOpDecEq
  decide

lemma subdividedFour_size : subdividedFour.size = 13 := rfl

set_option maxHeartbeats 5000000 in
lemma subdividedFour_noTriangle :
    ∀ u v w : Fin 8, subdividedFourGraph.Adj u v →
      subdividedFourGraph.Adj v w → ¬ subdividedFourGraph.Adj w u := by
  decide

set_option maxHeartbeats 5000000 in
lemma subdividedFour_noFour : PEqualNP.TopForm.NoFourCycle subdividedFourGraph := by
  decide

end PEqualNP.Outside.L_meta_1772_aux

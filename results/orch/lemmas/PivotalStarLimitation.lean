import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.PivotalExample

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

abbrev graph : SimpleGraph (Fin 5) :=
  edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

def circuit : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [1, 3]⟩,
    ⟨.or, [2, 6]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [7, 8]⟩,
    ⟨.or, [9, 10]⟩], 11⟩

lemma mono : Monotone2 circuit := by simp [Monotone2, circuit]

lemma correct : circuitFun 5 circuit = graphFun graph ∅ := by decide

lemma profile : HasStarProfile 5 graph circuit := by decide

lemma size : circuit.size = 7 := rfl

lemma owns_star_two :
    ∀ u v : Fin 5, graph.Adj u v → Owns 5 circuit 5 u v → u = 2 ∨ v = 2 := by
  decide

lemma pivotal_edges_have_no_center :
    ¬∃ c : Fin 5, ∀ u v : Fin 5, graph.Adj u v →
      circuitFun 5 ⟨circuit.gates.set 5 ⟨GateOp.or, []⟩, circuit.output⟩
        (pairInput u v) = false → u = c ∨ v = c := by
  decide

lemma left_operand_rejects_center :
    gateVal 5 circuit 2 (pairInput (2 : Fin 5) 2) = false := by decide

lemma right_operand_accepts_center :
    gateVal 5 circuit 3 (pairInput (2 : Fin 5) 2) = true := by decide

end PEqualNP.Outside.L_meta_2448_aux.PivotalExample

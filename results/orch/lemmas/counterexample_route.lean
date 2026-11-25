import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma edgeless_case (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∀ u v, ¬ G.Adj u v) :
    ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
      ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ u v, G.Adj u v ∧ Owns n C j u v := by
  refine ⟨⟨[], n⟩, ?_, ?_, ?_⟩
  · simp [IsMinimalMonoCircuit, Monotone2, Circuit.size]
  · funext x
    simp [circuitFun, Circuit.eval, Circuit.wires, graphFun, hG]
  · simp

abbrev cycle5Graph : SimpleGraph (Fin 5) :=
  edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

def cycle5Circuit : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [2, 7]⟩,
    ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.or, [10, 9]⟩], 11⟩

lemma cycle5_size : cycle5Circuit.size = 7 := rfl

lemma cycle5_mono : Monotone2 cycle5Circuit := by
  let _ := gateOpDecEq
  unfold Monotone2
  decide

lemma cycle5_function : circuitFun 5 cycle5Circuit = graphFun cycle5Graph ∅ := by
  decide

lemma cycle5_ownership :
    ∀ j < cycle5Circuit.gates.length, (gateAt cycle5Circuit j).op = GateOp.and →
      ∃ u v, cycle5Graph.Adj u v ∧ Owns 5 cycle5Circuit j u v := by
  let _ := gateOpDecEq
  decide

end PEqualNP.Outside.L_meta_1772_aux

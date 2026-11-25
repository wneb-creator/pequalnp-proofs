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

end PEqualNP.Outside.L_meta_1772_aux

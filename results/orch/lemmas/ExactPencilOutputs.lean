import ExactLinearOutputs
import GuardGeometry

namespace PEqualNP.Outside.L_meta_1896_aux.ExactPencilOutputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Routes
open PEqualNP.Outside.L_meta_1896_aux.ExactLinearOutputs
open PEqualNP.Outside.L_meta_1896_aux.GuardGeometry

theorem exact_pencil_output_bound (gates : List Gate) (outputs : Fin 13 → ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 13 + i.val)
    (hcomplement : ∀ p, val gates (outputs p) (complementInput (pencil p)) = false)
    (hsingleton : ∀ p, ∀ v ∈ pencil p,
      val gates (outputs p) (singletonInput v) = true) :
    39 ≤ {j : Fin gates.length | (gates.get j).op = GateOp.or}.ncard := by
  have h := exact_linear_output_bound gates pencil outputs legal hin
    (fun p => by rw [pencil_card]; omega)
    (fun p q hpq => by rw [pencil_inter_card p q hpq]) hcomplement hsingleton
  simpa [pencil_card] using h

end PEqualNP.Outside.L_meta_1896_aux.ExactPencilOutputs

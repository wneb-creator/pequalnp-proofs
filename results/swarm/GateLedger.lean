import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds

def andGate (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

def orGate (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

lemma gate_partition (gs : List Gate)
    (h : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    gs.countP andGate + gs.countP orGate = gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
      have hg := h g (by simp)
      have ht : ∀ a ∈ gs, a.op = GateOp.and ∨ a.op = GateOp.or := by
        intro a ha
        exact h a (by simp [ha])
      have hi := ih ht
      rcases hg with hg | hg <;> simp [andGate, orGate, hg, List.countP_cons] at * <;> omega

lemma ao2_gate_partition (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) :
    C.gates.countP andGate + C.gates.countP orGate = C.size := by
  apply gate_partition
  exact h.1

lemma ledger_closes (n m : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C)
    (cover : Finset (Fin n))
    (ho : m ≤ C.gates.countP orGate + 1)
    (ha : cover.card ≤ C.gates.countP andGate) : m + cover.card ≤ C.size + 1 := by
  have hc := ao2_gate_partition n C h
  omega

end PEqualNP.Outside.L_meta_4970_aux

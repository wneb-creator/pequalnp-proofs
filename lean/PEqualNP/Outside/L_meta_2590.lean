import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590

lemma total_gate_count (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) :
    Nat.card {i : Fin C.gates.length // (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and} +
    Nat.card {i : Fin C.gates.length // (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or} =
      C.size := by
  classical
  have he (i : Fin C.gates.length) :
      (C.gates.get i).op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ↔
      (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    have h := (hm (C.gates.get i) (List.get_mem C.gates i)).1
    change (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or at h
    constructor
    · intro hn
      rcases h with ha | ho
      · exact (hn ha).elim
      · exact ho
    · intro ho ha
      have impossible : PEqualNP.CircuitLowerBounds.GateOp.and =
          PEqualNP.CircuitLowerBounds.GateOp.or := ha.symm.trans ho
      cases impossible
  have hc := Fintype.card_congr (Equiv.subtypeEquivRight he)
  have hn := Fintype.card_subtype_compl
    (fun i : Fin C.gates.length => (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  have hl := Fintype.card_subtype_le
    (fun i : Fin C.gates.length => (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  rw [hc] at hn
  simp only [Fintype.card_fin] at hn hl
  simp only [Nat.card_eq_fintype_card, PEqualNP.CircuitLowerBounds.Circuit.size]
  omega

lemma impossible_from_gate_bounds (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (hs : C.size ≤ 19)
    (ha : 6 ≤ Nat.card {i : Fin C.gates.length //
      (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and})
    (ho : 14 ≤ Nat.card {i : Fin C.gates.length //
      (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}) : False := by
  have h := total_gate_count C hm
  omega

end PEqualNP.Outside.L_meta_2590

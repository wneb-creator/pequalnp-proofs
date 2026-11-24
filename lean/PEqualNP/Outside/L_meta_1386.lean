import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1386_aux
open PEqualNP.CircuitLowerBounds

def C0 : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [25, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 26] }], output := 27 }

theorem snd (z : Fin (7 + 7) → Bool) (h0 : PEqualNP.MetaComplexity.circuitFun (7 + 7) C0 z = true) :
    ∃ p l : Fin 7, (l.val = p.val ∨ (l.val + 1) % 7 = p.val ∨ (l.val + 3) % 7 = p.val) ∧
      z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true := by
  simp [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires, C0, GateOp.eval, List.ofFn_succ] at h0
  rcases h0 with ⟨(((h|h)|h)|h), (((g|g)|g)|g)⟩
  all_goals first | (exact ⟨0, 0, by decide, g.1, g.2⟩) | (exact ⟨0, 0, by decide, h.1, g.2⟩) | (exact ⟨0, 0, by decide, h.1, h.2⟩) | (exact ⟨0, 4, by decide, h.1, g.2⟩) | (exact ⟨0, 6, by decide, h.1, g.2⟩) | (exact ⟨1, 0, by decide, h.1, g.2⟩) | (exact ⟨2, 6, by decide, h.1, g.2⟩) | (exact ⟨3, 2, by decide, g.1, h.2⟩) | (exact ⟨3, 3, by decide, g.1, h.2⟩) | (exact ⟨4, 3, by decide, g.1, h.2⟩) | (exact ⟨5, 2, by decide, g.1, h.2⟩)

end PEqualNP.Outside.L_meta_1386_aux

theorem PEqualNP.Outside.L_meta_1386 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [25, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 26] }], output := 27 } → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 14 ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (7 + 7) (Finset.Ico 7 (7 + 7)) C 2 ∧ (C.lineDegrees (7 + 7) (Finset.Ico 7 (7 + 7))).getD 20 0 ≤ 1 ∧ (C.lineDegrees (7 + 7) (Finset.Ico 7 (7 + 7))).getD 26 0 ≤ 1 ∧ (∀ z : Fin (7 + 7) → Bool, PEqualNP.MetaComplexity.circuitFun (7 + 7) C z = true → ∃ p l : Fin 7, (l.val = p.val ∨ (l.val + 1) % 7 = p.val ∨ (l.val + 3) % 7 = p.val) ∧ z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true) ∧ (C.wires (List.ofFn (fun v : Fin (7 + 7) => if v = Fin.castAdd 7 0 then true else if v = Fin.natAdd 7 0 then true else false))).getD 20 false = true ∧ (C.wires (List.ofFn (fun v : Fin (7 + 7) => if v = Fin.castAdd 7 0 then true else if v = Fin.natAdd 7 0 then true else false))).getD 26 false = true ∧ (C.wires (List.ofFn (fun u : Fin (7 + 7) => decide (u = Fin.castAdd 7 0)))).getD 20 false = false ∧ (C.wires (List.ofFn (fun u : Fin (7 + 7) => decide (u = Fin.castAdd 7 0)))).getD 26 false = false ∧ (∀ l1 : Fin 7, ∃ z1 : Fin (7 + 7) → Bool, (∀ p1 : Fin 7, (l1.val = p1.val ∨ (l1.val + 1) % 7 = p1.val ∨ (l1.val + 3) % 7 = p1.val) → z1 (Fin.castAdd 7 p1) = false) ∧ (C.wires (List.ofFn z1)).getD 20 false = true ∧ ¬ ∃ q1 m1 : Fin 7, (m1.val = q1.val ∨ (m1.val + 1) % 7 = q1.val ∨ (m1.val + 3) % 7 = q1.val) ∧ z1 (Fin.castAdd 7 q1) = true ∧ z1 (Fin.natAdd 7 m1) = true) ∧ (∀ l2 : Fin 7, ∃ z2 : Fin (7 + 7) → Bool, (∀ p2 : Fin 7, (l2.val = p2.val ∨ (l2.val + 1) % 7 = p2.val ∨ (l2.val + 3) % 7 = p2.val) → z2 (Fin.castAdd 7 p2) = false) ∧ (C.wires (List.ofFn z2)).getD 26 false = true ∧ ¬ ∃ q2 m2 : Fin 7, (m2.val = q2.val ∨ (m2.val + 1) % 7 = q2.val ∨ (m2.val + 3) % 7 = q2.val) ∧ z2 (Fin.castAdd 7 q2) = true ∧ z2 (Fin.natAdd 7 m2) = true) := by
  intro C hC
  have hC' : C = PEqualNP.Outside.L_meta_1386_aux.C0 := hC
  subst hC
  refine ⟨?_, rfl, by decide, by decide, by decide, ?_, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · intro z hz
    rw [hC'] at hz
    exact PEqualNP.Outside.L_meta_1386_aux.snd z hz
  · intro l1
    fin_cases l1
    · exact ⟨fun v => decide (v = Fin.castAdd 7 2 ∨ v = Fin.natAdd 7 3), by decide⟩
    · exact ⟨fun v => decide (v = Fin.castAdd 7 0 ∨ v = Fin.natAdd 7 1), by decide⟩
    · exact ⟨fun v => decide (v = Fin.castAdd 7 0 ∨ v = Fin.natAdd 7 1), by decide⟩
    · exact ⟨fun v => decide (v = Fin.castAdd 7 0 ∨ v = Fin.natAdd 7 1), by decide⟩
    · exact ⟨fun v => decide (v = Fin.castAdd 7 1 ∨ v = Fin.natAdd 7 2), by decide⟩
    · exact ⟨fun v => decide (v = Fin.castAdd 7 0 ∨ v = Fin.natAdd 7 1), by decide⟩
    · exact ⟨fun v => decide (v = Fin.castAdd 7 1 ∨ v = Fin.natAdd 7 2), by decide⟩
  · intro l2
    fin_cases l2
    · exact ⟨fun v => decide (v = Fin.castAdd 7 4 ∨ v = Fin.natAdd 7 0), by decide⟩
    · exact ⟨fun v => decide (v = Fin.castAdd 7 3 ∨ v = Fin.natAdd 7 4), by decide⟩
    · exact ⟨fun v => decide (v = Fin.castAdd 7 4 ∨ v = Fin.natAdd 7 0), by decide⟩
    · exact ⟨fun v => decide (v = Fin.castAdd 7 5 ∨ v = Fin.natAdd 7 6), by decide⟩
    · exact ⟨fun v => decide (v = Fin.castAdd 7 3 ∨ v = Fin.natAdd 7 4), by decide⟩
    · exact ⟨fun v => decide (v = Fin.castAdd 7 3 ∨ v = Fin.natAdd 7 4), by decide⟩
    · exact ⟨fun v => decide (v = Fin.castAdd 7 3 ∨ v = Fin.natAdd 7 4), by decide⟩

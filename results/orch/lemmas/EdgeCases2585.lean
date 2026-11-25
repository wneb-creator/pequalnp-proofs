import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma readK_of_false (n : Nat) (C : Circuit) (k : Nat)
    (hfalse : ∀ x : Fin n → Bool, circuitFun n C x = false) :
    PEqualNP.ReadK.IsReadK n C k := by
  intro S hS
  have h := hS.1
  rw [hfalse] at h
  contradiction

lemma empty_incidence (P L : Nat) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hI : ∀ p l, ¬ I p l) (hAO : PEqualNP.TopForm.IsAO2 (P + L) C)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      (∀ y : Fin (P + L) → Bool, circuitFun (P + L) D y =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1 := by
  refine ⟨C, hAO, hC, le_rfl, readK_of_false _ _ _ ?_⟩
  intro x
  rw [hC]
  simp only [hI, false_and, exists_false, decide_false]

def emptyCircuit (n : Nat) : Circuit := ⟨[], n⟩

lemma emptyCircuit_AO (n : Nat) : PEqualNP.TopForm.IsAO2 n (emptyCircuit n) := by
  simp [PEqualNP.TopForm.IsAO2, PEqualNP.EdgeOwnership.AndOrOnly,
    PEqualNP.MetaComplexity.NestedCover.ReadsBack, emptyCircuit]

lemma emptyCircuit_eval (n : Nat) (x : Fin n → Bool) :
    circuitFun n (emptyCircuit n) x = false := by
  simp [circuitFun, Circuit.eval, Circuit.wires, emptyCircuit, List.getD_eq_getElem?_getD]

lemma emptyCircuit_readK (n k : Nat) : PEqualNP.ReadK.IsReadK n (emptyCircuit n) k :=
  readK_of_false _ _ _ (emptyCircuit_eval n)

def edgeCircuit : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩], 2⟩

lemma edgeCircuit_AO : PEqualNP.TopForm.IsAO2 2 edgeCircuit := by decide

lemma edgeCircuit_read1 : PEqualNP.ReadK.IsReadK 2 edgeCircuit 1 := by decide

end PEqualNP.Outside.L_meta_2585

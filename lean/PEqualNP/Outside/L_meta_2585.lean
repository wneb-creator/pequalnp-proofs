import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585

open PEqualNP.CircuitLowerBounds

lemma empty_incidence_replacement (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit) (hI : ∀ p l, ¬ I p l) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      (∀ y : Fin (P + L) → Bool,
        PEqualNP.MetaComplexity.circuitFun (P + L) D y =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1 := by
  let D : Circuit := ⟨[], P + L⟩
  have eval_false (y : Fin (P + L) → Bool) :
      PEqualNP.MetaComplexity.circuitFun (P + L) D y = false := by
    simp [D, PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires,
      List.getD_eq_default]
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · simp [D, PEqualNP.TopForm.IsAO2,
      PEqualNP.EdgeOwnership.AndOrOnly,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  · intro y
    rw [eval_false]
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨p, l, hi, _, _⟩
    exact hI p l hi
  · simp [D, Circuit.size]
  · intro S hS
    have htrue := hS.1
    rw [eval_false] at htrue
    exact Bool.false_ne_true htrue |>.elim

end PEqualNP.Outside.L_meta_2585

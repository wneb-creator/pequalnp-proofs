namespace PEqualNP.Outside.L_meta_2583.Stars

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma replacement_iff_lower_bound (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (C : Circuit) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    (∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ IsReadK (N + N) D 1) ↔
      N * (q + 2) ≤ C.size + 1 := by
  constructor
  · rintro ⟨D,hao,hfun,hsize,hread⟩
    have hb := PlaneCount.read_one_lower q N I D hq hN hc hu hao hfun hread
    omega
  · exact replacement_of_lower_bound q N I C (by omega) hc

end PEqualNP.Outside.L_meta_2583.Stars

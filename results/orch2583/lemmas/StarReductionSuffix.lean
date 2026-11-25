namespace PEqualNP.Outside.L_meta_2583.Stars

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma replacement_of_lower_bound (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (C : Circuit) (hN : 0 < N)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hlower : N * (q + 2) ≤ C.size + 1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ IsReadK (N + N) D 1 := by
  obtain ⟨D, hao, hfun, hread, hsize⟩ := upper q N I hN hc
  exact ⟨D, hao, hfun, by omega, hread⟩

lemma posted_of_lower_bound
    (hlower : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit), 2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) → N * (q + 2) ≤ C.size + 1) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit), 2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) →
      ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
        (∀ y : Fin (N + N) → Bool, circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧
            y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ IsReadK (N + N) D 1 := by
  intro q N I inst C hq hN hc hu hao hfun
  exact replacement_of_lower_bound q N I C (by omega) hc
    (hlower q N I C hq hN hc hu hao hfun)

end PEqualNP.Outside.L_meta_2583.Stars

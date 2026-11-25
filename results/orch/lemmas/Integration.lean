lemma normalization_of_topForm_noJunk
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hcompute : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true))
    (hAdj : ∀ u v, G.Adj u v ↔ ∃ p l : Fin N, I p l ∧
      (u = Fin.castAdd N p ∧ v = Fin.natAdd N l ∨
       v = Fin.castAdd N p ∧ u = Fin.natAdd N l))
    (hTop : PEqualNP.TopForm.TopForm G C)
    (hJunk : PEqualNP.TopForm.junk G C = ∅) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ y : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧
            y (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  have hfun : PEqualNP.MetaComplexity.circuitFun (N + N) C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext z
    rw [hcompute z]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
      false_and, exists_false, decide_false, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨p, l, hI, hp, hl⟩
      exact ⟨Fin.castAdd N p, Fin.natAdd N l,
        (hAdj _ _).mpr ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨p, l, hI, h | h⟩ := (hAdj u v).mp huv
      · exact ⟨p, l, hI, h.1 ▸ hu, h.2 ▸ hv⟩
      · exact ⟨p, l, hI, h.1 ▸ hv, h.2 ▸ hu⟩
  obtain ⟨σ, hσ⟩ := plane_incidence_perm q N I hq hN hL hU
  exact normalization_of_size I C hL
    (NoJunk.plane_noJunk_lower I σ G C hL hU hσ hAdj hAO hfun hTop hJunk)

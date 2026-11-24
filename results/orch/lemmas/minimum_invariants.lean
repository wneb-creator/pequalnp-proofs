import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

lemma minimum_invariants (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (hreads : ReadsBack (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      circuitFun (N + N) D = circuitFun (N + N) C ∧
      (∀ E : Circuit, Monotone2 E → ReadsBack (N + N) E →
        circuitFun (N + N) E = circuitFun (N + N) D → D.size ≤ E.size) ∧
      (∀ j < D.gates.length, mdDirty N I D j →
        ∃ p l : Fin N, I p l ∧ lcEssential N D j p l ∧
          ∃ p' l' : Fin N, I p' l' ∧ lcEssential N D j p' l' ∧ (p ≠ p' ∨ l ≠ l')) ∧
      (∀ j < D.gates.length,
        frDirty (N + N) (fun z => circuitFun (N + N) D z = false) D j →
        (∀ k < D.gates.length,
          frDirty (N + N) (fun z => circuitFun (N + N) D z = false) D k → k ≤ j) →
        (raReaderRoots (N + N) D j).card = 1) := by
  classical
  let P : ℕ → Prop := fun k => ∃ M : Circuit,
    Monotone2 M ∧ ReadsBack (N + N) M ∧
      circuitFun (N + N) M = circuitFun (N + N) C ∧ M.size = k
  have hex : ∃ k, P k := ⟨C.size, C, hmono, hreads, rfl, rfl⟩
  obtain ⟨M, hm, hr, hf, hs⟩ := Nat.find_spec hex
  have hminM (E : Circuit) (hem : Monotone2 E) (her : ReadsBack (N + N) E)
      (hef : circuitFun (N + N) E = circuitFun (N + N) M) : M.size ≤ E.size := by
    rw [hs]
    exact Nat.find_min' hex ⟨E, hem, her, hef.trans hf, rfl⟩
  have hfunM : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) M z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    rw [hf]
    exact hfun z
  obtain ⟨D, hdm, hdr, hds, hdf, hessential⟩ := minimum_dirty_essential N I M hm hr hfunM
  have hDM : circuitFun (N + N) D = circuitFun (N + N) M := by
    funext z
    exact Bool.eq_iff_iff.mpr ((hdf z).trans (hfunM z).symm)
  have hminD (E : Circuit) (hem : Monotone2 E) (her : ReadsBack (N + N) E)
      (hef : circuitFun (N + N) E = circuitFun (N + N) D) : D.size ≤ E.size :=
    hds.trans (hminM E hem her (hef.trans hDM))
  refine ⟨D, hdm, hdr, hds.trans (hminM C hmono hreads hf.symm),
    hDM.trans hf, hminD, hessential, ?_⟩
  intro j hj hd hlast
  exact raMinimumReaderOne (N + N) D hdm hdr hminD j hj hd hlast

end PEqualNP.Outside.L_meta_3451

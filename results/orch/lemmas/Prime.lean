import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma prime_incidence_iff (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (S : Finset (Fin (P + L))) :
    IsPrimeImplicant (P + L) C S ↔
      ∃ p : Fin P, ∃ l : Fin L, I p l ∧
        S = {Fin.castAdd L p, Fin.natAdd P l} := by
  constructor
  · intro hS
    have hs := hS.1
    rw [hC] at hs
    obtain ⟨p, l, hi, hp, hl⟩ := of_decide_eq_true hs
    have hp' : Fin.castAdd L p ∈ S := of_decide_eq_true hp
    have hl' : Fin.natAdd P l ∈ S := of_decide_eq_true hl
    refine ⟨p, l, hi, ?_⟩
    have hsub : ({Fin.castAdd L p, Fin.natAdd P l} : Finset _) ⊆ S := by
      simpa using (Finset.insert_subset_iff.mpr ⟨hp', Finset.singleton_subset_iff.mpr hl'⟩)
    by_contra hne
    have hproper : ({Fin.castAdd L p, Fin.natAdd P l} : Finset _) ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩
    have hz := hS.2 _ (Finset.mem_ssubsets.mpr hproper)
    rw [hC] at hz
    have ht : (∃ p' : Fin P, ∃ l' : Fin L, I p' l' ∧
        setInput ({Fin.castAdd L p, Fin.natAdd P l} : Finset _)
          (Fin.castAdd L p') = true ∧
        setInput ({Fin.castAdd L p, Fin.natAdd P l} : Finset _)
          (Fin.natAdd P l') = true) := by
      exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
    simpa [ht] using hz
  · rintro ⟨p, l, hi, rfl⟩
    constructor
    · rw [hC]
      apply decide_eq_true
      exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
    · intro T hT
      rw [hC, decide_eq_false_iff_not]
      rintro ⟨p', l', hi', hp', hl'⟩
      have hsub := (Finset.mem_ssubsets.mp hT).1
      have hpT : Fin.castAdd L p' ∈ T := of_decide_eq_true hp'
      have hlT : Fin.natAdd P l' ∈ T := of_decide_eq_true hl'
      have hpPair := hsub hpT
      have hlPair := hsub hlT
      have hple : (Fin.castAdd L p' : Fin (P + L)) ≠ Fin.natAdd P l := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      have hlpe : (Fin.natAdd P l' : Fin (P + L)) ≠ Fin.castAdd L p := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      have heqp : Fin.castAdd L p' = Fin.castAdd L p := by
        simpa [Finset.mem_insert, Finset.mem_singleton, hple] using hpPair
      have heql : Fin.natAdd P l' = Fin.natAdd P l := by
        simpa [Finset.mem_insert, Finset.mem_singleton, hlpe] using hlPair
      have hback : ({Fin.castAdd L p, Fin.natAdd P l} : Finset _) ⊆ T := by
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨heqp ▸ hpT, heql ▸ hlT⟩
      exact (Finset.mem_ssubsets.mp hT).2 hback

lemma read_one_of_incidence_edges (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (hread : ∀ p : Fin P, ∀ l : Fin L, I p l →
      readsAtMost C (P + L) (setList {Fin.castAdd L p, Fin.natAdd P l}) 1 = true) :
    IsReadK (P + L) C 1 := by
  intro S hS
  obtain ⟨p, l, hi, rfl⟩ := (prime_incidence_iff P L I C hC S).mp hS
  exact hread p l hi

end PEqualNP.Outside.L_meta_2585

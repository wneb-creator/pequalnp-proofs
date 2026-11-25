import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma castAdd_ne_natAdd {N : ℕ} (p l : Fin N) :
    Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

lemma prime_incidence_pair {N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I] (C : Circuit)
    (hC : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z = decide (∃ p l : Fin N,
        I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (S : Finset (Fin (N + N))) :
    IsPrimeImplicant (N + N) C S ↔
      ∃ p l : Fin N, I p l ∧ S = {Fin.castAdd N p, Fin.natAdd N l} := by
  constructor
  · intro hS
    have hpos := hS.1
    rw [hC] at hpos
    simp only [setInput, decide_eq_true_eq] at hpos
    obtain ⟨p, l, hI, hp, hl⟩ := hpos
    refine ⟨p, l, hI, ?_⟩
    have hsub : ({Fin.castAdd N p, Fin.natAdd N l} : Finset _) ⊆ S := by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hp hl
    by_contra hne
    have hproper : ({Fin.castAdd N p, Fin.natAdd N l} : Finset _) ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩
    have hfalse := hS.2 _ (Finset.mem_ssubsets.mpr hproper)
    rw [hC] at hfalse
    have htrue : (decide (∃ a b : Fin N, I a b ∧
        setInput {Fin.castAdd N p, Fin.natAdd N l} (Fin.castAdd N a) = true ∧
        setInput {Fin.castAdd N p, Fin.natAdd N l} (Fin.natAdd N b) = true)) = true := by
      simp only [decide_eq_true_eq, setInput]
      exact ⟨p, l, hI, by simp, by simp⟩
    rw [htrue] at hfalse
    cases hfalse
  · rintro ⟨p, l, hI, rfl⟩
    constructor
    · rw [hC]
      simp only [decide_eq_true_eq, setInput]
      exact ⟨p, l, hI, by simp, by simp⟩
    · intro T hT
      have hproper := Finset.mem_ssubsets.mp hT
      rw [hC]
      simp only [decide_eq_false_iff_not, setInput, decide_eq_true_eq]
      rintro ⟨a, b, hab, ha, hb⟩
      have hamem := hproper.subset ha
      have hbmem := hproper.subset hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hamem hbmem
      have hap : a = p := by
        rcases hamem with h | h
        · exact Fin.castAdd_inj.mp h
        · exact (castAdd_ne_natAdd a l h).elim
      have hbl : b = l := by
        rcases hbmem with h | h
        · exact (castAdd_ne_natAdd p b h.symm).elim
        · apply Fin.ext
          have hv := congrArg Fin.val h
          simpa only [Fin.val_natAdd, Nat.add_left_cancel_iff] using hv
      subst a
      subst b
      have hrev : ({Fin.castAdd N p, Fin.natAdd N l} : Finset _) ⊆ T := by
        simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro ha hb
      exact (not_le_of_gt hproper) hrev

end PEqualNP.Outside.L_meta_2583_aux

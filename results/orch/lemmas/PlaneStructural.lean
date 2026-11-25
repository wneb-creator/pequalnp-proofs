import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def incidence {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (z : Fin (N + N) → Bool) : Bool :=
  decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
    z (Fin.natAdd N l) = true)

lemma opposite_ne {N : Nat} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  change p.val = N + l.val at hv
  have hp := p.isLt
  omega

lemma incidence_set_true {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (S : Finset (Fin (N + N))) :
    incidence I (setInput S) = true ↔
      ∃ p l : Fin N, I p l ∧ Fin.castAdd N p ∈ S ∧ Fin.natAdd N l ∈ S := by
  simp [incidence, setInput]

lemma incidence_pair_true {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (p l : Fin N) (hil : I p l) :
    incidence I (setInput {Fin.castAdd N p, Fin.natAdd N l}) = true := by
  exact (incidence_set_true I _).2 ⟨p, l, hil, by simp, by simp⟩

lemma point_mem_pair {N : Nat} (p p' l : Fin N)
    (h : Fin.castAdd N p' ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N)))) :
    p' = p := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exact Fin.ext (congrArg (fun x : Fin (N + N) => x.val) h)
  · exact False.elim (opposite_ne p' l h)

lemma line_mem_pair {N : Nat} (p l l' : Fin N)
    (h : Fin.natAdd N l' ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N)))) :
    l' = l := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exact False.elim (opposite_ne p l' h.symm)
  · apply Fin.ext
    have hv := congrArg Fin.val h
    change N + l'.val = N + l.val at hv
    omega

lemma prime_incidence_pair {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (computes : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = incidence I z)
    (S : Finset (Fin (N + N))) :
    IsPrimeImplicant (N + N) C S ↔
      ∃ p l : Fin N, I p l ∧ S = {Fin.castAdd N p, Fin.natAdd N l} := by
  constructor
  · rintro ⟨htrue, hminimal⟩
    rw [computes] at htrue
    obtain ⟨p, l, hil, hp, hl⟩ := (incidence_set_true I S).1 htrue
    refine ⟨p, l, hil, ?_⟩
    have hsub : ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ⊆ S := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> assumption
    by_contra hne
    have hproper : ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ⊂ S := by
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩
    have hfalse := hminimal _ (Finset.mem_ssubsets.mpr hproper)
    rw [computes, incidence_pair_true I p l hil] at hfalse
    cases hfalse
  · rintro ⟨p, l, hil, rfl⟩
    constructor
    · rw [computes]
      exact incidence_pair_true I p l hil
    · intro T hT
      rw [computes]
      apply Bool.eq_false_iff.mpr
      intro htrue
      obtain ⟨p', l', hi', hp', hl'⟩ := (incidence_set_true I T).1 htrue
      have hproper := Finset.mem_ssubsets.mp hT
      have hp := point_mem_pair p p' l (hproper.subset hp')
      have hl := line_mem_pair p l l' (hproper.subset hl')
      subst p'
      subst l'
      have hback : ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ⊆ T := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> assumption
      exact (Finset.ssubset_iff_subset_ne.mp hproper).2 (Finset.Subset.antisymm hproper.subset hback)

lemma prime_incidence_card_two {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (computes : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = incidence I z)
    (S : Finset (Fin (N + N))) (hprime : IsPrimeImplicant (N + N) C S) : S.card = 2 := by
  obtain ⟨p, l, _, rfl⟩ := (prime_incidence_pair I C computes S).1 hprime
  have hnot : Fin.castAdd N p ∉ ({Fin.natAdd N l} : Finset (Fin (N + N))) := by
    simpa only [Finset.mem_singleton] using opposite_ne p l
  rw [Finset.card_insert_of_notMem hnot, Finset.card_singleton]

lemma read_one_iff_incident_pairs {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (computes : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = incidence I z) :
    IsReadK (N + N) C 1 ↔ ∀ p l : Fin N, I p l →
      readsAtMost C (N + N) (setList {Fin.castAdd N p, Fin.natAdd N l}) 1 = true := by
  constructor
  · intro h p l hil
    exact h _ ((prime_incidence_pair I C computes _).2 ⟨p, l, hil, rfl⟩)
  · intro h S hs
    obtain ⟨p, l, hil, rfl⟩ := (prime_incidence_pair I C computes S).1 hs
    exact h p l hil

end PEqualNP.Outside.L_meta_2583

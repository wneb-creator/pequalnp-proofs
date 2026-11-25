import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma point_ne_line {N : ℕ} (p l : Fin N) :
    Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

lemma pair_prime {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (correct : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    {p l : Fin N} (incident : I p l) :
    IsPrimeImplicant (N + N) C {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  constructor
  · rw [correct, decide_eq_true_eq]
    exact ⟨p, l, incident, by simp [setInput], by simp [setInput]⟩
  · intro T hT
    have strict := Finset.mem_ssubsets.mp hT
    rw [correct, decide_eq_false_iff_not]
    rintro ⟨p', l', _, hp, hl⟩
    have hp' : Fin.castAdd N p' ∈ T := of_decide_eq_true hp
    have hl' : Fin.natAdd N l' ∈ T := of_decide_eq_true hl
    have pe : Fin.castAdd N p' = Fin.castAdd N p := by
      have := Finset.mem_insert.mp (strict.subset hp')
      exact this.resolve_right (fun hm => point_ne_line p' l (Finset.mem_singleton.mp hm))
    have le : Fin.natAdd N l' = Fin.natAdd N l := by
      have := Finset.mem_insert.mp (strict.subset hl')
      exact Finset.mem_singleton.mp (this.resolve_left (fun e => point_ne_line p l' e.symm))
    exact strict.not_ge (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simpa only [pe] using hp'
      · rw [Finset.mem_singleton.mp hw, ← le]
        exact hl')

lemma prime_iff_pair {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (correct : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (S : Finset (Fin (N + N))) :
    IsPrimeImplicant (N + N) C S ↔
      ∃ p l : Fin N, I p l ∧ S = {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  constructor
  · intro prime
    have accepted := prime.1
    rw [correct, decide_eq_true_eq] at accepted
    obtain ⟨p, l, incident, hp, hl⟩ := accepted
    have hp' : Fin.castAdd N p ∈ S := of_decide_eq_true hp
    have hl' : Fin.natAdd N l ∈ S := of_decide_eq_true hl
    have sub : {Fin.castAdd N p, Fin.natAdd N l} ⊆ S := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hp', hl'⟩
    refine ⟨p, l, incident, ?_⟩
    by_contra different
    have strict : {Fin.castAdd N p, Fin.natAdd N l} ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨sub, Ne.symm different⟩
    have rejected := prime.2 _ (Finset.mem_ssubsets.mpr strict)
    have truePair := (pair_prime I C correct incident).1
    rw [truePair] at rejected
    cases rejected
  · rintro ⟨p, l, incident, rfl⟩
    exact pair_prime I C correct incident

lemma read_iff_edges {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit)
    (correct : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true)) (k : ℕ) :
    IsReadK (N + N) C k ↔
      ∀ p l : Fin N, I p l →
        readsAtMost C (N + N) (setList {Fin.castAdd N p, Fin.natAdd N l}) k = true := by
  constructor
  · intro read p l incident
    exact read _ (pair_prime I C correct incident)
  · intro edges S prime
    obtain ⟨p, l, incident, rfl⟩ := (prime_iff_pair I C correct S).mp prime
    exact edges p l incident

end PEqualNP.Outside.L_meta_2583.Restriction

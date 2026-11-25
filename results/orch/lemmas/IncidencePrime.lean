import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma point_ne_line {N : ℕ} (p l : Fin N) :
    Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

lemma incident_pair_prime {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    {p l : Fin N} (hi : I p l) :
    IsPrimeImplicant (N + N) C {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  constructor
  · rw [hC, decide_eq_true_eq]
    exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
  · intro T hT
    have hT' := Finset.mem_ssubsets.mp hT
    rw [hC, decide_eq_false_iff_not]
    rintro ⟨p', l', _, hp, hl⟩
    have hp' : Fin.castAdd N p' ∈ T := of_decide_eq_true hp
    have hl' : Fin.natAdd N l' ∈ T := of_decide_eq_true hl
    have pe : Fin.castAdd N p' = Fin.castAdd N p := by
      have := Finset.mem_insert.mp (hT'.subset hp')
      exact this.resolve_right (fun hm => point_ne_line p' l (Finset.mem_singleton.mp hm))
    have le : Fin.natAdd N l' = Fin.natAdd N l := by
      have := Finset.mem_insert.mp (hT'.subset hl')
      exact Finset.mem_singleton.mp (this.resolve_left (fun e => point_ne_line p l' e.symm))
    exact hT'.not_ge (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simpa only [pe] using hp'
      · rw [Finset.mem_singleton.mp hw, ← le]
        exact hl')

lemma prime_iff_incident_pair {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (S : Finset (Fin (N + N))) :
    IsPrimeImplicant (N + N) C S ↔
      ∃ p l : Fin N, I p l ∧ S = {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  constructor
  · intro h
    have accepts := h.1
    rw [hC, decide_eq_true_eq] at accepts
    obtain ⟨p, l, hi, hp, hl⟩ := accepts
    have hp' : Fin.castAdd N p ∈ S := of_decide_eq_true hp
    have hl' : Fin.natAdd N l ∈ S := of_decide_eq_true hl
    have sub : ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ⊆ S := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hp'
      · simpa only [Finset.mem_singleton.mp hw] using hl'
    refine ⟨p, l, hi, ?_⟩
    by_contra different
    have proper : ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨sub, Ne.symm different⟩
    have rejects := h.2 _ (Finset.mem_ssubsets.mpr proper)
    have accepts := (incident_pair_prime I hC hi).1
    rw [accepts] at rejects
    contradiction
  · rintro ⟨p, l, hi, rfl⟩
    exact incident_pair_prime I hC hi

lemma read_one_iff_incident_pairs {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true)) :
    IsReadK (N + N) C 1 ↔ ∀ p l : Fin N, I p l →
      readsAtMost C (N + N) (setList {Fin.castAdd N p, Fin.natAdd N l}) 1 = true := by
  constructor
  · intro h p l hi
    exact h _ (incident_pair_prime I hC hi)
  · intro h S hs
    obtain ⟨p, l, hi, rfl⟩ := (prime_iff_incident_pair I hC S).mp hs
    exact h p l hi

end PEqualNP.Outside.L_meta_2583_aux

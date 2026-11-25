import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.Semantics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma point_ne_line {N : ℕ} (p l : Fin N) :
    Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

lemma setList_pair {n : ℕ} (a b : Fin n) (hab : a < b) :
    setList ({a, b} : Finset (Fin n)) = [a.val, b.val] := by
  have key : ∀ x y : Fin n, x < y → y < x → x = y :=
    fun x y h1 h2 => absurd h1 (lt_asymm h2)
  have hp1 : List.Pairwise (fun x y : Fin n => x < y)
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) :=
    List.Pairwise.filter _ (List.pairwise_lt_finRange n)
  have hp2 : List.Pairwise (fun x y : Fin n => x < y) [a, b] := by simp [hab]
  have hperm : List.Perm
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) [a, b] := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.Nodup.filter _ (List.nodup_finRange n)
    · simp [ne_of_lt hab]
    · ext x
      simp
  have h : (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) = [a, b] :=
    List.Perm.eq_of_pairwise (fun x y _ _ => key x y) hp1 hp2 hperm
  unfold setList
  rw [h]
  rfl

variable {N : ℕ} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]

lemma incident_pair_prime
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
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

lemma prime_iff_incident_pair
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (S : Finset (Fin (N + N))) :
    IsPrimeImplicant (N + N) C S ↔
      ∃ p l : Fin N, I p l ∧ S = {Fin.castAdd N p, Fin.natAdd N l} := by
  constructor
  · intro hS
    have accepted := hS.1
    rw [hC, decide_eq_true_eq] at accepted
    obtain ⟨p, l, hpl, hp, hl⟩ := accepted
    have hp' : Fin.castAdd N p ∈ S := of_decide_eq_true hp
    have hl' : Fin.natAdd N l ∈ S := of_decide_eq_true hl
    refine ⟨p, l, hpl, ?_⟩
    have hsub : {Fin.castAdd N p, Fin.natAdd N l} ⊆ S := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hp'
      · simpa only [Finset.mem_singleton.mp hv] using hl'
    by_contra hne
    have hstrict : {Fin.castAdd N p, Fin.natAdd N l} ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩
    have hz := hS.2 _ (Finset.mem_ssubsets.mpr hstrict)
    have ht := (incident_pair_prime I hC hpl).1
    rw [hz] at ht
    contradiction
  · rintro ⟨p, l, hpl, rfl⟩
    exact incident_pair_prime I hC hpl

lemma read_iff_incident_pairs
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (k : ℕ) :
    IsReadK (N + N) C k ↔
      ∀ p l : Fin N, I p l → readsAtMost C (N + N) [p.val, N + l.val] k = true := by
  have pair_list (p l : Fin N) :
      setList ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) =
        [p.val, N + l.val] := by
    apply setList_pair
    change p.val < N + l.val
    omega
  constructor
  · intro h p l hpl
    have hpair := h _ (incident_pair_prime I hC hpl)
    rwa [pair_list] at hpair
  · intro h S hS
    obtain ⟨p, l, hpl, rfl⟩ := (prime_iff_incident_pair I hC S).mp hS
    rw [pair_list]
    exact h p l hpl

end PEqualNP.Outside.L_meta_2583_aux.Semantics

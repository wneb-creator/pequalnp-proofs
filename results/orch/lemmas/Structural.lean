import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma cast_ne_nat {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

lemma pair_prime {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
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
      exact this.resolve_right (fun hm => cast_ne_nat p' l (Finset.mem_singleton.mp hm))
    have le : Fin.natAdd N l' = Fin.natAdd N l := by
      have := Finset.mem_insert.mp (hT'.subset hl')
      exact Finset.mem_singleton.mp (this.resolve_left (fun e => cast_ne_nat p l' e.symm))
    exact hT'.not_ge (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simpa only [pe] using hp'
      · rw [Finset.mem_singleton.mp hw, ← le]
        exact hl')

lemma prime_iff_pair {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (S : Finset (Fin (N + N))) :
    IsPrimeImplicant (N + N) C S ↔
      ∃ p l : Fin N, I p l ∧ S = {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  constructor
  · intro hs
    have htrue := hs.1
    rw [hC, decide_eq_true_eq] at htrue
    obtain ⟨p, l, hi, hp, hl⟩ := htrue
    have hp' : Fin.castAdd N p ∈ S := of_decide_eq_true hp
    have hl' : Fin.natAdd N l ∈ S := of_decide_eq_true hl
    have hsub : ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ⊆ S := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hp'
      · rw [Finset.mem_singleton.mp hw]
        exact hl'
    refine ⟨p, l, hi, ?_⟩
    by_contra hne
    have hstrict : ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩
    have hfalse := hs.2 _ (Finset.mem_ssubsets.mpr hstrict)
    have hpair := (pair_prime I hC hi).1
    exact Bool.noConfusion (hfalse.symm.trans hpair)
  · rintro ⟨p, l, hi, rfl⟩
    exact pair_prime I hC hi

lemma setList_pair_sorted {n : ℕ} (a b : Fin n) (hab : a < b) :
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

lemma setList_incident {N : ℕ} (p l : Fin N) :
    setList ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) =
      [p.val, N + l.val] := by
  apply setList_pair_sorted
  change p.val < N + l.val
  omega

lemma read_iff_pairs {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (k : ℕ) :
    IsReadK (N + N) C k ↔ ∀ p l : Fin N, I p l →
      readsAtMost C (N + N) (setList {Fin.castAdd N p, Fin.natAdd N l}) k = true := by
  constructor
  · intro h p l hi
    exact h _ (pair_prime I hC hi)
  · intro h S hs
    obtain ⟨p, l, hi, rfl⟩ := (prime_iff_pair I hC S).mp hs
    exact h p l hi

lemma least_equivalent (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size ≤ C.size ∧ ∀ E : Circuit, PEqualNP.TopForm.IsAO2 n E →
        circuitFun n E = circuitFun n C → D.size ≤ E.size := by
  classical
  have hex : ∃ s : ℕ, ∃ D : Circuit,
      PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧ D.size = s :=
    ⟨C.size, C, hC, rfl, rfl⟩
  obtain ⟨D, hAO, hfun, hsize⟩ := Nat.find_spec hex
  refine ⟨D, hAO, hfun, ?_, ?_⟩
  · rw [hsize]
    exact Nat.find_min' hex ⟨C, hC, rfl, rfl⟩
  · intro E hE hfunE
    rw [hsize]
    exact Nat.find_min' hex ⟨E, hE, hfunE, rfl⟩

end PEqualNP.Outside.L_meta_2583

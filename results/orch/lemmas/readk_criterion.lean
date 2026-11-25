import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

lemma sides_disjoint (N : ℕ) (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  change p.val = N + l.val at hv
  omega

lemma incidence_prime_iff (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧
          z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (S : Finset (Fin (N + N))) :
    PEqualNP.ReadK.IsPrimeImplicant (N + N) C S ↔
      ∃ p l : Fin N, I p l ∧ S = {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  constructor
  · intro hS
    obtain ⟨p, l, hI, hp, hl⟩ : ∃ p l : Fin N,
        I p l ∧ Fin.castAdd N p ∈ S ∧ Fin.natAdd N l ∈ S := by
      simpa [hfun, PEqualNP.ReadK.setInput] using hS.1
    refine ⟨p, l, hI, ?_⟩
    have hsub : {Fin.castAdd N p, Fin.natAdd N l} ⊆ S := by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hp hl
    by_contra hne
    have hss : {Fin.castAdd N p, Fin.natAdd N l} ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩
    have hfalse := hS.2 _ (Finset.mem_ssubsets.mpr hss)
    have htrue : PEqualNP.MetaComplexity.circuitFun (N + N) C
        (PEqualNP.ReadK.setInput {Fin.castAdd N p, Fin.natAdd N l}) = true := by
      rw [hfun, decide_eq_true_eq]
      exact ⟨p, l, hI, by simp [PEqualNP.ReadK.setInput], by simp [PEqualNP.ReadK.setInput]⟩
    rw [htrue] at hfalse
    cases hfalse
  · rintro ⟨p, l, hI, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hfun, decide_eq_true_eq]
      exact ⟨p, l, hI, by simp [PEqualNP.ReadK.setInput], by simp [PEqualNP.ReadK.setInput]⟩
    · intro T hT
      rw [hfun, decide_eq_false_iff_not]
      rintro ⟨a, b, _, ha, hb⟩
      have haT : Fin.castAdd N a ∈ T := by simpa [PEqualNP.ReadK.setInput] using ha
      have hbT : Fin.natAdd N b ∈ T := by simpa [PEqualNP.ReadK.setInput] using hb
      have hss := Finset.mem_ssubsets.mp hT
      have hap : Fin.castAdd N a = Fin.castAdd N p := by
        have hmem := hss.subset haT
        rcases Finset.mem_insert.mp hmem with h | h
        · exact h
        · exact (sides_disjoint N a l (Finset.mem_singleton.mp h)).elim
      have hbl : Fin.natAdd N b = Fin.natAdd N l := by
        have hmem := hss.subset hbT
        rcases Finset.mem_insert.mp hmem with h | h
        · exact (sides_disjoint N p b h.symm).elim
        · exact Finset.mem_singleton.mp h
      have hpT : Fin.castAdd N p ∈ T := by simpa only [hap] using haT
      have hlT : Fin.natAdd N l ∈ T := by simpa only [hbl] using hbT
      have hback : {Fin.castAdd N p, Fin.natAdd N l} ⊆ T := by
        simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hpT hlT
      have hlt := Finset.card_lt_card hss
      have hle := Finset.card_le_card hback
      omega

lemma readk_setList_pair {n : ℕ} (a b : Fin n) (hab : a < b) :
    PEqualNP.ReadK.setList ({a, b} : Finset (Fin n)) = [a.val, b.val] := by
  have key : ∀ x y : Fin n, x < y → y < x → x = y :=
    fun x y h1 h2 => absurd h1 (lt_asymm h2)
  have hp1 : List.Pairwise (fun x y : Fin n => x < y)
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) :=
    List.Pairwise.filter _ (List.pairwise_lt_finRange n)
  have hp2 : List.Pairwise (fun x y : Fin n => x < y) [a, b] := by
    simp [hab]
  have hperm : List.Perm
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) [a, b] := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.Nodup.filter _ (List.nodup_finRange n)
    · simp [ne_of_lt hab]
    · ext x
      simp
  have h : (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) = [a, b] :=
    List.Perm.eq_of_pairwise (fun x y _ _ => key x y) hp1 hp2 hperm
  unfold PEqualNP.ReadK.setList
  rw [h]
  rfl
lemma incidence_setList_pair (N : ℕ) (p l : Fin N) :
    PEqualNP.ReadK.setList ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) =
      [p.val, N + l.val] := by
  have hp : Fin.castAdd N p < Fin.natAdd N l := by
    change p.val < N + l.val
    omega
  exact readk_setList_pair _ _ hp

lemma incidence_isReadK_iff (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧
          z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) (k : ℕ) :
    PEqualNP.ReadK.IsReadK (N + N) C k ↔
      ∀ p l : Fin N, I p l → PEqualNP.ReadK.readsAtMost C (N + N) [p.val, N + l.val] k = true := by
  constructor
  · intro h p l hI
    have hs := h _ ((incidence_prime_iff N I C hfun _).mpr ⟨p, l, hI, rfl⟩)
    rwa [incidence_setList_pair] at hs
  · intro h S hS
    obtain ⟨p, l, hI, rfl⟩ := (incidence_prime_iff N I C hfun S).mp hS
    rw [incidence_setList_pair]
    exact h p l hI

end PEqualNP.Outside.L_meta_2583

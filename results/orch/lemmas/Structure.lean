import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.Structure

open Finset

lemma strict_neighbors (N d : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hrow : ∀ p, (Finset.univ.filter fun l => I p l).card = d)
    (hcol : ∀ l, (Finset.univ.filter fun p => I p l).card = d)
    (hpairs : ∀ p p', p ≠ p' → ∃ l, I p l ∧ I p' l)
    (S : Finset (Fin N)) (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    S.card < (Finset.univ.filter fun l => ∃ p ∈ S, I p l).card := by
  classical
  let T := Finset.univ.filter fun l => ∃ p ∈ S, I p l
  have hcount : S.card * d = ∑ l ∈ T, (S.filter fun p => I p l).card := by
    calc
      S.card * d = ∑ p ∈ S, (Finset.univ.filter fun l => I p l).card := by
        simp [hrow]
      _ = ∑ l : Fin N, (S.filter fun p => I p l).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
      _ = ∑ l ∈ T, (S.filter fun p => I p l).card := by
        symm
        apply Finset.sum_subset (Finset.subset_univ T)
        intro l _ hl
        have hempty : S.filter (fun p => I p l) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro p hp
          exact hl (by simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
                       exact ⟨p, (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩)
        simp [hempty]
  have hle (l : Fin N) : (S.filter fun p => I p l).card ≤ d := by
    rw [← hcol l]
    apply Finset.card_le_card
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  obtain ⟨p, hp⟩ := hne
  obtain ⟨p', hp'⟩ : ∃ p' : Fin N, p' ∉ S := by
    by_contra h
    push Not at h
    exact hproper (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨l, hl, hl'⟩ := hpairs p p' (by intro h; subst p'; exact hp' hp)
  have hlT : l ∈ T := by simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨p, hp, hl⟩
  have hlt : (S.filter fun p => I p l).card < d := by
    rw [← hcol l]
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
    · intro heq
      have hm : p' ∈ S.filter fun p => I p l := by
        rw [heq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'⟩
      exact hp' (Finset.mem_filter.mp hm).1
  have htotal : S.card * d < T.card * d := by
    rw [hcount]
    calc
      (∑ l ∈ T, (S.filter fun p => I p l).card) < ∑ _l ∈ T, d :=
        Finset.sum_lt_sum (fun l _ => hle l) ⟨l, hlT, hlt⟩
      _ = T.card * d := by simp
  exact Nat.lt_of_mul_lt_mul_right htotal

lemma minimum_cover_rigidity (N d : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hd : 0 < d)
    (hrow : ∀ p, (Finset.univ.filter fun l => I p l).card = d)
    (hcol : ∀ l, (Finset.univ.filter fun p => I p l).card = d)
    (hpairs : ∀ p p', p ≠ p' → ∃ l, I p l ∧ I p' l)
    (A B : Finset (Fin N))
    (hcover : ∀ p l, I p l → p ∈ A ∨ l ∈ B)
    (hsize : A.card + B.card ≤ N) :
    (A = ∅ ∧ B = Finset.univ) ∨ (A = Finset.univ ∧ B = ∅) := by
  classical
  by_cases hA : A = ∅
  · left
    refine ⟨hA, Finset.eq_univ_iff_forall.mpr ?_⟩
    intro l
    have hpos : 0 < (Finset.univ.filter fun p => I p l).card := by rw [hcol]; exact hd
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    rcases hcover p l (Finset.mem_filter.mp hp).2 with hpA | hlB
    · simpa [hA] using hpA
    · exact hlB
  · right
    have hAU : A = Finset.univ := by
      by_contra hAU
      let S := Finset.univ \ A
      have hSne : S.Nonempty := by
        apply Finset.nonempty_iff_ne_empty.mpr
        intro hS
        have hall : ∀ p : Fin N, p ∈ A := by
          intro p
          by_contra hp
          have : p ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hp⟩
          simpa [hS] using this
        exact hAU (Finset.eq_univ_iff_forall.mpr hall)
      have hSproper : S ≠ Finset.univ := by
        obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hA
        intro hS
        have : p ∈ S := by rw [hS]; exact Finset.mem_univ _
        exact (Finset.mem_sdiff.mp this).2 hp
      have hstrict := strict_neighbors N d I hrow hcol hpairs S hSne hSproper
      have hsub : (Finset.univ.filter fun l => ∃ p ∈ S, I p l) ⊆ B := by
        intro l hl
        obtain ⟨p, hp, hI⟩ := (Finset.mem_filter.mp hl).2
        exact (hcover p l hI).resolve_left (Finset.mem_sdiff.mp hp).2
      have hcard := Finset.card_le_card hsub
      have hpartition : S.card + A.card = N := by
        dsimp [S]
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, Fintype.card_fin]
        have hAN : A.card ≤ N := by simpa using Finset.card_le_univ A
        omega
      omega
    refine ⟨hAU, Finset.card_eq_zero.mp ?_⟩
    rw [hAU, Finset.card_univ, Fintype.card_fin] at hsize
    omega

end PEqualNP.Outside.L_meta_2583_aux.Structure

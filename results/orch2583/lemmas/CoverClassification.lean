import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Outside.L_meta_2583.Geometry

lemma lines_have_at_most_one_common_point {N : ℕ}
    (I : Fin N → Fin N → Prop)
    (join : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {l l' p p' : Fin N} (hne : l ≠ l')
    (hp : I p l ∧ I p l') (hp' : I p' l ∧ I p' l') : p = p' := by
  by_contra hpp
  obtain ⟨a, ha, hu⟩ := join p p' hpp
  exact hne ((hu l ⟨hp.1, hp'.1⟩).trans (hu l' ⟨hp.2, hp'.2⟩).symm)

lemma dual_unique_point_of_degrees {N d : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hd : 0 < d)
    (columns : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = d)
    (rows : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = d)
    (join : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (l l' : Fin N) (hne : l ≠ l') : ∃! p : Fin N, I p l ∧ I p l' := by
  classical
  have hex : ∃ p : Fin N, I p l ∧ I p l' := by
    by_contra hdisjoint
    have hcolpos : 0 < (Finset.univ.filter (fun p => I p l')).card := by
      rw [columns]
      exact hd
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hcolpos
    have hpl' : I p l' := (Finset.mem_filter.mp hp).2
    have hpl : ¬ I p l := fun h => hdisjoint ⟨p, h, hpl'⟩
    let L := Finset.univ.filter (fun r => I r l)
    let P := Finset.univ.filter (fun a => I p a)
    have hdistinct : ∀ r ∈ L, p ≠ r := by
      intro r hr hpr
      exact hpl (hpr.symm ▸ (Finset.mem_filter.mp hr).2)
    let f : Fin N → Fin N := fun r =>
      if hr : r ∈ L then Classical.choose (join p r (hdistinct r hr)) else l'
    have hf : ∀ r ∈ L, I p (f r) ∧ I r (f r) := by
      intro r hr
      simp only [f, dite_eq_left hr]
      exact (Classical.choose_spec (join p r (hdistinct r hr))).1
    have hf_inj : Set.InjOn f L := by
      intro r hr s hs heq
      by_contra hrs
      obtain ⟨a, ha, hu⟩ := join r s hrs
      have hrl : I r l := (Finset.mem_filter.mp hr).2
      have hsl : I s l := (Finset.mem_filter.mp hs).2
      have hsame : f r = l :=
        (hu (f r) ⟨(hf r hr).2, heq.symm ▸ (hf s hs).2⟩).trans (hu l ⟨hrl, hsl⟩).symm
      exact hpl (hsame ▸ (hf r hr).1)
    have hsub : L.image f ⊆ P.erase l' := by
      intro a ha
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        exact hdisjoint ⟨r, (Finset.mem_filter.mp hr).2, heq ▸ (hf r hr).2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf r hr).1⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr hf_inj] at hcard
    have hpP : l' ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl'⟩
    rw [Finset.card_erase_of_mem hpP] at hcard
    have hL : L.card = d := columns l
    have hP : P.card = d := rows p
    rw [hL, hP] at hcard
    exact (not_le_of_gt (Nat.sub_lt hd (by decide : 0 < 1))) hcard
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, hp, ?_⟩
  intro p' hp'
  exact lines_have_at_most_one_common_point I join hne hp' hp


open scoped BigOperators

lemma nonincident_mixed_sets_bound_of_degrees {N q : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q)
    (columns : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (rows : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (join : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (hA : A.Nonempty) (hB : B.Nonempty)
    (none : ∀ p ∈ A, ∀ l ∈ B, ¬ I p l) : A.card + B.card ≤ N - q := by
  classical
  obtain ⟨p₀, hp₀⟩ := hA
  obtain ⟨l₀, hl₀⟩ := hB
  let A' := A.erase p₀
  let P := Finset.univ.filter (fun l => I p₀ l)
  let R := Finset.univ \ (P ∪ B)
  have hPB : Disjoint P B := by
    apply Finset.disjoint_left.mpr
    intro l hlP hlB
    exact none p₀ hp₀ l hlB (Finset.mem_filter.mp hlP).2
  have hR : R.card + ((q + 1) + B.card) = N := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (P ∪ B))
    rw [Finset.card_union_of_disjoint hPB] at h
    change R.card + (P.card + B.card) = (Finset.univ : Finset (Fin N)).card at h
    simpa only [P, rows, Finset.card_univ, Fintype.card_fin] using h
  have hrow : ∀ p ∈ A', (R.filter (fun l => I p l)).card = q := by
    intro p hp
    have hpA : p ∈ A := (Finset.mem_erase.mp hp).2
    have hpp₀ : p ≠ p₀ := (Finset.mem_erase.mp hp).1
    obtain ⟨a, ⟨hpa, hp₀a⟩, hu⟩ := join p p₀ hpp₀
    have heq : R.filter (fun l => I p l) =
        (Finset.univ.filter (fun l => I p l)).erase a := by
      ext l
      constructor
      · intro hl
        obtain ⟨hlR, hpl⟩ := Finset.mem_filter.mp hl
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩⟩
        intro hla
        have hlP : l ∈ P := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hla.symm ▸ hp₀a⟩
        exact (Finset.mem_sdiff.mp hlR).2 (Finset.mem_union_left B hlP)
      · intro hl
        obtain ⟨hla, hlQ⟩ := Finset.mem_erase.mp hl
        have hpl : I p l := (Finset.mem_filter.mp hlQ).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, hpl⟩
        intro hlU
        rcases Finset.mem_union.mp hlU with hlP | hlB
        · exact hla (hu l ⟨hpl, (Finset.mem_filter.mp hlP).2⟩)
        · exact none p hpA l hlB hpl
    rw [heq, Finset.card_erase_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpa⟩), rows]
    simp
  have hcol : ∀ l ∈ R, (A'.filter (fun p => I p l)).card ≤ q := by
    intro l hlR
    have hlB : l ∉ B := fun h =>
      (Finset.mem_sdiff.mp hlR).2 (Finset.mem_union_right P h)
    have hll₀ : l ≠ l₀ := fun h => hlB (h.symm ▸ hl₀)
    obtain ⟨r, ⟨hrl, hrl₀⟩, _⟩ :=
      dual_unique_point_of_degrees I (Nat.succ_pos q) columns rows join l l₀ hll₀
    have hrA : r ∉ A' := fun h => none r (Finset.mem_erase.mp h).2 l₀ hl₀ hrl₀
    have hsub : A'.filter (fun p => I p l) ⊆
        (Finset.univ.filter (fun p => I p l)).erase r := by
      intro p hp
      obtain ⟨hpA, hpl⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩⟩
      intro hpr
      exact hrA (hpr ▸ hpA)
    have hc := Finset.card_le_card hsub
    have hrQ : r ∈ Finset.univ.filter (fun p => I p l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrl⟩
    rw [Finset.card_erase_of_mem hrQ, columns] at hc
    simpa using hc
  have double_count :
      (∑ p ∈ A', (R.filter (fun l => I p l)).card) =
        ∑ l ∈ R, (A'.filter (fun p => I p l)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hsum : A'.card * q ≤ R.card * q := by
    rw [← Finset.sum_const_nat hrow, double_count]
    calc
      (∑ l ∈ R, (A'.filter (fun p => I p l)).card) ≤ ∑ l ∈ R, q :=
        Finset.sum_le_sum hcol
      _ = R.card * q := by simp
  have hsmall : A'.card ≤ R.card := Nat.le_of_mul_le_mul_right hsum hq
  have hAc : A'.card + 1 = A.card := Finset.card_erase_add_one hp₀
  omega

lemma point_degree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) : (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  classical
  let L : Finset (Fin N) := Finset.univ.filter (fun l => I p l)
  let F (l : Fin N) : Finset (Fin N) := (Finset.univ.filter (fun r => I r l)).erase p
  have hc : ∀ l ∈ L, (F l).card = q := by
    intro l hl
    have hp : p ∈ Finset.univ.filter (fun r => I r l) := by
      simpa [L] using hl
    simp only [F, Finset.card_erase_of_mem hp, hline]
    omega
  have hd : (L : Set (Fin N)).PairwiseDisjoint F := by
    intro l hl l' hl' hne
    apply Finset.disjoint_left.mpr
    intro r hr hr'
    have hrl : r ≠ p ∧ I r l := by simpa [F] using hr
    have hrl' : r ≠ p ∧ I r l' := by simpa [F] using hr'
    have hpl : I p l := by simpa [L] using hl
    have hpl' : I p l' := by simpa [L] using hl'
    obtain ⟨a, ha, hu⟩ := hpair p r (Ne.symm hrl.1)
    exact hne ((hu l ⟨hpl, hrl.2⟩).trans (hu l' ⟨hpl', hrl'.2⟩).symm)
  have hu : L.biUnion F = Finset.univ.erase p := by
    ext r
    simp only [Finset.mem_biUnion, L, F, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    constructor
    · rintro ⟨l, hpl, hrp, hrl⟩
      exact ⟨hrp, trivial⟩
    · rintro ⟨hrp, _⟩
      obtain ⟨l, ⟨hpl, hrl⟩, _⟩ := hpair p r (Ne.symm hrp)
      exact ⟨l, hpl, hrp, hrl⟩
  have hsum : (L.biUnion F).card = L.card * q := by
    rw [Finset.card_biUnion hd]
    exact Finset.sum_const_nat hc
  have hcount : (Finset.univ.erase p).card + 1 = N := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ p)
  rw [← hu, hsum] at hcount
  change L.card = q + 1
  have heq : L.card * q = q ^ 2 + q := Nat.add_right_cancel (hcount.trans hN)
  have hmul : q * L.card = q * (q + 1) := by
    calc
      q * L.card = L.card * q := Nat.mul_comm _ _
      _ = q ^ 2 + q := heq
      _ = q * (q + 1) := by simp only [pow_two, Nat.mul_add, Nat.mul_one]
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul

lemma nonincident_mixed_sets_bound (q N : ℕ)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (hA : A.Nonempty) (hB : B.Nonempty)
    (none : ∀ p ∈ A, ∀ l ∈ B, ¬ I p l) : A.card + B.card ≤ N - q := by
  exact nonincident_mixed_sets_bound_of_degrees I (by omega) hline
    (point_degree q N I hq hN hline hpair) hpair A B hA hB none

lemma mixed_vertex_cover_bound (q N : ℕ)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (S T : Finset (Fin N)) (hS : S ≠ Finset.univ) (hT : T ≠ Finset.univ)
    (cover : ∀ p l, I p l → p ∈ S ∨ l ∈ T) : N + q ≤ S.card + T.card := by
  classical
  let A := Finset.univ \ S
  let B := Finset.univ \ T
  have hA : A.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    exact hS (Finset.eq_univ_of_forall fun p => by
      by_contra hp
      have : p ∈ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hp⟩
      simpa [h] using this)
  have hB : B.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    exact hT (Finset.eq_univ_of_forall fun l => by
      by_contra hl
      have : l ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hl⟩
      simpa [h] using this)
  have none : ∀ p ∈ A, ∀ l ∈ B, ¬ I p l := by
    intro p hp l hl hi
    rcases cover p l hi with h | h
    · exact (Finset.mem_sdiff.mp hp).2 h
    · exact (Finset.mem_sdiff.mp hl).2 h
  have bound := nonincident_mixed_sets_bound q N I hq hN hline hpair A B hA hB none
  have hcA : A.card + S.card = N := by
    simpa [A] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  have hcB : B.card + T.card = N := by
    simpa [B] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hpos := Finset.card_pos.mpr hA
  omega

lemma vertex_cover_bound (q N : ℕ)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (S T : Finset (Fin N))
    (cover : ∀ p l, I p l → p ∈ S ∨ l ∈ T) : N ≤ S.card + T.card := by
  classical
  by_cases hS : S = Finset.univ
  · simp only [hS, Finset.card_univ, Fintype.card_fin]
    omega
  by_cases hT : T = Finset.univ
  · simp only [hT, Finset.card_univ, Fintype.card_fin]
    omega
  have h := mixed_vertex_cover_bound q N I hq hN hline hpair S T hS hT cover
  omega

lemma minimum_vertex_cover_pure (q N : ℕ)
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (S T : Finset (Fin N))
    (cover : ∀ p l, I p l → p ∈ S ∨ l ∈ T)
    (hsize : S.card + T.card = N) :
    (S = Finset.univ ∧ T = ∅) ∨ (S = ∅ ∧ T = Finset.univ) := by
  classical
  by_cases hS : S = Finset.univ
  · left
    refine ⟨hS, Finset.card_eq_zero.mp ?_⟩
    simpa only [hS, Finset.card_univ, Fintype.card_fin, Nat.add_eq_left] using hsize
  by_cases hT : T = Finset.univ
  · right
    refine ⟨Finset.card_eq_zero.mp ?_, hT⟩
    simpa only [hT, Finset.card_univ, Fintype.card_fin, Nat.add_eq_right] using hsize
  have h := mixed_vertex_cover_bound q N I hq hN hline hpair S T hS hT cover
  omega

end PEqualNP.Outside.L_meta_2583.Geometry

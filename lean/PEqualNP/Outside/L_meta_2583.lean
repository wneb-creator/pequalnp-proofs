import PEqualNP.Defs

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
      simp only [f, dif_pos hr]
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

end PEqualNP.Outside.L_meta_2583.Geometry


namespace PEqualNP.Outside.L_meta_2583.Deletion

lemma restricted_card_left (N d : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (P : Finset (Fin N))
    (hdegree : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = d) :
    ((Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).filter
      (fun e => e.1 ∈ P)).card = P.card * d := by
  classical
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  have hf (p : Fin N) : (E.filter (fun e => e.1 = p)).card =
      (Finset.univ.filter (fun l => I p l)).card := by
    apply Finset.card_bij (fun e _ => e.2)
    · intro e he
      have he' : I e.1 e.2 ∧ e.1 = p := by simpa [E] using he
      simpa [he'.2] using he'.1
    · intro e he e' he' heq
      have h : e.1 = p := (Finset.mem_filter.mp he).2
      have h' : e'.1 = p := (Finset.mem_filter.mp he').2
      exact Prod.ext (h.trans h'.symm) heq
    · intro l hl
      refine ⟨(p, l), ?_, rfl⟩
      simpa [E] using hl
  have hs := Finset.sum_card_fiberwise_eq_card_filter E P Prod.fst
  change (E.filter (fun e => e.1 ∈ P)).card = P.card * d
  rw [← hs]
  exact Finset.sum_const_nat (fun p _ => (hf p).trans (hdegree p))

lemma restricted_card_right (N d : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (L : Finset (Fin N))
    (hdegree : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = d) :
    ((Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).filter
      (fun e => e.2 ∈ L)).card = L.card * d := by
  classical
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  have hf (l : Fin N) : (E.filter (fun e => e.2 = l)).card =
      (Finset.univ.filter (fun p => I p l)).card := by
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      have he' : I e.1 e.2 ∧ e.2 = l := by simpa [E] using he
      simpa [he'.2] using he'.1
    · intro e he e' he' heq
      have h : e.2 = l := (Finset.mem_filter.mp he).2
      have h' : e'.2 = l := (Finset.mem_filter.mp he').2
      exact Prod.ext heq (h.trans h'.symm)
    · intro p hp
      refine ⟨(p, l), ?_, rfl⟩
      simpa [E] using hp
  have hs := Finset.sum_card_fiberwise_eq_card_filter E L Prod.snd
  change (E.filter (fun e => e.2 ∈ L)).card = L.card * d
  rw [← hs]
  exact Finset.sum_const_nat (fun l _ => (hf l).trans (hdegree l))

lemma cover_after_deletion_count (N d : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I]
    (hrow : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = d)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = d)
    (U : Finset (Fin N × Fin N)) (P L : Finset (Fin N))
    (hcover : ∀ p l, I p l → (p, l) ∉ U → p ∈ P ∨ l ∈ L) :
    N * d ≤ (P.card + L.card) * d + U.card := by
  classical
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  have hsub : E ⊆ (E.filter (fun e => e.1 ∈ P) ∪ E.filter (fun e => e.2 ∈ L)) ∪ U := by
    intro e he
    by_cases hu : e ∈ U
    · exact Finset.mem_union.mpr (Or.inr hu)
    apply Finset.mem_union.mpr
    apply Or.inl
    have hi : I e.1 e.2 := by simpa [E] using he
    rcases hcover e.1 e.2 hi hu with hp | hl
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨he, hp⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨he, hl⟩))
  have hcount := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hsplit := Finset.card_union_le (E.filter (fun e => e.1 ∈ P))
    (E.filter (fun e => e.2 ∈ L))
  have he : E.card = N * d := by
    simpa [E] using restricted_card_left N d I Finset.univ hrow
  have hp := restricted_card_left N d I P hrow
  have hl := restricted_card_right N d I L hcol
  change (E.filter (fun e => e.1 ∈ P)).card = P.card * d at hp
  change (E.filter (fun e => e.2 ∈ L)).card = L.card * d at hl
  rw [he] at hcount
  rw [hp, hl] at hsplit
  rw [Nat.add_mul]
  omega

lemma cover_after_deletion (N d : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hd : 0 < d)
    (hrow : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = d)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = d)
    (U : Finset (Fin N × Fin N)) (P L : Finset (Fin N))
    (hcover : ∀ p l, I p l → (p, l) ∉ U → p ∈ P ∨ l ∈ L) :
    N ≤ P.card + L.card + U.card / d := by
  have hc := cover_after_deletion_count N d I hrow hcol U P L hcover
  by_cases hsmall : N ≤ P.card + L.card
  · exact hsmall.trans (Nat.le_add_right _ _)
  have hmul : (N - (P.card + L.card)) * d ≤ U.card := by
    rw [Nat.sub_mul]
    omega
  have hdiv := (Nat.le_div_iff_mul_le hd).mpr hmul
  exact (Nat.sub_le_iff_le_add.mp hdiv).trans_eq (Nat.add_comm _ _)

end PEqualNP.Outside.L_meta_2583.Deletion

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

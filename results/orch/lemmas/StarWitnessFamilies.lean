import Mathlib

namespace PEqualNP.Outside.L_meta_4970

lemma right_stars_inter_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (haa' : a ≠ a') (Q Q' : Finset (Fin l))
    (hQ : ∀ b ∈ Q, (a, b) ∈ E) (hQ' : ∀ b ∈ Q', (a', b) ∈ E) :
    (Q ∩ Q').card ≤ 1 := by
  by_contra hlarge
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp (by omega : 1 < (Q ∩ Q').card)
  obtain ⟨hbQ, hbQ'⟩ := Finset.mem_inter.mp hb
  obtain ⟨hb'Q, hb'Q'⟩ := Finset.mem_inter.mp hb'
  exact hC4 a a' b b' haa' hbb' ⟨hQ b hbQ, hQ b' hb'Q, hQ' b hbQ', hQ' b' hb'Q'⟩

lemma left_stars_inter_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} (hbb' : b ≠ b') (P P' : Finset (Fin p))
    (hP : ∀ a ∈ P, (a, b) ∈ E) (hP' : ∀ a ∈ P', (a, b') ∈ E) :
    (P ∩ P').card ≤ 1 := by
  by_contra hlarge
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (by omega : 1 < (P ∩ P').card)
  obtain ⟨haP, haP'⟩ := Finset.mem_inter.mp ha
  obtain ⟨ha'P, ha'P'⟩ := Finset.mem_inter.mp ha'
  exact hC4 a a' b b' haa' hbb' ⟨hP a haP, hP' a haP', hP a' ha'P, hP' a' ha'P'⟩

def starLeafFamily {p l : ℕ} (Q : Fin p → Finset (Fin l))
    (P : Fin l → Finset (Fin p)) : Fin p ⊕ Fin l → Finset (Fin (p + l))
  | .inl a => (Q a).image (Fin.natAdd p)
  | .inr b => (P b).image (Fin.castAdd l)

lemma starLeafFamily_separated {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (Q : Fin p → Finset (Fin l)) (P : Fin l → Finset (Fin p))
    (hQ : ∀ a b, b ∈ Q a → (a, b) ∈ E)
    (hP : ∀ b a, a ∈ P b → (a, b) ∈ E) :
    ∀ c d, c ≠ d → (starLeafFamily Q P c ∩ starLeafFamily Q P d).card ≤ 1 := by
  have hinjR : Function.Injective (Fin.natAdd p : Fin l → Fin (p + l)) := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa using hv
  have hinjL : Function.Injective (Fin.castAdd l : Fin p → Fin (p + l)) := by
    intro a b h
    exact Fin.castAdd_inj.mp h
  have hcross : ∀ (a : Fin p) (b : Fin l),
      Disjoint ((Q a).image (Fin.natAdd p)) ((P b).image (Fin.castAdd l)) := by
    intro a b
    apply Finset.disjoint_left.mpr
    intro i hiR hiL
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hiR
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hiL
    have heq := congrArg Fin.val (hv.trans hu.symm)
    have huLt := u.isLt
    simp only [Fin.val_natAdd, Fin.val_castAdd] at heq
    omega
  intro c d hcd
  cases c with
  | inl a =>
    cases d with
    | inl a' =>
      change ((Q a).image (Fin.natAdd p) ∩ (Q a').image (Fin.natAdd p)).card ≤ 1
      rw [← Finset.image_inter _ _ hinjR, Finset.card_image_of_injective _ hinjR]
      exact right_stars_inter_card_le_one E hC4 (fun h => hcd (congrArg Sum.inl h))
        (Q a) (Q a') (hQ a) (hQ a')
    | inr b =>
      change ((Q a).image (Fin.natAdd p) ∩ (P b).image (Fin.castAdd l)).card ≤ 1
      rw [Finset.disjoint_iff_inter_eq_empty.mp (hcross a b)]
      simp
  | inr b =>
    cases d with
    | inl a =>
      change ((P b).image (Fin.castAdd l) ∩ (Q a).image (Fin.natAdd p)).card ≤ 1
      rw [Finset.disjoint_iff_inter_eq_empty.mp (hcross a b).symm]
      simp
    | inr b' =>
      change ((P b).image (Fin.castAdd l) ∩ (P b').image (Fin.castAdd l)).card ≤ 1
      rw [← Finset.image_inter _ _ hinjL, Finset.card_image_of_injective _ hinjL]
      exact left_stars_inter_card_le_one E hC4 (fun h => hcd (congrArg Sum.inr h))
        (P b) (P b') (hP b) (hP b')

lemma star_families_from_witnesses {p l : ℕ} (E : Finset (Fin p × Fin l))
    (J : Finset ℕ) (f : ℕ → (Fin (p + l) → Bool) → Bool)
    (hwitness : ∀ a b, (a, b) ∈ E →
      (∃ j ∈ J, ∃ Q : Finset (Fin l), 2 ≤ Q.card ∧ b ∈ Q ∧
        (∀ b' ∈ Q, (a, b') ∈ E) ∧
        ∀ x, f j x = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨
      (∃ j ∈ J, ∃ P : Finset (Fin p), 2 ≤ P.card ∧ a ∈ P ∧
        (∀ a' ∈ P, (a', b) ∈ E) ∧
        ∀ x, f j x = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) :
    ∃ (Q : Fin p → Finset (Fin l)) (P : Fin l → Finset (Fin p))
      (F : Fin p ⊕ Fin l → Finset ℕ),
      (∀ a b, b ∈ Q a → (a, b) ∈ E) ∧
      (∀ b a, a ∈ P b → (a, b) ∈ E) ∧
      (∀ a b, (a, b) ∈ E → b ∈ Q a ∨ a ∈ P b) ∧
      (∀ c, F c ⊆ J) ∧
      (∀ c j, j ∈ F c →
        f j (fun u => decide (u ∉ starLeafFamily Q P c)) = false) ∧
      (∀ c u, u ∈ starLeafFamily Q P c →
        ∃ j ∈ F c, f j (fun v => decide (v = u)) = true) := by
  classical
  let R := fun a : Fin p => J.filter fun j =>
    ∃ Q : Finset (Fin l), 2 ≤ Q.card ∧ (∀ b ∈ Q, (a, b) ∈ E) ∧
      ∀ x, f j x = decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)
  let L := fun b : Fin l => J.filter fun j =>
    ∃ P : Finset (Fin p), 2 ≤ P.card ∧ (∀ a ∈ P, (a, b) ∈ E) ∧
      ∀ x, f j x = decide (∃ a ∈ P, x (Fin.castAdd l a) = true)
  let Q := fun a : Fin p => Finset.univ.filter fun b : Fin l =>
    ∃ j ∈ R a, f j (fun v => decide (v = Fin.natAdd p b)) = true
  let P := fun b : Fin l => Finset.univ.filter fun a : Fin p =>
    ∃ j ∈ L b, f j (fun v => decide (v = Fin.castAdd l a)) = true
  let F : Fin p ⊕ Fin l → Finset ℕ := Sum.elim R L
  have hQa : ∀ a b, b ∈ Q a → (a, b) ∈ E := by
    intro a b hb
    obtain ⟨j, hj, hjb⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨Qj, _, hQj, hfun⟩ := (Finset.mem_filter.mp hj).2
    have hbQ : b ∈ Qj := by
      have ht := (hfun _).symm.trans hjb
      simpa using ht
    exact hQj b hbQ
  have hPb : ∀ b a, a ∈ P b → (a, b) ∈ E := by
    intro b a ha
    obtain ⟨j, hj, hja⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨Pj, _, hPj, hfun⟩ := (Finset.mem_filter.mp hj).2
    have haP : a ∈ Pj := by
      have ht := (hfun _).symm.trans hja
      simpa using ht
    exact hPj a haP
  refine ⟨Q, P, F, hQa, hPb, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    rcases hwitness a b hab with ⟨j, hj, Qj, hcard, hb, hadj, hfun⟩ |
      ⟨j, hj, Pj, hcard, ha, hadj, hfun⟩
    · apply Or.inl
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hj, Qj, hcard, hadj, hfun⟩
      · rw [hfun]
        simpa using hb
    · apply Or.inr
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hj, Pj, hcard, hadj, hfun⟩
      · rw [hfun]
        simpa using ha
  · intro c j hj
    cases c <;> exact (Finset.mem_filter.mp hj).1
  · intro c j hj
    cases c with
    | inl a =>
      obtain ⟨Qj, _, _, hfun⟩ := (Finset.mem_filter.mp hj).2
      rw [hfun]
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨b, hb, hnot⟩ := of_decide_eq_true ht
      have hbQ : b ∈ Q a := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, ?_⟩
        rw [hfun]
        simpa using hb
      exact (of_decide_eq_true hnot) (Finset.mem_image.mpr ⟨b, hbQ, rfl⟩)
    | inr b =>
      obtain ⟨Pj, _, _, hfun⟩ := (Finset.mem_filter.mp hj).2
      rw [hfun]
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨a, ha, hnot⟩ := of_decide_eq_true ht
      have haP : a ∈ P b := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, ?_⟩
        rw [hfun]
        simpa using ha
      exact (of_decide_eq_true hnot) (Finset.mem_image.mpr ⟨a, haP, rfl⟩)
  · intro c u hu
    cases c with
    | inl a =>
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp hb).2
    | inr b =>
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp ha).2

end PEqualNP.Outside.L_meta_4970

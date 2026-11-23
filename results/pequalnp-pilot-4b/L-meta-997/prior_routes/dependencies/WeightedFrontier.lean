import Mathlib

namespace PEqualNP.Outside.L_meta_997.WeightedFrontier

variable {α : Type*} [DecidableEq α]

lemma paid_succ (A : Finset ℕ) (t : ℕ) :
    (A.filter (fun w => w < t + 1)).card =
      (A.filter (fun w => w < t)).card + (if t ∈ A then 1 else 0) := by
  by_cases ht : t ∈ A
  · have he : A.filter (fun w => w < t + 1) = insert t (A.filter (fun w => w < t)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hwA, hw⟩
        by_cases hwt : w = t
        · exact Or.inl hwt
        · exact Or.inr ⟨hwA, by omega⟩
      · rintro (rfl | ⟨hwA, hw⟩)
        · exact ⟨ht, by omega⟩
        · exact ⟨hwA, by omega⟩
    rw [he]
    simp [ht]
  · have he : A.filter (fun w => w < t + 1) = A.filter (fun w => w < t) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hwA, hw⟩
        have hwt : w ≠ t := by rintro rfl; exact ht hwA
        exact ⟨hwA, by omega⟩
      · rintro ⟨hwA, hw⟩
        exact ⟨hwA, by omega⟩
    rw [he]
    simp [ht]

theorem frontier_cut
    (Sup : ℕ → Finset α) (Good : ℕ → Prop) (A : Finset ℕ)
    (step : ∀ w, Good w → 2 ≤ (Sup w).card →
      ∃ P : Finset ℕ,
        P.card ≤ 1 + (if w ∈ A then 1 else 0) ∧
        (∀ r ∈ P, r < w ∧ Good r) ∧ Sup w ⊆ P.biUnion Sup) :
    ∀ t (F : Finset ℕ),
      (∀ w ∈ F, Good w) →
      (∀ w ∈ F, 2 ≤ (Sup w).card → w < t) →
      ∃ B : Finset ℕ,
        (∀ w ∈ B, Good w) ∧ (∀ w ∈ B, (Sup w).card ≤ 1) ∧
        F.biUnion Sup ⊆ B.biUnion Sup ∧
        B.card ≤ F.card + (A.filter (fun w => w < t)).card := by
  intro t
  induction t with
  | zero =>
    intro F hgood hbound
    refine ⟨F, hgood, ?_, Finset.Subset.refl _, ?_⟩
    · intro w hw
      by_contra! hlarge
      have := hbound w hw (by omega)
      omega
    · simp
  | succ t ih =>
    intro F hgood hbound
    by_cases htF : t ∈ F
    · by_cases htlarge : 2 ≤ (Sup t).card
      · obtain ⟨P, hPcard, hPgood, hPcover⟩ := step t (hgood t htF) htlarge
        let F' := F.erase t ∪ P
        have hgood' : ∀ w ∈ F', Good w := by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hgood w (Finset.mem_of_mem_erase hw)
          · exact (hPgood w hw).2
        have hbound' : ∀ w ∈ F', 2 ≤ (Sup w).card → w < t := by
          intro w hw hlarge
          rcases Finset.mem_union.mp hw with hw | hw
          · have hwF := Finset.mem_of_mem_erase hw
            have hne := (Finset.mem_erase.mp hw).1
            have hb := hbound w hwF hlarge
            omega
          · exact (hPgood w hw).1
        obtain ⟨B, hBg, hBs, hBcover, hBcard⟩ := ih F' hgood' hbound'
        refine ⟨B, hBg, hBs, ?_, ?_⟩
        · apply Finset.Subset.trans ?_ hBcover
          intro a ha
          obtain ⟨w, hw, ha⟩ := Finset.mem_biUnion.mp ha
          by_cases hwt : w = t
          · subst w
            obtain ⟨r, hr, har⟩ := Finset.mem_biUnion.mp (hPcover ha)
            exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, har⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwt, hw⟩), ha⟩
        · have hFcard : F'.card ≤ (F.erase t).card + P.card := Finset.card_union_le _ _
          have herase := Finset.card_erase_add_one htF
          have hpaid := paid_succ A t
          change B.card ≤ F.card + (A.filter (fun w => w < t + 1)).card
          omega
      · have hbound' : ∀ w ∈ F, 2 ≤ (Sup w).card → w < t := by
          intro w hw hlarge
          have hne : w ≠ t := by rintro rfl; exact htlarge hlarge
          have hb := hbound w hw hlarge
          omega
        obtain ⟨B, hBg, hBs, hBc, hBcard⟩ := ih F hgood hbound'
        refine ⟨B, hBg, hBs, hBc, ?_⟩
        have hpaid := paid_succ A t
        change B.card ≤ F.card + (A.filter (fun w => w < t + 1)).card
        omega
    · have hbound' : ∀ w ∈ F, 2 ≤ (Sup w).card → w < t := by
        intro w hw hlarge
        have hne : w ≠ t := by rintro rfl; exact htF hw
        have hb := hbound w hw hlarge
        omega
      obtain ⟨B, hBg, hBs, hBc, hBcard⟩ := ih F hgood hbound'
      refine ⟨B, hBg, hBs, hBc, ?_⟩
      have hpaid := paid_succ A t
      change B.card ≤ F.card + (A.filter (fun w => w < t + 1)).card
      omega

theorem support_card_le_paid_add_one
    (Sup : ℕ → Finset α) (Good : ℕ → Prop) (A : Finset ℕ)
    (step : ∀ w, Good w → 2 ≤ (Sup w).card →
      ∃ P : Finset ℕ,
        P.card ≤ 1 + (if w ∈ A then 1 else 0) ∧
        (∀ r ∈ P, r < w ∧ Good r) ∧ Sup w ⊆ P.biUnion Sup)
    (o : ℕ) (ho : Good o) : (Sup o).card ≤ A.card + 1 := by
  obtain ⟨B, _, hsmall, hcover, hcard⟩ := frontier_cut Sup Good A step (o + 1) {o}
    (by intro w hw; simpa using (Finset.mem_singleton.mp hw) ▸ ho)
    (by intro w hw _; simp only [Finset.mem_singleton] at hw; omega)
  have hcov : Sup o ⊆ B.biUnion Sup := by simpa using hcover
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_biUnion_le_card_mul B Sup 1 hsmall
  have h3 := Finset.card_filter_le A (fun w => w < o + 1)
  simp only [Finset.card_singleton] at hcard
  simp only [mul_one] at h2
  omega

end PEqualNP.Outside.L_meta_997.WeightedFrontier

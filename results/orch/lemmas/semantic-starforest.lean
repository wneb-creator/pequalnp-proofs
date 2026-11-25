import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.SemanticStarForest

lemma point_ne_line {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have := a.isLt
  omega

lemma star_forest_cover {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hstar : ∀ a b, (a, b) ∈ E →
      (∀ b', (a, b') ∈ E → b' = b) ∨ (∀ a', (a', b) ∈ E → a' = a)) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card = ((E.image fun e => Fin.castAdd l e.1) ∪
        (E.image fun e => Fin.natAdd p e.2)).card := by
  classical
  let U : Fin p → Prop := fun a => ∀ b b', (a, b) ∈ E → (a, b') ∈ E → b = b'
  let leaf : Fin p × Fin l → Fin (p + l) := fun e =>
    if U e.1 then Fin.castAdd l e.1 else Fin.natAdd p e.2
  let center : Fin p × Fin l → Fin (p + l) := fun e =>
    if U e.1 then Fin.natAdd p e.2 else Fin.castAdd l e.1
  have hu {a : Fin p} {b : Fin l} (hab : (a, b) ∈ E) (ha : ¬ U a) :
      ∀ a', (a', b) ∈ E → a' = a := by
    rcases hstar a b hab with hp | hl
    · exact False.elim (ha (fun b1 b2 hb1 hb2 => (hp b1 hb1).trans (hp b2 hb2).symm))
    · exact hl
  have hlinj : Set.InjOn leaf (E : Set (Fin p × Fin l)) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
    by_cases ha : U a <;> by_cases hc : U c
    · simp only [leaf, if_pos ha, if_pos hc] at h
      have hac : a = c := Fin.ext (congrArg (fun i : Fin (p + l) => i.val) h)
      subst c
      exact Prod.ext rfl (ha b d hab hcd)
    · simp only [leaf, if_pos ha, if_neg hc] at h
      exact False.elim (point_ne_line a d h)
    · simp only [leaf, if_neg ha, if_pos hc] at h
      exact False.elim (point_ne_line c b h.symm)
    · simp only [leaf, if_neg ha, if_neg hc] at h
      have hbd : b = d := by
        apply Fin.ext
        have hv := congrArg (fun i : Fin (p + l) => i.val) h
        simpa using hv
      subst d
      exact Prod.ext (hu hab ha c hcd).symm rfl
  have hdisj : Disjoint (E.image leaf) (E.image center) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨⟨a, b⟩, hab, habv⟩ := Finset.mem_image.mp hv
    obtain ⟨⟨c, d⟩, hcd, hcdv⟩ := Finset.mem_image.mp hw
    have h : leaf (a, b) = center (c, d) := habv.trans hcdv.symm
    by_cases ha : U a <;> by_cases hc : U c
    · simp only [leaf, center, if_pos ha, if_pos hc] at h
      exact point_ne_line a d h
    · simp only [leaf, center, if_pos ha, if_neg hc] at h
      have hac : a = c := Fin.ext (congrArg (fun i : Fin (p + l) => i.val) h)
      exact hc (hac ▸ ha)
    · simp only [leaf, center, if_neg ha, if_pos hc] at h
      have hbd : b = d := by
        apply Fin.ext
        have hv := congrArg (fun i : Fin (p + l) => i.val) h
        simpa using hv
      subst d
      have hca := hu hab ha c hcd
      exact ha (hca ▸ hc)
    · simp only [leaf, center, if_neg ha, if_neg hc] at h
      exact point_ne_line c b h.symm
  have hunion : (E.image leaf) ∪ (E.image center) =
      (E.image fun e => Fin.castAdd l e.1) ∪ (E.image fun e => Fin.natAdd p e.2) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
      · by_cases hu' : U e.1
        · exact Or.inl ⟨e, he, by simp [leaf, hu']⟩
        · exact Or.inr ⟨e, he, by simp [leaf, hu']⟩
      · by_cases hu' : U e.1
        · exact Or.inr ⟨e, he, by simp [center, hu']⟩
        · exact Or.inl ⟨e, he, by simp [center, hu']⟩
    · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
      · by_cases hu' : U e.1
        · exact Or.inl ⟨e, he, by simp [leaf, hu']⟩
        · exact Or.inr ⟨e, he, by simp [center, hu']⟩
      · by_cases hu' : U e.1
        · exact Or.inr ⟨e, he, by simp [center, hu']⟩
        · exact Or.inl ⟨e, he, by simp [leaf, hu']⟩
  refine ⟨E.image center, ?_, ?_⟩
  · intro a b hab
    by_cases ha : U a
    · right
      exact Finset.mem_image.mpr ⟨(a, b), hab, by simp [center, ha]⟩
    · left
      exact Finset.mem_image.mpr ⟨(a, b), hab, by simp [center, ha]⟩
  · rw [← hunion, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_iff.mpr hlinj]

end PEqualNP.Outside.L_meta_4675.SemanticStarForest

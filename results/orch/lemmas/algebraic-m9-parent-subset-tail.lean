def equality_mask_parent (Q : Finset (Fin 7) → Prop) (T : Finset (Fin 7)) : Prop :=
  (∃ A, Q A ∧ A.card = 2 ∧ A ⊆ T) ∨
    (∃ A, Q A ∧ A.card = 4 ∧ T ⊆ A) ∨
    (∃ A B, A ≠ B ∧ Q A ∧ Q B ∧ A.card = 5 ∧ B.card = 5 ∧
      T ⊆ A ∧ T ⊆ B ∧ A ∩ B = T)

theorem equality_occurring_parent_pull_subset {D : Dag} (hS : Strict 14 D)
    (f : Fin 7 → Fin 14) (injective : Function.Injective f) (P R : Finset (Fin 14)) (subrange : P ⊆ R)
    (range : Finset.univ.image f = R) (T : Finset (Fin 7)) (hT : T.card = 3)
    (occur : sup_Occ 14 D P (T.image f)) :
    equality_mask_parent (fun M => sup_Occ 14 D P (M.image f)) T := by
  classical
  have p7 : P.card ≤ 7 := by
    have bound := Finset.card_le_card subrange
    rw [← range,Finset.card_image_of_injective _ injective] at bound
    simpa only [Finset.card_univ,Fintype.card_fin] using bound
  have imageCard : (T.image f).card = 3 := by
    rw [Finset.card_image_of_injective _ injective]
    exact hT
  have back (A : Finset (Fin 14)) (hA : sup_Occ 14 D P A) :
      (equality_mask_pull f A).image f = A :=
    equality_mask_pull_image f R range (fun x hx => subrange (sup_occ_sub hA hx))
  have card (A : Finset (Fin 14)) (hA : sup_Occ 14 D P A) :
      (equality_mask_pull f A).card = A.card := by
    rw [← Finset.card_image_of_injective _ injective,back A hA]
  rcases sup_triple_parent hS p7 imageCard occur with
    ⟨A,hA,ca,sa⟩ | ⟨A,hA,ca,sa⟩ | ⟨A,B,ne,hA,hB,ca,cb,_,_,inter⟩
  · refine Or.inl ⟨equality_mask_pull f A,?_,?_,?_⟩
    · change sup_Occ 14 D P ((equality_mask_pull f A).image f)
      rwa [back A hA]
    · rw [card A hA,ca]
    · apply (Finset.image_subset_image_iff injective).1
      rwa [back A hA]
  · refine Or.inr (Or.inl ⟨equality_mask_pull f A,?_,?_,?_⟩)
    · change sup_Occ 14 D P ((equality_mask_pull f A).image f)
      rwa [back A hA]
    · rw [card A hA,ca]
    · apply (Finset.image_subset_image_iff injective).1
      rwa [back A hA]
  · have eq : equality_mask_pull f A ∩ equality_mask_pull f B = T := by
      apply Finset.image_injective injective
      rw [Finset.image_inter _ _ injective,back A hA,back B hB,inter]
    refine Or.inr (Or.inr ⟨equality_mask_pull f A,equality_mask_pull f B,?_,?_,?_,?_,?_,?_,?_,eq⟩)
    · intro same
      apply ne
      rw [← back A hA,← back B hB,same]
    · change sup_Occ 14 D P ((equality_mask_pull f A).image f)
      rwa [back A hA]
    · change sup_Occ 14 D P ((equality_mask_pull f B).image f)
      rwa [back B hB]
    · rw [card A hA,ca]
    · rw [card B hB,cb]
    · rw [← eq]
      exact Finset.inter_subset_left
    · rw [← eq]
      exact Finset.inter_subset_right

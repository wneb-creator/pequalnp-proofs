namespace PEqualNP.Outside.L_meta_6659_aux

lemma q2f_pull_union (f : Fin 7 → Fin 14) (A B : Finset (Fin 14)) :
    equality_mask_pull f (A ∪ B) = equality_mask_pull f A ∪ equality_mask_pull f B := by
  classical
  ext i
  simp only [equality_mask_pull, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union]

lemma q2f_pull_inter (f : Fin 7 → Fin 14) (A B : Finset (Fin 14)) :
    equality_mask_pull f (A ∩ B) = equality_mask_pull f A ∩ equality_mask_pull f B := by
  classical
  ext i
  simp only [equality_mask_pull, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter]

lemma q2f_pull_image (f : Fin 7 → Fin 14) (inj : Function.Injective f)
    (A : Finset (Fin 7)) : equality_mask_pull f (A.image f) = A := by
  classical
  ext i
  simp only [equality_mask_pull, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨j,hj,eq⟩
    exact inj eq ▸ hj
  · intro hi
    exact ⟨i,hi,rfl⟩

lemma q2f_actual_closed {D : Dag} (hS : Strict 14 D)
    (f : Fin 7 → Fin 14) (inj : Function.Injective f)
    (P : Finset (Fin 14)) (range : Finset.univ.image f = P)
    (s : Fin 15) (a b c : Fin 10) (gen : q2f_generators s a b c = true)
    (allowed : ∀ w, q2f_allowed s a b c
      (cap7_encode (equality_mask_pull f (supp 14 D w ∩ P))) = true) :
    ∀ w, q2f_closed s a b c
      (cap7_encode (equality_mask_pull f (supp 14 D w ∩ P))) = true := by
  classical
  apply support_mask_closed hS P
    (fun M => q2f_allowed s a b c (cap7_encode (equality_mask_pull f M)) = true)
    (fun M => q2f_closed s a b c (cap7_encode (equality_mask_pull f M)) = true)
    allowed
  · simpa only [equality_mask_pull, Finset.notMem_empty, Finset.filter_false] using
      q2f_closed_empty s a b c
  · intro i hi
    have member : i ∈ Finset.univ.image f := by rwa [range]
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp member
    have single : equality_mask_pull f {f j} = {j} := by
      simpa only [Finset.image_singleton] using q2f_pull_image f inj {j}
    rw [single]
    exact q2f_closed_singleton s a b c j
  · intro A B ha hb hab
    rw [q2f_pull_union] at hab ⊢
    exact q2f_finset_union s a b c gen _ _ ha hb hab
  · intro A B ha hb hab
    rw [q2f_pull_inter] at hab ⊢
    exact q2f_finset_inter s a b c gen _ _ ha hb hab

lemma q2f_occurring_shape {D : Dag} (hS : Strict 14 D)
    (f : Fin 7 → Fin 14) (inj : Function.Injective f)
    (P : Finset (Fin 14)) (range : Finset.univ.image f = P)
    (s : Fin 15) (a b c : Fin 10) (cert : q2f_certificate s a b c = true)
    (bound : (q2f_codes s a b c).card ≤ 7)
    (occurs : ∀ m ∈ q2f_codes s a b c, sup_Occ 14 D P ((cap7_decode m).image f))
    (allowed : ∀ w, q2f_allowed s a b c
      (cap7_encode (equality_mask_pull f (supp 14 D w ∩ P))) = true) :
    q2f_shape s a b c = true := by
  apply q2f_certificate_shape s a b c cert bound
  intro gen m hm
  obtain ⟨w,hw⟩ := occurs m hm
  have closed := q2f_actual_closed hS f inj P range s a b c gen allowed w
  rw [hw, q2f_pull_image f inj, cap7_encode_decode] at closed
  exact closed

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_2962.SharedP4
open Finset
variable {ι V : Type} [DecidableEq ι] [DecidableEq V]

lemma and_cover (T : Finset ι) (x y z w : ι → V) :
    ∃ S : Finset V, (∀ e ∈ E T x y z w, ∃ v ∈ S, v ∈ e) ∧
      S.card ≤ (T.image (A x y)).card + (T.image (O x y z w)).card := by
  classical
  let pick : Sym2 V → V := fun a => a.out.1
  let S := (T.image (A x y)).image pick ∪ T.image z
  have hz (t : ι) (ht : t ∈ T) : z t ∈ S := mem_union_right _ (mem_image.mpr ⟨t,ht,rfl⟩)
  refine ⟨S, ?_, ?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · obtain ⟨t,ht,rfl⟩ := mem_image.mp he
        refine ⟨pick (A x y t), mem_union_left _ (mem_image.mpr ⟨A x y t,mem_image.mpr ⟨t,ht,rfl⟩,rfl⟩), ?_⟩
        exact Sym2.out_fst_mem _
      · obtain ⟨t,ht,rfl⟩ := mem_image.mp he
        exact ⟨z t,hz t ht,by simp⟩
    · obtain ⟨t,ht,rfl⟩ := mem_image.mp he
      exact ⟨z t,hz t ht,by simp⟩
  · have hp : ((T.image (A x y)).image pick).card ≤ (T.image (A x y)).card := card_image_le
    have hzcard := image_factor_card T (O x y z w) z (by
      intro t ht r hr he
      exact congrArg (fun a => a.1.2) he)
    exact (card_union_le _ _).trans (Nat.add_le_add hp hzcard)

lemma or_edge_bound (T : Finset ι) (x y z w : ι → V) (col : V → Bool)
    (hc : ∀ t ∈ T, col (x t) = col (z t) ∧ col (y t) ≠ col (z t))
    (hz : ∀ t ∈ T, ∀ r ∈ T, C y w t = C y w r → z t = z r) :
    (E T x y z w).card ≤ (T.image (B x y z)).card + (T.image (C y w)).card +
      (T.image (O x y z w)).card := by
  classical
  let E2 := T.image (fun t => s(y t,z t))
  let I := T.filter fun t => s(z t,w t) ∉ E2
  have hi : (I.image (fun t => s(z t,w t))).card ≤ (T.image (C y w)).card := by
    have h := image_factor_card I (C y w) (fun t => s(z t,w t)) (by
      intro t ht r hr he
      have htT := (mem_filter.mp ht).1
      have hrT := (mem_filter.mp hr).1
      have hzz := hz t htT r hrT he
      rcases Sym2.eq_iff.mp he with hh | hh
      · rw [hzz,hh.2]
      · exfalso
        apply (mem_filter.mp ht).2
        exact mem_image.mpr ⟨r,hrT,by rw [hzz,hh.2]; exact Sym2.eq_swap⟩)
    exact h.trans (card_le_card (image_subset_image (filter_subset _ _)))
  have hmid := image_factor_card T (B x y z) (fun t => s(y t,z t)) (by
    intro t ht r hr he
    obtain ⟨hy,hzz⟩ := middle_unique T x y z col hc ht hr he
    rw [hy,hzz])
  have ha := image_factor_card T (O x y z w) (A x y) (by
    intro t ht r hr he
    exact congrArg (fun a => a.1.1) he)
  have hsub : E T x y z w ⊆ (T.image (A x y) ∪ E2) ∪ I.image (fun t => s(z t,w t)) := by
    intro e he
    rcases mem_union.mp he with he | he
    · exact mem_union_left _ he
    · obtain ⟨t,ht,rfl⟩ := mem_image.mp he
      by_cases hm : s(z t,w t) ∈ E2
      · exact mem_union_left _ (mem_union_right _ hm)
      · exact mem_union_right _ (mem_image.mpr ⟨t,mem_filter.mpr ⟨ht,hm⟩,rfl⟩)
  have hcard := card_le_card hsub
  have h1 := card_union_le (T.image (A x y)) E2
  have h2 := card_union_le (T.image (A x y) ∪ E2) (I.image (fun t => s(z t,w t)))
  change E2.card ≤ (T.image (B x y z)).card at hmid
  omega

lemma common_center_of_no_four {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (T : Finset ι) (y z w : ι → Fin n)
    (hp : ∀ t ∈ T, y t ≠ w t ∧ G.Adj (y t) (z t) ∧ G.Adj (w t) (z t)) :
    ∀ t ∈ T, ∀ r ∈ T, C y w t = C y w r → z t = z r := by
  intro t ht r hr he
  have hz1 : z t ∈ Finset.univ.filter (fun a => G.Adj (y t) a ∧ G.Adj (w t) a) :=
    by simp [hp t ht]
  have hz2 : z r ∈ Finset.univ.filter (fun a => G.Adj (y t) a ∧ G.Adj (w t) a) := by
    rcases Sym2.eq_iff.mp he with hh | hh
    · simp [hh.1,hh.2,hp r hr]
    · simp [hh.1,hh.2,hp r hr]
  exact Finset.card_le_one.mp (h4 (y t) (w t) (hp t ht).1) _ hz1 _ hz2

lemma path_identity (a b c d : Bool) :
    (((a && b) || c) && (b || d)) = ((a && b) || (b && c) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
end PEqualNP.Outside.L_meta_2962.SharedP4

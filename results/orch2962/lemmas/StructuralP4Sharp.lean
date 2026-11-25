import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2962.SharedP4
open Finset

lemma image_factor_card {α β γ : Type} [DecidableEq β] [DecidableEq γ]
    (T : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ T, ∀ b ∈ T, f a = f b → g a = g b) :
    (T.image g).card ≤ (T.image f).card := by
  classical
  have reps : ∀ c : ↥(T.image g), ∃ a ∈ T, g a = c.val := by
    intro c
    exact Finset.mem_image.mp c.property
  choose r hr he using reps
  let F : ↥(T.image g) → ↥(T.image f) := fun c => ⟨f (r c), mem_image.mpr ⟨r c,hr c,rfl⟩⟩
  apply Finset.card_le_card_of_injective (f := F)
  intro c d hd
  apply Subtype.ext
  rw [← he c, ← he d]
  exact h (r c) (hr c) (r d) (hr d) (congrArg Subtype.val hd)

variable {ι V : Type} [DecidableEq ι] [DecidableEq V]
def A (x y : ι → V) (t : ι) : Sym2 V := s(x t,y t)
def B (x y z : ι → V) (t : ι) : Sym2 V × V := (A x y t,z t)
def C (y w : ι → V) (t : ι) : Sym2 V := s(y t,w t)
def O (x y z w : ι → V) (t : ι) : (Sym2 V × V) × Sym2 V := (B x y z t,C y w t)
def E (T : Finset ι) (x y z w : ι → V) : Finset (Sym2 V) :=
  (T.image (fun t => s(x t,y t)) ∪ T.image (fun t => s(y t,z t))) ∪
    T.image (fun t => s(z t,w t))

lemma middle_unique (T : Finset ι) (x y z : ι → V) (col : V → Bool)
    (hc : ∀ t ∈ T, col (x t) = col (z t) ∧ col (y t) ≠ col (z t))
    {t r : ι} (ht : t ∈ T) (hr : r ∈ T) (he : B x y z t = B x y z r) :
    y t = y r ∧ z t = z r := by
  have ha : s(x t,y t) = s(x r,y r) := congrArg Prod.fst he
  have hz : z t = z r := congrArg Prod.snd he
  refine ⟨?_,hz⟩
  rcases Sym2.eq_iff.mp ha with ha | ha
  · exact ha.2
  · apply False.elim
    apply (hc t ht).2
    calc
      col (y t) = col (x r) := congrArg col ha.2
      _ = col (z r) := (hc r hr).1
      _ = col (z t) := congrArg col hz.symm

lemma final_unique (T : Finset ι) (x y z w : ι → V) (col : V → Bool)
    (hc : ∀ t ∈ T, col (x t) = col (z t) ∧ col (y t) ≠ col (z t))
    {t r : ι} (ht : t ∈ T) (hr : r ∈ T) (he : O x y z w t = O x y z w r) :
    z t = z r ∧ w t = w r := by
  obtain ⟨hy,hz⟩ := middle_unique T x y z col hc ht hr (congrArg Prod.fst he)
  have hw : s(y t,w t) = s(y r,w r) := congrArg Prod.snd he
  refine ⟨hz,?_⟩
  rcases Sym2.eq_iff.mp hw with hw | hw
  · exact hw.2
  · exact hw.2.trans (hy.symm.trans hw.1)

lemma edges_bound (T : Finset ι) (x y z w : ι → V) (col : V → Bool)
    (hc : ∀ t ∈ T, col (x t) = col (z t) ∧ col (y t) ≠ col (z t)) :
    (E T x y z w).card ≤ (T.image (A x y)).card + (T.image (B x y z)).card +
      (T.image (O x y z w)).card := by
  have hmid := image_factor_card T (B x y z) (fun t => s(y t,z t)) (by
    intro t ht r hr he
    obtain ⟨hy,hz⟩ := middle_unique T x y z col hc ht hr he
    rw [hy,hz])
  have hlast := image_factor_card T (O x y z w) (fun t => s(z t,w t)) (by
    intro t ht r hr he
    obtain ⟨hz,hw⟩ := final_unique T x y z w col hc ht hr he
    rw [hz,hw])
  have hfirst := card_union_le (T.image (fun t => s(x t,y t))) (T.image (fun t => s(y t,z t)))
  have hsecond := card_union_le (T.image (fun t => s(x t,y t)) ∪ T.image (fun t => s(y t,z t)))
    (T.image (fun t => s(z t,w t)))
  change _ ≤ (T.image (fun t => s(x t,y t))).card + _ + _
  unfold E
  omega

lemma shared_family_cover (T : Finset ι) (x y z w : ι → V) (col : V → Bool)
    (hc : ∀ t ∈ T, col (x t) = col (z t) ∧ col (y t) ≠ col (z t)) :
    ∃ S : Finset V, (∀ e ∈ E T x y z w, ∃ v ∈ S, v ∈ e) ∧
      (E T x y z w).card + S.card ≤
        (T.image (A x y)).card + (T.image (B x y z)).card + (T.image (C y w)).card +
          2 * (T.image (O x y z w)).card := by
  classical
  let S := (T.image (C y w)).biUnion Sym2.toFinset
  have hys (t : ι) (ht : t ∈ T) : y t ∈ S := by
    apply mem_biUnion.mpr
    exact ⟨C y w t,mem_image.mpr ⟨t,ht,rfl⟩,by simp [C,Sym2.toFinset_mk_eq]⟩
  have hws (t : ι) (ht : t ∈ T) : w t ∈ S := by
    apply mem_biUnion.mpr
    exact ⟨C y w t,mem_image.mpr ⟨t,ht,rfl⟩,by simp [C,Sym2.toFinset_mk_eq]⟩
  refine ⟨S,?_,?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · rcases mem_union.mp he with he | he
      · obtain ⟨t,ht,rfl⟩ := mem_image.mp he
        exact ⟨y t,hys t ht,by simp⟩
      · obtain ⟨t,ht,rfl⟩ := mem_image.mp he
        exact ⟨y t,hys t ht,by simp⟩
    · obtain ⟨t,ht,rfl⟩ := mem_image.mp he
      exact ⟨w t,hws t ht,by simp⟩
  · have hs : S.card ≤ 2 * (T.image (C y w)).card := by
      have h := card_biUnion_le_card_mul (T.image (C y w)) Sym2.toFinset 2 (by
        intro a ha
        rw [Sym2.card_toFinset]
        split_ifs <;> omega)
      simpa [S,Nat.mul_comm] using h
    have hco := image_factor_card T (O x y z w) (C y w) (by
      intro t ht r hr he
      exact congrArg Prod.snd he)
    have he := edges_bound T x y z w col hc
    omega
end PEqualNP.Outside.L_meta_2962.SharedP4
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

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.GuardedReuseOverlap

lemma package_reused_stars_overlap {n : ℕ} (G : SimpleGraph (Fin n))
    (r t : Fin n) (hrt : r ≠ t) (X Y S : Finset (Fin n))
    (hrS : r ∉ S)
    (hX : ∀ x ∈ X, G.Adj r x) (hY : ∀ y ∈ Y, G.Adj t y)
    (hS : ∀ v ∈ S, G.Adj r v) {E : Finset (Sym2 (Fin n))}
    (hcov : E ⊆ X.image (fun x => s(r,x)) ∪ Y.image (fun y => s(t,y)) ∪
      S.image (fun v => s(r,v))) :
    ∃ (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n)), S ⊆ Z ∧
      (∀ v ∈ Z, (L v).Nonempty) ∧ (∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u) ∧
      (∀ e ∈ E, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) ∧
      (∑ v ∈ Z, (L v).card) + (Z \ S).card ≤ X.card+Y.card+S.card+2 ∧
      (∀ v ∈ S, L v = if v=t then insert r Y else {r}) ∧
      (t ∈ S → (Z \ S).card ≤ 1) := by
  classical
  let core : Fin n → Finset (Fin n) := fun v => if v=r then X else if v=t then Y else ∅
  let K := ({r,t} : Finset (Fin n)).filter (fun v => v ∉ S ∧ (core v).Nonempty)
  let Z := K ∪ S
  let L : Fin n → Finset (Fin n) :=
    fun v => if v ∈ S then if v=t then insert r Y else {r} else core v
  have hKsub : K ⊆ ({r,t} : Finset (Fin n)) := Finset.filter_subset _ _
  have hKS : Disjoint K S := by
    apply Finset.disjoint_left.mpr
    intro v hv hvS
    exact (Finset.mem_filter.mp hv).2.1 hvS
  have hLcore : ∀ v ∈ K, L v = core v := by
    intro v hv
    exact if_neg (Finset.mem_filter.mp hv).2.1
  have hKsmall (htS : t ∈ S) : K ⊆ {r} := by
    intro v hv
    have hv' : v=r ∨ v=t := by simpa using hKsub hv
    rcases hv' with rfl | rfl
    · simp
    · exact ((Finset.mem_filter.mp hv).2.1 htS).elim
  have hsumK : (∑ v ∈ K, (L v).card) ≤ X.card + if t ∈ S then 0 else Y.card := by
    rw [show (∑ v ∈ K, (L v).card) = ∑ v ∈ K, (core v).card by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hLcore v hv]]
    by_cases htS : t ∈ S
    · have hh := Finset.sum_le_sum_of_subset_of_nonneg (hKsmall htS)
        (f := fun v => (core v).card) (by intros; exact Nat.zero_le _)
      simpa [core, htS] using hh
    · have hh := Finset.sum_le_sum_of_subset_of_nonneg hKsub
        (f := fun v => (core v).card) (by intros; exact Nat.zero_le _)
      simpa [core, htS, hrt, Ne.symm hrt] using hh
  have hsumS : (∑ v ∈ S, (L v).card) ≤ S.card + if t ∈ S then Y.card else 0 := by
    calc
      (∑ v ∈ S, (L v).card) ≤ ∑ v ∈ S, (1 + if v=t then Y.card else 0) := by
        apply Finset.sum_le_sum
        intro v hv
        by_cases hvt : v=t
        · subst v
          have hh := Finset.card_insert_le r Y
          simpa [L,hv,Nat.add_comm] using hh
        · simp [L,hv,hvt]
      _ = S.card + if t ∈ S then Y.card else 0 := by
        simp [Finset.sum_add_distrib]
  have hdiff : Z \ S = K := Finset.union_sdiff_cancel_right hKS
  have hcard : (Z \ S).card ≤ 2 := by
    rw [hdiff]
    simpa [hrt] using Finset.card_le_card hKsub
  refine ⟨Z,L,Finset.subset_union_right,?_,?_,?_,?_,?_,?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hvK | hvS
    · rw [hLcore v hvK]
      exact (Finset.mem_filter.mp hvK).2.2
    · by_cases hvt : v=t
      · subst v
        simp [L,hvS]
      · simp [L,hvS,hvt]
  · intro v hv u hu
    rcases Finset.mem_union.mp hv with hvK | hvS
    · rw [hLcore v hvK] at hu
      have hv' : v=r ∨ v=t := by simpa using hKsub hvK
      rcases hv' with rfl | rfl
      · exact hX u (by simpa [core] using hu)
      · exact hY u (by simpa [core,Ne.symm hrt] using hu)
    · by_cases hvt : v=t
      · subst v
        have hu' : u=r ∨ u∈Y := by simpa [L,hvS] using hu
        rcases hu' with rfl | huY
        · exact (hS t hvS).symm
        · exact hY u huY
      · have hur : u=r := by simpa [L,hvS,hvt] using hu
        subst u
        exact (hS v hvS).symm
  · intro e he
    rcases Finset.mem_union.mp (hcov he) with he | he
    · rcases Finset.mem_union.mp he with he | he
      · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
        have hrK : r ∈ K := by
          simp only [K,Finset.mem_filter]
          exact ⟨by simp,hrS,by simpa [core] using (show X.Nonempty from ⟨x,hx⟩)⟩
        exact ⟨r,Finset.mem_union_left _ hrK,x,by simpa [L,hrS,core] using hx,rfl⟩
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
        by_cases htS : t ∈ S
        · exact ⟨t,Finset.mem_union_right _ htS,y,by simp [L,htS,hy],rfl⟩
        · have htK : t ∈ K := by
            simp only [K,Finset.mem_filter]
            exact ⟨by simp,htS,by simpa [core,Ne.symm hrt] using (show Y.Nonempty from ⟨y,hy⟩)⟩
          exact ⟨t,Finset.mem_union_left _ htK,y,by simpa [L,htS,core,Ne.symm hrt] using hy,rfl⟩
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
      refine ⟨v,Finset.mem_union_right _ hv,r,?_,Sym2.eq_swap⟩
      by_cases hvt : v=t
      · subst v
        simp [L,hv]
      · simp [L,hv,hvt]
  · have hsum : (∑ v ∈ Z, (L v).card) =
        (∑ v ∈ K, (L v).card) + (∑ v ∈ S, (L v).card) := Finset.sum_union hKS
    by_cases htS : t ∈ S <;> simp [htS] at hsumK hsumS <;> omega
  · intro v hv
    simp [L,hv]
  · intro htS
    rw [hdiff]
    simpa using Finset.card_le_card (hKsmall htS)

end PEqualNP.Outside.L_meta_5012.GuardedReuseOverlap

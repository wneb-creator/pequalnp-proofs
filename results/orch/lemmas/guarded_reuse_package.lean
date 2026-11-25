import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.GuardedReuse

lemma package_reused_stars {n : ℕ} (G : SimpleGraph (Fin n))
    (r t : Fin n) (hrt : r ≠ t) (X Y S : Finset (Fin n))
    (hrS : r ∉ S) (htS : t ∉ S)
    (hX : ∀ x ∈ X, G.Adj r x) (hY : ∀ y ∈ Y, G.Adj t y)
    (hS : ∀ v ∈ S, G.Adj r v) {E : Finset (Sym2 (Fin n))}
    (hcov : E ⊆ X.image (fun x => s(r,x)) ∪ Y.image (fun y => s(t,y)) ∪
      S.image (fun v => s(r,v))) :
    ∃ (Z : Finset (Fin n)) (L : Fin n → Finset (Fin n)), S ⊆ Z ∧
      (∀ v ∈ Z, (L v).Nonempty) ∧ (∀ v ∈ Z, ∀ u ∈ L v, G.Adj v u) ∧
      (∀ e ∈ E, ∃ v ∈ Z, ∃ u ∈ L v, e = s(v,u)) ∧
      (∑ v ∈ Z, (L v).card) + (Z \ S).card ≤ X.card+Y.card+S.card+2 ∧
      (∀ v ∈ S, L v = {r}) := by
  classical
  let core : Fin n → Finset (Fin n) := fun v => if v=r then X else if v=t then Y else ∅
  let K := ({r,t} : Finset (Fin n)).filter (fun v => (core v).Nonempty)
  let Z := K ∪ S
  let L : Fin n → Finset (Fin n) := fun v => if v ∈ S then {r} else core v
  have hKsub : K ⊆ ({r,t} : Finset (Fin n)) := Finset.filter_subset _ _
  have hKS : Disjoint K S := by
    apply Finset.disjoint_left.mpr
    intro v hv hvS
    have hv' : v=r ∨ v=t := by simpa using hKsub hv
    rcases hv' with rfl | rfl
    · exact hrS hvS
    · exact htS hvS
  have hLcore : ∀ v ∈ K, L v = core v := by
    intro v hv
    exact if_neg (fun hs => Finset.disjoint_left.mp hKS hv hs)
  have hsumK : (∑ v ∈ K, (L v).card) ≤ X.card+Y.card := by
    calc
      (∑ v ∈ K, (L v).card) = ∑ v ∈ K, (core v).card := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hLcore v hv]
      _ ≤ ∑ v ∈ ({r,t} : Finset (Fin n)), (core v).card :=
        Finset.sum_le_sum_of_subset_of_nonneg hKsub (by intros; exact Nat.zero_le _)
      _ = X.card+Y.card := by simp [core, hrt, Ne.symm hrt]
  have hsumS : (∑ v ∈ S, (L v).card) = S.card := by
    calc
      (∑ v ∈ S, (L v).card) = ∑ _v ∈ S, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro v hv
        simp [L,hv]
      _ = S.card := by simp
  have hcard : (Z \ S).card ≤ 2 := by
    have hsub : Z \ S ⊆ ({r,t} : Finset (Fin n)) := by
      intro v hv
      obtain ⟨hvZ, hvS⟩ := Finset.mem_sdiff.mp hv
      rcases Finset.mem_union.mp hvZ with hvK | hvS'
      · exact hKsub hvK
      · exact (hvS hvS').elim
    simpa [hrt] using Finset.card_le_card hsub
  refine ⟨Z, L, Finset.subset_union_right, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hvK | hvS
    · rw [hLcore v hvK]
      exact (Finset.mem_filter.mp hvK).2
    · simp [L, hvS]
  · intro v hv u hu
    rcases Finset.mem_union.mp hv with hvK | hvS
    · rw [hLcore v hvK] at hu
      have hv' : v=r ∨ v=t := by simpa using hKsub hvK
      rcases hv' with rfl | rfl
      · exact hX u (by simpa [core] using hu)
      · exact hY u (by simpa [core, Ne.symm hrt] using hu)
    · have hur : u=r := by simpa [L,hvS] using hu
      subst u
      exact (hS v hvS).symm
  · intro e he
    rcases Finset.mem_union.mp (hcov he) with he | he
    · rcases Finset.mem_union.mp he with he | he
      · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
        have hrK : r ∈ K := by simp only [K, Finset.mem_filter]; exact ⟨by simp,by simpa [core] using (show X.Nonempty from ⟨x,hx⟩)⟩
        exact ⟨r,Finset.mem_union_left _ hrK,x,by simpa [L,hrS,core] using hx,rfl⟩
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
        have htK : t ∈ K := by simp only [K, Finset.mem_filter]; exact ⟨by simp,by simpa [core,Ne.symm hrt] using (show Y.Nonempty from ⟨y,hy⟩)⟩
        exact ⟨t,Finset.mem_union_left _ htK,y,by simpa [L,htS,core,Ne.symm hrt] using hy,rfl⟩
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
      exact ⟨v,Finset.mem_union_right _ hv,r,by simp [L,hv],Sym2.eq_swap⟩
  · have hsum : (∑ v ∈ Z, (L v).card) =
        (∑ v ∈ K, (L v).card) + S.card := by
      rw [show Z=K∪S from rfl, Finset.sum_union hKS, hsumS]
    omega
  · intro v hv
    simp [L,hv]

end PEqualNP.Outside.L_meta_5012.GuardedReuse

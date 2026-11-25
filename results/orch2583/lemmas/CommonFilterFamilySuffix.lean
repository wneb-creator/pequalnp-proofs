namespace PEqualNP.Outside.L_meta_2583.CommonFilter

variable {ι α β : Type} [DecidableEq ι] [DecidableEq α] [DecidableEq β]

lemma family_edges (T : Finset ι) (P : ι → Finset α) (L : ι → Finset β)
    (A : Finset α) (B : Finset β)
    (hp : ∀ i ∈ T, (P i).Nonempty) (hl : ∀ i ∈ T, (L i).Nonempty)
    (hfour : NoFour (T.biUnion fun i => Rect (P i) A (L i) B)) :
    (T.biUnion fun i => Rect (P i) A (L i) B).card + T.card ≤
      ∑ i ∈ T, ((P i).card + (L i).card) := by
  revert hp hl hfour
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    intro hp hl hfour
    have hi4 : NoFour (Rect (P i) A (L i) B) := noFour_subset (by
      intro e he
      exact Finset.mem_biUnion.mpr ⟨i,by simp,he⟩) hfour
    have ht4 : NoFour (T.biUnion fun i => Rect (P i) A (L i) B) := noFour_subset (by
      intro e he
      obtain ⟨j,hj,he⟩ := Finset.mem_biUnion.mp he
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_insert_of_mem hj,he⟩) hfour
    have hnew := rect_edges (P i) A (L i) B (hp i (by simp)) (hl i (by simp)) hi4
    have hold := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      (fun j hj => hl j (Finset.mem_insert_of_mem hj)) ht4
    have hu := Finset.card_union_le (Rect (P i) A (L i) B)
      (T.biUnion fun i => Rect (P i) A (L i) B)
    rw [Finset.biUnion_insert,Finset.card_insert_of_notMem hi,Finset.sum_insert hi]
    omega

lemma family_cover (T : Finset ι) (P : ι → Finset α) (L : ι → Finset β)
    (A : Finset α) (B : Finset β)
    (hp : ∀ i ∈ T, (P i).Nonempty) (hl : ∀ i ∈ T, (L i).Nonempty)
    (hfour : NoFour (T.biUnion fun i => Rect (P i) A (L i) B)) :
    (∀ p l, (p,l) ∈ (T.biUnion fun i => Rect (P i) A (L i) B) → p ∈ A ∨ l ∈ B) ∧
    (T.biUnion fun i => Rect (P i) A (L i) B).card + A.card + B.card + T.card ≤
      (∑ i ∈ T, ((P i).card + (L i).card)) + A.card + B.card := by
  constructor
  · intro p l h
    obtain ⟨i,_,he⟩ := Finset.mem_biUnion.mp h
    exact (Finset.mem_filter.mp he).2
  · have := family_edges T P L A B hp hl hfour
    omega

lemma core_family (T : Finset ι) (P : ι → Finset α) (L : ι → Finset β)
    (A : Finset α) (B : Finset β) :
    Core (T.biUnion fun i => P i ×ˢ L i) A B =
      T.biUnion fun i => Rect (P i) A (L i) B := by
  ext e
  simp only [Core,Rect,Finset.mem_filter,Finset.mem_biUnion]
  aesop

end PEqualNP.Outside.L_meta_2583.CommonFilter

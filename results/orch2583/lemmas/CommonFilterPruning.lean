import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.CommonFilter

variable {α β : Type} [DecidableEq α] [DecidableEq β]

def Rect (P A : Finset α) (L B : Finset β) : Finset (α × β) :=
  (P ×ˢ L).filter fun e => e.1 ∈ A ∨ e.2 ∈ B

def NoFour (E : Finset (α × β)) : Prop :=
  ∀ p p' l l', p ≠ p' → l ≠ l' →
    ¬ ((p,l) ∈ E ∧ (p,l') ∈ E ∧ (p',l) ∈ E ∧ (p',l') ∈ E)

lemma rectangle_small_side (E : Finset (α × β)) (hE : NoFour E)
    (P : Finset α) (L : Finset β) (hPL : P ×ˢ L ⊆ E) : P.card ≤ 1 ∨ L.card ≤ 1 := by
  by_contra h
  simp only [not_or, not_le] at h
  obtain ⟨p,hp,p',hp',hpp⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨l,hl,l',hl',hll⟩ := Finset.one_lt_card.mp h.2
  exact hE p p' l l' hpp hll
    ⟨hPL (Finset.mem_product.mpr ⟨hp,hl⟩), hPL (Finset.mem_product.mpr ⟨hp,hl'⟩),
      hPL (Finset.mem_product.mpr ⟨hp',hl⟩), hPL (Finset.mem_product.mpr ⟨hp',hl'⟩)⟩

lemma rect_union (P A : Finset α) (L B : Finset β) :
    Rect P A L B = ((P ∩ A) ×ˢ L) ∪ (P ×ˢ (L ∩ B)) := by
  ext e
  simp only [Rect,Finset.mem_filter,Finset.mem_product,Finset.mem_inter,Finset.mem_union]
  tauto

lemma rect_count (P A : Finset α) (L B : Finset β) :
    (Rect P A L B).card + (P ∩ A).card * (L ∩ B).card =
      (P ∩ A).card * L.card + P.card * (L ∩ B).card := by
  have hinter : (((P ∩ A) ×ˢ L) ∩ (P ×ˢ (L ∩ B))) = (P ∩ A) ×ˢ (L ∩ B) := by
    ext e
    simp only [Finset.mem_product,Finset.mem_inter]
    tauto
  have h := Finset.card_union_add_card_inter ((P ∩ A) ×ˢ L) (P ×ˢ (L ∩ B))
  rw [← rect_union,hinter] at h
  simpa only [Finset.card_product] using h

lemma rect_edges (P A : Finset α) (L B : Finset β)
    (hp : P.Nonempty) (hl : L.Nonempty) (hfour : NoFour (Rect P A L B)) :
    (Rect P A L B).card + 1 ≤ P.card + L.card := by
  have hp0 : 0 < P.card := Finset.card_pos.mpr hp
  have hl0 : 0 < L.card := Finset.card_pos.mpr hl
  have hsub : Rect P A L B ⊆ P ×ˢ L := Finset.filter_subset _ _
  have hcnt := Finset.card_le_card hsub
  rw [Finset.card_product] at hcnt
  by_cases hp1 : P.card ≤ 1
  · have he : P.card = 1 := by omega
    rw [he] at hcnt ⊢
    simp only [one_mul] at hcnt
    omega
  by_cases hl1 : L.card ≤ 1
  · have he : L.card = 1 := by omega
    rw [he] at hcnt ⊢
    simp only [mul_one] at hcnt
    omega
  have hpa : (P ∩ A).card ≤ 1 := by
    have hs : (P ∩ A) ×ˢ L ⊆ Rect P A L B := by rw [rect_union]; exact Finset.subset_union_left
    exact (rectangle_small_side _ hfour _ _ hs).resolve_right hl1
  have hlb : (L ∩ B).card ≤ 1 := by
    have hs : P ×ˢ (L ∩ B) ⊆ Rect P A L B := by rw [rect_union]; exact Finset.subset_union_right
    exact (rectangle_small_side _ hfour _ _ hs).resolve_left hp1
  have he := rect_count P A L B
  interval_cases h : (P ∩ A).card <;> interval_cases k : (L ∩ B).card <;>
    simp only [h,k,zero_mul,mul_zero,one_mul,mul_one,Nat.add_zero,Nat.zero_add] at he <;> omega

lemma noFour_subset {E F : Finset (α × β)} (h : E ⊆ F) (hf : NoFour F) : NoFour E := by
  intro p p' l l' hp hl he
  exact hf p p' l l' hp hl ⟨h he.1,h he.2.1,h he.2.2.1,h he.2.2.2⟩

lemma common_filter_cover (P1 P2 A : Finset α) (L1 L2 B : Finset β)
    (hp1 : P1.Nonempty) (hp2 : P2.Nonempty) (hl1 : L1.Nonempty) (hl2 : L2.Nonempty)
    (hfour : NoFour (Rect P1 A L1 B ∪ Rect P2 A L2 B)) :
    (∀ p l, (p,l) ∈ Rect P1 A L1 B ∪ Rect P2 A L2 B → p ∈ A ∨ l ∈ B) ∧
    (Rect P1 A L1 B ∪ Rect P2 A L2 B).card + A.card + B.card + 2 ≤
      P1.card + L1.card + P2.card + L2.card + A.card + B.card := by
  have h1 := rect_edges P1 A L1 B hp1 hl1 (noFour_subset Finset.subset_union_left hfour)
  have h2 := rect_edges P2 A L2 B hp2 hl2 (noFour_subset Finset.subset_union_right hfour)
  have hsum := Finset.card_union_le (Rect P1 A L1 B) (Rect P2 A L2 B)
  constructor
  · intro p l h
    rcases Finset.mem_union.mp h with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact (Finset.mem_filter.mp h).2
  · omega

end PEqualNP.Outside.L_meta_2583.CommonFilter

namespace PEqualNP.Outside.L_meta_2583.CommonFilter

variable {α β : Type} [DecidableEq α] [DecidableEq β]

def neighbors (E : Finset (α × β)) (p : α) : Finset β :=
  (E.filter fun e => e.1 = p).image Prod.snd

lemma mem_neighbors (E : Finset (α × β)) (p : α) (l : β) :
    l ∈ neighbors E p ↔ (p,l) ∈ E := by
  simp only [neighbors,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨⟨p',l'⟩,⟨he,hp⟩,hl⟩
    dsimp at hp hl
    subst p'
    subst l'
    exact he
  · intro he
    exact ⟨(p,l),⟨he,rfl⟩,rfl⟩

lemma nested_heavy_unique (E : Finset (α × β)) (hfour : NoFour E)
    (p p' : α) (hnest : neighbors E p ⊆ neighbors E p' ∨ neighbors E p' ⊆ neighbors E p)
    (hp : 1 < (neighbors E p).card) (hp' : 1 < (neighbors E p').card) : p = p' := by
  by_contra hne
  rcases hnest with h | h
  · obtain ⟨l,hl,l',hl',hll⟩ := Finset.one_lt_card.mp hp
    exact hfour p p' l l' hne hll
      ⟨(mem_neighbors E p l).mp hl,(mem_neighbors E p l').mp hl',
        (mem_neighbors E p' l).mp (h hl),(mem_neighbors E p' l').mp (h hl')⟩
  · obtain ⟨l,hl,l',hl',hll⟩ := Finset.one_lt_card.mp hp'
    exact hfour p p' l l' hne hll
      ⟨(mem_neighbors E p l).mp (h hl),(mem_neighbors E p l').mp (h hl'),
        (mem_neighbors E p' l).mp hl,(mem_neighbors E p' l').mp hl'⟩

lemma common_neighbors (P1 P2 A : Finset α) (L1 L2 B : Finset β)
    (p : α) (hp1 : p ∈ P1) (hp2 : p ∈ P2) :
    neighbors (Rect P1 A L1 B ∪ Rect P2 A L2 B) p =
      (L1 ∪ L2).filter fun l => p ∈ A ∨ l ∈ B := by
  ext l
  rw [mem_neighbors]
  simp only [Rect,Finset.mem_filter,Finset.mem_union,Finset.mem_product,hp1,hp2,true_and]
  tauto

lemma common_heavy_unique (P1 P2 A : Finset α) (L1 L2 B : Finset β)
    (hfour : NoFour (Rect P1 A L1 B ∪ Rect P2 A L2 B))
    (p p' : α) (hp1 : p ∈ P1) (hp2 : p ∈ P2) (hp1' : p' ∈ P1) (hp2' : p' ∈ P2)
    (hp : 1 < (neighbors (Rect P1 A L1 B ∪ Rect P2 A L2 B) p).card)
    (hp' : 1 < (neighbors (Rect P1 A L1 B ∪ Rect P2 A L2 B) p').card) : p = p' := by
  apply nested_heavy_unique _ hfour p p' _ hp hp'
  rw [common_neighbors P1 P2 A L1 L2 B p hp1 hp2,
    common_neighbors P1 P2 A L1 L2 B p' hp1' hp2']
  by_cases ha : p ∈ A <;> by_cases ha' : p' ∈ A <;>
    simp only [ha,ha',true_or,false_or,Finset.filter_true]
  · exact Or.inl (Finset.Subset.refl _)
  · exact Or.inr (Finset.filter_subset _ _)
  · exact Or.inl (Finset.filter_subset _ _)
  · exact Or.inl (Finset.Subset.refl _)

end PEqualNP.Outside.L_meta_2583.CommonFilter

namespace PEqualNP.Outside.L_meta_2583.CommonFilter

variable {α β : Type} [DecidableEq α] [DecidableEq β]

lemma delete_left_count (E : Finset (α × β)) (S : Finset α)
    (hdeg : ∀ p ∈ S, (neighbors E p).card ≤ 1) :
    E.card ≤ (E.filter fun e => e.1 ∉ S).card + S.card := by
  have hremoved : (E.filter fun e => e.1 ∈ S).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro e he
      exact (Finset.mem_filter.mp he).2
    · intro e he f hf heq
      rcases e with ⟨p,l⟩
      rcases f with ⟨p',l'⟩
      dsimp at heq
      subst p'
      have hp : p ∈ S := (Finset.mem_filter.mp he).2
      have hl : l ∈ neighbors E p := (mem_neighbors E p l).mpr (Finset.mem_filter.mp he).1
      have hl' : l' ∈ neighbors E p := (mem_neighbors E p l').mpr (Finset.mem_filter.mp hf).1
      have he : l = l' := Finset.card_le_one.mp (hdeg p hp) l hl l' hl'
      rw [he]
  have hsub : E ⊆ (E.filter fun e => e.1 ∉ S) ∪ (E.filter fun e => e.1 ∈ S) := by
    intro e he
    by_cases hp : e.1 ∈ S <;> simp [he,hp]
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

lemma filter_left_core (P1 P2 A S : Finset α) (L1 L2 B : Finset β) :
    ((Rect P1 A L1 B ∪ Rect P2 A L2 B).filter fun e => e.1 ∉ S) =
      Rect (P1 \ S) A L1 B ∪ Rect (P2 \ S) A L2 B := by
  ext e
  simp only [Rect,Finset.mem_filter,Finset.mem_product,Finset.mem_union,Finset.mem_sdiff]
  tauto

lemma prune_common_left (P1 P2 A : Finset α) (L1 L2 B : Finset β)
    (hp1 : P1.Nonempty) (hp2 : P2.Nonempty)
    (hfour : NoFour (Rect P1 A L1 B ∪ Rect P2 A L2 B)) :
    ∃ S : Finset α, S ⊆ P1 ∩ P2 ∧ S.card = (P1 ∩ P2).card - 1 ∧
      (P1 \ S).Nonempty ∧ (P2 \ S).Nonempty ∧
      (Rect P1 A L1 B ∪ Rect P2 A L2 B).card ≤
        (Rect (P1 \ S) A L1 B ∪ Rect (P2 \ S) A L2 B).card + S.card := by
  by_cases hi : (P1 ∩ P2).Nonempty
  · obtain ⟨p0,hp0,hothers⟩ : ∃ p0 ∈ P1 ∩ P2,
        ∀ p ∈ P1 ∩ P2, p ≠ p0 →
          (neighbors (Rect P1 A L1 B ∪ Rect P2 A L2 B) p).card ≤ 1 := by
      by_cases hh : ∃ p ∈ P1 ∩ P2,
          1 < (neighbors (Rect P1 A L1 B ∪ Rect P2 A L2 B) p).card
      · obtain ⟨p0,hp0,hdeg0⟩ := hh
        refine ⟨p0,hp0,?_⟩
        intro p hp hne
        by_contra! hdeg
        exact hne (common_heavy_unique P1 P2 A L1 L2 B hfour p p0
          (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hp).2
          (Finset.mem_inter.mp hp0).1 (Finset.mem_inter.mp hp0).2 hdeg hdeg0)
      · obtain ⟨p0,hp0⟩ := hi
        refine ⟨p0,hp0,?_⟩
        intro p hp _
        by_contra! hdeg
        exact hh ⟨p,hp,hdeg⟩
    let S := (P1 ∩ P2).erase p0
    refine ⟨S,Finset.erase_subset _ _,?_,?_,?_,?_⟩
    · exact Finset.card_erase_of_mem hp0
    · exact ⟨p0,Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hp0).1,by simp [S]⟩⟩
    · exact ⟨p0,Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hp0).2,by simp [S]⟩⟩
    · have hd : ∀ p ∈ S,
          (neighbors (Rect P1 A L1 B ∪ Rect P2 A L2 B) p).card ≤ 1 := by
        intro p hp
        exact hothers p (Finset.mem_erase.mp hp).2 (Finset.mem_erase.mp hp).1
      have hc := delete_left_count (Rect P1 A L1 B ∪ Rect P2 A L2 B) S hd
      rw [filter_left_core] at hc
      exact hc
  · have he : P1 ∩ P2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
    refine ⟨∅,by simp,by simp [he],?_,?_,?_⟩
    · simpa using hp1
    · simpa using hp2
    · simp

end PEqualNP.Outside.L_meta_2583.CommonFilter

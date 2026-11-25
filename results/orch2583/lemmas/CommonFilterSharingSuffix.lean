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

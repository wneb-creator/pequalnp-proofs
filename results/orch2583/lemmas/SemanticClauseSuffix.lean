namespace PEqualNP.Outside.L_meta_2583.Semantic

def clause {α β : Type*} (P : Finset α) (L : Finset β)
    (X : α → Prop) (Y : β → Prop) : Prop :=
  (∃ p ∈ P, X p) ∨ (∃ l ∈ L, Y l)

lemma pure_factors {α β : Type*} (I : α → β → Prop)
    (P : Fin 3 → Finset α) (L : Fin 3 → Finset β)
    (inhabited : ∀ i, (P i).Nonempty ∨ (L i).Nonempty)
    (below : ∀ X Y, (∀ i, clause (P i) (L i) X Y) →
      ∃ p l, I p l ∧ X p ∧ Y l) :
    ∃ i j : Fin 3, i ≠ j ∧ P i = ∅ ∧ L j = ∅ := by
  classical
  have hp : ∃ i, P i = ∅ := by
    by_contra hn
    push Not at hn
    have h : ∀ i, clause (P i) (L i) (fun _ => True) (fun _ => False) := by
      intro i
      obtain ⟨p, hp⟩ := hn i
      exact Or.inl ⟨p, hp, trivial⟩
    obtain ⟨_, _, _, _, absurd⟩ := below _ _ h
    exact absurd
  have hl : ∃ j, L j = ∅ := by
    by_contra hn
    push Not at hn
    have h : ∀ i, clause (P i) (L i) (fun _ => False) (fun _ => True) := by
      intro i
      obtain ⟨l, hl⟩ := hn i
      exact Or.inr ⟨l, hl, trivial⟩
    obtain ⟨_, _, _, absurd, _⟩ := below _ _ h
    exact absurd
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hl
  refine ⟨i, j, ?_, hi, hj⟩
  intro he
  subst j
  rcases inhabited i with h | h
  · simpa [hi] using h
  · simpa [hj] using h

def threeClause {α β : Type*} (P Wp : Finset α) (L Wl : Finset β)
    (X : α → Prop) (Y : β → Prop) : Prop :=
  (∃ p ∈ P, X p) ∧ (∃ l ∈ L, Y l) ∧ clause Wp Wl X Y

lemma three_clause_pair_core {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P Wp : Finset α) (L Wl : Finset β) (p : α) (l : β) :
    threeClause P Wp L Wl (fun a => a = p) (fun b => b = l) ↔
      (p, l) ∈ ((P ∩ Wp) ×ˢ L) ∪ (P ×ˢ (L ∩ Wl)) := by
  simp only [threeClause, clause, exists_eq_right, Finset.mem_union,
    Finset.mem_product, Finset.mem_inter]
  tauto

lemma three_clause_incidence_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : α → β → Prop) (P Wp : Finset α) (L Wl : Finset β)
    (noRectangle : ∀ p p' l l', p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (below : ∀ X Y, threeClause P Wp L Wl X Y →
      ∃ p l, I p l ∧ X p ∧ Y l) :
    ∃ U : Finset α, ∃ V : Finset β,
      (∀ e ∈ ((P ∩ Wp) ×ˢ L) ∪ (P ×ˢ (L ∩ Wl)), e.1 ∈ U ∨ e.2 ∈ V) ∧
      (((P ∩ Wp) ×ˢ L) ∪ (P ×ˢ (L ∩ Wl))).card + U.card + V.card ≤
        P.card + L.card + Wp.card + Wl.card := by
  have accepted (p : α) (l : β) (hp : p ∈ P) (hl : l ∈ L)
      (hw : p ∈ Wp ∨ l ∈ Wl) : I p l := by
    have h : threeClause P Wp L Wl (fun a => a = p) (fun b => b = l) := by
      refine ⟨⟨p, hp, rfl⟩, ⟨l, hl, rfl⟩, ?_⟩
      rcases hw with hpw | hlw
      · exact Or.inl ⟨p, hpw, rfl⟩
      · exact Or.inr ⟨l, hlw, rfl⟩
    obtain ⟨p', l', hi, rfl, rfl⟩ := below _ _ h
    exact hi
  apply triple_pair_core_cover P Wp L Wl
  intro p hp p' hp' l hl l' hl' hpp hll h
  exact noRectangle p p' l l' hpp hll
    ⟨accepted p l hp hl h.1, accepted p l' hp hl' h.2.1,
      accepted p' l hp' hl h.2.2.1, accepted p' l' hp' hl' h.2.2.2⟩

end PEqualNP.Outside.L_meta_2583.Semantic

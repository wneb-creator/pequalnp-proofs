import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.Semantic

lemma triple_pair_core_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P Wp : Finset α) (L Wl : Finset β)
    (noRectangle : ∀ p ∈ P, ∀ p' ∈ P, ∀ l ∈ L, ∀ l' ∈ L,
      p ≠ p' → l ≠ l' →
      ¬ ((p ∈ Wp ∨ l ∈ Wl) ∧ (p ∈ Wp ∨ l' ∈ Wl) ∧
         (p' ∈ Wp ∨ l ∈ Wl) ∧ (p' ∈ Wp ∨ l' ∈ Wl))) :
    ∃ U : Finset α, ∃ V : Finset β,
      (∀ e ∈ ((P ∩ Wp) ×ˢ L) ∪ (P ×ˢ (L ∩ Wl)), e.1 ∈ U ∨ e.2 ∈ V) ∧
      (((P ∩ Wp) ×ˢ L) ∪ (P ×ˢ (L ∩ Wl))).card + U.card + V.card ≤
        P.card + L.card + Wp.card + Wl.card := by
  let E := ((P ∩ Wp) ×ˢ L) ∪ (P ×ˢ (L ∩ Wl))
  have subset : E ⊆ P ×ˢ L := by
    intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact Finset.mem_product.mpr ⟨(Finset.mem_inter.mp (Finset.mem_product.mp h).1).1,
        (Finset.mem_product.mp h).2⟩
    · exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp h).1,
        (Finset.mem_inter.mp (Finset.mem_product.mp h).2).1⟩
  have card : E.card ≤ P.card * L.card := by
    simpa using Finset.card_le_card subset
  by_cases hp : P.card ≤ 1
  · refine ⟨P, ∅, ?_, ?_⟩
    · intro e he
      exact Or.inl (Finset.mem_product.mp (subset he)).1
    · have hm : P.card * L.card ≤ L.card := by
        simpa using Nat.mul_le_mul_right L.card hp
      change E.card + P.card + 0 ≤ _
      omega
  by_cases hl : L.card ≤ 1
  · refine ⟨∅, L, ?_, ?_⟩
    · intro e he
      exact Or.inr (Finset.mem_product.mp (subset he)).2
    · have hm : P.card * L.card ≤ P.card := by
        simpa using Nat.mul_le_mul_left P.card hl
      change E.card + 0 + L.card ≤ _
      omega
  have aSmall : (P ∩ Wp).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hpa p' hpa'
    by_contra hne
    obtain ⟨l, hlL, l', hlL', hll'⟩ := Finset.one_lt_card.mp (by omega : 1 < L.card)
    exact noRectangle p (Finset.mem_inter.mp hpa).1 p' (Finset.mem_inter.mp hpa').1
      l hlL l' hlL' hne hll'
      ⟨Or.inl (Finset.mem_inter.mp hpa).2, Or.inl (Finset.mem_inter.mp hpa).2,
        Or.inl (Finset.mem_inter.mp hpa').2, Or.inl (Finset.mem_inter.mp hpa').2⟩
  have bSmall : (L ∩ Wl).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro l hlb l' hlb'
    by_contra hne
    obtain ⟨p, hpP, p', hpP', hpp'⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
    exact noRectangle p hpP p' hpP' l (Finset.mem_inter.mp hlb).1
      l' (Finset.mem_inter.mp hlb').1 hpp' hne
      ⟨Or.inr (Finset.mem_inter.mp hlb).2, Or.inr (Finset.mem_inter.mp hlb').2,
        Or.inr (Finset.mem_inter.mp hlb).2, Or.inr (Finset.mem_inter.mp hlb').2⟩
  refine ⟨P ∩ Wp, L ∩ Wl, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact Or.inl (Finset.mem_product.mp h).1
    · exact Or.inr (Finset.mem_product.mp h).2
  · have he : E.card ≤ (P ∩ Wp).card * L.card + P.card * (L ∩ Wl).card := by
      simpa [E] using Finset.card_union_le ((P ∩ Wp) ×ˢ L) (P ×ˢ (L ∩ Wl))
    have hm1 : (P ∩ Wp).card * L.card ≤ L.card := by
      simpa using Nat.mul_le_mul_right L.card aSmall
    have hm2 : P.card * (L ∩ Wl).card ≤ P.card := by
      simpa using Nat.mul_le_mul_left P.card bSmall
    have hwa : (P ∩ Wp).card ≤ Wp.card := Finset.card_le_card Finset.inter_subset_right
    have hwb : (L ∩ Wl).card ≤ Wl.card := Finset.card_le_card Finset.inter_subset_right
    change E.card + (P ∩ Wp).card + (L ∩ Wl).card ≤ _
    omega

end PEqualNP.Outside.L_meta_2583.Semantic

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

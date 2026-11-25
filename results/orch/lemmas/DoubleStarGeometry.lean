import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.DoubleStarGeometry

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma cross_edge_center {V : Type*} (G : SimpleGraph V)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (P Q : Set V) (p q : V) (hpq : G.Adj p q)
    (hpQ : ∀ b ∈ Q, G.Adj p b) (hqP : ∀ a ∈ P, G.Adj q a)
    (a b : V) (ha : a ∈ P) (hb : b ∈ Q) (hab : G.Adj a b) :
    a = p ∨ b = q := by
  rcases hfour p b a q (hpQ b hb) hab.symm (hqP a ha).symm hpq.symm with h | h
  · exact Or.inl h.symm
  · exact Or.inr h

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab.ne rfl).elim
    · exact hab
    · exact hab.symm
    · exact (hab.ne rfl).elim
  · intro huv
    exact ⟨u, v, huv, Or.inl rfl, Or.inr rfl⟩

lemma clean_context_centers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q R : Set (Fin n)) (p q : Fin n)
    (hpP : p ∈ P) (hpR : p ∈ R) (hqQ : q ∈ Q) (hqR : q ∈ R)
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ P, x a = true) → (∃ b ∈ Q, x b = true) →
      (∃ c ∈ R, x c = true) → graphFun G ∅ x = true) :
    (∀ b ∈ Q, G.Adj p b) ∧ (∀ a ∈ P, G.Adj q a) := by
  constructor
  · intro b hb
    apply (graph_pair G p b).mp
    exact hclean (pairInput p b)
      ⟨p, hpP, by simp [pairInput]⟩ ⟨b, hb, by simp [pairInput]⟩
      ⟨p, hpR, by simp [pairInput]⟩
  · intro a ha
    apply (graph_pair G q a).mp
    exact hclean (pairInput q a)
      ⟨a, ha, by simp [pairInput]⟩ ⟨q, hqQ, by simp [pairInput]⟩
      ⟨q, hqR, by simp [pairInput]⟩

def twoStars {V : Type*} (P Q : Set V) (p q : V) (x : V → Bool) : Prop :=
  (x p = true ∧ ∃ b ∈ Q, x b = true) ∨
  (x q = true ∧ ∃ a ∈ P, x a = true)

lemma clean_context_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (P Q R : Set (Fin n)) (hdisjoint : Disjoint P Q) (p q : Fin n)
    (hpP : p ∈ P) (hpR : p ∈ R) (hqQ : q ∈ Q) (hqR : q ∈ R)
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ P, x a = true) → (∃ b ∈ Q, x b = true) →
      (∃ c ∈ R, x c = true) → graphFun G ∅ x = true) :
    (∀ x, twoStars P Q p q x → graphFun G ∅ x = true) ∧
    (∀ u v, G.Adj u v →
      (∃ a ∈ P, pairInput u v a = true) →
      (∃ b ∈ Q, pairInput u v b = true) →
      twoStars P Q p q (pairInput u v)) := by
  obtain ⟨hpQ, hqP⟩ := clean_context_centers G P Q R p q hpP hpR hqQ hqR hclean
  constructor
  · intro x hx
    rcases hx with ⟨hp, b, hb, hx⟩ | ⟨hq, a, ha, hx⟩
    · exact hclean x ⟨p, hpP, hp⟩ ⟨b, hb, hx⟩ ⟨p, hpR, hp⟩
    · exact hclean x ⟨a, ha, hx⟩ ⟨q, hqQ, hq⟩ ⟨q, hqR, hq⟩
  · rintro u v huv ⟨a, ha, hxa⟩ ⟨b, hb, hxb⟩
    have habne : a ≠ b := by
      intro h
      subst b
      exact Set.disjoint_left.mp hdisjoint ha hb
    have hab : G.Adj a b := by
      simp only [pairInput, decide_eq_true_eq] at hxa hxb
      rcases hxa with rfl | rfl <;> rcases hxb with rfl | rfl
      · exact (habne rfl).elim
      · exact huv
      · exact huv.symm
      · exact (habne rfl).elim
    rcases cross_edge_center G hfour P Q p q (hpQ q hqQ) hpQ hqP a b ha hb hab with h | h
    · exact Or.inl ⟨h ▸ hxa, b, hb, hxb⟩
    · exact Or.inr ⟨h ▸ hxb, a, ha, hxa⟩

lemma clean_context_input_edge_obstruction {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htriangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (P Q : Set (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ P, x a = true) → (∃ b ∈ Q, x b = true) → graphFun G ∅ x = true)
    (a d : Fin n) (ha : a ∈ P) (hd : d ∈ P) (had : G.Adj a d) : Q = ∅ := by
  ext v
  constructor
  · intro hv
    have hav : G.Adj a v := (graph_pair G a v).mp
      (hclean (pairInput a v) ⟨a, ha, by simp [pairInput]⟩ ⟨v, hv, by simp [pairInput]⟩)
    have hdv : G.Adj d v := (graph_pair G d v).mp
      (hclean (pairInput d v) ⟨d, hd, by simp [pairInput]⟩ ⟨v, hv, by simp [pairInput]⟩)
    exact (htriangle a d v had hdv hav.symm).elim
  · intro hv
    exact hv.elim

end PEqualNP.Outside.L_meta_2448_aux.DoubleStarGeometry

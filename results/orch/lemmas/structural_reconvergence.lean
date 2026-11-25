import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.Reconvergence

lemma ancestors_comparable_of_unique_parents {α : Type*} (R : α → α → Prop) (r : α)
    (hunique : ∀ p q y, Relation.ReflTransGen R r p → Relation.ReflTransGen R r q →
      R p y → R q y → p = q)
    {a b x : α} (hra : Relation.ReflTransGen R r a)
    (hrb : Relation.ReflTransGen R r b)
    (hax : Relation.ReflTransGen R a x) (hbx : Relation.ReflTransGen R b x) :
    Relation.ReflTransGen R a b ∨ Relation.ReflTransGen R b a := by
  induction hax generalizing b with
  | refl => exact Or.inr hbx
  | @tail x y hax hxy ih =>
    rcases Relation.ReflTransGen.cases_tail hbx with hby | ⟨z, hbz, hzy⟩
    · subst b
      exact Or.inl (hax.tail hxy)
    · have hxz : x = z := hunique x z y (hra.trans hax) (hrb.trans hbz) hxy hzy
      subst z
      exact ih hrb hbz

lemma incomparable_paths_reconverge {α : Type*} (R : α → α → Prop) (r : α)
    {a b x : α} (hra : Relation.ReflTransGen R r a)
    (hrb : Relation.ReflTransGen R r b)
    (hax : Relation.ReflTransGen R a x) (hbx : Relation.ReflTransGen R b x)
    (hab : ¬ Relation.ReflTransGen R a b) (hba : ¬ Relation.ReflTransGen R b a) :
    ∃ p q y, Relation.ReflTransGen R r p ∧ Relation.ReflTransGen R r q ∧
      R p y ∧ R q y ∧ p ≠ q := by
  classical
  by_contra hno
  have hu : ∀ p q y, Relation.ReflTransGen R r p → Relation.ReflTransGen R r q →
      R p y → R q y → p = q := by
    intro p q y hp hq hpy hqy
    by_contra hpq
    exact hno ⟨p, q, y, hp, hq, hpy, hqy, hpq⟩
  rcases ancestors_comparable_of_unique_parents R r hu hra hrb hax hbx with h | h
  · exact hab h
  · exact hba h

end PEqualNP.Outside.L_meta_5012.Reconvergence

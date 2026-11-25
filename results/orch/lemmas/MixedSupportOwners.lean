import Mathlib.Init

namespace PEqualNP.Outside.L_meta_2732_aux

lemma mixedSupport_ownedSides {α : Type} (R : α → α → Prop)
    (A B S : α → Prop) (c d : α)
    (irrefl : ∀ u, ¬ R u u)
    (safe : ∀ u v, (A u ∨ A v) → (B u ∨ B v) → (S u ∨ S v) → R u v)
    (hc : A c) (hd : A d) (hB : B c ∨ B d) (hS : S c ∨ S d) :
    (B c ∧ ¬ B d ∧ ¬ S c ∧ S d ∧
      (∀ x, B x → R d x) ∧ (∀ x, S x → R c x)) ∨
    (B d ∧ ¬ B c ∧ S c ∧ ¬ S d ∧
      (∀ x, B x → R c x) ∧ (∀ x, S x → R d x)) := by
  rcases hB with hbc | hbd
  · have hnsc : ¬ S c := fun hsc =>
      irrefl c (safe c c (Or.inl hc) (Or.inl hbc) (Or.inl hsc))
    have hsd := hS.resolve_left hnsc
    have hnbd : ¬ B d := fun hbd =>
      irrefl d (safe d d (Or.inl hd) (Or.inl hbd) (Or.inl hsd))
    refine Or.inl ⟨hbc, hnbd, hnsc, hsd, ?_, ?_⟩
    · exact fun x hx => safe d x (Or.inl hd) (Or.inr hx) (Or.inl hsd)
    · exact fun x hx => safe c x (Or.inl hc) (Or.inl hbc) (Or.inr hx)
  · have hnsd : ¬ S d := fun hsd =>
      irrefl d (safe d d (Or.inl hd) (Or.inl hbd) (Or.inl hsd))
    have hsc := hS.resolve_right hnsd
    have hnbc : ¬ B c := fun hbc =>
      irrefl c (safe c c (Or.inl hc) (Or.inl hbc) (Or.inl hsc))
    refine Or.inr ⟨hbd, hnbc, hsc, hnsd, ?_, ?_⟩
    · exact fun x hx => safe c x (Or.inl hc) (Or.inr hx) (Or.inl hsc)
    · exact fun x hx => safe d x (Or.inl hd) (Or.inl hbd) (Or.inr hx)

end PEqualNP.Outside.L_meta_2732_aux

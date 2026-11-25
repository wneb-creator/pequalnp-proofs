import Mathlib.Init

namespace PEqualNP.Outside.L_meta_2732_aux

lemma tripleFilter_cross {α : Type} (A B S : α → Prop) (a b c d : α)
    (habA : A a ∨ A b) (habB : B a ∨ B b) (habS : S a ∨ S b)
    (hcdA : A c ∨ A d) (hcdB : B c ∨ B d) (hcdS : S c ∨ S d) :
    ((A a ∨ A c) ∧ (B a ∨ B c) ∧ (S a ∨ S c)) ∨
    ((A a ∨ A d) ∧ (B a ∨ B d) ∧ (S a ∨ S d)) ∨
    ((A b ∨ A c) ∧ (B b ∨ B c) ∧ (S b ∨ S c)) ∨
    ((A b ∨ A d) ∧ (B b ∨ B d) ∧ (S b ∨ S d)) := by
  cases habA <;> cases habB <;> cases habS <;>
    cases hcdA <;> cases hcdB <;> cases hcdS <;>
    first
    | exact Or.inl ⟨(by first | exact Or.inl ‹A a› | exact Or.inr ‹A c›), (by first | exact Or.inl ‹B a› | exact Or.inr ‹B c›), (by first | exact Or.inl ‹S a› | exact Or.inr ‹S c›)⟩
    | exact (fun h => Or.inr (Or.inl h)) ⟨(by first | exact Or.inl ‹A a› | exact Or.inr ‹A d›), (by first | exact Or.inl ‹B a› | exact Or.inr ‹B d›), (by first | exact Or.inl ‹S a› | exact Or.inr ‹S d›)⟩
    | exact (fun h => Or.inr (Or.inr (Or.inl h))) ⟨(by first | exact Or.inl ‹A b› | exact Or.inr ‹A c›), (by first | exact Or.inl ‹B b› | exact Or.inr ‹B c›), (by first | exact Or.inl ‹S b› | exact Or.inr ‹S c›)⟩
    | exact (fun h => Or.inr (Or.inr (Or.inr h))) ⟨(by first | exact Or.inl ‹A b› | exact Or.inr ‹A d›), (by first | exact Or.inl ‹B b› | exact Or.inr ‹B d›), (by first | exact Or.inl ‹S b› | exact Or.inr ‹S d›)⟩

end PEqualNP.Outside.L_meta_2732_aux

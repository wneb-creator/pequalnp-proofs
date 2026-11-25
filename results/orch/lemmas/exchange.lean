namespace PEqualNP.Outside.L_meta_1031_aux.Exchange

theorem rotate_and (a b c : Bool) :
    ((a && b) && c) = ((a && c) && b) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem rotate_or_of_implies (a b d : Bool) (h : d = true → a = true) :
    ((a && b) || d) = (a && (b || d)) := by
  cases a <;> cases b <;> cases d <;> first | rfl | exact Bool.noConfusion (h rfl)

theorem double_star_exchange (a b c d : Bool) :
    (((a || c) && (b || d)) && (a || d)) = ((a && (b || d)) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem filter_left_unique {α : Type} (R : α → α → Prop)
    (symm : ∀ {a b}, R a b → R b a)
    (no_four : ∀ a b c d, R a b → R b c → R c d → R d a → a = c ∨ b = d)
    (A B T : α → Prop)
    (cross : ∀ a b, A a → B b → (T a ∨ T b) → R a b)
    (b d : α) (hb : B b) (hd : B d) (hne : b ≠ d)
    (a c : α) (ha : A a) (hc : A c) (hta : T a) (htc : T c) : a = c := by
  have hab := cross a b ha hb (Or.inl hta)
  have hbc := symm (cross c b hc hb (Or.inl htc))
  have hcd := cross c d hc hd (Or.inl htc)
  have hda := symm (cross a d ha hd (Or.inl hta))
  cases no_four a b c d hab hbc hcd hda with
  | inl h => exact h
  | inr h => exact (hne h).elim

theorem filter_right_unique {α : Type} (R : α → α → Prop)
    (symm : ∀ {a b}, R a b → R b a)
    (no_four : ∀ a b c d, R a b → R b c → R c d → R d a → a = c ∨ b = d)
    (A B T : α → Prop)
    (cross : ∀ a b, A a → B b → (T a ∨ T b) → R a b)
    (a c : α) (ha : A a) (hc : A c) (hne : a ≠ c)
    (b d : α) (hb : B b) (hd : B d) (htb : T b) (htd : T d) : b = d := by
  have hab := cross a b ha hb (Or.inr htb)
  have hbc := symm (cross c b hc hb (Or.inr htb))
  have hcd := cross c d hc hd (Or.inr htd)
  have hda := symm (cross a d ha hd (Or.inr htd))
  cases no_four a b c d hab hbc hcd hda with
  | inl h => exact (hne h).elim
  | inr h => exact h

theorem double_star_exchange_of_implies (A B a d : Bool)
    (ha : a = true → A = true) (hd : d = true → B = true) :
    ((A && B) && (a || d)) = ((a && B) || (d && A)) := by
  cases A <;> cases B <;> cases a <;> cases d <;>
    first | rfl | exact Bool.noConfusion (ha rfl) | exact Bool.noConfusion (hd rfl)

end PEqualNP.Outside.L_meta_1031_aux.Exchange

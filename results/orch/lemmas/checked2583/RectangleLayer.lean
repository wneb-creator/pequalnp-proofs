import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.RectangleLayer

lemma rectangle_split (p l a b : Bool)
    (hp : p = true → a = true) (hl : l = true → b = true) :
    ((a && b) && (p || l)) = ((p && b) || (l && a)) := by
  cases p <;> cases l <;> simp_all

lemma rectangle_family_split (p l : Bool) (xs : List (Bool × Bool))
    (hp : ∀ x ∈ xs, p = true → x.1 = true)
    (hl : ∀ x ∈ xs, l = true → x.2 = true) :
    ((xs.any fun x => x.1 && x.2) && (p || l)) =
      ((p && xs.any Prod.snd) || (l && xs.any Prod.fst)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := rectangle_split p l x.1 x.2 (hp x (by simp)) (hl x (by simp))
    have hi := ih (fun y hy => hp y (by simp [hy])) (fun y hy => hl y (by simp [hy]))
    simp only [List.any_cons]
    have distrib (a b c : Bool) : ((a || b) && c) = ((a && c) || (b && c)) := by
      cases a <;> cases b <;> cases c <;> rfl
    rw [distrib, hx, hi]
    cases p <;> cases l <;> simp [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

lemma shared_centre_projection (p : Bool) (xs : List (Bool × Bool))
    (hp : ∀ x ∈ xs, p = true → x.1 = true) :
    (p && (xs.any fun x => x.1 && x.2)) = (p && xs.any Prod.snd) := by
  cases p
  · simp
  · simp only [Bool.true_and]
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      rw [List.any_cons, List.any_cons, hp x (by simp) rfl]
      simp only [Bool.true_and]
      rw [ih (fun y hy => hp y (by simp [hy]))]

lemma distinct_pair_selectors {P L : Type} [DecidableEq P] [DecidableEq L]
    (p p' : P) (l l' : L) (S : Finset (Sum P L))
    (hne : p ≠ p' ∨ l ≠ l')
    (hleft : ∀ x ∈ S, x = Sum.inl p ∨ x = Sum.inr l)
    (hright : ∀ x ∈ S, x = Sum.inl p' ∨ x = Sum.inr l') :
    S.card ≤ 1 := by
  rcases hne with hpp | hll
  · have hs : S ⊆ {Sum.inr l} := by
      intro x hx
      apply Finset.mem_singleton.mpr
      rcases hleft x hx with rfl | he
      · rcases hright (Sum.inl p) hx with he | he
        · exact False.elim (hpp (Sum.inl.inj he))
        · cases he
      · exact he
    exact (Finset.card_le_card hs).trans_eq (Finset.card_singleton _)
  · have hs : S ⊆ {Sum.inl p} := by
      intro x hx
      apply Finset.mem_singleton.mpr
      rcases hleft x hx with he | rfl
      · exact he
      · rcases hright (Sum.inr l) hx with he | he
        · cases he
        · exact False.elim (hll (Sum.inr.inj he))
    exact (Finset.card_le_card hs).trans_eq (Finset.card_singleton _)

end PEqualNP.Outside.L_meta_2583.RectangleLayer

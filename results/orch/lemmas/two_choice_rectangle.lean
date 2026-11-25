import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_meta_1031_aux.TwoChoiceRectangle

lemma factor_singleton {α : Type} [DecidableEq α] (A B C D : Finset α)
    (hAC : (A ∪ C).card = 2) (hAD : (A ∪ D).card = 2)
    (hBC : (B ∪ C).card = 2)
    (hrow : A ∪ C ≠ A ∪ D) (hcol : A ∪ C ≠ B ∪ C) :
    ∃ a, A = {a} := by
  have hle : A.card ≤ 2 := (Finset.card_le_card Finset.subset_union_left).trans_eq hAC
  have hzero : A.card ≠ 0 := by
    intro hz
    have he : A = ∅ := Finset.card_eq_zero.mp hz
    have hc : C.card = 2 := by simpa [he] using hAC
    have heq : C = B ∪ C := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
    apply hcol
    simpa [he] using heq
  have htwo : A.card ≠ 2 := by
    intro ht
    have h1 : A = A ∪ C := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    have h2 : A = A ∪ D := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    exact hrow (h1.symm.trans h2)
  exact Finset.card_eq_one.mp (by omega)

def HasEdge {α : Type} (G : SimpleGraph α) (S : Finset α) : Prop :=
  ∃ u ∈ S, ∃ v ∈ S, G.Adj u v

lemma hasEdge_pair {α : Type} [DecidableEq α] (G : SimpleGraph α) (a b : α) :
    HasEdge G {a, b} ↔ G.Adj a b := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (G.ne_of_adj huv rfl).elim
    · exact huv
    · exact huv.symm
    · exact (G.ne_of_adj huv rfl).elim
  · intro hab
    exact ⟨a, by simp, b, by simp, hab⟩

lemma corners_repeat {α : Type} [DecidableEq α] (G : SimpleGraph α)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B C D : Finset α)
    (hAC : (A ∪ C).card = 2) (hAD : (A ∪ D).card = 2)
    (hBC : (B ∪ C).card = 2) (hBD : (B ∪ D).card = 2)
    (eAC : HasEdge G (A ∪ C)) (eAD : HasEdge G (A ∪ D))
    (eBC : HasEdge G (B ∪ C)) (eBD : HasEdge G (B ∪ D)) :
    A ∪ C = A ∪ D ∨ A ∪ C = B ∪ C ∨ B ∪ C = B ∪ D ∨ A ∪ D = B ∪ D := by
  by_contra hn
  simp only [not_or] at hn
  obtain ⟨a, rfl⟩ := factor_singleton A B C D hAC hAD hBC hn.1 hn.2.1
  obtain ⟨b, rfl⟩ := factor_singleton B {a} C D hBC hBD hAC hn.2.2.1 (Ne.symm hn.2.1)
  obtain ⟨c, rfl⟩ := factor_singleton C D {a} {b}
    (by simpa [Finset.union_comm] using hAC)
    (by simpa [Finset.union_comm] using hBC)
    (by simpa [Finset.union_comm] using hAD)
    (by simpa [Finset.union_comm] using hn.2.1)
    (by simpa [Finset.union_comm] using hn.1)
  obtain ⟨d, rfl⟩ := factor_singleton D {c} {a} {b}
    (by simpa [Finset.union_comm] using hAD)
    (by simpa [Finset.union_comm] using hBD)
    (by simpa [Finset.union_comm] using hAC)
    (by simpa [Finset.union_comm] using hn.2.2.2)
    (by simpa [Finset.union_comm] using (Ne.symm hn.1))
  have hac : G.Adj a c := (hasEdge_pair G a c).mp (by simpa using eAC)
  have had : G.Adj a d := (hasEdge_pair G a d).mp (by simpa using eAD)
  have hbc : G.Adj b c := (hasEdge_pair G b c).mp (by simpa using eBC)
  have hbd : G.Adj b d := (hasEdge_pair G b d).mp (by simpa using eBD)
  rcases hfour a c b d hac hbc.symm hbd had.symm with hab | hcd
  · subst b
    exact hn.2.1 rfl
  · subst d
    exact hn.1 rfl


noncomputable def edgeCorners {α : Type} [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (A B C D : Finset α) : Finset (Finset α) := by
  classical
  exact ({A ∪ C, A ∪ D, B ∪ C, B ∪ D} : Finset (Finset α)).filter (fun S => S.card = 2 ∧ HasEdge G S)

lemma edgeCorners_card_le_three {α : Type} [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d) (A B C D : Finset α) :
    (edgeCorners G A B C D).card ≤ 3 := by
  classical
  let corners : Finset (Finset α) := {A ∪ C, A ∪ D, B ∪ C, B ∪ D}
  have hsub : edgeCorners G A B C D ⊆ corners := Finset.filter_subset _ _
  have hcard : corners.card ≤ 4 := Finset.card_le_four
  by_contra hn
  have heq : edgeCorners G A B C D = corners :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hp (S : Finset α) (hS : S ∈ corners) : S.card = 2 ∧ HasEdge G S := by
    rw [← heq] at hS
    exact (Finset.mem_filter.mp hS).2
  have hAC := hp (A ∪ C) (by simp [corners])
  have hAD := hp (A ∪ D) (by simp [corners])
  have hBC := hp (B ∪ C) (by simp [corners])
  have hBD := hp (B ∪ D) (by simp [corners])
  have hsmall : corners.card ≤ 3 := by
    rcases corners_repeat G hfour A B C D hAC.1 hAD.1 hBC.1 hBD.1
      hAC.2 hAD.2 hBC.2 hBD.2 with h | h | h | h
    · simpa [corners, h] using (Finset.card_le_three (a := A ∪ D) (b := B ∪ C) (c := B ∪ D))
    · have hs : corners ⊆ {A ∪ D, B ∪ C, B ∪ D} := by
        intro S hS
        simp only [corners, Finset.mem_insert, Finset.mem_singleton] at hS ⊢
        rcases hS with rfl | rfl | rfl | rfl <;> simp_all
      exact (Finset.card_le_card hs).trans Finset.card_le_three
    · simpa [corners, h] using (Finset.card_le_three (a := A ∪ C) (b := A ∪ D) (c := B ∪ D))
    · have hs : corners ⊆ {A ∪ C, B ∪ C, B ∪ D} := by
        intro S hS
        simp only [corners, Finset.mem_insert, Finset.mem_singleton] at hS ⊢
        rcases hS with rfl | rfl | rfl | rfl <;> simp_all
      exact (Finset.card_le_card hs).trans Finset.card_le_three
  rw [← heq] at hsmall
  exact hn hsmall


lemma HasEdge.card_ge_two {α : Type} [DecidableEq α] {G : SimpleGraph α}
    {S : Finset α} (h : HasEdge G S) : 2 ≤ S.card := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  have hpair : ({u, v} : Finset α).card = 2 := by simp [G.ne_of_adj huv]
  have hsub : ({u, v} : Finset α) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  rw [← hpair]
  exact Finset.card_le_card hsub

lemma two_choices_at_most_three {α : Type} [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B C D : Finset α) (E : Finset (Finset α))
    (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E, (A ⊆ S ∨ B ⊆ S) ∧ (C ⊆ S ∨ D ⊆ S))
    (hsound : ∀ S : Finset α, (A ⊆ S ∨ B ⊆ S) → (C ⊆ S ∨ D ⊆ S) →
      HasEdge G S) : E.card ≤ 3 := by
  classical
  have hsub : E ⊆ edgeCorners G A B C D := by
    intro S hS
    obtain ⟨hl, hr⟩ := haccept S hS
    have hcorner : ∃ T ∈ ({A ∪ C, A ∪ D, B ∪ C, B ∪ D} : Finset (Finset α)),
        T ⊆ S ∧ HasEdge G T := by
      rcases hl with hA | hB <;> rcases hr with hC | hD
      · exact ⟨A ∪ C, by simp, Finset.union_subset hA hC,
          hsound _ (Or.inl Finset.subset_union_left) (Or.inl Finset.subset_union_right)⟩
      · exact ⟨A ∪ D, by simp, Finset.union_subset hA hD,
          hsound _ (Or.inl Finset.subset_union_left) (Or.inr Finset.subset_union_right)⟩
      · exact ⟨B ∪ C, by simp, Finset.union_subset hB hC,
          hsound _ (Or.inr Finset.subset_union_left) (Or.inl Finset.subset_union_right)⟩
      · exact ⟨B ∪ D, by simp, Finset.union_subset hB hD,
          hsound _ (Or.inr Finset.subset_union_left) (Or.inr Finset.subset_union_right)⟩
    obtain ⟨T, hT, hTS, hEdge⟩ := hcorner
    have hEq : T = S := Finset.eq_of_subset_of_card_le hTS (by
      have := hEdge.card_ge_two
      have := hcard S hS
      omega)
    subst T
    exact Finset.mem_filter.mpr ⟨hT, hcard S hS, hEdge⟩
  exact (Finset.card_le_card hsub).trans (edgeCorners_card_le_three G hfour A B C D)


lemma three_monomials_at_most_three {α : Type} [DecidableEq α] (G : SimpleGraph α)
    (A B C : Finset α) (E : Finset (Finset α))
    (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E, A ⊆ S ∨ B ⊆ S ∨ C ⊆ S)
    (hsound : ∀ S : Finset α, (A ⊆ S ∨ B ⊆ S ∨ C ⊆ S) → HasEdge G S) :
    E.card ≤ 3 := by
  have hsub : E ⊆ {A, B, C} := by
    intro S hS
    have hEq (T : Finset α) (hTS : T ⊆ S) (hEdge : HasEdge G T) : T = S :=
      Finset.eq_of_subset_of_card_le hTS (by
        have := hEdge.card_ge_two
        have := hcard S hS
        omega)
    rcases haccept S hS with hA | hB | hC
    · have he := hEq A hA (hsound A (Or.inl Finset.Subset.rfl))
      simp [← he]
    · have he := hEq B hB (hsound B (Or.inr (Or.inl Finset.Subset.rfl)))
      simp [← he]
    · have he := hEq C hC (hsound C (Or.inr (Or.inr Finset.Subset.rfl)))
      simp [← he]
  exact (Finset.card_le_card hsub).trans Finset.card_le_three

def pattern {α : Type} [DecidableEq α] (A B C D K : Finset α)
    (p q r u : Prop) (S : Finset α) : Prop :=
  K ⊆ S ∧ (r → A ⊆ S ∨ B ⊆ S) ∧
    (u → ((C ⊆ S ∧ (p → A ⊆ S ∨ B ⊆ S)) ∨
      (D ⊆ S ∧ (q → A ⊆ S ∨ B ⊆ S))))

lemma two_or_pattern_at_most_three {α : Type} [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B C D K : Finset α) (p q r u : Prop) (E : Finset (Finset α))
    (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E, pattern A B C D K p q r u S)
    (hsound : ∀ S : Finset α, pattern A B C D K p q r u S → HasEdge G S) :
    E.card ≤ 3 := by
  classical
  by_cases hu : u
  · by_cases hr : r
    · apply two_choices_at_most_three G hfour (K ∪ A) (K ∪ B) C D E hcard
      · intro S hS
        have h := haccept S hS
        simp only [pattern, hr, hu, true_implies, Finset.union_subset_iff] at h ⊢
        aesop
      · intro S hl hrS
        apply hsound S
        simp only [pattern, hr, hu, true_implies, Finset.union_subset_iff] at hl ⊢
        aesop
    · by_cases hp : p
      · by_cases hq : q
        · apply two_choices_at_most_three G hfour (K ∪ A) (K ∪ B) C D E hcard
          · intro S hS
            have h := haccept S hS
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies,
              Finset.union_subset_iff] at h ⊢
            aesop
          · intro S hl hrS
            apply hsound S
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies,
              Finset.union_subset_iff] at hl ⊢
            aesop
        · apply three_monomials_at_most_three G ((K ∪ A) ∪ C) ((K ∪ B) ∪ C) (K ∪ D) E hcard
          · intro S hS
            have h := haccept S hS
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies, and_true,
              Finset.union_subset_iff] at h ⊢
            aesop
          · intro S h
            apply hsound S
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies, and_true,
              Finset.union_subset_iff] at h ⊢
            aesop
      · by_cases hq : q
        · apply three_monomials_at_most_three G (K ∪ C) ((K ∪ A) ∪ D) ((K ∪ B) ∪ D) E hcard
          · intro S hS
            have h := haccept S hS
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies, and_true,
              Finset.union_subset_iff] at h ⊢
            aesop
          · intro S h
            apply hsound S
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies, and_true,
              Finset.union_subset_iff] at h ⊢
            aesop
        · apply three_monomials_at_most_three G (K ∪ C) (K ∪ D) (K ∪ D) E hcard
          · intro S hS
            have h := haccept S hS
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies, and_true,
              Finset.union_subset_iff] at h ⊢
            aesop
          · intro S h
            apply hsound S
            simp only [pattern, hr, hu, hp, hq, true_implies, false_implies, and_true,
              Finset.union_subset_iff] at h ⊢
            aesop
  · by_cases hr : r
    · apply three_monomials_at_most_three G (K ∪ A) (K ∪ B) (K ∪ B) E hcard
      · intro S hS
        have h := haccept S hS
        simp only [pattern, hr, hu, true_implies, false_implies, and_true,
          Finset.union_subset_iff] at h ⊢
        aesop
      · intro S h
        apply hsound S
        simp only [pattern, hr, hu, true_implies, false_implies, and_true,
          Finset.union_subset_iff] at h ⊢
        aesop
    · apply three_monomials_at_most_three G K K K E hcard
      · intro S hS
        have h := haccept S hS
        simp only [pattern, hr, hu, false_implies, and_true] at h
        exact Or.inl h
      · intro S h
        apply hsound S
        simpa only [pattern, hr, hu, false_implies, and_true, or_self] using h

end PEqualNP.Outside.L_meta_1031_aux.TwoChoiceRectangle

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD

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


namespace PEqualNP.Outside.L_meta_1031_aux.TwoOrBridge

open TwoChoiceRectangle

def support (n : ℕ) (atoms : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val ∈ atoms)

def input (n : ℕ) (S : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ S))

def meet (values : List Bool) (atoms : List ℕ) : Bool :=
  atoms.all (fun i => values.getD i false)

def bounded (n : ℕ) (atoms : List ℕ) : Prop := ∀ i ∈ atoms, i < n

lemma input_length (n : ℕ) (S : Finset (Fin n)) : (input n S).length = n := by
  simp [input]

lemma input_get (n : ℕ) (S : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    (input n S).getD i false = decide ((⟨i, hi⟩ : Fin n) ∈ S) := by
  simp [input, hi]

lemma support_subset (n : ℕ) (atoms : List ℕ) (S : Finset (Fin n)) :
    support n atoms ⊆ S ↔ ∀ i : Fin n, i.val ∈ atoms → i ∈ S := by
  simp only [support, Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]

lemma meet_input (n : ℕ) (atoms : List ℕ) (hb : bounded n atoms) (S : Finset (Fin n)) :
    meet (input n S) atoms = true ↔ support n atoms ⊆ S := by
  rw [support_subset]
  simp only [meet, List.all_eq_true]
  constructor
  · intro h i hi
    have hv := h i.val hi
    rw [input_get n S i.val i.isLt] at hv
    exact of_decide_eq_true hv
  · intro h i hi
    rw [input_get n S i (hb i hi)]
    exact decide_eq_true (h ⟨i, hb i hi⟩ hi)

lemma meet_append_one (n : ℕ) (atoms : List ℕ) (hb : bounded (n + 1) atoms)
    (S : Finset (Fin n)) (v : Bool) :
    meet (input n S ++ [v]) atoms = true ↔
      support n atoms ⊆ S ∧ (n ∈ atoms → v = true) := by
  rw [support_subset]
  simp only [meet, List.all_eq_true]
  constructor
  · intro h
    constructor
    · intro i hi
      have hv := h i.val hi
      rw [List.getD_append _ _ _ _ (by simp [input_length]),
        input_get n S i.val i.isLt] at hv
      exact of_decide_eq_true hv
    · intro hn
      have hv := h n hn
      simpa [List.getD_eq_getElem?_getD, input_length] using hv
  · rintro ⟨hS, hv⟩ i hi
    by_cases hin : i < n
    · rw [List.getD_append _ _ _ _ (by simpa [input_length] using hin), input_get n S i hin]
      exact decide_eq_true (hS ⟨i, hin⟩ hi)
    · have heq : i = n := by have := hb i hi; omega
      subst i
      simpa [List.getD_eq_getElem?_getD, input_length] using hv hi

lemma meet_append_two (n : ℕ) (atoms : List ℕ) (hb : bounded (n + 2) atoms)
    (S : Finset (Fin n)) (v w : Bool) :
    meet (input n S ++ [v] ++ [w]) atoms = true ↔
      support n atoms ⊆ S ∧ (n ∈ atoms → v = true) ∧ (n + 1 ∈ atoms → w = true) := by
  rw [support_subset]
  simp only [meet, List.all_eq_true]
  constructor
  · intro h
    constructor
    · intro i hi
      have hv := h i.val hi
      rw [List.getD_append _ _ _ _ (by
          simpa only [List.length_append, List.length_singleton, input_length]
            using Nat.lt_succ_of_lt i.isLt),
        List.getD_append _ _ _ _ (by simp [input_length]),
        input_get n S i.val i.isLt] at hv
      exact of_decide_eq_true hv
    · constructor
      · intro hn
        have hv := h n hn
        simpa [List.getD_eq_getElem?_getD, input_length] using hv
      · intro hn
        have hv := h (n + 1) hn
        simpa [List.getD_eq_getElem?_getD, input_length] using hv
  · rintro ⟨hS, hv, hw⟩ i hi
    by_cases hin : i < n
    · rw [List.getD_append _ _ _ _ (by
          simpa only [List.length_append, List.length_singleton, input_length]
            using Nat.lt_succ_of_lt hin),
        List.getD_append _ _ _ _ (by simpa [input_length] using hin), input_get n S i hin]
      exact decide_eq_true (hS ⟨i, hin⟩ hi)
    · have heq : i = n ∨ i = n + 1 := by have := hb i hi; omega
      rcases heq with rfl | rfl
      · simpa [List.getD_eq_getElem?_getD, input_length] using hv hi
      · simpa [List.getD_eq_getElem?_getD, input_length] using hw hi


def evalTwo (a b c d out : List ℕ) (x : List Bool) : Bool :=
  let v := meet x a || meet x b
  let w := meet (x ++ [v]) c || meet (x ++ [v]) d
  meet (x ++ [v] ++ [w]) out

lemma evalTwo_pattern (n : ℕ) (a b c d out : List ℕ)
    (ha : bounded n a) (hb : bounded n b)
    (hc : bounded (n + 1) c) (hd : bounded (n + 1) d)
    (hout : bounded (n + 2) out) (S : Finset (Fin n)) :
    evalTwo a b c d out (input n S) = true ↔
      pattern (support n a) (support n b) (support n c) (support n d) (support n out)
        (n ∈ c) (n ∈ d) (n ∈ out) (n + 1 ∈ out) S := by
  let v := meet (input n S) a || meet (input n S) b
  let w := meet (input n S ++ [v]) c || meet (input n S ++ [v]) d
  have hv : v = true ↔ support n a ⊆ S ∨ support n b ⊆ S := by
    simp only [v, Bool.or_eq_true, meet_input n a ha S, meet_input n b hb S]
  have hw : w = true ↔
      (support n c ⊆ S ∧ (n ∈ c → support n a ⊆ S ∨ support n b ⊆ S)) ∨
      (support n d ⊆ S ∧ (n ∈ d → support n a ⊆ S ∨ support n b ⊆ S)) := by
    simp only [w, Bool.or_eq_true, meet_append_one n c hc S v, meet_append_one n d hd S v, hv]
  change meet (input n S ++ [v] ++ [w]) out = true ↔ _
  rw [meet_append_two n out hout S v w]
  simp only [pattern, hv, hw]

theorem two_or_program_at_most_three (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (a b c d out : List ℕ)
    (ha : bounded n a) (hb : bounded n b)
    (hc : bounded (n + 1) c) (hd : bounded (n + 1) d)
    (hout : bounded (n + 2) out) (E : Finset (Finset (Fin n)))
    (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E, evalTwo a b c d out (input n S) = true)
    (hsound : ∀ S : Finset (Fin n), evalTwo a b c d out (input n S) = true → HasEdge G S) :
    E.card ≤ 3 := by
  apply two_or_pattern_at_most_three G hfour
    (support n a) (support n b) (support n c) (support n d) (support n out)
    (n ∈ c) (n ∈ d) (n ∈ out) (n + 1 ∈ out) E hcard
  · intro S hS
    exact (evalTwo_pattern n a b c d out ha hb hc hd hout S).mp (haccept S hS)
  · intro S hp
    exact hsound S ((evalTwo_pattern n a b c d out ha hb hc hd hout S).mpr hp)

end PEqualNP.Outside.L_meta_1031_aux.TwoOrBridge


namespace PEqualNP.Outside.L_meta_1031_aux.FirstOrDeletion

def meet (values : List Bool) (atoms : List Nat) : Bool :=
  atoms.all (fun i => values.getD i false)

def step (values : List Bool) (g : List Nat × List Nat) : List Bool :=
  values ++ [meet values g.1 || meet values g.2]

def wires (program : List (List Nat × List Nat)) (values : List Bool) : List Bool :=
  program.foldl step values

def eval (program : List (List Nat × List Nat)) (output : List Nat) (x : List Bool) : Bool :=
  meet (wires program x) output

def bounded (n : Nat) (atoms : List Nat) : Prop := ∀ i ∈ atoms, i < n

def atom (n : Nat) (replacement : List Nat) (i : Nat) : List Nat :=
  if i < n then [i] else if i = n then replacement else [i - 1]

def rewrite (n : Nat) (replacement atoms : List Nat) : List Nat :=
  atoms.flatMap (atom n replacement)

def rewriteGate (n : Nat) (replacement : List Nat) (g : List Nat × List Nat) : List Nat × List Nat :=
  (rewrite n replacement g.1, rewrite n replacement g.2)

def Rel (n : Nat) (replacement : List Nat) (old fresh : List Bool) : Prop :=
  ∀ i, old.getD i false = meet fresh (atom n replacement i)

theorem meet_append (values : List Bool) (a b : List Nat) :
    meet values (a ++ b) = (meet values a && meet values b) := by
  simp [meet]

theorem meet_singleton (values : List Bool) (i : Nat) :
    meet values [i] = values.getD i false := by simp [meet]

theorem meet_extend (values suffix : List Bool) (atoms : List Nat)
    (h : bounded values.length atoms) : meet (values ++ suffix) atoms = meet values atoms := by
  induction atoms with
  | nil => rfl
  | cons i atoms ih =>
    have hi := h i (by simp)
    have ht : bounded values.length atoms := fun j hj => h j (by simp [hj])
    change ((values ++ suffix).getD i false && meet (values ++ suffix) atoms) =
      (values.getD i false && meet values atoms)
    rw [List.getD_append values suffix false i hi, ih ht]

theorem getD_append_one (values : List Bool) (v : Bool) (i : Nat) :
    (values ++ [v]).getD i false =
      if i < values.length then values.getD i false else if i = values.length then v else false := by
  by_cases hi : i < values.length
  · simp only [hi, ite_true]
    exact List.getD_append values [v] false i hi
  · by_cases he : i = values.length
    · subst i
      simp [List.getD_eq_getElem?_getD]
    · simp only [hi, he, ite_false]
      apply List.getD_eq_default
      simp only [List.length_append, List.length_singleton]
      omega

theorem rel_initial (n : Nat) (replacement : List Nat) (x : List Bool) (hx : x.length = n) :
    Rel n replacement (x ++ [meet x replacement]) x := by
  intro i
  rw [getD_append_one, hx]
  by_cases hi : i < n
  · simp [atom, hi, meet_singleton]
  · by_cases he : i = n
    · simp [atom, he]
    · simp only [atom, hi, he, ite_false, meet_singleton]
      symm
      apply List.getD_eq_default
      omega

theorem meet_rewrite {n : Nat} {replacement : List Nat} {old fresh : List Bool}
    (hr : Rel n replacement old fresh) (atoms : List Nat) :
    meet fresh (rewrite n replacement atoms) = meet old atoms := by
  induction atoms with
  | nil => rfl
  | cons i atoms ih =>
    change meet fresh (atom n replacement i ++ rewrite n replacement atoms) =
      (old.getD i false && meet old atoms)
    rw [meet_append, ← hr i, ih]

theorem rel_append {n : Nat} {replacement : List Nat} {old fresh : List Bool}
    (hr : Rel n replacement old fresh) (hlen : old.length = fresh.length + 1)
    (hn : n ≤ fresh.length) (hb : bounded n replacement) (v : Bool) :
    Rel n replacement (old ++ [v]) (fresh ++ [v]) := by
  intro i
  by_cases hi : i < n
  · have hio : i < old.length := by omega
    have hif : i < fresh.length := by omega
    simp only [atom, hi, ite_true, meet_singleton]
    rw [List.getD_append old [v] false i hio, List.getD_append fresh [v] false i hif]
    simpa only [atom, hi, ite_true, meet_singleton] using hr i
  · by_cases he : i = n
    · subst i
      have hno : n < old.length := by omega
      have hbf : bounded fresh.length replacement := fun j hj => Nat.lt_of_lt_of_le (hb j hj) hn
      simp only [atom, Nat.lt_irrefl, ite_false, ite_true]
      rw [List.getD_append old [v] false n hno, meet_extend fresh [v] replacement hbf]
      simpa only [atom, Nat.lt_irrefl, ite_false, ite_true] using hr n
    · simp only [atom, hi, he, ite_false, meet_singleton]
      rw [getD_append_one, getD_append_one]
      by_cases hio : i < old.length
      · have hif : i - 1 < fresh.length := by omega
        simp only [hio, hif, ite_true]
        simpa only [atom, hi, he, ite_false, meet_singleton] using hr i
      · by_cases hioeq : i = old.length
        · subst i
          have hifeq : old.length - 1 = fresh.length := by omega
          simp [hifeq]
        · have hif : ¬ i - 1 < fresh.length := by omega
          have hifeq : i - 1 ≠ fresh.length := by omega
          simp [hio, hioeq, hif, hifeq]

theorem wires_length (program : List (List Nat × List Nat)) (values : List Bool) :
    (wires program values).length = values.length + program.length := by
  induction program generalizing values with
  | nil => simp [wires]
  | cons g gs ih =>
    change (wires gs (step values g)).length = _
    rw [ih]
    simp [step]
    omega

theorem rel_wires {n : Nat} {replacement : List Nat} (program : List (List Nat × List Nat))
    (old fresh : List Bool) (hr : Rel n replacement old fresh)
    (hlen : old.length = fresh.length + 1) (hn : n ≤ fresh.length)
    (hb : bounded n replacement) :
    Rel n replacement (wires program old)
      (wires (program.map (rewriteGate n replacement)) fresh) := by
  induction program generalizing old fresh with
  | nil => exact hr
  | cons g gs ih =>
    change Rel n replacement (wires gs (step old g))
      (wires (gs.map (rewriteGate n replacement)) (step fresh (rewriteGate n replacement g)))
    have hstep : step fresh (rewriteGate n replacement g) =
        fresh ++ [meet old g.1 || meet old g.2] := by
      simp only [step, rewriteGate, meet_rewrite hr]
    rw [hstep]
    apply ih
    · exact rel_append hr hlen hn hb _
    · simp [step, hlen]
    · simp only [List.length_append, List.length_singleton]
      omega

theorem delete_first_eval (n : Nat) (b output : List Nat)
    (program : List (List Nat × List Nat)) (x : List Bool) (hx : x.length = n)
    (hb : bounded n b) :
    eval (program.map (rewriteGate n b)) (rewrite n b output) x =
      meet (wires program (x ++ [meet x b])) output := by
  apply meet_rewrite
  apply rel_wires program (x ++ [meet x b]) x (rel_initial n b x hx)
  · simp
  · omega
  · exact hb

theorem meet_mono {a b : List Bool} (h : ∀ i, a.getD i false = true → b.getD i false = true)
    (atoms : List Nat) : meet a atoms = true → meet b atoms = true := by
  simp only [meet, List.all_eq_true]
  intro ha i hi
  exact h i (ha i hi)

theorem append_mono {a b : List Bool} (hlen : a.length = b.length)
    (h : ∀ i, a.getD i false = true → b.getD i false = true)
    {u v : Bool} (huv : u = true → v = true) :
    ∀ i, (a ++ [u]).getD i false = true → (b ++ [v]).getD i false = true := by
  intro i
  rw [getD_append_one, getD_append_one, ← hlen]
  by_cases hi : i < a.length
  · simpa only [hi, ite_true] using h i
  · by_cases he : i = a.length
    · subst i
      simpa using huv
    · simp [hi, he]

theorem wires_mono (program : List (List Nat × List Nat)) (a b : List Bool)
    (hlen : a.length = b.length)
    (h : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (wires program a).getD i false = true → (wires program b).getD i false = true := by
  induction program generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    change ∀ i, (wires gs (step a g)).getD i false = true →
      (wires gs (step b g)).getD i false = true
    apply ih
    · simp [step, hlen]
    · apply append_mono hlen h
      simp only [Bool.or_eq_true]
      intro hg
      exact hg.imp (meet_mono h g.1) (meet_mono h g.2)

theorem delete_first_below (n : Nat) (a b output : List Nat)
    (program : List (List Nat × List Nat)) (x : List Bool) (hx : x.length = n)
    (hb : bounded n b) :
    eval (program.map (rewriteGate n b)) (rewrite n b output) x = true →
      eval ((a,b) :: program) output x = true := by
  rw [delete_first_eval n b output program x hx hb]
  change meet (wires program (x ++ [meet x b])) output = true →
    meet (wires program (x ++ [meet x a || meet x b])) output = true
  apply meet_mono
  apply wires_mono program _ _ (by simp)
  apply append_mono rfl (fun _ h => h)
  intro h
  simp [h]

theorem delete_first_agrees (n : Nat) (a b output : List Nat)
    (program : List (List Nat × List Nat)) (x : List Bool) (hx : x.length = n)
    (hb : bounded n b) (ha : meet x a = false) :
    eval (program.map (rewriteGate n b)) (rewrite n b output) x =
      eval ((a,b) :: program) output x := by
  rw [delete_first_eval n b output program x hx hb]
  change meet (wires program (x ++ [meet x b])) output =
    meet (wires program (x ++ [meet x a || meet x b])) output
  simp [ha]

theorem rewrite_bounded {n k : Nat} {replacement atoms : List Nat}
    (hb : bounded n replacement) (ha : bounded (n + 1 + k) atoms) :
    bounded (n + k) (rewrite n replacement atoms) := by
  intro i hi
  obtain ⟨j, hj, hij⟩ := List.mem_flatMap.mp hi
  have hjb := ha j hj
  by_cases hjn : j < n
  · have heq : i = j := by simpa [atom, hjn] using hij
    omega
  · by_cases he : j = n
    · have hbmem : i ∈ replacement := by simpa [atom, hjn, he] using hij
      have := hb i hbmem
      omega
    · have heq : i = j - 1 := by simpa [atom, hjn, he] using hij
      omega

theorem rewrite_length (n : Nat) (replacement : List Nat) (program : List (List Nat × List Nat)) :
    (program.map (rewriteGate n replacement)).length = program.length := by simp

def wellFormed (n : Nat) (program : List (List Nat × List Nat)) : Prop :=
  ∀ j < program.length,
    bounded (n + j) (program.getD j ([], [])).1 ∧
    bounded (n + j) (program.getD j ([], [])).2

theorem rewrite_wellFormed {n : Nat} {replacement : List Nat}
    (program : List (List Nat × List Nat)) (hb : bounded n replacement)
    (hwf : wellFormed (n + 1) program) :
    wellFormed n (program.map (rewriteGate n replacement)) := by
  intro j hj
  have hjold : j < program.length := by simpa using hj
  obtain ⟨ha, hc⟩ := hwf j hjold
  have hget : (program.map (rewriteGate n replacement)).getD j ([], []) =
      rewriteGate n replacement (program.getD j ([], [])) := by
    simpa [rewriteGate, rewrite] using
      List.getD_map program ([], []) (n := j) (rewriteGate n replacement)
  rw [hget]
  exact ⟨rewrite_bounded hb ha, rewrite_bounded hb hc⟩

theorem deleted_positive_requires_branch (n : Nat) (a b output : List Nat)
    (program : List (List Nat × List Nat)) (x : List Bool) (hx : x.length = n)
    (hb : bounded n b)
    (hold : eval ((a,b) :: program) output x = true)
    (hnew : eval (program.map (rewriteGate n b)) (rewrite n b output) x = false) :
    meet x a = true := by
  cases ha : meet x a with
  | true => rfl
  | false =>
    have h := delete_first_agrees n a b output program x hx hb ha
    rw [hold, hnew] at h
    exact Bool.noConfusion h

def pairInput {n : Nat} (u v : Fin n) : List Bool :=
  List.ofFn (fun w : Fin n => decide (w = u ∨ w = v))

theorem branch_pair_unique {n : Nat} (a : List Nat) (i j u v : Fin n)
    (hi : i.val ∈ a) (hj : j.val ∈ a) (hne : i ≠ j)
    (ha : meet (pairInput u v) a = true) :
    (u = i ∧ v = j) ∨ (u = j ∧ v = i) := by
  have hival := List.all_eq_true.mp ha i.val hi
  have hjval := List.all_eq_true.mp ha j.val hj
  have hipair : i = u ∨ i = v := by
    simpa [pairInput, List.getD_eq_getElem?_getD] using hival
  have hjpair : j = u ∨ j = v := by
    simpa [pairInput, List.getD_eq_getElem?_getD] using hjval
  rcases hipair with hiu | hiv <;> rcases hjpair with hju | hjv
  · exact False.elim (hne (hiu.trans hju.symm))
  · exact Or.inl ⟨hiu.symm, hjv.symm⟩
  · exact Or.inr ⟨hju.symm, hiv.symm⟩
  · exact False.elim (hne (hiv.trans hjv.symm))

theorem lost_pair_unique (n : Nat) (a b output : List Nat)
    (program : List (List Nat × List Nat)) (hb : bounded n b)
    (i j : Fin n) (hi : i.val ∈ a) (hj : j.val ∈ a) (hne : i ≠ j)
    (u v : Fin n)
    (hold : eval ((a,b) :: program) output (pairInput u v) = true)
    (hnew : eval (program.map (rewriteGate n b)) (rewrite n b output) (pairInput u v) = false) :
    (u = i ∧ v = j) ∨ (u = j ∧ v = i) := by
  exact branch_pair_unique a i j u v hi hj hne
    (deleted_positive_requires_branch n a b output program (pairInput u v)
      (by simp [pairInput]) hb hold hnew)

end PEqualNP.Outside.L_meta_1031_aux.FirstOrDeletion

namespace PEqualNP.Outside.L_meta_1031_aux.FirstOrReduction

open FirstOrDeletion

theorem first_left_unique (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : ∀ i j k l, G.Adj i j → G.Adj j k → G.Adj k l → G.Adj l i →
      i = k ∨ j = l)
    (a b c d e f out : List Nat)
    (hb : bounded n b) (hc : bounded (n + 1) c) (hd : bounded (n + 1) d)
    (he : bounded (n + 2) e) (hf : bounded (n + 2) f) (ho : bounded (n + 3) out)
    (E : Finset (Finset (Fin n))) (hsize : 5 ≤ E.card)
    (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E,
      eval [(a,b),(c,d),(e,f)] out (TwoOrBridge.input n S) = true)
    (hsound : ∀ S : Finset (Fin n),
      eval [(a,b),(c,d),(e,f)] out (TwoOrBridge.input n S) = true →
        TwoChoiceRectangle.HasEdge G S)
    (i j : Fin n) (hi : i.val ∈ a) (hj : j.val ∈ a) : i = j := by
  classical
  by_contra hne
  let E' := E.erase {i,j}
  have herase : E.card ≤ E'.card + 1 := by
    by_cases hm : ({i,j} : Finset (Fin n)) ∈ E
    · simp only [E', Finset.card_erase_of_mem hm]
      omega
    · simp [E', Finset.erase_eq_of_notMem hm]
  have haccept' : ∀ S ∈ E',
      TwoOrBridge.evalTwo (rewrite n b c) (rewrite n b d)
        (rewrite n b e) (rewrite n b f) (rewrite n b out) (TwoOrBridge.input n S) = true := by
    intro S hS
    have hSE : S ∈ E := Finset.mem_of_mem_erase hS
    have hnot : S ≠ ({i,j} : Finset (Fin n)) := (Finset.mem_erase.mp hS).1
    have hfalse : meet (TwoOrBridge.input n S) a = false := by
      cases hval : meet (TwoOrBridge.input n S) a with
      | false => rfl
      | true =>
        have hival := List.all_eq_true.mp hval i.val hi
        have hjval := List.all_eq_true.mp hval j.val hj
        have hiS : i ∈ S := by
          simpa [TwoOrBridge.input, List.getD_eq_getElem?_getD] using hival
        have hjS : j ∈ S := by
          simpa [TwoOrBridge.input, List.getD_eq_getElem?_getD] using hjval
        have hsub : ({i,j} : Finset (Fin n)) ⊆ S := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have hpair : ({i,j} : Finset (Fin n)).card = 2 := by simp [hne]
        have heq : ({i,j} : Finset (Fin n)) = S :=
          Finset.eq_of_subset_of_card_le hsub (by rw [hcard S hSE, hpair])
        exact False.elim (hnot heq.symm)
    have hagree := delete_first_agrees n a b out [(c,d),(e,f)] (TwoOrBridge.input n S)
      (by simp [TwoOrBridge.input]) hb hfalse
    have hval := haccept S hSE
    rw [← hagree] at hval
    exact hval
  have hsound' : ∀ S : Finset (Fin n),
      TwoOrBridge.evalTwo (rewrite n b c) (rewrite n b d)
        (rewrite n b e) (rewrite n b f) (rewrite n b out) (TwoOrBridge.input n S) = true →
          TwoChoiceRectangle.HasEdge G S := by
    intro S hS
    apply hsound S
    apply delete_first_below n a b out [(c,d),(e,f)] (TwoOrBridge.input n S)
      (by simp [TwoOrBridge.input]) hb
    exact hS
  have hbound : E'.card ≤ 3 := TwoOrBridge.two_or_program_at_most_three n G hfour
    (rewrite n b c) (rewrite n b d) (rewrite n b e) (rewrite n b f) (rewrite n b out)
    (rewrite_bounded (k := 0) hb (by simpa using hc))
    (rewrite_bounded (k := 0) hb (by simpa using hd))
    (rewrite_bounded (k := 1) hb (by simpa [Nat.add_assoc] using he))
    (rewrite_bounded (k := 1) hb (by simpa [Nat.add_assoc] using hf))
    (rewrite_bounded (k := 2) hb (by simpa [Nat.add_assoc] using ho)) E'
    (fun S hS => hcard S (Finset.mem_of_mem_erase hS)) haccept' hsound'
  omega

theorem first_swap (a b out : List Nat) (program : List (List Nat × List Nat))
    (x : List Bool) : eval ((a,b)::program) out x = eval ((b,a)::program) out x := by
  change meet (program.foldl step (x ++ [meet x a || meet x b])) out =
    meet (program.foldl step (x ++ [meet x b || meet x a])) out
  rw [Bool.or_comm (meet x a) (meet x b)]

theorem first_right_unique (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : ∀ i j k l, G.Adj i j → G.Adj j k → G.Adj k l → G.Adj l i →
      i = k ∨ j = l)
    (a b c d e f out : List Nat)
    (ha : bounded n a) (hc : bounded (n + 1) c) (hd : bounded (n + 1) d)
    (he : bounded (n + 2) e) (hf : bounded (n + 2) f) (ho : bounded (n + 3) out)
    (E : Finset (Finset (Fin n))) (hsize : 5 ≤ E.card)
    (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E,
      eval [(a,b),(c,d),(e,f)] out (TwoOrBridge.input n S) = true)
    (hsound : ∀ S : Finset (Fin n),
      eval [(a,b),(c,d),(e,f)] out (TwoOrBridge.input n S) = true →
        TwoChoiceRectangle.HasEdge G S)
    (i j : Fin n) (hi : i.val ∈ b) (hj : j.val ∈ b) : i = j := by
  apply first_left_unique n G hfour b a c d e f out ha hc hd he hf ho E hsize hcard
  · intro S hS
    rw [← first_swap a b out [(c,d),(e,f)] (TwoOrBridge.input n S)]
    exact haccept S hS
  · intro S hS
    apply hsound S
    rw [first_swap a b out [(c,d),(e,f)] (TwoOrBridge.input n S)]
    exact hS
  · exact hi
  · exact hj

end PEqualNP.Outside.L_meta_1031_aux.FirstOrReduction

namespace PEqualNP.Outside.L_meta_1031_aux.FirstOrReduction

open FirstOrDeletion

theorem first_not_dominated (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : ∀ i j k l, G.Adj i j → G.Adj j k → G.Adj k l → G.Adj l i →
      i = k ∨ j = l)
    (a b c d e f out : List Nat)
    (hb : bounded n b) (hc : bounded (n + 1) c) (hd : bounded (n + 1) d)
    (he : bounded (n + 2) e) (hf : bounded (n + 2) f) (ho : bounded (n + 3) out)
    (E : Finset (Finset (Fin n))) (hsize : 5 ≤ E.card)
    (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E,
      eval [(a,b),(c,d),(e,f)] out (TwoOrBridge.input n S) = true)
    (hsound : ∀ S : Finset (Fin n),
      eval [(a,b),(c,d),(e,f)] out (TwoOrBridge.input n S) = true →
        TwoChoiceRectangle.HasEdge G S)
    (hdom : ∀ S : Finset (Fin n),
      (meet (TwoOrBridge.input n S) a || meet (TwoOrBridge.input n S) b) =
        meet (TwoOrBridge.input n S) b) : False := by
  have heval (S : Finset (Fin n)) :
      TwoOrBridge.evalTwo (rewrite n b c) (rewrite n b d)
        (rewrite n b e) (rewrite n b f) (rewrite n b out) (TwoOrBridge.input n S) =
      eval [(a,b),(c,d),(e,f)] out (TwoOrBridge.input n S) := by
    have heq := delete_first_eval n b out [(c,d),(e,f)] (TwoOrBridge.input n S)
      (by simp [TwoOrBridge.input]) hb
    change eval ([(c,d),(e,f)].map (rewriteGate n b)) (rewrite n b out)
      (TwoOrBridge.input n S) = _
    rw [heq]
    change meet (wires [(c,d),(e,f)]
      (TwoOrBridge.input n S ++ [meet (TwoOrBridge.input n S) b])) out =
      meet (wires [(c,d),(e,f)] (TwoOrBridge.input n S ++
        [meet (TwoOrBridge.input n S) a || meet (TwoOrBridge.input n S) b])) out
    rw [hdom S]
  have hbound : E.card ≤ 3 := TwoOrBridge.two_or_program_at_most_three n G hfour
    (rewrite n b c) (rewrite n b d) (rewrite n b e) (rewrite n b f) (rewrite n b out)
    (rewrite_bounded (k := 0) hb (by simpa using hc))
    (rewrite_bounded (k := 0) hb (by simpa using hd))
    (rewrite_bounded (k := 1) hb (by simpa [Nat.add_assoc] using he))
    (rewrite_bounded (k := 1) hb (by simpa [Nat.add_assoc] using hf))
    (rewrite_bounded (k := 2) hb (by simpa [Nat.add_assoc] using ho)) E hcard
    (fun S hS => by rw [heval]; exact haccept S hS)
    (fun S hS => hsound S (by rw [← heval]; exact hS))
  omega

theorem meet_of_unique (xs : List Nat) (i : Nat) (hi : i ∈ xs)
    (hunique : ∀ j ∈ xs, j = i) (x : List Bool) : meet x xs = x.getD i false := by
  cases hv : x.getD i false with
  | false =>
    cases hm : meet x xs with
    | false => rfl
    | true =>
      have := List.all_eq_true.mp hm i hi
      rw [hv] at this
      contradiction
  | true =>
    apply List.all_eq_true.mpr
    intro j hj
    rw [hunique j hj, hv]

theorem first_distinct_literals (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : ∀ i j k l, G.Adj i j → G.Adj j k → G.Adj k l → G.Adj l i →
      i = k ∨ j = l)
    (a b c d e f out : List Nat)
    (ha : bounded n a) (hb : bounded n b)
    (hc : bounded (n + 1) c) (hd : bounded (n + 1) d)
    (he : bounded (n + 2) e) (hf : bounded (n + 2) f) (ho : bounded (n + 3) out)
    (E : Finset (Finset (Fin n))) (hsize : 5 ≤ E.card)
    (hcard : ∀ S ∈ E, S.card = 2)
    (haccept : ∀ S ∈ E,
      eval [(a,b),(c,d),(e,f)] out (TwoOrBridge.input n S) = true)
    (hsound : ∀ S : Finset (Fin n),
      eval [(a,b),(c,d),(e,f)] out (TwoOrBridge.input n S) = true →
        TwoChoiceRectangle.HasEdge G S) :
    ∃ i j : Fin n, i ≠ j ∧
      (∀ x, meet x a = x.getD i.val false) ∧
      (∀ x, meet x b = x.getD j.val false) := by
  have hbad := first_not_dominated n G hfour a b c d e f out hb hc hd he hf ho
    E hsize hcard haccept hsound
  have hbadSwap : ¬ (∀ S : Finset (Fin n),
      (meet (TwoOrBridge.input n S) b || meet (TwoOrBridge.input n S) a) =
        meet (TwoOrBridge.input n S) a) := by
    intro hdom
    apply first_not_dominated n G hfour b a c d e f out ha hc hd he hf ho
      E hsize hcard
    · intro S hS
      rw [← first_swap a b out [(c,d),(e,f)] (TwoOrBridge.input n S)]
      exact haccept S hS
    · intro S hS
      apply hsound S
      rw [first_swap a b out [(c,d),(e,f)] (TwoOrBridge.input n S)]
      exact hS
    · exact hdom
  cases a with
  | nil =>
    exfalso
    apply hbadSwap
    intro S
    simp [meet]
  | cons i as =>
    cases b with
    | nil =>
      exfalso
      apply hbad
      intro S
      simp [meet]
    | cons j bs =>
      let ii : Fin n := ⟨i, ha i (by simp)⟩
      let jj : Fin n := ⟨j, hb j (by simp)⟩
      have hua : ∀ k ∈ i :: as, k = i := by
        intro k hk
        have hv := first_left_unique n G hfour (i::as) (j::bs) c d e f out
          hb hc hd he hf ho E hsize hcard haccept hsound ⟨k, ha k hk⟩ ii hk (by simp [ii])
        exact congrArg Fin.val hv
      have hub : ∀ k ∈ j :: bs, k = j := by
        intro k hk
        have hv := first_right_unique n G hfour (i::as) (j::bs) c d e f out
          ha hc hd he hf ho E hsize hcard haccept hsound ⟨k, hb k hk⟩ jj hk (by simp [jj])
        exact congrArg Fin.val hv
      have hma := meet_of_unique (i::as) i (by simp) hua
      have hmb := meet_of_unique (j::bs) j (by simp) hub
      refine ⟨ii, jj, ?_, hma, hmb⟩
      intro heq
      have hij : i = j := congrArg Fin.val heq
      apply hbad
      intro S
      rw [hma, hmb, hij]
      exact Bool.or_self _

end PEqualNP.Outside.L_meta_1031_aux.FirstOrReduction

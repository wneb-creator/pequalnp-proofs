import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Image
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Intervals
import PEqualNP.Defs
-- The first-OR lower bound is from tkind94's merged proof in PR 6929.

namespace PEqualNP.Outside.L_meta_3825_aux

def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]

inductive Sol (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol m T q (insert (a ^^^ m) S) → Sol m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S →
      Sol m T q (insert (op d a b) S) → Sol m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) (ih (by omega) (Set.insert_subset_insert hs))

inductive Live (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live m T k t (insert (a ^^^ m) U) →
      Live m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Live m T k t (insert (op d a b) U) →
      Live m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : Sol m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, by omega, t + 1, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q S d a b ha hb _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩

def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left

def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live m T k t S') :
    Live m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live m T k t S') :
    Live m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl⟩ := h; exact .bi hab hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') : Bi d b a S S' := by
  obtain ⟨hab, U, rfl, rfl⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm]⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]

def Min (m T k t : ℕ) (S : Finset ℕ) : Prop := Live m T k t S ∧ ∀ q < k, ¬ Sol m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol m T q (C m S')) :
    Sol m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hs : Sol m T q (C m S')) :
    Sol m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : Min m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : Min m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'

lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hl ih =>
    have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega

def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := by
  obtain ⟨U, rfl, rfl⟩ := h
  refine ⟨insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a : ℕ} {X : Finset ℕ} (h : a ^^^ m ∈ X) : Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m), rfl, by rw [Finset.insert_erase h]⟩
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn
  simp [phi, hn.2]
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h

lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi d a b S S1 ∧ Live m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi d (a ^^^ m) c S1 S2 ∧ Live m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl⟩, hl⟩
  | @un k t a U hl =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf := hu.fresh hl hm
    have hn : a ^^^ m ∉ insert a U := fun h => hf (sub_C _ _ (by simpa using h))
    have hmin := hu.min hl hm
    have hxx : ∀ c : ℕ, c ^^^ m ^^^ m = c := fun c => by simp
    have hc' : 2 ≤ (insert (a ^^^ m) U).card := by
      have h1 := Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1 : insert (a ^^^ m) U = S1 at *
    have hnS1 : a ^^^ m ∈ S1 := by rw [← hS1]; simp
    have hst := phi_start hu hn
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3 := hsub hx
        have h4 : x ∈ insert a (insert (a ^^^ m) U) := by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0, d, x, y, S2, rfl, hb, hl2⟩ | ⟨k0, t0, c, d, y, S2, S3, rfl, rfl, h1, hb, hl2⟩ |
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hu, n1, h1, hb.symm, hl2⟩)
      have hk2 := un_keep h1 hnS1 n1
      have hg : op d (c ^^^ m) y ≠ a ^^^ m := fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1, t0 + 1, c, d, y, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, rfl, rfl, ?_, phi_bi hb n2 hy hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1 := hb.live hl2
      have hb2 := h2.live hb1
      obtain ⟨n1, n2⟩ := dbl h1 hb2 rfl
      have hm2 := h1.min hb2 hmin.2
      have hk2 := un_keep h1 hnS1 n1
      have hm3 := h2.min hb1 hm2.2
      have n3 : c' ≠ a ^^^ m := by
        rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS, hsub1⟩ := h1.sub
        have hcS' : c ∈ insert a U := by
          have : c ∈ insert (a ^^^ m) U := by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (.un (a := c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3 : x = a ∨ x = c ^^^ m ∨ x ∈ S1 := by
          have := hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have := hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4 : c' ^^^ m ≠ a ^^^ m := fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3 := un_keep h2 hk2 n3
      have hg : op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m := fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol n (T &&& n) q (C n (Im n S'))) :
    Sol n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hs : Sol n (T &&& n) q (C n (Im n S'))) :
    Sol n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol n (T &&& n) q (C n (Im n S'))) :
    Sol n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol n (T &&& n) q (C n (Im n S'))) : Sol n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q, ?_, hu.kill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1, ?_, hu.im hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hl ih =>
    have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩

def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have weak : sepb N true w i = true := by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a, by simp, ?_⟩
      revert weak; simp [sepb, pos', m1, m2]
    · exact ⟨w, by simp [hw], by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hl : Live m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min m T k t (insert (op d a b) U) := by
  have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live m T k 0 S) (hm : ∀ q < k, ¬ Sol m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live m T k t S) (hm : ∀ q < k, ¬ Sol m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    have := ih hmin.2 hc' (a := if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; tauto)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1, h2.1] using this
    · exact this
  | @bi k t d x y U hxy hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live m T k t S) (hm : ∀ q < k, ¬ Sol m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; tauto
    · split_ifs with h <;> simp at hb ⊢; tauto
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e, h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e, h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp), h1.1, h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp), h3.2.1, h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect

structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
def NN : Nat := 1118
def AA : Nat := 0x1ffff7df7fffef7fffefbdffffbefbeeffffdffff7df7bef7fffefbdef6ffffbeffffdf7bef7deffffdef6fbffff7bffff7df7ddef6fbeefbbbbffd6ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6d6b56b6daadb5adb5ad7fff6b5ad56b7fff6b56b6d6dab5b6dad57fff5b6aad6dafffeb5fffdb5fffd6fffed7fff7fff0000000000000000
def HX : Nat := 0x2954955552924a49554a5494800092552500015494a9200029294a94925524a524a52800094a52a94800094a94929254a49252a8000a4955292500014a00024a0002900012800080000000000000000000
def HY : Nat := 0x2000082080001080001042000041041100002000082084108000104210900004100002084108210000210904000084000082082210904110444400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
noncomputable section core
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f (Nat.succ m)) n
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩ :: ih) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def tail (f : Nat → List W → Bool) (d : Bool) (l e n z : Nat) (r : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (f z r) (Bool.rec (motive := fun _ => Bool) (f z r) false (rect d l (Nat.xor l (twice d l r)) r [])) (Nat.beq n e)
def child (f : Nat → List W → Bool) (d : Bool) (l g e n : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (st z (fun z => mk (tail f d l e n z))) (Nat.beq (Nat.land z g) g)
def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((st (x) (fun x => (st (y) (fun y => (st (Nat.lor x y) (fun w => ins ⟨s, x, y, w⟩ v h))))))) (false) (Nat.beq s m))) (false) (Nat.beq s 0))))
def kids (c : Nat → ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (Nat.succ (Nat.succ n)) mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (Nat.succ n) (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (c (Nat.succ n) (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc))))) (Nat.ble (Nat.succ n) e))))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) (false) (c n (fun h => mk (fun r => rm a c' r h)) z) (oc))) (oa))))
def mid (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f d l g e) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))
def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u => X.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : X → Bool) (xs : List X) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def nots (f : Nat → Nat → List W → Bool) (d : Bool) (l m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) d l g e (Nat.succ n) (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) d l g e n (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v))
  (mid f d l m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => (fun n => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => node (ih (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub k 2) s) v.length z v (pairsQ q q')) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z (Nat.succ q) v v)) (true) (node (ih (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z v (pairsP q)))) (pos s) l m g (Nat.sub k s) n z 0 v v)) (true) (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub k t) n z v pairs))) (true) (Nat.ble n 1))) v.length) fuel
end core
lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb NN d s i) := by
  cases d <;> simp [sp, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq NN d S w.s i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this
def segsX : List (ℕ × ℕ) := [(63,79), (79,95), (95,97), (97,100), (100,116), (116,119), (119,121), (121,137), (137,139), (139,142), (142,145), (145,161), (161,163), (163,166), (166,168), (168,184), (184,186), (186,189), (189,192), (192,195), (195,197), (197,200), (200,202), (202,204), (204,206), (206,208), (208,211), (211,214), (214,217), (217,219), (219,235), (235,237), (237,239), (239,241), (241,244), (244,246), (246,249), (249,252), (252,255), (255,258), (258,261), (261,263), (263,266), (266,268), (268,270), (270,273), (273,276), (276,279), (279,281), (281,284), (284,287), (287,290), (290,292), (292,295), (295,297), (297,299), (299,302), (302,304), (304,307), (307,323), (323,326), (326,328), (328,331), (331,333), (333,335), (335,337), (337,340), (340,342), (342,345), (345,347), (347,350), (350,352), (352,355), (355,371), (371,373), (373,376), (376,378), (378,381), (381,383), (383,386), (386,389), (389,392), (392,394), (394,397), (397,399), (399,402), (402,405), (405,408), (408,410), (410,412), (412,414), (414,417), (417,420), (420,423), (423,426), (426,428), (428,431), (431,433), (433,435), (435,438), (438,440), (440,443), (443,445), (445,448), (448,451), (451,453), (453,469), (469,472), (472,475), (475,477), (477,479), (479,482), (482,484), (484,487), (487,490), (490,492), (492,494), (494,496), (496,512), (512,514), (514,517), (517,520), (520,522), (522,524), (524,526), (526,529), (529,532), (532,535), (535,551), (551,554), (554,556), (556,559), (559,562), (562,564), (564,566), (566,569), (569,571), (571,574), (574,576), (576,578), (578,580), (580,582), (582,584), (584,587), (587,590), (590,593), (593,595), (595,598), (598,601), (601,604), (604,607), (607,609), (609,612), (612,614), (614,616), (616,618), (618,620), (620,622), (622,624), (624,626), (626,628), (628,631), (631,634), (634,636), (636,638), (638,640), (640,643), (643,645)]
def segsY : List (ℕ × ℕ) := [(645,658), (658,662), (662,666), (666,670), (670,676), (676,680), (680,686), (686,692), (692,695), (695,700), (700,705), (705,709), (709,715), (715,721), (721,727), (727,746), (746,751), (751,770), (770,776), (776,779), (779,784), (784,789), (789,808), (808,813), (813,819), (819,824), (824,830), (830,835), (835,841), (841,860), (860,866), (866,884), (884,887), (887,892), (892,897), (897,902), (902,908), (908,927), (927,932), (932,938), (938,943), (943,949), (949,955), (955,973), (973,992), (992,996), (996,1002), (1002,1008), (1008,1014), (1014,1033), (1033,1038), (1038,1044), (1044,1063), (1063,1068), (1068,1087), (1087,1093), (1093,1099), (1099,1117)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all segOk = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 32) : pk n f < 2 ^ (5 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    have : 2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 16) < 2 ^ (5 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 16 = 16 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (5 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 5 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (5 * j) <;> simp
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
def Cl (P : List ℕ) (T k : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop := ∀ j < P.length, ∀ q, q + b j < k →
  ¬ Sol (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k b S) (hm : Min m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q, hq, hs⟩ := hm.const p1 p2 p3
  have hqb : ¬ q + b j < k := fun h => hc j hj q h hs
  have : cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
    have e : cnt v j = (v.filter (fun w => w.c.testBit (5 * j))).length := by
      clear hr hw
      induction v with
      | nil => rfl
      | cons w v ih =>
        rw [cnt_cons, ih, List.filter_cons, fl]
        cases w.c.testBit (5 * j) <;> simp; omega
    rw [e, ← List.length_map W.s, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
    apply Finset.card_le_card
    intro x hx
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
    obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
    rw [Finset.mem_filter]
    exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
  omega
lemma tail_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    (hr : StOk P T l k z r S) (hm : Min m T k' t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = r.length)
    (he : e = k + 1 - t) (h : tail f d l e n z r = false) : f z r = false := by
  simp only [tail, bR] at h
  by_cases hne : n = e
  · have hb : Nat.beq n e = true := by simpa using hne
    rw [hb, cond_true] at h
    cases hrect : rect d l (Nat.xor l (twice d l r)) r [] with
    | false => rw [hrect] at h; simpa using h
    | true =>
      exfalso
      have hs := hm.size
      have hcard := hr.rep.card
      have hpos : 0 < S.card := hm.1.pos
      have htight : S.card + t = k' + 1 := by omega
      rw [rect_false (o := Nat.xor l (twice d l r))] at hrect; · simp at hrect
      · have hnd : r.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hr.rep.1
        refine hnd.imp_of_mem fun {a b} ha hb' hab => ?_
        by_contra hhit
        rw [Bool.not_eq_false] at hhit
        obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec hhit
        have hu : ∀ w, ∀ i, (Nat.land (sp d l w) (wst d l r)).testBit i = true → AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
        have ma := hr.rep.mem.2 ⟨a, ha, rfl⟩
        have mb := hr.rep.mem.2 ⟨b, hb', rfl⟩
        rcases Nat.eq_zero_or_pos t with rfl | htp
        · have hd' : d = false := by rw [hd]; simp [pos']
          subst hd'
          exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
        · have hd' : d = true := by rw [hd]; simp [pos', htp]
          subst hd'
          exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
      · simp
  · have hb : Nat.beq n e = false := Bool.eq_false_iff.2 fun h => hne (Nat.eq_of_beq_eq_true h)
    rw [hb, cond_false] at h; exact h
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k z r S) (hm : Min m T k' t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = r.length)
    (he : e = k + 1 - t) (h : child f d l g e n mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact tail_sound X hr hm hk hd hn he h
end sound
lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.s ≠ o.s) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.s w.s = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl
lemma filter_perm {v : List W} (hv : (v.map W.s).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.s a.s) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x) := by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases h with
  | ff h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases h with
  | ff h => have := h.length_eq; simp at this ⊢; omega
  | tf h => have := h.length_eq; simp at this ⊢; omega
  | ft h => have := h.length_eq; simp at this ⊢; omega
  | tt h => have := h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ho : o.s ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map W.s ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.s).1 (List.mem_map_of_mem hc)
  have hao : a.s ≠ o.s := fun e => ho (e ▸ haS)
  have hco : c.s ≠ o.s := fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.s := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.s := fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n1, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp
lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r := by
  have hnd : (r.map W.s).Nodup := by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_, .tf ?_, .ft ?_, .tt hp⟩
  · rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.s a.s) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map W.s).Nodup) (hac : a.s ≠ c.s) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.s a.s) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map W.s).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b)⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b)⟩
lemma opW_s (d : Bool) (a c : W) : (opW d a c).s = op d a.s c.s := by cases d <;> rfl
lemma opW_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa, isPk_and ha.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a ||| c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h : (a.b &&& c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.cb j hj h.1, hc.cb j hj h.2, op_self]
  · refine ⟨isPk_and ha.pa, isPk_or ha.pb hc.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a &&& c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.ca j hj h.1, hc.ca j hj h.2, op_self]
    · have h : (a.b ||| c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y : ℕ} (d : Bool) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]
lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.c &&& c.c = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> rfl
lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.c = pk P.length (fl a) := pk_of ha.pc
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi d' a.s c.s S S')
    (hl : Live m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hab : a.s ≠ c.s := hb.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).s ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have hrep : Rep r S' := by
    refine hsh.rep hs.rep ha hc hab hfS fun x => ?_
    obtain ⟨_, U, e1, e2⟩ := hb
    rw [opW_s] at hfS ⊢
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_, ?_⟩
        · rintro rfl; rw [hka, e2]; simp [h]
        · rintro rfl; rw [hkc, e2]; simp [h]
    · rintro (h | ⟨h, f1, f2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · have := f2 h; rw [hkc, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hsh.mem hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - max (fl a j) (fl c j)
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q + 1) ?_ (hb.im hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill.1]
      have e2 : fl c j = 0 := by simp [fl, hkill.2]
      rw [e1, e2] at hq; simp at hq; omega
  have hmin := hb.min hl hm.2
  have hle' := cnt_le X hrep hwok hcl' hmin hk
  have num : ∀ j < P.length, 1 ≤ 16 + b j - cnt v j + fl a j * fl c j ∧ fl (opW d' a c) j ≤ 1 ∧
      16 ≤ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j ∧ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j < 32 ∧
      16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (bif ka then fl a j else 0) - (bif kc then fl c j else 0) = 16 + b' j - cnt r j := by
    intro j hj
    have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_two ha hc hs.rep.1 hab j; have q4 := hb15 j hj
    have q5 := hsh.cnt j; have q6 := fl_le a j; have q7 := fl_le c j; have q8 := fl_le (opW d' a c) j
    simp only [b'] at q2 ⊢
    generalize fl a j = fa at *; generalize fl c j = fc at *; generalize fl (opW d' a c) j = fo at *
    interval_cases fa <;> interval_cases fc <;> cases ka <;> cases kc <;> simp at q2 q3 q5 ⊢ <;> omega
  have e1 : z + (a.c &&& c.c) - (opW d' a c).c = pk P.length (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, fl_pk wo, pk_add, pk_sub]
    intro j hj; have := num j hj; omega
  refine ⟨⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩, ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · rw [e1]
    have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have ec : (bif kc then c.c else 0) = pk P.length (fun j => bif kc then fl c j else 0) := by
      cases kc
      · simp [pk]
      · exact fl_pk wc
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    have le2 : ∀ j, (bif kc then fl c j else 0) ≤ 1 := fun j => by cases kc <;> simp [fl_le]
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (num j hj).2.2.2.2
    · intro j hj; have := num j hj; have := le1 j; have := le2 j; omega
    · intro j hj; have := num j hj; have := le1 j; omega
  · rw [e1, nl, X.hg, pk_guard]; · simp
    intro j hj; have := num j hj; omega
lemma drop_ok {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi d' a.s c.s S S') (hl : Live m T k' t S')
    (ha : a ∈ v) (hk : a.s ∉ S')
    (hu : (Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (X → X → Bool) → List X → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f d l m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma modeF_false {n e : ℕ} {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {a c : W} {da dc : ℕ} {s x y : ℕ}
    (hf : modeF n e h a c da dc s x y = false) (h0 : ¬ n ≤ e → da = 0 ∧ dc = 0) (h1 : ¬ n + 1 ≤ e → da = 0 ∨ dc = 0) :
    h a c da dc s x y = false := by
  unfold modeF at hf
  cases b1 : Nat.ble n e with
  | false =>
    have := h0 (fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1)
    rw [b1, this.1, this.2] at hf; rw [this.1, this.2]; exact hf
  | true =>
    cases b2 : Nat.ble (Nat.succ n) e with
    | false =>
      have := h1 (fun h => by rw [Nat.ble_eq_true_of_le h] at b2; simp at b2)
      have h3 : Nat.beq (Nat.mul da dc) 0 = true := by
        change Nat.beq (da * dc) 0 = true
        rcases this with h | h <;> simp [h]
      rw [b1, b2] at hf
      simp only [Bool.cond_true, Bool.cond_false, f1, h3] at hf
      exact hf
    | true => rw [b1, b2] at hf; exact hf
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o : ℕ} {a c : W}
    (hp : pair h (mkx d l o a) (mkx d l o c) = false) (d' : Bool) :
    h a c (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pair, mkx, bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma put_eq {m : ℕ} {o : W} {v : List W} (ho : Nat.lor o.a o.b = o.c) (h0 : o.s ≠ 0) (h1 : o.s ≠ m) (h : List W → Bool) :
    put m o.s o.a o.b v h = ins o v h := by
  have hb0 : Nat.beq o.s 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  have hb1 : Nat.beq o.s m = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  simp only [put, st_eq, hb0, hb1, ho]
lemma mid_false {f : ℕ → List W → Bool} {d : Bool} {l m g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : Bool}
    (h : mid f d l m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    kids (child f d l g e) e n (z + (a.c &&& c.c) - (opW d' a c).c) a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0)
      (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) = false := by
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  simp only [mid, st_eq, ec] at h
  have hg' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (opW d' a c).c) g) g = true := hg
  rw [hg'] at h
  exact h
lemma kids_false {ch : ℕ → ((List W → Bool) → Bool) → ℕ → Bool} {e n z x y a c : ℕ} {oa oc : Bool} {mk : (List W → Bool) → Bool}
    (h : kids ch e n z x y a c oa oc mk = false) :
    (oa = true → oc = true → ch n (fun h => mk (fun r => rm a c r h)) z = false) ∧
    (oc = true → n + 1 ≤ e → ch (n + 1) (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (oa = true → n + 1 ≤ e → ch (n + 1) (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (n + 2 ≤ e → ch (n + 2) mk (z - x - y) = false) := by
  simp only [kids, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2; subst h1 h2
    revert h; simp only [Bool.cond_true]; cases ch n (fun h => mk (fun r => rm a c r h)) z <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (Nat.succ n) (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) = false
    cases ch (Nat.succ n) (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (Nat.succ n) (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) = false
    cases ch (Nat.succ n) (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) <;> simp
  · intro h2; rw [b2 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (Nat.succ (Nat.succ n)) mk (Nat.sub (Nat.sub z x) y) = false
    cases ch (Nat.succ (Nat.succ n)) mk (Nat.sub (Nat.sub z x) y) <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma gate_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (he : e = k + 1 - t) (hb : Bi d' a.s c.s S S') (hl : Live m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f d l m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hsz := hmin.size
  have hpos := hl.pos
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp := pair_false hp d'
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false, nl, nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by
    rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep hb.symm hl hc h hi
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) ho0 ho1, hins]
  have hv2 : 2 ≤ v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hb.1] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ S'.card ≤ e ∧ StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' := by
    intro ka kc r h1 h2 h3
    have := (bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm, by omega, this⟩
  have hguard : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
    by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s1).2
  have fin : ∀ {n z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k z' r S' → n = r.length →
      child f (pos' t) l g e n mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' :=
    fun {n z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound X h1 h2 hmin hk rfl h3 he h4, h2⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c2, c3⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard
    exact fin hput c3 (by omega) ((kids_false hmid).2.2.2 (by omega))
  · obtain ⟨c1, c2, c3⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) (by omega) ((kids_false hmid).2.1 (b0 (fc q2)) (by omega))
  · obtain ⟨c1, c2, c3⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) (by omega) ((kids_false hmid).2.2.1 (b0 (fa q1)) (by omega))
  · obtain ⟨c1, c2, c3⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) (by omega) ((kids_false hmid).1 (b0 (fa q1)) (b0 (fc q2)))
end sound
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) r S' := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hfr := hb.fresh hl hm.2
  have hfS : a.s ^^^ m ∉ S := fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha
  have haS : a.s ∈ S := hb.sub.1
  have wo : WOk P (notW m a) := by
    refine ⟨wa.pb, wa.pa, by rw [Nat.or_comm]; exact wa.ec, fun j hj h => ?_, fun j hj h => ?_⟩
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.cb j hj h]; simp
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.ca j hj h]; simp
  have hov : ((notW m a :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => hfS ?_, hs.rep.1⟩
    rw [← hs.rep.2]; simpa [notW] using hm
  have hov2 : ∀ x, x ∈ (notW m a :: v).map W.s ↔ x = a.s ^^^ m ∨ x ∈ S := fun x => by
    rw [← hs.rep.2]; simp [notW]
  have hS' : ∀ x, x ∈ S' ↔ x = a.s ^^^ m ∨ (x ∈ S ∧ (x = a.s → ka = true)) := by
    intro x
    obtain ⟨U, e1, e2⟩ := hb
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_⟩
        rintro rfl; rw [hka, e2]; simp [h]
    · rintro (h | ⟨h, f1⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hne : a.s ≠ a.s ^^^ m := fun e => hfS (e ▸ haS)
  have hrep : Rep r S' := by
    cases hkk : ka with
    | true =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      refine ⟨hn, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, (hsh.map W.s).mem_iff, hov2, hS']; simp
    | false =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      simp only [List.map_cons, List.nodup_cons] at hn
      refine ⟨hn.2, Finset.ext fun x => ?_⟩
      have hx := (hsh.map W.s).mem_iff (a := x)
      rw [hov2] at hx; simp only [List.map_cons, List.mem_cons] at hx
      rw [List.mem_toFinset, hS']
      constructor
      · intro h1
        rcases hx.1 (Or.inr h1) with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e, fun e => absurd (e ▸ h1) hn.1⟩
      · rintro (e | ⟨e, f1⟩)
        · exact (hx.2 (Or.inl e)).resolve_left fun e' => hne (e'.symm.trans e)
        · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  have hmem : ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
    intro w hw
    have : w ∈ notW m a :: v := by
      cases hkk : ka <;> rw [hkk] at hsh
      · exact List.Perm.subset hsh (by simp [hw])
      · exact List.Perm.subset hsh hw
    simpa using this
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) = fl a j + cnt v j := by
    intro j
    have ef : fl (notW m a) j = fl a j := rfl
    cases hkk : ka <;> rw [hkk] at hsh
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hmem w hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hmem w hw with rfl | h
    · have hg := hs.good a ha
      refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
      · change (a.s ^^^ m).testBit i = (a.s ^^^ m).testBit j
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.1 i j h h1 h2, (X.lg i h1).1.1, (X.lg j h2).1.1]
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - fl a j
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_one ha hs.rep.1 j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (X.hP j hj).1 (wa.cst hj hkill) hsol)
      have : fl a j = 1 := by simp [fl, hkill]
      omega
    · refine hcl j hj (q + 1) ?_ (hb.im (X.hP j hj).1 hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill]
      omega
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    conv_lhs => rw [fl_pk wa]
    rw [pk_sub, pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; have := fl_le a j; omega
    · intro j hj; have := hle j hj; have := fl_le a j; omega
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {d : Bool} {l m g e n z q : ℕ} {v r : List W} (h : nots f d l m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) d l g e n (rm a.s a.s v) (z - a.c) else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) d l g e (n + 1) (fun h => h v) (z - a.c - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f d l m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st (Nat.sub z w.c) (fun z => ins ⟨s, w.b, w.a, w.c⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) d l g e (Nat.succ n) (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) d l g e n (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) d l g e n (rm a.s a.s v) (z - a.c) else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) d l g e (n + 1) (fun h => h v) (z - a.c - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) d l g e n (rm a.s a.s v) (z - a.c) else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) d l g e (n + 1) (fun h => h v) (z - a.c - a.c) else false))) then true
          else nots f d l m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f d l m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {d : Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (he : e = k + 1 - t) (hb : Un m a.s S S') (hl : Live m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f d l m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hsz := hmin.size
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have h := nots_false hp har' hq
  rw [hins] at h
  have hl0 : r0.length = v.length + 1 := by rw [hr0.length_eq]; simp
  have hnd : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
  have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
  by_cases q1 : a.s ∈ S'
  · have hst := un_st X hs hm hk hb hl ha (ka := true) (by simp [q1]) hr0
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) (pos' t) l g e (v.length + 1) (fun h => h r0) (z - a.c - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) (pos' t) l g e (v.length + 1) (fun h => h r0) (z - a.c - a.c) <;> simp
    exact ⟨_, _, child_sound X (fun h => rfl) hst hmin hk rfl (by omega) he h, hst⟩
  · have hperm : (a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v) := by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst := un_st X hs hm hk hb hl ha (ka := false) (by simp [q1]) hperm
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    have hc := hst.rep.card
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1 : Nat.ble v.length e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) (pos' t) l g e v.length (rm a.s a.s r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) (pos' t) l g e v.length (rm a.s a.s r0) (z - a.c) <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk rfl (by omega) he h, hst⟩
end sound
def FM (m T k t : ℕ) (S : Finset ℕ) (KP : ℕ → ℕ → Prop) (KN : ℕ → Prop) : Prop :=
  (∃ k0 d a b S1, k = k0 + 1 ∧ KP a b ∧ Bi d a b S S1 ∧ Live m T k0 t S1) ∨
  (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ KN a ∧ Un m a S S1 ∧ Bi d (a ^^^ m) c S1 S2 ∧ Live m T k0 t0 S2) ∨
  (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ KN a ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
    Bi d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live m T k0 t0 S3)
lemma FM_of {m T k t : ℕ} {S : Finset ℕ} (h : Min m T k t S) (hc : 2 ≤ S.card) : FM m T k t S (fun _ _ => True) (fun _ => True) := by
  rcases first_move k t S h hc with ⟨k0, d, a, b, S1, e, h⟩ | ⟨k0, t0, a, d, c, S1, S2, e, e', h⟩ | ⟨k0, t0, a, a', d, S1, S2, S3, e, e', h⟩
  · exact Or.inl ⟨k0, d, a, b, S1, e, trivial, h⟩
  · exact Or.inr (Or.inl ⟨k0, t0, a, d, c, S1, S2, e, e', trivial, h⟩)
  · exact Or.inr (Or.inr ⟨k0, t0, a, a', d, S1, S2, S3, e, e', trivial, h⟩)
lemma scan_false {p : X → Bool} {xs : List X} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (scan p r) true (p a) : Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairs h r) true (scan (h a) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma beq_f {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma pairsP_false {h : X → X → Bool} {xs : List X} {q : ℕ} {a c : X} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : X → X → Bool} {xs : List X} {q q' : ℕ} {a c : X} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma look_succ (l m g fuel k t z : ℕ) (v : List W) (h : look l m g (fuel + 1) k t z v = false) :
    2 ≤ v.length ∧ node (look l m g fuel (k - 1) t) (pos' t) l m g (k - t) v.length z v pairs = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => bif node (look l m g fuel (k - 2) s) (pos' s) l m g (k - 1 - s) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => node (look l m g fuel (k - 3) s) (pos' s) l m g (k - 2 - s) v.length z v (pairsQ q q'))
        (pos' s) l m g (k - 1 - s) v.length z (q + 1) v v)) (pos' s) l m g (k - s) v.length z 0 v v = false := by
  change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => node (look l m g fuel (k - 3) s) (pos s) l m g (k - 2 - s)
        v.length z v (pairsQ q q')) (pos s) l m g (k - 1 - s) v.length z (q + 1) v v)) true
        (node (look l m g fuel (k - 2) s) (pos s) l m g (k - 1 - s) v.length z v (pairsP q)))) (pos s) l m g (k - s) v.length z 0 v v)) true
      (node (look l m g fuel (k - 1) t) (pos t) l m g (k - t) v.length z v pairs)) true (Nat.ble v.length 1) : Bool) = false at h
  simp only [bR, pos_eq] at h
  cases h0 : Nat.ble v.length 1 with
  | true => rw [h0] at h; simp at h
  | false =>
    rw [h0, Bool.cond_false] at h
    have hlen : 2 ≤ v.length := by
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
    cases h1 : node (look l m g fuel (k - 1) t) (pos' t) l m g (k - t) v.length z v pairs with
    | true => rw [h1] at h; simp at h
    | false =>
      rw [h1, Bool.cond_false] at h
      refine ⟨hlen, rfl, ?_⟩
      rintro s rfl
      exact h
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (L_meta_3825_aux.X → L_meta_3825_aux.X → Bool) → List L_meta_3825_aux.X → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (he : e = k + 1 - t) (hb : Bi d' x y S S') (hl : Live m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · exact gate_sound X hs hm hk hd hn he hb hl ha hc h
  · exact gate_sound X hs hm hk hd hn he hb.symm hl hc ha h
lemma step_sound {fuel : ℕ} (ih : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S →
    ∀ k' ≤ k, ¬ Min m T k' t S) {k t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hlen : 2 ≤ v.length)
    {KP : ℕ → ℕ → Prop} {KN : ℕ → Prop}
    (hA : ∀ x y : ℕ, x ≠ y → KP x y → ∃ go : (L_meta_3825_aux.X → L_meta_3825_aux.X → Bool) → List L_meta_3825_aux.X → Bool,
      node (look l m g fuel (k - 1) t) (pos' t) l m g (k - t) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false)
    (hN : ∀ s, t = s + 1 → ∀ a ∈ v, KN a.s → ∃ rr, a ∈ rr ∧ nots (fun q z v =>
      bif node (look l m g fuel (k - 2) s) (pos' s) l m g (k - 1 - s) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => node (look l m g fuel (k - 3) s) (pos' s) l m g (k - 2 - s) v.length z v (pairsQ q q'))
        (pos' s) l m g (k - 1 - s) v.length z (q + 1) v v)) (pos' s) l m g (k - s) v.length z 0 v rr = false) :
    ∀ k' ≤ k, Min m T k' t S → ¬ FM m T k' t S KP KN := by
  intro k' hk hm hfm
  rcases hfm with
    ⟨k0, d, a, b, S1, rfl, hkp, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hkn, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, hkn, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨go, h1, hgo⟩ := hA a b hb.1 hkp
    obtain ⟨z', r, hf, hst⟩ := node_bi X hs hm (by omega) rfl rfl (by omega) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact hgo h hp a c ha hc hax hcy) h1
    exact ih _ _ _ _ _ hf hst k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    obtain ⟨rr, hrr, h2⟩ := hN t0 rfl wa hwa hkn
    obtain ⟨z1, r1, hf1, hst1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl rfl (by omega) hu hl1 hwa (by omega) hrr h2
    have hm1 := hu.min hl1 hm.2
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (by omega) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsP_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) (fun e => hb.1 (by rw [← hcy, ← e]; rfl)))) hf2
    exact ih _ _ _ _ _ hf hst k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    obtain ⟨rr, hrr, h2⟩ := hN (t0 + 1) rfl wa hwa hkn
    obtain ⟨z1, r1, hf1, hst1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl rfl (by omega) hu hl2 hwa (by omega) hrr h2
    have hm1 := hu.min hl2 hm.2
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl rfl (by omega) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    obtain ⟨z', r, hf, hst⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (by omega) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsQ_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) hcy)) hf3
    exact ih _ _ _ _ _ hf hst k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S →
    ∀ k' ≤ k, ¬ Min m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs
    obtain ⟨hlen, h1, h2⟩ := look_succ _ _ _ _ _ _ _ _ h
    intro k' hk hm
    refine step_sound X (KP := fun _ _ => True) (KN := fun _ => True) ih hs hlen (fun x y hxy _ => ⟨pairs, h1, fun h hp a c ha hc hax hcy => ?_⟩)
      (fun s hs a ha _ => ⟨v, ha, h2 s hs⟩) k' hk hm (FM_of hm (by rw [hs.rep.card]; exact hlen))
    have hpw := pairs_false hp
    have : Std.Symm (fun a c : L_meta_3825_aux.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
    refine (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_
    intro e
    have : a.s = c.s := congrArg L_meta_3825_aux.X.s e
    exact hxy (by rw [← hax, ← hcy, this])
end sound
def rawP : List ℕ := [0x1ffff8000000007fffe000f8000007fffc07c000000003e003c00000000000000001f03ffff03c00000000000000000000000f83e00e000020c00800086060800008c0ca44000080948800085032910410204200288610001004a8402001108ca8408000010822020b0844a880000000821511012a20042a221951014a880a888000000000000000010290417e052000852085ad14800be0008a51e2901f002100252f802f0005482002a4108217c089ea40f00800690800690410442120be0f80b80a40830020016181860000230300000002020000006b40c00010c0810801a218400040100000802c4630000601080c6188186c2110000000a8161afffe04000035fffc60000d00007fff2cb20284c2023205, 0x7fffc07c00000000003e00000003e0000000000000000f81ffff80078000000000000000000000000000000ffffc0ffffc001f003c3e00000e000040202208843010100010002102183080620460842018408c0a000000100100230c0310431810841210431000808010000400101043860888410a08c0c41182141184208c21046904700000000000000001f04301f02086001086f80012182f8200110c02430410be046e86081e1000a1840050c210420420030c2121127c30127c30027c04f0f82008b8810d0080882210c04060004000800000c20180000230806000016c000000c02c058c300c000060421068000060460610c0043002d57fff1862210c2000030000184000100000d7fff7fff605989290008a0c3, 0x1ffff8007fffef80000000000000000000000000000003fffe0000007c0f80003ffff7803e0000000000007c0078000003ee00000000000001000024208c00d806141800b00c282098140185050401000800024080008061400020000461482140405808160120506281012010260c502018a04c18a008c510462906280000000000000000020860820410c16b90c101ad433e100002218048608210420050c1044228bc30002819f03e00848be19e00f8088600088609f081e201042fb90021800000002c0005b08230036000006002c0000083605000001610040060281b020002000000058150b7fff08503016020580d814000040682c0d80000800001b000016fffe17fff00004840d0f006c20810, 0x7fffdf000001ffffbef0000000003ffff000001f78000000000000000ffffdf00000003efb8000000002800000001240002000a000068800a0000d2000000901a60002c02400ab00000d6000c90a40055800c9004009b000240024b000d102400a58001a405034a000348501a6300d200d200000000000000000421410408428202428208060a042042140513e147c000844ee28fbc000110a0899e50400847de104504002041141165d47c4000844fbee110008500a00002800db0000800280000000028000000a80056dfffc000b00b002ac0000358000006b00156000000b0036c002b000dac000005b002d6000000b5fffc0000016fffec00000000000004525d9ab670, 0x7fffdf00000001ffffbef00000000003ffff000000000fbc00000000003fffef80000000fbc00000000003effffde00000000007bd8000000000005800280ab500000280d600014911b600029242ad2800524800580009b400000b600015121096a00015120295a00000894d00001522149aa00002a4828549469549402a4801524152400000000000000001f0187c01003006b830fbc080c0000808f860081810403ef0083020804089cc3e01060003ef10800860020f925d8780118100001ef62084200100616000a02ad600000a035800000006d80000000ab6b0000000016000b6d800002d800000006b5ac00000000b56800002b5b6000000005b6a800000000b5fffdb5fffc000000000000004c32000238851dce, 0x3fffefbffff7de00000000000003effffdeffffdf7df70000000000000000000000000000002aa000000019892a1200370000000006c00485080000000092429001b80000000001b02d5ada53400000000003316daab534806e0000d80000d80006c00036003600000000000000000852020820a4040c2404103090084104284805120208210813040410884add03eade81f780020025080040f9b5e079b5e07df7dc0000100400214800000aa800000000aa80000000006daadafffe00000000000016b56000000002db5ad7fff0000000000000b56b6d6d80000000000005b6aad6dafffe00000000000000000000000000940c0523a2600210, 0x3ffff7fffdf7de00000000000003fffefbffff7defbdf7bffff7bd8000000000000000000000000000000000a84800000000002aa42a4840de00000001b800000000370005ad5ada6aa6d400000019c00000000019c02d52d35a6ad69b6a541bc00000000003700006e00006e000370001b801b800000000000000001084041041080830080820c020108208cf9019e407df7a0024080001000c9e03ec9f01f7bef7dec9f01ef60206000206000001000804000002021016ab600000000000aab5ab6b7fff000000000000000000000016b56b6daadb580000000000000000000000b56b6d6dab5b6dad57fff000000000000000000000000000000000000000a180bb188920c1a4, 0x7fffdf7dffffbc000000000000000003ffff7fffdf7defbdffffbef7bd8000000000000000000000000000000000000000000000000000000000005aadaaaaa5b6d498000000018e000000031c0000000063800012852d36ab4962494259e01ad4b55a99e018000000000000000019c0000000000338000670000670003380019c019c000000000000000001f1807df7e300f4030000100c02000008fe011f807df7bef47f00fbdef60e00100e000821000000e0008004038002038002082090000000820006016ab6aaaad6db5b6000000000000000000000000000000000016b56b6daadb5adb5ad7fff6b5ad56b7fff6000000000000000000000000000000000000000000000000000000000000130220c900310c00, 0x7fffdf7dffffbdffffbef7fffefbefb80000000000000000000000000000000000000000000000000000000000000000000000000000000000000050292aaab5a496d800940929f001240a4be002adad527c005b0000000000000000001e00000000001e000000000000000000001e000000000003c0000780000780003c0001e001e0000000000000000001fe007df7fc00f7fc00fbdff003efbeef0001e000410400078000820000f00020f000104208410f000108483c00043c0004104100008208000038016ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000092683e00754c0101]
def rawL : List ℕ := rawP ++ [rawP.getD 0 0 ||| rawP.getD 1 0]
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := 0x1ffff7df7fffef7fffefbdffffbefbeeffffdffff7df7bef7fffefbdef6ffffbeffffdf7bef7deffffdef6fbffff7bffff7df7ddef6fbeefbbbbffd6ab6aaaad6db5b6aab5ab6b7fff6daadafffeab6b56dfffd6d6b56b6daadb5adb5ad7fff6b5ad56b7fff6b56b6d6dab5b6dad57fff5b6aad6dafffeb5fffdb5fffd6fffed7fff7ffffc7abffbffeabfd5
def kz (Z : ℕ) : ℕ := (List.range 9).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else x) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG : AA &&& TG = AA := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt : TG < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt : AA < 2 ^ NN := by decide +kernel
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg NN (mz Z) (tz Z) i ∧ AA.testBit i = true := by
  have hA : AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< NN).testBit (NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good : rawL.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true := by decide +kernel
lemma segGood_eq {w o : ℕ} {s : ℕ × ℕ} (h : segGood w o s = true) {i j : ℕ} (h1 : s.1 < i) (h2 : i < s.2) (h3 : s.1 < j) (h4 : j < s.2) :
    w.testBit (o + i) = w.testBit (o + j) := by
  have key : ∀ i, s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1) := by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2, key j h3 h4]
  simp only [segGood, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega, show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma wire_good {w : ℕ} (hw : w ∈ rawL) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  have h := List.all_eq_true.1 raw_good w hw
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_, fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s, hs, a1, a2, a3, a4⟩ := hij
  · have := segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
noncomputable section
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end
lemma pL_cons (d : ℕ) (L : List ℕ) : pL (d :: L) = 2 ^ 5 * pL L + d := by
  change (pL L <<< 5) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L : List ℕ) : pL L = pk L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => simp [pL, pk]
  | cons d L ih =>
    rw [pL_cons, ih, pk, pk, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 5 * (j + 1) = 5 * j + 5 by ring, pow_add]; ring
lemma pL_bit {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : ∀ i, (pL L).testBit i = true ↔ (i % 5 = 0 ∧ i / 5 < L.length ∧ L.getD (i / 5) 0 = 1) := by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd := h d (by simp)
    have ih := ih fun x hx => h x (by simp [hx])
    rw [pL_cons, Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have : i / 5 = 0 := by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have : d.testBit i = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih, show i / 5 = (i - 5) / 5 + 1 by omega]
      simp only [List.length_cons, List.getD_cons_succ]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
lemma pL_isPk {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : isPk L.length (pL L) := fun i hi => by
  have := (pL_bit h i).1 hi; exact ⟨this.1, this.2.1⟩
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)))⟩
lemma mkW_ok (P : List ℕ) (s : ℕ) : WOk P (mkW P s) := by
  have h01 : ∀ f : ℕ → Bool, ∀ d ∈ P.map (fun n => bit01 (f n)), d ≤ 1 := by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n, _, rfl⟩ := hd; cases f n <;> simp [bit01]
  have bt : ∀ f : ℕ → Bool, ∀ j < P.length, (pL (P.map fun n => bit01 (f n))).testBit (5 * j) = true → f (P.getD j 0) = true := by
    intro f j hj h
    have h := ((pL_bit (h01 f) _).1 h).2.2
    rw [show 5 * j / 5 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf : f P[j] <;> simp [bit01, hf] at h ⊢
  refine ⟨?_, ?_, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0); rwa [List.length_map] at this
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n); rwa [List.length_map] at this
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section
def addS (o : W) (v : List W) : List W := List.rec (motive := fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def avl (P : List ℕ) (m : ℕ) (L : List ℕ) : List W := List.rec (motive := fun _ => List W) []
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c⟩ :: r)) v
def anySub (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (ih h) true (ih fun r => h (w :: r))) v
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def filt (H : ℕ) (v : List W) : List W := List.rec (motive := fun _ => List W) [] (fun w _ ih => Bool.rec (motive := fun _ => List W) ih (w :: ih) (hb H w.s)) v
def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g fuel H HN k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => node (look l m g fuel (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub k 2) s)
        v.length z v (pairsQ q q')) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z (Nat.succ q) v v)) true
        (node (look l m g fuel (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub k 1) s) v.length z v (pairsP q)))) (pos s) l m g (Nat.sub k s) v.length z 0 v (filt HN v))) true
      (node (look l m g fuel (Nat.sub k 1) t) (pos t) l m g (Nat.sub k t) v.length z v (pairsC H))) true (Nat.ble v.length 1)
def startv (l m g B K t H HN : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H HN K t z r) (pos t) l g (Nat.sub (Nat.succ K) t) v.length (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (Nat.beq (cov (pos t) l v) l)
end
lemma frc_eq (v : List W) : ∀ h, frc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c => frc v fun r => h (⟨s, a, b, c⟩ :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {v : List W} : ∀ {h : List W → Bool}, anySub v h = false → ∀ r, r.Sublist v → h r = false := by
  induction v with
  | nil => intro h hh r hr; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro h hh r hr
    change (Bool.rec (motive := fun _ => Bool) (anySub v h) true (anySub v fun r => h (w :: r)) : Bool) = false at hh
    rw [bR] at hh
    cases h1 : anySub v (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1, Bool.cond_false] at hh
      cases hr with
      | cons _ hr => exact ih hh r hr
      | cons_cons _ hr => exact ih h1 _ hr
lemma addS_cons (o w : W) (t : List W) : addS o (w :: t) = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then w :: t else o :: w :: t) else w :: addS o t := by
  change Bool.rec (motive := fun _ => List W) (w :: addS o t) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s) = _
  cases Nat.ble w.s o.s <;> cases Nat.beq o.s w.s <;> rfl
def Srt (v : List W) : Prop := v.Pairwise (fun a b => b.s < a.s)
lemma addS_spec {o : W} {v : List W} (hv : Srt v) : Srt (addS o v) ∧ (∀ w ∈ addS o v, w = o ∨ w ∈ v) ∧
    (∃ w ∈ addS o v, w.s = o.s) ∧ ∀ w ∈ v, w ∈ addS o v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addS], ⟨o, by simp [addS], rfl⟩, by simp⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2, i3, i4⟩ := ih hp.2
    rw [addS_cons]
    cases h1 : Nat.ble x.s o.s with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o.s x.s with
      | true => exact ⟨hv, fun w hw => Or.inr hw, ⟨x, by simp, (Nat.eq_of_beq_eq_true h2).symm⟩, fun w hw => hw⟩
      | false =>
        have hne : o.s ≠ x.s := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w hw => by simpa using hw, ⟨o, by simp, rfl⟩, fun w hw => by simp at hw ⊢; tauto⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o.s < x.s := by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, i1⟩, fun w hw => ?_, ?_, fun w hw => ?_⟩
      · rcases i2 w hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · rcases i2 w hw with h | h <;> simp [h]
      · obtain ⟨w, hw, e⟩ := i3; exact ⟨w, by simp [hw], e⟩
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · exact Or.inr (i4 w hw)
lemma avl_spec (P : List ℕ) (m : ℕ) (L : List ℕ) : Srt (avl P m L) ∧ (∀ w ∈ avl P m L, ∃ x ∈ L, w = mkW P (x &&& m)) ∧
    ∀ x ∈ L, x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ avl P m L, w.s = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl], by simp⟩
  | cons y L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have e : avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else bif Nat.beq (Nat.land y m) m then avl P m L else addS (mkW P (Nat.land y m)) (avl P m L) := by
      change Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) m)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    have old : ∀ w ∈ avl P m L, ∃ x ∈ y :: L, w = mkW P (x &&& m) := fun w hw => by
      obtain ⟨x, hx, e⟩ := i2 w hw; exact ⟨x, by simp [hx], e⟩
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd (Nat.eq_of_beq_eq_true h1) h2
      · exact i3 x hx h2 h3
    | false =>
      cases h1' : Nat.beq (Nat.land y m) m with
      | true =>
        refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd (Nat.eq_of_beq_eq_true h1') h3
        · exact i3 x hx h2 h3
      | false =>
        obtain ⟨j1, j2, j3, j4⟩ := addS_spec (o := mkW P (Nat.land y m)) i1
        refine ⟨j1, fun w hw => ?_, fun x hx h2 h3 => ?_⟩
        · rcases j2 w hw with rfl | h
          · exact ⟨y, by simp, rfl⟩
          · exact old w h
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact j3
          · obtain ⟨w, hw, e⟩ := i3 x hx h2 h3; exact ⟨w, j4 w hw, e⟩
lemma filt_mem {H : ℕ} {v : List W} {w : W} (hw : w ∈ v) (hH : hb H w.s = true) : w ∈ filt H v := by
  induction v with
  | nil => simp at hw
  | cons x v ih =>
    have e : filt H (x :: v) = bif hb H x.s then x :: filt H v else filt H v := by
      change Bool.rec (motive := fun _ => List W) (filt H v) (x :: filt H v) (hb H x.s) = _
      cases hb H x.s <;> rfl
    rw [e]
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · rw [hH]; simp
    · cases hb H x.s <;> simp [ih hw]
lemma pairsC_false {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.s b.s) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
lemma topC_succ {l m g fuel H HN k t z : ℕ} {v : List W} (h : topC l m g fuel H HN k t z v = false) :
    2 ≤ v.length ∧ node (look l m g fuel (k - 1) t) (pos' t) l m g (k - t) v.length z v (pairsC H) = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => bif node (look l m g fuel (k - 2) s) (pos' s) l m g (k - 1 - s) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => node (look l m g fuel (k - 3) s) (pos' s) l m g (k - 2 - s) v.length z v (pairsQ q q'))
        (pos' s) l m g (k - 1 - s) v.length z (q + 1) v v)) (pos' s) l m g (k - s) v.length z 0 v (filt HN v) = false := by
  simp only [topC, bR, pos_eq] at h
  cases h0 : Nat.ble v.length 1 with
  | true => rw [h0] at h; simp at h
  | false =>
    rw [h0, Bool.cond_false] at h
    have hlen : 2 ≤ v.length := by
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
    cases h1 : node (look l m g fuel (Nat.sub k 1) t) (pos' t) l m g (Nat.sub k t) v.length z v (pairsC H) with
    | true => rw [h1] at h; simp at h
    | false =>
      rw [h1, Bool.cond_false] at h
      refine ⟨hlen, rfl, ?_⟩
      rintro s rfl
      exact h
def KP (M : List (ℕ × ℕ)) (x y : ℕ) : Prop := ∃ p ∈ M, hb p.1 (x + y) = true
def KN (M : List (ℕ × ℕ)) (x : ℕ) : Prop := ∃ p ∈ M, hb p.2 x = true
lemma topC_sound {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T) {fuel k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)} (hlen : 2 ≤ v.length)
    (h : ∀ p ∈ M, topC l m g fuel p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) :
    ∀ k' ≤ k, Min m T k' t S → ¬ FM m T k' t S (KP M) (KN M) := by
  refine step_sound X (look_sound X fuel) hs hlen (fun x y hxy ⟨p, hpM, hpx⟩ => ⟨pairsC p.1, (topC_succ (h p hpM)).2.1, ?_⟩)
    (fun s hst a ha ⟨p, hpM, hpa⟩ => ⟨_, filt_mem ha hpa, (topC_succ (h p hpM)).2.2 s hst⟩)
  intro h hp a b ha hb' hax hby
  have hpw := pairsC_false hp
  have : Std.Symm (fun a b : L_meta_3825_aux.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
    ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
  refine (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
    (List.mem_map_of_mem ha) (List.mem_map_of_mem hb') ?_ ?_
  · intro e
    have : a.s = b.s := congrArg L_meta_3825_aux.X.s e
    exact hxy (by rw [← hax, ← hby, this])
  · change hb p.1 (a.s + b.s) = true; rw [hax, hby]; exact hpx
def tab : List (ℕ × ℕ) := [(16,13), (64,13), (128,13), (1,12), (2,12), (4,12), (8,12), (32,12), (256,12), (17,11), (24,11), (66,11), (80,11), (132,11), (144,11), (160,11), (192,11), (320,11), (3,9), (6,9), (12,9), (18,9), (20,9), (33,9), (48,9), (65,9), (68,9), (72,9), (96,9), (129,9), (130,9), (136,9), (264,9), (272,9), (288,9), (384,9), (5,8), (9,8), (10,8), (34,8), (36,8), (40,8), (257,8), (258,8), (260,8), (19,8), (25,8), (28,8), (49,8), (67,8), (70,8), (81,8), (82,8), (88,8), (134,8), (140,8), (145,8), (148,8), (152,8), (161,8), (164,8), (176,8), (194,8), (196,8), (208,8), (224,8), (280,8), (322,8), (328,8), (336,8), (352,8), (416,8), (448,8), (7,7), (14,7), (21,7), (26,7), (35,7), (56,7), (74,7), (84,7), (98,7), (112,7), (133,7), (146,7), (162,7), (168,7), (193,7), (200,7), (268,7), (273,7), (289,7), (296,7), (321,7), (324,7), (388,7), (400,7), (22,6), (76,6), (97,6), (131,6), (304,6), (392,6), (11,5), (13,5), (37,5), (38,5), (41,5), (42,5), (44,5), (50,5), (52,5), (69,5), (73,5), (100,5), (104,5), (137,5), (138,5), (259,5), (261,5), (262,5), (265,5), (266,5), (274,5), (276,5), (290,5), (292,5), (385,5), (386,5)]
def pr (Z : ℕ) : List (ℕ × ℕ) := tab.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
def WZ (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL, x = w &&& mz Z}
def Imp (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol (mz Z) (tz Z) q (C (mz Z) (WZ Z))
def PZ (Z : ℕ) : List ℕ := (pr Z).map (fun e => mz e.1)
def pOk (Z : ℕ) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && (pr Z).all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
noncomputable def chk (Z K t H HN : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B =>
    frc (avl P m rawL) (fun v => anySub v (fun r => st l fun l => st m fun m => st g fun g => st B fun B => startv l m g B K t H HN r)))
    (pL ((pr Z).map fun e => 16 + (K - e.2)))) (pL ((pr Z).map fun _ => 16))) (PZ Z)) (mz Z)) (lz Z)
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ Z) : Im (mz Z') S ⊆ WZ Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩
lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Z K : ℕ) : pL ((pr Z).map fun e => 16 + (K - e.2)) = pk (PZ Z).length (fun j => 16 + (K - ((pr Z).getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
theorem imp_of {Z L : ℕ} (hp : pOk Z = true) (hL : L ≤ 15) (hI : ∀ e ∈ pr Z, Imp e.1 e.2)
    (hb : (∃ e ∈ pr Z, L ≤ e.2) ∨ ∀ t < L, ∃ M : List (ℕ × ℕ), M ≠ [] ∧ (∀ p ∈ M, chk Z (L - 1) t p.1 p.2 = false) ∧
      ∀ (k : ℕ) (S : Finset ℕ), (S : Set ℕ) ⊆ WZ Z → Min (mz Z) (tz Z) k t S → 2 ≤ S.card →
        ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ Z ∧ Min (mz Z) (tz Z) k t S' ∧ FM (mz Z) (tz Z) k t S' (KP M) (KN M)) : Imp Z L := by
  intro q hq hsol
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  classical
  have hex : ∃ q, Sol (mz Z) (tz Z) q (C (mz Z) (WZ Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm : Min (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ pr Z, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ WZ Z → ∀ e ∈ pr Z, ∀ q < e.2, ¬ Sol (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro S hSW e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno S hSW e he q' (by omega) hs'
  obtain ⟨M, hM, hchk, hsym⟩ := hb t (by omega)
  have key : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ WZ Z → Min (mz Z) (tz Z) k t S → 2 ≤ S.card ∧ ¬ FM (mz Z) (tz Z) k t S (KP M) (KN M) := by
    clear h0 h1 hbd hl hm hSW hCS hS S
    intro S hSW hm
    have hl := hm.1
    have hbd : ∀ x ∈ S, x &&& mz Z = x := by
      intro x hx
      obtain ⟨w, _, rfl⟩ := hSW hx
      rw [Nat.and_assoc, Nat.and_self]
    obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
    obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Z) (mz Z) rawL
    set v := (avl (PZ Z) (mz Z) rawL).filter (fun w => decide (w.s ∈ S)) with hv
    have hsub : v.Sublist (avl (PZ Z) (mz Z) rawL) := List.filter_sublist
    have hnd : (v.map W.s).Nodup := by
      rw [List.Nodup, List.pairwise_map]
      exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
    have hrep : Rep v S := by
      refine ⟨hnd, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [hv, List.mem_filter] at hw; simpa using hw.2
      · intro hx
        obtain ⟨w, hw, rfl⟩ := hSW hx
        obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
        exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
    have hwok : ∀ w ∈ v, WOk (PZ Z) w := by
      intro w hw
      obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
    have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good hx Z
    have hPlen : (PZ Z).length = (pr Z).length := by simp [PZ]
    have hPget : ∀ j < (PZ Z).length, (PZ Z).getD j 0 = mz ((pr Z).getD j (0, L - 1)).1 ∧ (pr Z).getD j (0, L - 1) ∈ pr Z := by
      intro j hj
      rw [hPlen] at hj
      simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
    have X : Ctx (PZ Z) (lz Z) (mz Z) (pL ((pr Z).map fun _ => 16)) (tz Z) := by
      refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
      · obtain ⟨e1, e2⟩ := hPget j hj
        have h3 := hproj _ e2
        rw [e1, tz_sub h3.1]; exact h3
      · rw [pL_pk, List.length_map, hPlen]
        refine pk_congr fun j hj => ?_
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
    have hcl : Cl (PZ Z) (tz Z) (L - 1) (fun j => L - 1 - ((pr Z).getD j (0, L - 1)).2) S := by
      intro j hj q hq
      obtain ⟨e1, e2⟩ := hPget j hj
      have hq' : q + (L - 1 - ((pr Z).getD j (0, L - 1)).2) < L - 1 := hq
      rw [e1]; exact hno S hSW _ e2 q (by omega)
    have hle := cnt_le X hrep hwok hcl hm (by omega)
    have hst : StOk (PZ Z) (tz Z) (lz Z) (L - 1) (pL ((pr Z).map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
      refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
      rw [sumc_eq hwok, pk16, pk_sub]
      intro j hj; have := hle j hj; omega
    have hcov : Nat.beq (cov (pos t) (lz Z) v) (lz Z) = true := by
      rw [Nat.beq_eq]
      apply Nat.eq_of_testBit_eq; intro i
      cases hli : (lz Z).testBit i with
      | false =>
        by_contra hc
        obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
        rw [sp_bit, hli] at hw; simp at hw
      | true =>
        rw [cov_bit]
        obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
        obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
        obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
        exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
    have hsz := hm.size.1
    have hcard := hrep.card
    have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
      change v.length ≤ L - 1 + 1 - t; omega)
    have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL ((pr Z).map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL ((pr Z).map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
      intro p hpM
      have h2 := hchk p hpM
      simp only [chk, frc_eq, st_eq] at h2
      have h3 := anySub_false h2 v hsub
      simp only [startv, bR, hcov, hble, Bool.cond_true] at h3
      exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) (pos_eq t) rfl rfl h3
    obtain ⟨p0, hp0M⟩ := List.exists_mem_of_ne_nil M hM
    have hlen := (topC_succ (all p0 hp0M)).1
    exact ⟨by rw [hcard]; exact hlen, topC_sound X hlen all hst k (by omega) hm⟩
  obtain ⟨S', hS', hm', hfm⟩ := hsym k S hSW hm (key S hSW hm).1
  exact (key S' hS' hm').2 hfm
def PIK : ℕ := 0x22ebc778cf31e43c5780ef9e4bc3788efddebcb784f29e0bbc896ee1dbbba772eda22b89710e2dc538787ee5dcb39a73ce65cab9171ee6dca398720e39ceb93738e49c6c2c706e09c2b8484ed5daa34e6a6d31adb516a4d61aab5669ad2dad3506b2d3da5414660cbd9933165d03995b2a658ca604ae55c0b716fada5c4ba1732de5c6b916dad95d2b8573add5b0fd96aad45a6b59693f0556aa956aac552fa958ab0564acd57be454ca9553be07b4f49e83dc7b2f7dedbd77b0f55eb3d179ef79ea3dd7a6f39e6c5a8a113a2ac598b916e2c4538a913e26c578a515a28c4c77712223c4a893119daba774cea5d43a575ee89d0ba3740ea9d93b1768ecdd83a4758eb9d6bab73f0ee18c2f86d0f21d43487d0f61cc358610ba1c43386f0ca16b8c88510622443880e1a14c288570a9c0b7a6f2dedbc37c6fce01bfb7d6eedd5bb3746d8d9db2b706dedb5b73736d4dadb33646e4da5b8b686c6d899db3c67ace59d35c8430660bc1e84d0720ec2584707e1041882d0920dc22835055a4b0560cc1d81b04686afd602bd57ccf9afb606c2d75af33866ccdd9a3356670460841382503d96c0b81b032053285f0bd1792fe5fabed7e2f75f4c017b2f35e2c057caff5eabc18aaec5dabb975b10574ae55dab8616ad95ab0868cd1da434468ac098d31e630c9191b21644c7d8cb27640c758bb26638c958db165dec4989b14622ba9fdc027f3006043fe7ff00dfd40780b001fc4067fb011fe3f75aefc9fabf47e6fc568ace59eb41662cd596a8151aa1544a7d62a9c53aa6d60b41684cfda02bc61ac3d8730c56ec2984ab47ccf9df4be87caab9f6bec7defb9f5aa87c2f8df12a4592b1d642ca58ca7961ac4584a694a295526a594c29952ea494528851ea354728950ea4546290516a19429ab5066a0d4a804d29f933a7c2be9e8b09624ee570aea7433a9c8cda7029c9b8a826c2989a93fa684fa998dba6436a6d1309994be65ccb25c4ae9612ca5a4b69592a2554a65f928981300938be17b496524a524825e91886a443de9086d24014e8f89612d47642d1c9082128d8f6a343d68c86b8d845e3506aa2c1448a8520a544e26c4d09812a24c4e0a013e2644f09612825c4e89242e484902141f63e9088f81ee838ef20c3b882864a0818e319028760ea8083c2000dc1b4358680ce1bc398720d81c43486a0e0198329f04867b91a9ec4667a88d91a3ce4788e9e41ea788798f23be834eea0b3b6758eb9d83b2768ea9ce39a72ce41c739e750e99cc3a4724e51d13a0718e28c4386308609c00c418cde9bc376698d29b84ca6d931a62366624d895a35e560ab9ac5086a940a8234e6e8dc9a434067cd09a33446793999c4e2669301984bc974ca98730c648c218331e554c69532a4628d918832864cc29913206092824f2fe948bea4d4985e8bc97828a510ba9472e64f49e13926c4f8a11412764e8a01372704fc9a9342c69e13c9604f65793aa762b66c0ac9ae35a558c715431862ca8a6d29e9bca6a6b296925251482e8518bb9762865b4b61692cc5b8b91712d65a8b81672d05bcb29642664c49913048e4b91e23d2564a09492a24e4108192420c4890b21523e798f291c3d27a08c8cf22e3486891411a2308889011e4392290c4744291ba3820e48c8292624a4087f0fd1fe404800fc4268487ca1041e3d8f18f43c2780788cd1de32c7688a1d620c410800fa210440871022183f07c0fe2143d87a1b69046ca3046235916a2e1a64588a8d0230338780cc1dc329048c840e818629c4186708e08c01782ec5e8bf17c2e8300b80b21602b0530b41782e8570b81502a85b0a4144280a847e299142291468ac50a2043e8750ca2144c8950f22443487111a1b4448604891021e238899121163b0448e51c83886f0e61d43a4718e81be384738e01ba3703ca010ee811018743f27e0fb1f33f47fcff1f73fa7d0fa9fc3f67c8f886437c6fc308b90be2c8588af1582cc5b8b61602d4568ae1682ac550a909e124240460861282704d08e130220450961042104002e07c1a0260500bc0a0100020240783d0220b8118220740c8050210180680303b0400f00c81d0620c01602707c04c120180100a81281c07e0100583903c0141983806a00c0002b02a0b41b01b0040a40901601c01c1b80d
def pi0 (i : ℕ) : ℕ := Nat.mod (Nat.shiftRight PIK (Nat.mul 11 i)) 2048
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pi0_ok : ∀ i < NN, pi0 i < NN ∧ pi0 (pi0 i) = i := by decide +kernel
def pi (i : ℕ) : ℕ := if i < NN then pi0 i else if i < NN + NN then NN + pi0 (i - NN) else i
lemma pi_pi (i : ℕ) : pi (pi i) = i := by
  unfold pi
  by_cases h1 : i < NN
  · have := pi0_ok i h1; simp [h1, this]
  · by_cases h2 : i < NN + NN
    · have := pi0_ok (i - NN) (by omega)
      simp [h1, h2, this]; omega
    · simp [h1, h2]
lemma pi_lt {i : ℕ} (h : i < NN + NN) : pi i < NN + NN := by
  unfold pi
  by_cases h1 : i < NN
  · have := pi0_ok i h1; simp [h1]; omega
  · have := pi0_ok (i - NN) (by omega); simp [h1, h]; omega
def rho (w : ℕ) : ℕ := (∑ i ∈ Finset.range (NN + NN), (w.testBit (pi i)).toNat * 2 ^ i) + 2 ^ (NN + NN) * (w >>> (NN + NN))
lemma bits_sum (n : ℕ) (f : ℕ → Bool) : (∑ i ∈ Finset.range n, (f i).toNat * 2 ^ i) < 2 ^ n ∧
    ∀ j, (∑ i ∈ Finset.range n, (f i).toNat * 2 ^ i).testBit j = (decide (j < n) && f j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_comm, Nat.mul_comm]
    have hb : (f n).toNat ≤ 1 := by cases f n <;> simp
    constructor
    · have := ih.1
      have h2 : 2 ^ n * (f n).toNat ≤ 2 ^ n * 1 := Nat.mul_le_mul_left _ hb
      rw [pow_succ]; omega
    · intro j
      rw [Nat.testBit_two_pow_mul_add _ ih.1, ih.2]
      split_ifs with h
      · simp [h, show j < n + 1 by omega]
      · rcases Nat.eq_or_lt_of_le (not_lt.1 h) with rfl | h2
        · cases f n <;> simp
        · have : (f n).toNat.testBit (j - n) = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hb (Nat.one_lt_two_pow (by omega)))
          rw [this]; simp [show ¬ j < n + 1 by omega]
lemma rho_bit (w i : ℕ) : (rho w).testBit i = w.testBit (pi i) := by
  unfold rho
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ (bits_sum _ _).1]
  split_ifs with h
  · rw [(bits_sum _ _).2]; simp [h]
  · rw [Nat.testBit_shiftRight, show NN + NN + (i - (NN + NN)) = i by omega]
    unfold pi; simp [h, show ¬ i < NN by omega]
lemma rho_ext {w w' : ℕ} (h : ∀ i, w.testBit (pi i) = w'.testBit i) : rho w = w' :=
  Nat.eq_of_testBit_eq fun i => by rw [rho_bit, h]
lemma rho_phi (w : ℕ) : rho (rho w) = w := rho_ext fun i => by rw [rho_bit, pi_pi]
lemma rho_op (d : Bool) (a b : ℕ) : rho (op d a b) = op d (rho a) (rho b) :=
  rho_ext fun i => by simp only [op_bit, rho_bit]
lemma rho_xor (a b : ℕ) : rho (a ^^^ b) = rho a ^^^ rho b := rho_ext fun i => by simp only [Nat.testBit_xor, rho_bit]
lemma rho_and (a b : ℕ) : rho (a &&& b) = rho a &&& rho b := rho_ext fun i => by simp only [Nat.testBit_and, rho_bit]
lemma rho_zero : rho 0 = 0 := rho_ext fun i => by simp
lemma rho_inj {a b : ℕ} (h : rho a = rho b) : a = b := by rw [← rho_phi a, h, rho_phi]
def eqv (w w' : ℕ) : Bool := decide (w < 2 ^ (NN + NN)) && decide (w' < 2 ^ (NN + NN)) && (List.range (NN + NN)).all (fun i => w.testBit (pi i) == w'.testBit i)
lemma eqv_phi {w w' : ℕ} (h : eqv w w' = true) : rho w = w' := by
  simp only [eqv, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine rho_ext fun i => ?_
  by_cases hi : i < NN + NN
  · exact h.2 i hi
  · have : pi i = i := by unfold pi; simp [hi, show ¬ i < NN by omega]
    have hp : 2 ^ (NN + NN) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [this, Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]
lemma Sol.rho {m T q : ℕ} {S : Set ℕ} (h : Sol m T q S) : Sol (rho m) (rho T) q (L_meta_3825_aux.rho '' S) := by
  induction h with
  | done h => exact .done ⟨_, h, rfl⟩
  | un h _ ih =>
    refine .un (Set.mem_image_of_mem _ h) ?_
    rw [← rho_xor, ← Set.image_insert_eq]; exact ih
  | @bi _ _ d _ _ h1 h2 _ ih =>
    refine .bi (d := d) (Set.mem_image_of_mem _ h1) (Set.mem_image_of_mem _ h2) ?_
    rw [← rho_op, ← Set.image_insert_eq]; exact ih
lemma Live.rho {m T k t : ℕ} {S : Finset ℕ} (h : Live m T k t S) : Live (rho m) (rho T) k t (S.image L_meta_3825_aux.rho) := by
  induction h with
  | stop => rw [Finset.image_singleton]; exact .stop
  | un _ ih =>
    rw [Finset.image_insert, rho_xor] at ih
    rw [Finset.image_insert]; exact .un ih
  | bi hab _ ih =>
    rw [Finset.image_insert, rho_op] at ih
    rw [Finset.image_insert, Finset.image_insert]
    exact .bi (fun e => hab (rho_inj e)) ih
lemma Un.rho {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : Un (rho m) (rho a) (S.image L_meta_3825_aux.rho) (S'.image L_meta_3825_aux.rho) := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨U.image _, by rw [Finset.image_insert], by rw [Finset.image_insert, rho_xor]⟩
lemma Bi.rho {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi d a b S S') : Bi d (rho a) (rho b) (S.image L_meta_3825_aux.rho) (S'.image L_meta_3825_aux.rho) := by
  obtain ⟨hab, U, rfl, rfl⟩ := h
  exact ⟨fun e => hab (rho_inj e), U.image _, by rw [Finset.image_insert, Finset.image_insert], by rw [Finset.image_insert, rho_op]⟩
def rawS : List ℕ := (([1, 0, 5, 8, 6, 2, 4, 7, 3] : List ℕ).map (fun i => rawP.getD i 0)) ++ [rawP.getD 0 0 ||| rawP.getD 1 0]
def rawT : List (ℕ × ℕ) := rawL.zip rawS
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawT_ok : rawT.all (fun p => eqv p.1 p.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawT_fst : rawT.map Prod.fst = rawL := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawT_snd : rawT.all (fun p => rawL.contains p.2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_phi : eqv TG TG = true := by decide +kernel
lemma raw_phi {w : ℕ} (hw : w ∈ rawL) : ∃ p ∈ rawT, p.1 = w ∧ rho w = p.2 ∧ p.2 ∈ rawL := by
  rw [← rawT_fst, List.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  refine ⟨p, hp, rfl, eqv_phi (List.all_eq_true.1 rawT_ok p hp), ?_⟩
  simpa using List.all_eq_true.1 rawT_snd p hp
lemma WZ_phi {Z Z' : ℕ} (h : rho (mz Z') = mz Z) {x : ℕ} (hx : x ∈ WZ Z') : rho x ∈ WZ Z := by
  obtain ⟨w, hw, rfl⟩ := hx
  obtain ⟨p, _, _, e, hp⟩ := raw_phi hw
  exact ⟨p.2, hp, by rw [rho_and, h, e]⟩
lemma tz_phi {Z Z' : ℕ} (h : rho (mz Z') = mz Z) : rho (tz Z') = tz Z := by
  simp only [tz, nl]; rw [rho_and, h, eqv_phi TG_phi]
theorem imp_sym {Z Z' L : ℕ} (h : Imp Z L) (he : eqv (mz Z') (mz Z) = true) : Imp Z' L := by
  intro q hq hs
  have h' := eqv_phi he
  have h2 := hs.rho
  rw [h', tz_phi h'] at h2
  refine h q hq (h2.mono le_rfl ?_)
  rintro _ ⟨x, hx | hx, rfl⟩
  · exact Or.inl (WZ_phi h' hx)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [rho_zero]; exact Or.inr (Set.mem_insert _ _)
    · rw [h']; exact Or.inr (Set.mem_insert_of_mem _ rfl)
def kOk (M : List (ℕ × ℕ)) : Bool := rawT.all (fun p => (M.any (fun x => hb x.2 p.1) || M.any (fun x => hb x.2 p.2)) &&
  rawT.all (fun q => Nat.beq p.1 q.1 || M.any (fun x => hb x.1 (p.1 + q.1)) || M.any (fun x => hb x.1 (p.2 + q.2))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma m0_full : rawL.all (fun w => Nat.beq (Nat.land w (mz 0)) w) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma m0_phi : eqv (mz 0) (mz 0) = true := by decide +kernel
lemma WZ0 {x : ℕ} (hx : x ∈ WZ 0) : x ∈ rawL := by
  obtain ⟨w, hw, rfl⟩ := hx
  have := List.all_eq_true.1 m0_full w hw
  rw [Nat.beq_eq, nl] at this; rwa [this]
lemma sym0 {M : List (ℕ × ℕ)} (hM : kOk M = true) (k t : ℕ) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ WZ 0) (hm : Min (mz 0) (tz 0) k t S)
    (hc : 2 ≤ S.card) : ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ 0 ∧ Min (mz 0) (tz 0) k t S' ∧ FM (mz 0) (tz 0) k t S' (KP M) (KN M) := by
  have pm := eqv_phi m0_phi
  have pt := tz_phi pm
  have hN : ∀ a ∈ S, KN M a ∨ KN M (rho a) := by
    intro a ha
    obtain ⟨p, hp, e1, e2, _⟩ := raw_phi (WZ0 (hS ha))
    have := List.all_eq_true.1 hM p hp
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at this
    rw [e2, ← e1]; exact this.1.imp id id
  have hP : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → KP M a b ∨ KP M (rho a) (rho b) := by
    intro a ha b hb hab
    obtain ⟨p, hp, e1, e2, _⟩ := raw_phi (WZ0 (hS ha))
    obtain ⟨q, hq, f1, f2, _⟩ := raw_phi (WZ0 (hS hb))
    have := List.all_eq_true.1 hM p hp
    simp only [Bool.and_eq_true] at this
    have := List.all_eq_true.1 this.2 q hq
    simp only [Bool.or_eq_true, List.any_eq_true] at this
    rw [e2, f2, ← e1, ← f1]
    rcases this with (h | h) | h
    · exact absurd (e1.symm.trans ((Nat.eq_of_beq_eq_true h).trans f1)) hab
    · exact Or.inl h
    · exact Or.inr h
  have hS' : ((S.image L_meta_3825_aux.rho : Finset ℕ) : Set ℕ) ⊆ WZ 0 := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact WZ_phi pm (hS hy)
  have hm' : Min (mz 0) (tz 0) k t (S.image L_meta_3825_aux.rho) := by
    have h1 := hm.1.rho
    rw [pm, pt] at h1
    refine ⟨h1, fun q hq hs => hm.2 q hq ?_⟩
    have h2 := hs.rho
    rw [pm, pt] at h2
    refine h2.mono le_rfl ?_
    rintro _ ⟨x, hx | hx, rfl⟩
    · simp only [Finset.coe_image, Set.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [rho_phi]; exact Or.inl hy
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx, rho_zero]; exact Or.inr (Set.mem_insert _ _)
      · rw [hx, pm]; exact Or.inr (Set.mem_insert_of_mem _ rfl)
  rcases first_move k t S hm hc with ⟨k0, d, a, b, S1, e, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, e, e', hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, e, e', hu, hne, hu', hb, hl⟩
  · rcases hP a hb.sub.1 b hb.sub.2.1 hb.1 with h | h
    · exact ⟨S, hS, hm, Or.inl ⟨k0, d, a, b, S1, e, h, hb, hl⟩⟩
    · refine ⟨_, hS', hm', Or.inl ⟨k0, d, rho a, rho b, _, e, h, hb.rho, ?_⟩⟩
      have := hl.rho; rwa [pm, pt] at this
  · rcases hN a hu.sub.1 with h | h
    · exact ⟨S, hS, hm, Or.inr (Or.inl ⟨k0, t0, a, d, c, S1, S2, e, e', h, hu, hb, hl⟩)⟩
    · have h1 := hu.rho; rw [pm] at h1
      have h2 := hb.rho; rw [rho_xor, pm] at h2
      have h3 := hl.rho; rw [pm, pt] at h3
      exact ⟨_, hS', hm', Or.inr (Or.inl ⟨k0, t0, rho a, d, rho c, _, _, e, e', h, h1, h2, h3⟩)⟩
  · rcases hN a hu.sub.1 with h | h
    · exact ⟨S, hS, hm, Or.inr (Or.inr ⟨k0, t0, a, a', d, S1, S2, S3, e, e', h, hu, hne, hu', hb, hl⟩)⟩
    · have h1 := hu.rho; rw [pm] at h1
      have h1' := hu'.rho; rw [pm] at h1'
      have h2 := hb.rho; rw [rho_xor, rho_xor, pm] at h2
      have h3 := hl.rho; rw [pm, pt] at h3
      refine ⟨_, hS', hm', Or.inr (Or.inr ⟨k0, t0, rho a, rho a', d, _, _, _, e, e', h, h1, fun e => hne ?_, h1', h2, h3⟩)⟩
      apply rho_inj; rw [e, rho_xor, pm]
def FF : ℕ := 2 ^ MM - 1
lemma hbF (x : ℕ) : hb FF x = true := by
  have h : x % MM < MM := Nat.mod_lt _ (by decide)
  have h2 : FF.testBit (x % MM) = true := by rw [FF, Nat.testBit_two_pow_sub_one]; simpa using h
  unfold hb
  rw [Nat.beq_eq]
  change (FF >>> (x % MM)) &&& 1 = 1
  rw [Nat.testBit] at h2
  rw [Nat.and_one_is_mod]
  simp only [Nat.one_and_eq_mod_two, bne_iff_ne, ne_eq] at h2
  omega
lemma FM_mono {m T k t : ℕ} {S : Finset ℕ} {A A' : ℕ → ℕ → Prop} {B B' : ℕ → Prop} (h : FM m T k t S A B) (h1 : ∀ x y, A x y → A' x y)
    (h2 : ∀ x, B x → B' x) : FM m T k t S A' B' := by
  rcases h with ⟨k0, d, a, b, S1, e, q, h⟩ | ⟨k0, t0, a, d, c, S1, S2, e, e', q, h⟩ | ⟨k0, t0, a, a', d, S1, S2, S3, e, e', q, h⟩
  · exact Or.inl ⟨k0, d, a, b, S1, e, h1 _ _ q, h⟩
  · exact Or.inr (Or.inl ⟨k0, t0, a, d, c, S1, S2, e, e', h2 _ q, h⟩)
  · exact Or.inr (Or.inr ⟨k0, t0, a, a', d, S1, S2, S3, e, e', h2 _ q, h⟩)
theorem imp_full {Z L : ℕ} (hp : pOk Z = true) (hL : L ≤ 15) (hI : ∀ e ∈ pr Z, Imp e.1 e.2)
    (hb : (∃ e ∈ pr Z, L ≤ e.2) ∨ ∀ t < L, chk Z (L - 1) t FF FF = false) : Imp Z L := by
  refine imp_of hp hL hI (hb.imp id fun h t ht => ⟨[(FF, FF)], by simp, fun p hp => ?_, fun k S hS hm hc => ⟨S, hS, hm, ?_⟩⟩)
  · simp only [List.mem_singleton] at hp; subst hp; exact h t ht
  · exact FM_mono (FM_of hm hc) (fun x y _ => ⟨(FF, FF), by simp, hbF _⟩) (fun x _ => ⟨(FF, FF), by simp, hbF _⟩)
noncomputable def okT (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk Z (L - 1) t FF FF)
noncomputable def okE (e : ℕ × ℕ) : Bool := pOk e.1 && Nat.ble e.2 15 && ((pr e.1).any (fun x => Nat.ble e.2 x.2) || okT e.1 e.2 (List.range e.2))
def kFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r) && M.any (fun p => hb p.2 r))
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
lemma sym_full {Z t : ℕ} {M : List (ℕ × ℕ)} (hM : kFull M = true) (k : ℕ) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ WZ Z) (hm : Min (mz Z) (tz Z) k t S)
    (hc : 2 ≤ S.card) : ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ Z ∧ Min (mz Z) (tz Z) k t S' ∧ FM (mz Z) (tz Z) k t S' (KP M) (KN M) := by
  have h : ∀ x, (∃ p ∈ M, hb p.1 x = true) ∧ ∃ p ∈ M, hb p.2 x = true := by
    intro x
    have := List.all_eq_true.1 hM (x % MM) (List.mem_range.2 (Nat.mod_lt _ (by decide)))
    simp only [Bool.and_eq_true, List.any_eq_true, ← hb_mod] at this
    exact this
  exact ⟨S, hS, hm, FM_mono (FM_of hm hc) (fun x y _ => (h (x + y)).1) (fun x _ => (h x).2)⟩
lemma imp_okE {e : ℕ × ℕ} (h : okE e = true) (hI : ∀ e' ∈ pr e.1, Imp e'.1 e'.2) : Imp e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  refine imp_full h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) id)
def tab1 : List (ℕ × ℕ) := [(16, 13), (64, 13), (128, 13), (1, 12), (2, 12), (4, 12), (8, 12), (32, 12), (256, 12)]
def tab2 : List (ℕ × ℕ) := [(17, 11), (24, 11), (66, 11), (80, 11), (132, 11), (144, 11), (160, 11), (192, 11), (320, 11), (3, 9), (6, 9), (12, 9), (18, 9), (20, 9), (33, 9), (48, 9), (65, 9), (68, 9), (72, 9), (96, 9), (129, 9), (130, 9), (136, 9), (264, 9), (272, 9), (288, 9), (384, 9), (5, 8), (9, 8), (10, 8), (34, 8), (36, 8), (40, 8), (257, 8), (258, 8), (260, 8)]
def tab3 : List (ℕ × ℕ) := [(19, 8), (25, 8), (28, 8), (49, 8), (67, 8), (70, 8), (81, 8), (82, 8), (88, 8), (134, 8), (140, 8), (145, 8), (148, 8), (152, 8), (161, 8), (164, 8), (176, 8), (194, 8), (196, 8), (208, 8), (224, 8), (280, 8), (322, 8), (328, 8), (336, 8), (352, 8), (416, 8), (448, 8), (7, 7), (14, 7), (21, 7), (26, 7), (35, 7), (56, 7), (74, 7), (84, 7), (98, 7), (112, 7), (133, 7), (146, 7), (162, 7), (168, 7), (193, 7), (200, 7), (268, 7), (273, 7), (289, 7), (296, 7), (321, 7), (324, 7), (388, 7), (400, 7), (22, 6), (76, 6), (97, 6), (131, 6), (304, 6), (392, 6), (11, 5), (13, 5), (37, 5), (38, 5), (41, 5), (42, 5), (44, 5), (50, 5), (52, 5), (69, 5), (73, 5), (100, 5), (104, 5), (137, 5), (138, 5), (259, 5), (261, 5), (262, 5), (265, 5), (266, 5), (274, 5), (276, 5), (290, 5), (292, 5), (385, 5), (386, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr3 : tab3.all (fun e => (pr e.1).isEmpty) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr2 : tab2.all (fun e => (pr e.1).all (fun x => tab3.contains x)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr1 : tab1.all (fun e => (pr e.1).all (fun x => tab2.contains x || tab3.contains x)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr0 : (pr 0).all (fun x => tab1.contains x || tab2.contains x || tab3.contains x) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3 : tab3.all okE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2l : ([(3, 9), (6, 9), (12, 9), (18, 9), (20, 9), (33, 9), (48, 9), (65, 9), (68, 9), (72, 9), (96, 9), (129, 9), (130, 9), (136, 9), (264, 9), (272, 9), (288, 9), (384, 9), (5, 8), (9, 8), (10, 8), (34, 8), (36, 8), (40, 8), (257, 8), (258, 8), (260, 8)] : List (ℕ × ℕ)).all okE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c17 : okE (17, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c24 : okE (24, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c80 : okE (80, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c132 : okE (132, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c144 : okE (144, 11) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66 : eqv (mz 66) (mz 17) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s320 : eqv (mz 320) (mz 24) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s160 : eqv (mz 160) (mz 132) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s192 : eqv (mz 192) (mz 144) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c1l : ([(1, 12), (2, 12), (4, 12), (8, 12), (32, 12), (256, 12)] : List (ℕ × ℕ)).all okE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16 : pOk 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c16_0 : chk 16 12 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c16_2 : chk 16 12 2 FF FF = false := by decide +kernel
def N16 : List (ℕ × ℕ) := [(0x3fffffffffffffdfffffffefffff7ffffffbffffdffffff7ffffff, 0x3fff7ffffffffffeffffffffffffffffffffeffffffff7ffffffff), (0x4000000000008000000, 0x80000000000000000000000000000000100000000800000000), (0x2000000010000080000000000020000000000000, 0x100000000000000000000000000000000000000)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k16 : kFull N16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r16_0 : chk 16 12 1 0x3fffffffffffffdfffffffefffff7ffffffbffffdffffff7ffffff 0x3fff7ffffffffffeffffffffffffffffffffeffffffff7ffffffff = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r16_1 : chk 16 12 1 0x4000000000008000000 0x80000000000000000000000000000000100000000800000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r16_2 : chk 16 12 1 0x2000000010000080000000000020000000000000 0x100000000000000000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c16_r : okT 16 13 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p128 : pOk 128 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c128_0 : chk 128 12 0 FF FF = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c128_2 : chk 128 12 2 FF FF = false := by decide +kernel
def N128 : List (ℕ × ℕ) := [(0x3fffffffbfffffbffffffffffdbfffffffffffffffffffffffffff, 0x3fffffffdfffffffffffffffffdfffffffffffffffffffffffffed), (0x4000004000000000004000000000000000000000000000, 0x2000000000000000000000000000000000000000000010), (0x20000000000000000020000000000000000000000000000, 0x2000000000000000000000000002)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k128 : kFull N128 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r128_0 : chk 128 12 1 0x3fffffffbfffffbffffffffffdbfffffffffffffffffffffffffff 0x3fffffffdfffffffffffffffffdfffffffffffffffffffffffffed = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r128_1 : chk 128 12 1 0x4000004000000000004000000000000000000000000000 0x2000000000000000000000000000000000000000000010 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r128_2 : chk 128 12 1 0x20000000000000000020000000000000000000000000000 0x2000000000000000000000000002 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c128_r : okT 128 13 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64 : eqv (mz 64) (mz 16) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p0 : pOk 0 = true := by decide +kernel
def M0 : List (ℕ × ℕ) := [(0x90000044088000021100000000102000400810000010000, 0x1020000000000000000000000000040000100200000004000000), (0x40000000000000000000000000000800000, 0x0), (0x800000000000000001000, 0x0), (0x8000000000000000000000000000000000008000000000200, 0x0), (0x1000000000000080000000400000000000000000000000, 0x0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k0 : kOk M0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_0 : chk 0 14 0 0x90000044088000021100000000102000400810000010000 0x1020000000000000000000000000040000100200000004000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_1 : chk 0 14 0 0x40000000000000000000000000000800000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_2 : chk 0 14 0 0x800000000000000001000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_3 : chk 0 14 0 0x8000000000000000000000000000000000008000000000200 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r0_4 : chk 0 14 0 0x1000000000000080000000400000000000000000000000 0x0 = false := by decide +kernel
def M1 : List (ℕ × ℕ) := [(0x90000044088000021100000000102000400810000010000, 0x1000000000000000000000000000040000000000000000000000), (0x40000000000000000000000000000000000, 0x0), (0x200, 0x0), (0x800000, 0x0), (0x1000, 0x0), (0x80000000000800000000000000000000, 0x0), (0x8000000000000000000000000000000000000000000000000, 0x20000000000000000000000000000000100000000000000000), (0x400000000008000000000000, 0x0), (0x1000000000000000000000000000000000000000000000, 0x200000004000000)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k1 : kOk M1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_0 : chk 0 14 1 0x90000044088000021100000000102000400810000010000 0x1000000000000000000000000000040000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_1 : chk 0 14 1 0x40000000000000000000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_2 : chk 0 14 1 0x200 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_3 : chk 0 14 1 0x800000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_4 : chk 0 14 1 0x1000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_5 : chk 0 14 1 0x80000000000800000000000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_6 : chk 0 14 1 0x8000000000000000000000000000000000000000000000000 0x20000000000000000000000000000000100000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_7 : chk 0 14 1 0x400000000008000000000000 0x0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1_8 : chk 0 14 1 0x1000000000000000000000000000000000000000000000 0x200000004000000 = false := by decide +kernel
def M2 : List (ℕ × ℕ) := [(0x90000044088040021100000000102000400810000010000, 0x1020000000000000000000000000040000100000000004000000), (0x8001000000000000000000000000000000008000000000200, 0x200000000000000), (0x80000000400800000000000000801000, 0x0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k2 : kOk M2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_0 : chk 0 14 2 0x90000044088040021100000000102000400810000010000 0x1020000000000000000000000000040000100000000004000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_1 : chk 0 14 2 0x8001000000000000000000000000000000008000000000200 0x200000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2_2 : chk 0 14 2 0x80000000400800000000000000801000 0x0 = false := by decide +kernel
def M3 : List (ℕ × ℕ) := [(0x80910000440880400a1100000400902000408810000811200, 0x1020000000000000000000000000040000100200000004000000)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k3 : kOk M3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r3_0 : chk 0 14 3 0x80910000440880400a1100000400902000408810000811200 0x1020000000000000000000000000040000100200000004000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r_r : okT 0 15 [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
theorem i3 : ∀ e ∈ tab3, Imp e.1 e.2 := fun e he => imp_okE (List.all_eq_true.1 c3 e he) fun x hx => by
  have := List.all_eq_true.1 pr3 e he
  rw [List.isEmpty_iff] at this; rw [this] at hx; simp at hx
lemma up2 {e : ℕ × ℕ} (he : e ∈ tab2) : ∀ x ∈ pr e.1, Imp x.1 x.2 := fun x hx =>
  i3 x (by simpa using List.all_eq_true.1 (List.all_eq_true.1 pr2 e he) x hx)
theorem i17 : Imp 17 11 := imp_okE (e := (17, 11)) c17 (up2 (by decide +kernel))
theorem i24 : Imp 24 11 := imp_okE (e := (24, 11)) c24 (up2 (by decide +kernel))
theorem i80 : Imp 80 11 := imp_okE (e := (80, 11)) c80 (up2 (by decide +kernel))
theorem i132 : Imp 132 11 := imp_okE (e := (132, 11)) c132 (up2 (by decide +kernel))
theorem i144 : Imp 144 11 := imp_okE (e := (144, 11)) c144 (up2 (by decide +kernel))
theorem i66 : Imp 66 11 := imp_sym i17 s66
theorem i320 : Imp 320 11 := imp_sym i24 s320
theorem i160 : Imp 160 11 := imp_sym i132 s160
theorem i192 : Imp 192 11 := imp_sym i144 s192
theorem i2 : ∀ e ∈ tab2, Imp e.1 e.2 := by
  intro e he
  by_cases hl : e ∈ ([(3, 9), (6, 9), (12, 9), (18, 9), (20, 9), (33, 9), (48, 9), (65, 9), (68, 9), (72, 9), (96, 9), (129, 9), (130, 9), (136, 9), (264, 9), (272, 9), (288, 9), (384, 9), (5, 8), (9, 8), (10, 8), (34, 8), (36, 8), (40, 8), (257, 8), (258, 8), (260, 8)] : List (ℕ × ℕ))
  · exact imp_okE (List.all_eq_true.1 c2l e hl) (up2 he)
  · have : e ∈ ([(17, 11), (24, 11), (66, 11), (80, 11), (132, 11), (144, 11), (160, 11), (192, 11), (320, 11)] : List (ℕ × ℕ)) := by
      have h : tab2.all (fun e => ([(3, 9), (6, 9), (12, 9), (18, 9), (20, 9), (33, 9), (48, 9), (65, 9), (68, 9), (72, 9), (96, 9), (129, 9), (130, 9), (136, 9), (264, 9), (272, 9), (288, 9), (384, 9), (5, 8), (9, 8), (10, 8), (34, 8), (36, 8), (40, 8), (257, 8), (258, 8), (260, 8)] : List (ℕ × ℕ)).contains e || ([(17, 11), (24, 11), (66, 11), (80, 11), (132, 11), (144, 11), (160, 11), (192, 11), (320, 11)] : List (ℕ × ℕ)).contains e) = true := by decide +kernel
      have := List.all_eq_true.1 h e he
      rw [Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem] at this
      exact this.resolve_left hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact i17
    · exact i24
    · exact i66
    · exact i80
    · exact i132
    · exact i144
    · exact i160
    · exact i192
    · exact i320
lemma up1 {e : ℕ × ℕ} (he : e ∈ tab1) : ∀ x ∈ pr e.1, Imp x.1 x.2 := fun x hx => by
  have := List.all_eq_true.1 (List.all_eq_true.1 pr1 e he) x hx
  rw [Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem] at this
  exact this.elim (i2 x) (i3 x)
theorem i16 : Imp 16 13 := by
  refine imp_of p16 (by decide) (up1 (e := (16, 13)) (by decide +kernel)) (Or.inr fun t ht => ?_)
  have one : ∀ t, chk 16 12 t FF FF = false → ∃ M : List (ℕ × ℕ), M ≠ [] ∧ (∀ p ∈ M, chk 16 (13 - 1) t p.1 p.2 = false) ∧
      ∀ (k : ℕ) (S : Finset ℕ), (S : Set ℕ) ⊆ WZ 16 → Min (mz 16) (tz 16) k t S → 2 ≤ S.card →
        ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ 16 ∧ Min (mz 16) (tz 16) k t S' ∧ FM (mz 16) (tz 16) k t S' (KP M) (KN M) := fun t h =>
    ⟨[(FF, FF)], by simp, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact h,
      fun k S hS hm hc => ⟨S, hS, hm, FM_mono (FM_of hm hc) (fun x y _ => ⟨(FF, FF), by simp, hbF _⟩) (fun x _ => ⟨(FF, FF), by simp, hbF _⟩)⟩⟩
  by_cases h3 : t < 3
  · interval_cases t
    · exact one 0 c16_0
    · refine ⟨N16, by simp [N16], fun p hp => ?_, sym_full k16⟩
      simp only [N16, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact r16_0
      · exact r16_1
      · exact r16_2
    · exact one 2 c16_2
  · have h := List.all_eq_true.1 c16_r t (by simp; omega)
    rw [Bool.not_eq_true'] at h
    exact one t h
theorem i128 : Imp 128 13 := by
  refine imp_of p128 (by decide) (up1 (e := (128, 13)) (by decide +kernel)) (Or.inr fun t ht => ?_)
  have one : ∀ t, chk 128 12 t FF FF = false → ∃ M : List (ℕ × ℕ), M ≠ [] ∧ (∀ p ∈ M, chk 128 (13 - 1) t p.1 p.2 = false) ∧
      ∀ (k : ℕ) (S : Finset ℕ), (S : Set ℕ) ⊆ WZ 128 → Min (mz 128) (tz 128) k t S → 2 ≤ S.card →
        ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ WZ 128 ∧ Min (mz 128) (tz 128) k t S' ∧ FM (mz 128) (tz 128) k t S' (KP M) (KN M) := fun t h =>
    ⟨[(FF, FF)], by simp, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact h,
      fun k S hS hm hc => ⟨S, hS, hm, FM_mono (FM_of hm hc) (fun x y _ => ⟨(FF, FF), by simp, hbF _⟩) (fun x _ => ⟨(FF, FF), by simp, hbF _⟩)⟩⟩
  by_cases h3 : t < 3
  · interval_cases t
    · exact one 0 c128_0
    · refine ⟨N128, by simp [N128], fun p hp => ?_, sym_full k128⟩
      simp only [N128, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact r128_0
      · exact r128_1
      · exact r128_2
    · exact one 2 c128_2
  · have h := List.all_eq_true.1 c128_r t (by simp; omega)
    rw [Bool.not_eq_true'] at h
    exact one t h
theorem i64 : Imp 64 13 := imp_sym i16 s64
theorem i1 : ∀ e ∈ tab1, Imp e.1 e.2 := by
  intro e he
  by_cases hl : e ∈ ([(1, 12), (2, 12), (4, 12), (8, 12), (32, 12), (256, 12)] : List (ℕ × ℕ))
  · exact imp_okE (List.all_eq_true.1 c1l e hl) (up1 he)
  · simp only [tab1, List.mem_cons, List.not_mem_nil, or_false] at he hl
    push Not at hl
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact i16
    · exact i64
    · exact i128
    · simp at hl
    · simp at hl
    · simp at hl
    · simp at hl
    · simp at hl
    · simp at hl
theorem i0 : Imp 0 15 := by
  refine imp_of p0 le_rfl (fun x hx => ?_) (Or.inr fun t ht => ?_)
  · have := List.all_eq_true.1 pr0 x hx
    rw [Bool.or_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem, List.contains_iff_mem] at this
    exact this.elim (fun h => h.elim (i1 x) (i2 x)) (i3 x)
  by_cases h4 : t < 4
  · interval_cases t
    · refine ⟨M0, by simp [M0], fun p hp => ?_, fun k S => sym0 k0 k 0 S⟩
      simp only [M0, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact r0_0
      · exact r0_1
      · exact r0_2
      · exact r0_3
      · exact r0_4
    · refine ⟨M1, by simp [M1], fun p hp => ?_, fun k S => sym0 k1 k 1 S⟩
      simp only [M1, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact r1_0
      · exact r1_1
      · exact r1_2
      · exact r1_3
      · exact r1_4
      · exact r1_5
      · exact r1_6
      · exact r1_7
      · exact r1_8
    · refine ⟨M2, by simp [M2], fun p hp => ?_, fun k S => sym0 k2 k 2 S⟩
      simp only [M2, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact r2_0
      · exact r2_1
      · exact r2_2
    · refine ⟨M3, by simp [M3], fun p hp => ?_, fun k S => sym0 k3 k 3 S⟩
      simp only [M3, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl
      · exact r3_0
  · refine ⟨[(FF, FF)], by simp, fun p hp => ?_, fun k S hS hm hc => ⟨S, hS, hm, ?_⟩⟩
    · simp only [List.mem_singleton] at hp; subst hp
      have h := List.all_eq_true.1 r_r t (by simp; omega)
      rwa [Bool.not_eq_true'] at h
    · exact FM_mono (FM_of hm hc) (fun x y _ => ⟨(FF, FF), by simp, hbF _⟩) (fun x _ => ⟨(FF, FF), by simp, hbF _⟩)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0
lemma ex_sol {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → Sol m T gs.length S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol m T (g :: gs).length S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go : Sol m T gs.length (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go
lemma gv_sub {w : List ℕ} (hw : ∀ x ∈ w, x &&& m = x) (g : Gate) : gv m w g &&& m = gv m w g := by
  have rd : ∀ i, w.getD i 0 &&& m = w.getD i 0 := fun i => getD_mem (S := {x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc, rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right, rd, rd]
  · simp
  · rw [and_neg (Nat.and_self m), rd]
  · simp
lemma ex_sub {gs : List Gate} : ∀ {w : List ℕ}, (∀ x ∈ w, x &&& m = x) → ∀ x ∈ ex m gs w, x &&& m = x := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w := w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w : List ℕ) (b i : ℕ) : (w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b : ℕ} (hb : m.testBit b = true) (w : List ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [gv, e1, hb]
    | [i], _ => simp [gv, e1]
    | [i, j], _ => simp [gv, e1]
  · match l, hlen with
    | [], _ => simp [gv, e2]
    | [i], _ => simp [gv, e2]
    | [i, j], _ => simp [gv, e2]
  · match l, hlen with
    | [], _ => simp [gv, e3, hb]
    | [i], _ => simp [gv, e3, hb]
    | [i, j], _ => simp [gv, e3, hb]
lemma ex_bit {b : ℕ} (hb : m.testBit b = true) (gs : List Gate) : ∀ (w : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons, ← gv_bit m hb w g (hg g List.mem_cons_self)]
    have := ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuit
def EF : ℕ := (([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (ℕ × ℕ)).map
  (fun e => rawP.getD e.1 0 &&& rawP.getD e.2 0)).foldr (· ||| ·) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len : rawP.length = 9 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 9 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma fold_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma rawL_mem (i : ℕ) (hi : i < 9) : rawP.getD i 0 ∈ rawL := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [rawP_len]; exact hi)]
  exact List.mem_append_left _ (List.getElem_mem _)
lemma or01_mem : rawP.getD 0 0 ||| rawP.getD 1 0 ∈ rawL := List.mem_append_right _ (by simp)
lemma raw_sub {x : ℕ} (hx : x ∈ rawL) : x &&& mz 0 = x := by
  have := List.all_eq_true.1 m0_full x hx
  rwa [Nat.beq_eq, nl] at this
theorem final : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hfan hfirst hfun
  by_contra hsz
  obtain ⟨gates, out⟩ := C
  let row : ℕ → Fin 9 → Bool := fun b v => (rawP.getD v.val 0).testBit b
  have hrow : ∀ b, List.ofFn (row b) = rawP.map (fun x => x.testBit b) := row_list
  have hRP : ∀ x ∈ rawP, x &&& mz 0 = x := fun x hx => raw_sub (List.mem_append_left _ hx)
  match gates, hfan, hfirst, hfun, hsz with
  | [], _, hfirst, _, _ =>
    have := hfirst (fun _ => true)
    simp [PEqualNP.CircuitLowerBounds.Circuit.wires] at this
  | g :: gs, hfan, hfirst, hfun, hsz =>
    have hlen : gs.length ≤ 14 := by
      have : ¬ 16 ≤ gs.length + 1 := hsz
      omega
    have hg : ∀ x ∈ g :: gs, x.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
        PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ x.inputs.length ≤ 2 := hfan
    have hy : gv (mz 0) rawP g = rawP.getD 0 0 ||| rawP.getD 1 0 := by
      apply Nat.eq_of_testBit_eq; intro b
      cases hb : (mz 0).testBit b with
      | false =>
        have e1 := congrArg (fun x => x.testBit b) (gv_sub (mz 0) hRP g)
        have e2 := congrArg (fun x => x.testBit b) (raw_sub or01_mem)
        simp only [Nat.testBit_and, hb, Bool.and_false] at e1 e2
        rw [← e1, ← e2]
      | true =>
        have h := hfirst (row b)
        have e : (PEqualNP.CircuitLowerBounds.Circuit.mk (g :: gs) out).wires (List.ofFn (row b)) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (rawP.map (fun x => x.testBit b) ++ [g.op.eval (g.inputs.map fun i => (rawP.map (fun x => x.testBit b)).getD i false)]) := by
          rw [hrow]; rfl
        rw [e, fold_keep _ _ _ (by simp [rawP_len]), ← gv_bit (mz 0) hb rawP g (hg g List.mem_cons_self)] at h
        have h9 : (rawP.map (fun x => x.testBit b) ++ [(gv (mz 0) rawP g).testBit b]).getD 9 false = (gv (mz 0) rawP g).testBit b := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [rawP_len])]; simp [rawP_len]
        rw [h9] at h
        rw [h, Nat.testBit_or]; rfl
    have hsub : ∀ x ∈ rawP ++ [rawP.getD 0 0 ||| rawP.getD 1 0], x ∈ rawL := fun x hx => hx
    have hout : (ex (mz 0) gs (rawP ++ [rawP.getD 0 0 ||| rawP.getD 1 0])).getD out 0 = tz 0 := by
      rw [← EF_ok]
      have hs : ∀ x ∈ ex (mz 0) gs (rawP ++ [rawP.getD 0 0 ||| rawP.getD 1 0]), x &&& mz 0 = x :=
        ex_sub (mz 0) fun x hx => raw_sub (hsub x hx)
      have hs' := getD_mem (S := {x | x &&& mz 0 = x}) hs (by simp) out
      apply Nat.eq_of_testBit_eq; intro b
      have e1 := congrArg (fun x => x.testBit b) hs'
      simp only [Nat.testBit_and] at e1
      rw [← e1, Nat.testBit_and]
      cases hb : (mz 0).testBit b with
      | false => simp
      | true =>
        simp only [Bool.and_true]
        rw [← getD_map, ex_bit (mz 0) hb gs _ (fun x hx => hg x (List.mem_cons_of_mem _ hx))]
        have h := congrFun hfun (row b)
        have e : PEqualNP.MetaComplexity.circuitFun 9 ⟨g :: gs, out⟩ (row b) =
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (rawP.map (fun x => x.testBit b) ++ [g.op.eval (g.inputs.map fun i => (rawP.map (fun x => x.testBit b)).getD i false)])).getD out false := by
          change ((PEqualNP.CircuitLowerBounds.Circuit.mk (g :: gs) out).wires (List.ofFn (row b))).getD out false = _
          rw [hrow]; rfl
        rw [e, ← gv_bit (mz 0) hb rawP g (hg g List.mem_cons_self), hy] at h
        rw [List.map_append, List.map_singleton, h]
        simp only [EF, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.testBit_or, Nat.testBit_and, Nat.zero_testBit, Bool.or_false]
        simp only [Bool.or_assoc]; rfl
    have hsol := ex_sol (mz 0) gs (rawP ++ [rawP.getD 0 0 ||| rawP.getD 1 0]) (C (mz 0) (WZ 0))
      (fun x hx => Or.inl ⟨x, hsub x hx, (raw_sub (hsub x hx)).symm⟩) (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
      (fun x hx => hg x (List.mem_cons_of_mem _ hx)) ⟨out, hout⟩
    exact i0 _ (by omega) hsol
end PEqualNP.Outside.L_meta_3825_aux


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_3825_aux
theorem old_wire {α : Type} (f : List Bool → α → Bool) (gs : List α)
    (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun s g => s ++ [f s g]) w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl _ (w ++ [f w g])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem target_rows : ∀ x : Fin 9 → Bool, (fun (x8 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x9 : Fin (9 : ℕ)) (x10 : Fin (9 : ℕ)), ([(34 : ℕ), (68 : ℕ), (136 : ℕ), (272 : ℕ), (1 : ℕ), (128 : ℕ), (256 : ℕ), (0 : ℕ), (32 : ℕ)].getD ↑x9 (0 : ℕ)).testBit ↑x10 = Bool.true ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) x = ((fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) x := by decide +kernel
end PEqualNP.Outside.L_meta_3825_aux

theorem PEqualNP.Outside.L_meta_3825 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → x1.size = (15 : ℕ) → x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (1 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(1 : ℕ), (0 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (∀ x8 ∈ x6.inputs, x8 < (9 : ℕ) + x5) ∧ x6.inputs.Nodup ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.not → x6.inputs.length = (1 : ℕ)) ∧ (x6.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x6.inputs.length = (2 : ℕ))) → List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1.gates ≤ (2 : ℕ) → (∀ x7 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x9 : Finset ℕ), (∀ x10 ∈ x9, x10 < x1.size ∧ (↑x7 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).inputs ∨ ∃ x12 < x10, ↑x7 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).inputs ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ (9 : ℕ) + x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).inputs)) → x9.card ≤ (3 : ℕ)) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x8 : Fin (9 : ℕ) → Bool) => Decidable.decide (∃ (x9 : Fin (9 : ℕ)) (x10 : Fin (9 : ℕ)), ([(34 : ℕ), (68 : ℕ), (136 : ℕ), (272 : ℕ), (1 : ℕ), (128 : ℕ), (256 : ℕ), (0 : ℕ), (32 : ℕ)].getD ↑x9 (0 : ℕ)).testBit ↑x10 = Bool.true ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) := by

  intro C minimal size head _ _ _ computes
  have first (x : Fin 9 → Bool) : (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1) := by
    cases hg : C.gates with
    | nil => simp [hg] at head
    | cons g gs =>
      simp only [hg, List.getElem?_cons_zero, Option.some.injEq] at head
      rw [Circuit.wires,hg,List.foldl_cons]
      rcases head with rfl | rfl <;>
        rw [PEqualNP.Outside.L_meta_3825_aux.old_wire _ _ _ _ (by simp)] <;>
        simp [List.getD_eq_getElem?_getD, GateOp.eval] <;> exact Bool.or_comm _ _
  have eq : circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    funext x
    exact (congrFun computes x).trans (PEqualNP.Outside.L_meta_3825_aux.target_rows x)
  have lowerBound := PEqualNP.Outside.L_meta_3825_aux.final C minimal.1 first eq
  omega

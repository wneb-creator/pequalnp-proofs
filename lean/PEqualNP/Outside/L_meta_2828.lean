import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2828

def op (d : ℕ) (a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)

def bOp (d : ℕ) (a b : Bool) : Bool :=
  match d with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

lemma op_bit (d a b i : ℕ) : (op d a b).testBit i = bOp d (a.testBit i) (b.testBit i) := by
  rcases d with _ | _ | _ | d
  · simp [op, bOp]
  · simp [op, bOp]
  · simp only [op, bOp, Nat.testBit_xor, Nat.testBit_and]
    cases a.testBit i <;> cases b.testBit i <;> rfl
  · simp only [op, bOp, Nat.testBit_xor, Nat.testBit_and]
    cases a.testBit i <;> cases b.testBit i <;> rfl

lemma op_self (d a : ℕ) : op d a a = 0 ∨ op d a a = a := by
  rcases d with _ | _ | _ | d
  · right; simp [op]
  · right; simp [op]
  · left; simp [op]
  · left; simp [op]

lemma op_swap (d a b : ℕ) : ∃ d' < 4, op d a b = op d' b a := by
  rcases d with _ | _ | _ | d
  · exact ⟨0, by decide, Nat.and_comm a b⟩
  · exact ⟨1, by decide, Nat.or_comm a b⟩
  · exact ⟨3, by decide, by simp [op, Nat.and_comm]⟩
  · exact ⟨2, by decide, by simp [op, Nat.and_comm]⟩

lemma op_zero_left (d b : ℕ) : op d 0 b = 0 ∨ op d 0 b = b := by
  rcases d with _ | _ | _ | d <;> simp [op]

lemma op_zero_right (d a : ℕ) : op d a 0 = 0 ∨ op d a 0 = a := by
  rcases d with _ | _ | _ | d <;> simp [op]

lemma and_op (d a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, op_bit]
  rcases d with _ | _ | _ | d <;>
    cases a.testBit i <;> cases b.testBit i <;> cases n.testBit i <;> rfl

def Sol (T : ℕ) : ℕ → Set ℕ → Prop
  | 0, S => T ∈ S
  | q + 1, S => T ∈ S ∨ ∃ d < 4, ∃ a ∈ S, ∃ b ∈ S, Sol T q (insert (op d a b) S)

lemma Sol.mono {T : ℕ} : ∀ {q q' : ℕ} {S S' : Set ℕ},
    Sol T q S → q ≤ q' → S ⊆ S' → Sol T q' S' := by
  intro q
  induction q with
  | zero =>
    intro q' S S' h hq hs
    cases q' with
    | zero => exact hs h
    | succ r => exact Or.inl (hs h)
  | succ q ih =>
    intro q' S S' h hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    rcases h with h | ⟨d, hd, a, ha, b, hb, htail⟩
    · exact Or.inl (hs h)
    · exact Or.inr ⟨d, hd, a, hs ha, b, hs hb, ih htail (by omega) (Set.insert_subset_insert hs)⟩

def Live (T : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => S = {T}
  | k + 1, S => ∃ d < 4, ∃ a b : ℕ, ∃ U : Finset ℕ,
      a ≠ b ∧ S = insert a (insert b U) ∧ Live T k (insert (op d a b) U)

lemma Live.sol {T : ℕ} : ∀ {k : ℕ} {S : Finset ℕ}, Live T k S → Sol T k (S : Set ℕ) := by
  intro k
  induction k with
  | zero =>
    intro S h
    change S = {T} at h
    subst h
    simp [Sol]
  | succ k ih =>
    intro S ⟨d, hd, a, b, U, hab, hS, htail⟩
    subst hS
    refine Or.inr ⟨d, hd, a, by simp, b, by simp, (ih htail).mono le_rfl ?_⟩
    intro x hx
    simp at hx ⊢
    tauto

def C (S : Set ℕ) : Set ℕ := insert 0 S

lemma C_mono {S S' : Set ℕ} (h : S ⊆ S') : C S ⊆ C S' := Set.insert_subset_insert h

lemma sub_C (S : Set ℕ) : S ⊆ C S := Set.subset_insert 0 S

lemma Sol.live {T : ℕ} (hT : T ≠ 0) : ∀ {q : ℕ} {S : Set ℕ}, Sol T q (C S) →
    ∃ k ≤ q, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live T k S0 := by
  intro q
  induction q with
  | zero =>
    intro S h
    change T ∈ insert 0 S at h
    rcases h with rfl | h
    · exact absurd rfl hT
    · exact ⟨0, le_rfl, {T}, by simpa using h, rfl⟩
  | succ q ih =>
    intro S h
    rcases h with h | ⟨d, hd, a, ha, b, hb, htail⟩
    · rcases h with rfl | h
      · exact absurd rfl hT
      · exact ⟨0, Nat.zero_le _, {T}, by simpa using h, rfl⟩
    · have hsub : insert (op d a b) (C S) ⊆ C (insert (op d a b) S) := by
        intro x hx; simp only [C, Set.mem_insert_iff] at hx ⊢; tauto
      obtain ⟨k, hk, S1, hs, hl⟩ := ih (htail.mono le_rfl hsub)
      by_cases hg : op d a b ∈ S1
      · by_cases ha0 : a = 0
        · subst ha0
          rcases op_zero_left d b with he | he
          · rw [he] at hs
            have hS1 : (S1 : Set ℕ) ⊆ C S := by
              intro x hx
              rcases hs hx with rfl | hx
              · exact Or.inl rfl
              · exact Or.inr hx
            obtain ⟨k', hk', S2, hs2, hl2⟩ := ih (hl.sol.mono hk hS1)
            exact ⟨k', by omega, S2, hs2, hl2⟩
          · rw [he] at hs
            rcases hb with rfl | hb
            · have hS1 : (S1 : Set ℕ) ⊆ C S := by
                intro x hx
                rcases hs hx with rfl | hx
                · exact Or.inl rfl
                · exact Or.inr hx
              obtain ⟨k', hk', S2, hs2, hl2⟩ := ih (hl.sol.mono hk hS1)
              exact ⟨k', by omega, S2, hs2, hl2⟩
            · exact ⟨k, by omega, S1, fun x hx => (hs hx).elim (fun e => e ▸ hb) id, hl⟩
        · by_cases hb0 : b = 0
          · subst hb0
            rcases op_zero_right d a with he | he
            · rw [he] at hs
              have hS1 : (S1 : Set ℕ) ⊆ C S := by
                intro x hx
                rcases hs hx with rfl | hx
                · exact Or.inl rfl
                · exact Or.inr hx
              obtain ⟨k', hk', S2, hs2, hl2⟩ := ih (hl.sol.mono hk hS1)
              exact ⟨k', by omega, S2, hs2, hl2⟩
            · rw [he] at hs
              exact ⟨k, by omega, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha.resolve_left ha0) id, hl⟩
          · by_cases hab : a = b
            · subst hab
              rcases op_self d a with he | he
              · rw [he] at hs
                have hS1 : (S1 : Set ℕ) ⊆ C S := by
                  intro x hx
                  rcases hs hx with rfl | hx
                  · exact Or.inl rfl
                  · exact Or.inr hx
                obtain ⟨k', hk', S2, hs2, hl2⟩ := ih (hl.sol.mono hk hS1)
                exact ⟨k', by omega, S2, hs2, hl2⟩
              · rw [he] at hs
                exact ⟨k, by omega, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha.resolve_left ha0) id, hl⟩
            · refine ⟨k + 1, by omega, insert a (insert b (S1.erase (op d a b))), ?_,
                d, hd, a, b, S1.erase (op d a b), hab, rfl, by rwa [Finset.insert_erase hg]⟩
              intro x hx
              simp at hx
              rcases hx with rfl | rfl | ⟨h1, h2⟩
              · exact ha.resolve_left ha0
              · exact hb.resolve_left hb0
              · exact (hs h1).resolve_left h2
      · exact ⟨k, by omega, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩

def Bi (d a b : ℕ) (S S' : Finset ℕ) : Prop :=
  d < 4 ∧ a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U

lemma Bi.live {T a b k : ℕ} {d : ℕ} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live T k S') :
    Live T (k + 1) S := by
  obtain ⟨hd, hab, U, rfl, rfl⟩ := h
  exact ⟨d, hd, a, b, U, hab, rfl, hl⟩

lemma Bi.symm {a b : ℕ} {d : ℕ} {S S' : Finset ℕ} (h : Bi d a b S S') :
    ∃ d', Bi d' b a S S' := by
  obtain ⟨hd, hab, U, rfl, rfl⟩ := h
  obtain ⟨d', hd', heq⟩ := op_swap d a b
  exact ⟨d', hd', hab.symm, U, Finset.insert_comm _ _ _, by rw [heq]⟩

lemma Bi.sub {a b : ℕ} {d : ℕ} {S S' : Finset ℕ} (h : Bi d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, _, U, rfl, rfl⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx
  simp [hx]

def Min (T k : ℕ) (S : Finset ℕ) : Prop := Live T k S ∧ ∀ q < k, ¬ Sol T q (C S)

lemma Bi.sol {T a b q : ℕ} {d : ℕ} {S S' : Finset ℕ} (h : Bi d a b S S') (hs : Sol T q (C S')) :
    Sol T (q + 1) (C S) := by
  obtain ⟨ha, hb, hsub⟩ := Bi.sub h
  obtain ⟨hd, _, _, _, _⟩ := h
  refine Or.inr ⟨d, hd, a, sub_C _ ha, b, sub_C _ hb, hs.mono le_rfl ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · exact Or.inr (Or.inl rfl)
  · have := hsub hx
    simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inr h')

lemma Bi.min {T a b k : ℕ} {d : ℕ} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live T k S')
    (hm : ∀ q < k + 1, ¬ Sol T q (C S)) : Min T k S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (Bi.sol h hs)⟩

lemma Bi.fresh {T a b k : ℕ} {d : ℕ} {S S' : Finset ℕ} (h : Bi d a b S S') (hl : Live T k S')
    (hm : ∀ q < k + 1, ¬ Sol T q (C S)) : op d a b ∉ C (S : Set ℕ) := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := (Bi.sub h).2.2 hx
  simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inr h'

lemma Min.size {T : ℕ} : ∀ {k : ℕ} {S : Finset ℕ}, Min T k S → S.card ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro S ⟨hl, _⟩
    change S = {T} at hl
    subst hl
    simp
  | succ k ih =>
    intro S ⟨⟨d, hd, a, b, U, hab, hS, hl⟩, hm⟩
    subst hS
    have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hd, hab, U, rfl, rfl⟩
    have ih' := ih (Bi.min hu hl hm)
    have hf : op d a b ∉ U := fun h => Bi.fresh hu hl hm (sub_C _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih'
    omega

abbrev Cst (n x : ℕ) : Prop := x &&& n = 0

def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)

lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C (Im n S) :=
  Or.inr ⟨x, by simpa using h, rfl⟩

lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} {d : ℕ} (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C (Im n S) := by
  rw [and_op]
  rcases h with h | h
  · rw [h]
    rcases op_zero_left d (b &&& n) with e | e <;> rw [e]
    · exact Or.inl rfl
    · exact Im_mem hb
  · rw [h]
    rcases op_zero_right d (a &&& n) with e | e <;> rw [e]
    · exact Or.inl rfl
    · exact Im_mem ha

lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C (Im n S) ⊆ Q) : C (Im n S') ⊆ Q := by
  rintro x (rfl | ⟨y, hy, rfl⟩)
  · exact hQ (Or.inl rfl)
  · have := h hy
    simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')

lemma Bi.im {T n a b q : ℕ} {d : ℕ} {S S' : Finset ℕ} (h : Bi d a b S S')
    (hs : Sol (T &&& n) q (C (Im n S'))) :
    Sol (T &&& n) (q + 1) (C (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := Bi.sub h
  obtain ⟨hd, _, _, _, _⟩ := h
  refine Or.inr ⟨d, hd, a &&& n, Im_mem ha, b &&& n, Im_mem hb,
    hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _))⟩
  rw [and_op]
  exact Or.inl rfl

lemma Bi.kill {T n a b q : ℕ} {d : ℕ} {S S' : Finset ℕ} (h : Bi d a b S S')
    (hc : Cst n a ∨ Cst n b) (hs : Sol (T &&& n) q (C (Im n S'))) :
    Sol (T &&& n) q (C (Im n S)) :=
  hs.mono le_rfl (C_Im_sub (Bi.sub h).2.2 (op_cst_mem hc (Bi.sub h).1 (Bi.sub h).2.1) subset_rfl)

lemma op_cst2 {n a b : ℕ} (d : ℕ) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  unfold Cst at ha hb ⊢
  rw [and_op, ha, hb]
  rcases op_zero_left d 0 with e | e <;> exact e

lemma Min.const {T n : ℕ} (hT0 : T &&& n ≠ 0) : ∀ {k : ℕ} {S : Finset ℕ}, Min T k S →
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol (T &&& n) q (C (Im n S)) := by
  intro k
  induction k with
  | zero =>
    intro S ⟨hl, _⟩
    change S = {T} at hl
    subst hl
    refine ⟨0, ?_, Or.inr (⟨T, by simp, rfl⟩)⟩
    rw [Finset.filter_eq_empty_iff.2]
    · simp
    · intro x hx
      simp at hx
      subst hx
      exact hT0
  | succ k ih =>
    intro S ⟨⟨d, hd, a, b, U, hab, hS, hl⟩, hm⟩
    subst hS
    have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hd, hab, U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (Bi.min hu hl hm)
    have hf : op d a b ∉ U := fun h => Bi.fresh hu hl hm (sub_C _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, Bi.kill hu (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb),
          Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n)))
        omega
      · rw [ite_eq_right hcb]
        omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, Bi.kill hu (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]
        omega
      · refine ⟨q + 1, ?_, Bi.im hu hs⟩
        rw [ite_eq_right hcb]
        omega

lemma Min.nonzero {T k : ℕ} {S : Finset ℕ} (hT : T ≠ 0) (h : Min T k S) : 0 ∉ S := by
  intro h0
  obtain ⟨m, hm⟩ : ∃ m, T < 2 ^ m ∧ ∀ x ∈ S, x < 2 ^ m := by
    refine ⟨max T (S.sup id) + 1, ?_, ?_⟩
    · exact lt_of_lt_of_le (Nat.lt_two_pow_self (n := T)) (Nat.pow_le_pow_right (by omega) (by omega))
    · intro x hx
      have hle : x ≤ S.sup id := Finset.le_sup (f := id) hx
      have : x < 2 ^ (S.sup id + 1) := lt_of_le_of_lt hle (by
        have := Nat.lt_two_pow_self (n := S.sup id)
        omega)
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) (by omega))
  let n := 2 ^ m - 1
  have and_n : ∀ x < 2 ^ m, x &&& n = x := by
    intro x hx
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < m
    · simp [hi]
    · have : 2 ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx this)]
      simp [hi]
  have hTn : T &&& n = T := and_n T hm.1
  obtain ⟨q, hq, hs⟩ := h.const (n := n) (by rwa [hTn])
  have hi : Im n S = (S : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change y &&& n ∈ (S : Set ℕ)
      rw [and_n y (hm.2 y hy)]
      exact hy
    · intro hx
      exact ⟨x, hx, and_n x (hm.2 x hx)⟩
  rw [hi, hTn] at hs
  have hc0 : 0 < (S.filter (Cst n)).card :=
    Finset.card_pos.2 ⟨0, Finset.mem_filter.2 ⟨h0, by simp [Cst]⟩⟩
  exact h.2 q (by omega) hs

def sepb (N w i : ℕ) : Bool := xor (w.testBit i) (w.testBit (N + i))

def Lg (N T i : ℕ) : Prop := T.testBit i = true ∧ T.testBit (N + i) = false

lemma Live.cov {N T i : ℕ} (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false) :
    ∀ {k : ℕ} {S : Finset ℕ}, Live T k S → ∃ w ∈ S, sepb N w i = true := by
  intro k
  induction k with
  | zero =>
    intro S h
    change S = {T} at h
    subst h
    exact ⟨T, by simp, by simp [sepb, t1, t2]⟩
  | succ k ih =>
    intro S ⟨d, hd, a, b, U, hab, hS, hl⟩
    subst hS
    obtain ⟨w, hw, hs⟩ := ih hl
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb
        simp only [op_bit]
        rcases d with _ | _ | _ | d <;>
          cases a.testBit i <;> cases a.testBit (N + i) <;>
          cases b.testBit i <;> cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩

def Uq (N : ℕ) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N c i = false

lemma bi_uq {N T a b k c i : ℕ} {d : ℕ} {U : Finset ℕ}
    (hd : d < 4) (hl : Live T k (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N (insert a (insert b U)) c i) :
    Uq N (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := Live.cov hi.1 hi.2 hl
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl <;> contradiction
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx
      exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs
      simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2
      unfold sepb
      simp only [op_bit]
      rcases d with _ | _ | _ | d <;>
        cases a.testBit i <;> cases a.testBit (N + i) <;>
        cases b.testBit i <;> cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne

lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢
    tauto

lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U)
    (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab

lemma bi_tight {T a b k : ℕ} {d : ℕ} {U : Finset ℕ}
    (hd : d < 4) (hab : a ≠ b) (hl : Live T k (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol T q (C ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card = k + 1 ∧ Min T k (insert (op d a b) U) := by
  have hu : Bi d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hd, hab, U, rfl, rfl⟩
  have hf : op d a b ∉ U := fun h => Bi.fresh hu hl hm (sub_C _ (by simp [h]))
  have hmin := Bi.min hu hl hm
  have hs := hmin.size
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩

lemma polar_step (d : Fin 4) (a1 a3 b1 b3 : Bool)
    (hres : bOp d.val a1 b1 = bOp d.val a3 b3)
    (s1 : xor (bOp d.val a1 b1) (bOp d.val (!a1) b1) = true)
    (s2 : xor (bOp d.val a3 b3) (bOp d.val (!a3) b3) = true) :
    a1 = a3 := by
  revert d a1 a3 b1 b3
  decide

lemma polar {N T : ℕ} : ∀ {k : ℕ} {S : Finset ℕ}, Live T k S → (∀ q < k, ¬ Sol T q (C (S : Set ℕ))) →
    S.card = k + 1 → ∀ {i j : ℕ}, Lg N T i → Lg N T j →
    ∀ {a : ℕ}, a ∈ S → Uq N S a i → Uq N S a j → a.testBit i = a.testBit j := by
  intro k
  induction k with
  | zero =>
    intro S hl _ _ i j h1 h2 a ha _ _
    change S = {T} at hl
    subst hl
    simp at ha
    subst ha
    rw [h1.1, h2.1]
  | succ k ih =>
    intro S ⟨d, hd, x, y, U, hxy, hS, hl⟩ hm hc i j h1 h2 a ha u1 u2
    have ha0 : a ∈ insert x (insert y U) := hS ▸ ha
    have u1' : Uq N (insert x (insert y U)) a i := hS ▸ u1
    have u2' : Uq N (insert x (insert y U)) a j := hS ▸ u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hd hxy hl (hS ▸ hm) (hS ▸ hc)
    have v1 := bi_uq hd hl hx hy h1 ha0 u1'
    have v2 := bi_uq hd hl hx hy h2 ha0 u2'
    have hres := ih hl hmin.2 hc' h1 h2 (phi_mem ha0) v1 v2
    split_ifs at hres v1 v2 with h
    · obtain ⟨b, hb, hab, d', hd', hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ ∃ d' < 4, op d x y = op d' a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, d, hd, rfl⟩
        · obtain ⟨d', hd', heq⟩ := op_swap d x a
          exact ⟨x, by simp, hxy, d', hd', heq⟩
      rw [hop] at hres v1 v2
      have n1 := u1'.2 b hb hab
      have n2 := u2'.2 b hb hab
      have s1 := v1.1
      have s2 := v2.1
      have p1 := u1'.1
      have p2 := u2'.1
      have hne : ∀ p q : Bool, xor p q = true → p = !q := by decide
      have heq : ∀ p q : Bool, xor p q = false → p = q := by decide
      simp only [sepb, op_bit] at n1 n2 s1 s2 p1 p2
      have hb12 := heq _ _ n1
      have hb34 := heq _ _ n2
      have ha12 := hne _ _ p1
      have ha34 := hne _ _ p2
      have ha12' : a.testBit (N + i) = !a.testBit i := by rw [ha12]; cases a.testBit (N + i) <;> rfl
      have ha34' : a.testBit (N + j) = !a.testBit j := by rw [ha34]; cases a.testBit (N + j) <;> rfl
      rw [← hb12, ha12'] at s1
      rw [← hb34, ha34'] at s2
      simp only [op_bit] at hres
      exact polar_step ⟨d', hd'⟩ (a.testBit i) (a.testBit j) (b.testBit i) (b.testBit j) hres s1 s2
    · exact hres

lemma rect1_step (d : Fin 4) (a1 a6 b1 b6 : Bool)
    (s1 : xor (bOp d.val a1 b1) (bOp d.val (!a1) b1) = true)
    (s2 : xor (bOp d.val a1 b1) (bOp d.val a1 (!b1)) = true)
    (s3 : xor (bOp d.val (!a6) b6) (bOp d.val a6 b6) = true)
    (s4 : xor (bOp d.val a6 (!b6)) (bOp d.val a6 b6) = true)
    (hpol : bOp d.val a1 b1 = bOp d.val (!a6) b6) : False := by
  revert d a1 a6 b1 b6
  decide

lemma rect1 {N T : ℕ} : ∀ {k : ℕ} {S : Finset ℕ}, Live T k S → (∀ q < k, ¬ Sol T q (C (S : Set ℕ))) →
    S.card = k + 1 → ∀ {i1 i2 j1 j2 : ℕ}, Lg N T i1 → Lg N T i2 → Lg N T j1 → Lg N T j2 →
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N S a i1 → Uq N S b i2 → Uq N S a j1 → Uq N S b j2 → False := by
  intro k
  induction k with
  | zero =>
    intro S hl _ _ _ _ _ _ _ _ _ _ a b ha hb hab _ _ _ _ _ _
    change S = {T} at hl
    subst hl
    simp at ha hb
    exact absurd (ha.trans hb.symm) hab
  | succ k ih =>
    intro S ⟨d, hd, x, y, U, hxy, hS, hl⟩ hm hc i1 i2 j1 j2 h1 h2 h3 h4 a b ha hb hab r1 r2 u1 u2 u3 u4
    have ha0 : a ∈ insert x (insert y U) := hS ▸ ha
    have hb0 : b ∈ insert x (insert y U) := hS ▸ hb
    have u1' : Uq N (insert x (insert y U)) a i1 := hS ▸ u1
    have u2' : Uq N (insert x (insert y U)) b i2 := hS ▸ u2
    have u3' : Uq N (insert x (insert y U)) a j1 := hS ▸ u3
    have u4' : Uq N (insert x (insert y U)) b j2 := hS ▸ u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hd hxy hl (hS ▸ hm) (hS ▸ hc)
    have tr : ∀ {c i}, Lg N T i → c ∈ insert x (insert y U) → Uq N (insert x (insert y U)) c i →
        Uq N (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq hd hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha0 u1'
      have v2 := tr h2 hb0 u2'
      have v3 := tr h3 ha0 u3'
      have v4 := tr h4 hb0 u4'
      rw [ite_eq_left hab'.1] at v1 v3
      rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      obtain ⟨d', hd', hop⟩ : ∃ d' < 4, op d x y = op d' a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · exact ⟨d, hd, rfl⟩
        · exact op_swap d b a
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha
      have e2 := r2 a ha
      have e1b := r1 b hb
      have e2b := r2 b hb
      have n1 := u1'.2 b hb0 (Ne.symm hab)
      have n3 := u3'.2 b hb0 (Ne.symm hab)
      have n2 := u2'.2 a ha0 hab
      have n4 := u4'.2 a ha0 hab
      have s1 := v1.1
      have s2 := v2.1
      have s3 := v3.1
      have s4 := v4.1
      have p1 := u1'.1
      have p2 := u2'.1
      have p3 := u3'.1
      have p4 := u4'.1
      have heq : ∀ p q : Bool, xor p q = false → p = q := by decide
      have hne : ∀ p q : Bool, xor p q = true → p = !q := by decide
      simp only [sepb, op_bit] at n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      have hb12 := heq _ _ n1
      have hb56 := heq _ _ n3
      have ha34 := heq _ _ n2
      have ha78 := heq _ _ n4
      have ha12 := hne _ _ p1
      have hb34 := hne _ _ p2
      have ha56 := hne _ _ p3
      have hb78 := hne _ _ p4
      have ha12' : a.testBit i1 = !a.testBit (N + i1) := ha12
      have hb34' : b.testBit (N + i2) = !b.testBit i2 := by rw [hb34]; cases b.testBit (N + i2) <;> rfl
      have hb78' : b.testBit j2 = !b.testBit (N + j2) := hb78
      rw [← hb12, ha12'] at s1
      rw [← ha34, ← e1, ha12', hb34', ← e1b] at s2
      rw [← hb56, ha56] at s3
      rw [ha78, hb78', ← e2, ← e2b] at s4
      rw [ha12', ha56] at hpol
      have s1' : xor (bOp d' (!a.testBit (N + i1)) (b.testBit i1)) (bOp d' (!!a.testBit (N + i1)) (b.testBit i1)) = true := by
        simpa using s1
      have s2' : xor (bOp d' (!a.testBit (N + i1)) (b.testBit i1)) (bOp d' (!a.testBit (N + i1)) (!b.testBit i1)) = true := s2
      have s3' : xor (bOp d' (!a.testBit (N + j1)) (b.testBit j1)) (bOp d' (a.testBit (N + j1)) (b.testBit j1)) = true := s3
      have s4' : xor (bOp d' (a.testBit (N + j1)) (!b.testBit j1)) (bOp d' (a.testBit (N + j1)) (b.testBit j1)) = true := by
        simpa [hb56] using s4
      have hpol' : bOp d' (!a.testBit (N + i1)) (b.testBit i1) = bOp d' (!a.testBit (N + j1)) (b.testBit j1) := hpol
      exact rect1_step ⟨d', hd'⟩ (!a.testBit (N + i1)) (a.testBit (N + j1)) (b.testBit i1) (b.testBit j1) s1' s2' s3' s4' hpol'
    · refine ih hl hmin.2 hc' h1 h2 h3 h4 (phi_mem ha0) (phi_mem hb0) (phi_ne hg ha0 hb0 hab hab') ?_ ?_
        (tr h1 ha0 u1') (tr h2 hb0 u2') (tr h3 ha0 u3') (tr h4 hb0 u4')
      · intro w hw
        simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (hS ▸ by simp), r1 y (hS ▸ by simp)]
        · exact r1 w (hS ▸ by simp [hw])
      · intro w hw
        simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (hS ▸ by simp), r2 y (hS ▸ by simp)]
        · exact r2 w (hS ▸ by simp [hw])

abbrev W := ℕ × ℕ
abbrev X := W × ℕ

def NN : Nat := 647
def AA : Nat := 0x3efffef7fff7df7bbfff7bdefffef77bb7fff7def77fff7bb7fff7befbbdedeeedff956d56dadb555b5bff55b5ffab6ffd6d6ad56dadad6bff55adffb6dadb6d6abff5adb5ffadffb5ffbff00000000000
def HX : Nat := 0x2a92a92524aaa4a400aa4a0054900292952a9252529400aa52004925249295400a524a0052004a0040000000000000
def HY : Nat := 0x410001080008208440008421000108844800082108800084480008410442121112000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def segsX : List (ℕ × ℕ) := [(43, 54), (54, 65), (65, 67), (67, 70), (70, 81), (81, 84), (84, 86), (86, 97), (97, 99), (99, 102), (102, 105), (105, 108), (108, 110), (110, 113), (113, 115), (115, 126), (126, 128), (128, 130), (130, 132), (132, 135), (135, 137), (137, 140), (140, 143), (143, 146), (146, 149), (149, 152), (152, 154), (154, 157), (157, 160), (160, 163), (163, 166), (166, 177), (177, 180), (180, 182), (182, 185), (185, 187), (187, 189), (189, 191), (191, 202), (202, 204), (204, 207), (207, 209), (209, 212), (212, 214), (214, 217), (217, 220), (220, 222), (222, 225), (225, 228), (228, 231), (231, 233), (233, 235), (235, 237), (237, 240), (240, 242), (242, 244), (244, 247), (247, 249), (249, 252), (252, 255), (255, 257), (257, 268), (268, 271), (271, 274), (274, 276), (276, 278), (278, 289), (289, 291), (291, 294), (294, 297), (297, 299), (299, 301), (301, 303), (303, 314), (314, 317), (317, 319), (319, 322), (322, 325), (325, 327), (327, 329), (329, 331), (331, 333), (333, 335), (335, 338), (338, 341), (341, 344), (344, 346), (346, 349), (349, 352), (352, 355), (355, 357), (357, 359), (359, 361), (361, 364), (364, 367), (367, 369), (369, 371), (371, 373)]
def segsY : List (ℕ × ℕ) := [(374, 385), (385, 388), (388, 392), (392, 396), (396, 401), (401, 404), (404, 409), (409, 414), (414, 418), (418, 424), (424, 430), (430, 435), (435, 451), (451, 454), (454, 458), (458, 463), (463, 479), (479, 483), (483, 488), (488, 493), (493, 499), (499, 515), (515, 518), (518, 522), (522, 527), (527, 531), (531, 536), (536, 552), (552, 557), (557, 562), (562, 567), (567, 582), (582, 586), (586, 591), (591, 597), (597, 603), (603, 619), (619, 624), (624, 640), (640, 646)]
def rawP : List ℕ := [0x7fff03fff8003c1fff81e000007801c0000000783fff81c00000000000f0f006000830206060808c0da40202d210369082810886101005c40846e2080420b0845c800208e486e40ae41c90000000000002f81206a8900178238903c00092f00b80029042f044e903800190820885e1e02c04906040c0c3011818000404002060010d02110c20200800118c003018c3610880002c35ff8c0034003ff220050b4132, 0x1f00000000000f80000000007fff003c000000000000000003fff8007c1e000070000080830101000020112018090180481400001002c030222090111020040010023210421210121012826000000000003e08260009305f08009308428da610788005308411003308924f3004f83c2022e4098101060203000040004030000300016c0001602d80600041a00030c218016abff4218400200035ffbff21b125402a2, 0x3fffbe0000000000000000000000003e0003fffbc0000001f000000f700000000000024080d808402c042140210a00400024000808400024281016012050880409844024482450880000000000004104c16aa67c20001261084014c2111101867c02245e6780012613e100845ee401300000002d8101b00000580002800016008140d80010000542dff8602c06c0a000581b0002dff85ff800011a1e0d104, 0x1fffbc007fff7b8003fff8007b80000003fffbc0001ef60000000a0001240020a0003928001d0090ec00b00ab000d6006a2ac035026c0024b0072296003a143b183a074000000000000821082030408410a78478009d88f70004ce4100f708441002cb4788003dec440042140006d800414000005000002b6ffc0160156001ac000055800006d8006d600005ac00002dffb00000000008a1a7bc, 0x0, 0x3fffbef0000000003fffbdf7dc00000000000000000002a000009284805800028001420000042900b00000503694d00000122d4d20b000a000a0140000000000010429040c48108210a48210826104222256e87de40128801036b87befb80808008a400015000005400000055b5ff800000016ac00001ad6bff00000006dadb00000005adb5ff8000000000050c0a465814, 0x1fffbdef0000000003fffbef7bbfffbdd80000000000000000000a120000002aa4842e0000160000b000b56aa6d400004c000026034d69b6a545c000002c002c002c05800000000000208420830102104233907bde48200040064f07def764f07bb40c0000201000008108156c000000555b5bff000000000000016ad56dac00000000000006dadb6d6abff000000000000000000661763228c8, 0x1f7fff78000000001fffbdef7fff7bbdd800000000000000000000000000000000000ab6ab6d49800001300000980004c000a14ab4969425702ad4b8180000000016000000b000b000b0160000000000003ef8c0f40604000023e07bde8fc0f77bb07002080007002000700210410001080030156d56dadb00000000000000000000016ad56dadad6bff55adffb0000000000000000000000000000001c041940c00, 0x1f7fff7bfffbefbdc00000000000000000000000000000000000000000000000000000a4aa496d800929c00292e0152700b6000000000001800000c0000000000018000000c000c000c0180000000000003eff00f7f807df7bbc004210f00084000780041084780042278004208221080001c0156d56dadb555b5bff55b5ffab6ffd6c0000000000000000000000000000000000000000000000000005987c01b202]
def rawL : List ℕ := rawP ++ [rawP.getD 0 0 ||| rawP.getD 1 0]
def FPM : ℕ := 0x7ffffffffff
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := 0x3efffef7fff7df7bbfff7bdefffef77bb7fff7def77fff7bb7fff7befbbdedeeedff956d56dadb555b5bff55b5ffab6ffd6d6ad56dadad6bff55adffb6dadb6d6abff5adb5ffadffb5ffbff7197ff7fbb6
def MM : ℕ := 191
def FF : ℕ := 0x7fffffffffffffffffffffffffffffffffffffffffffffff
def tab3 : List (ℕ × ℕ) := [(19, 8), (25, 8), (28, 8), (49, 8), (81, 8), (82, 8), (88, 8), (145, 8), (148, 8), (152, 8), (176, 8), (208, 8), (280, 8), (336, 8), (21, 7), (26, 7), (56, 7), (84, 7), (112, 7), (146, 7), (273, 7), (400, 7), (22, 6), (304, 6), (50, 5), (52, 5), (274, 5), (276, 5)]
def tab2 : List (ℕ × ℕ) := [(17, 11), (24, 11), (80, 11), (144, 11), (18, 9), (20, 9), (48, 9), (272, 9)]
def M16 : List ℕ := [0x7ffffffffffb7fefffffffffffed6edfffffffffffee7fff, 0x200000000000000000, 0x10000000000000000000, 0x8000, 0x80000000000000000000, 0x1000000000000000000000000000000000, 0x1000000000000000000, 0x200000000000000100000, 0x800000000000001000000000000000000000, 0x4000000000000000000000000000000010000]
def M24 : List ℕ := [0x7fbf7ffeffffff7effdfffdfffffffff73fffffdfffffdef, 0x4080010000008100200020000000008c00000200000210]
def M80 : List ℕ := [0x7ebffbffff7fff3ffffffffffcfff5fffffffffff7ffff5f, 0x1400400008000c00000000003000a0000000000080000a0]
def M144 : List ℕ := [0x7ffbfffffffffbbffbbffffffffebfbfffffefffffeeffff, 0x400000000044004400000000140400000100000110000]

noncomputable def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f (Nat.succ m)) n
noncomputable def sp (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.shiftRight s NN)) l
noncomputable def cov (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp l w.1) ih) v
noncomputable def twice (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp l w.1) (cov l t)) ih) v
noncomputable def hit (f e : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) true false (Nat.beq (Nat.land (Nat.land f e) HY) 0))
    false (Nat.beq (Nat.land (Nat.land f e) HX) 0)
noncomputable def hits (f : Nat) (m : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ ih => Bool.rec (motive := fun _ => Bool) ih true (hit f e)) m
noncomputable def flag (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp l w.1) o) AA
noncomputable def rect (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => Bool.rec (motive := fun _ => Bool) (ih (flag l o w :: m)) true (hits (flag l o w) m)) v
noncomputable def mkX (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w _ ih => (w, Nat.land (sp l w.1) o) :: ih) v
noncomputable def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
    (fun w _ ih h => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.1 y))
      (ih h) (Nat.beq w.1 x)) v
noncomputable def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o])
    (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r)))
      (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.1 w.1)) (Nat.ble w.1 o.1)) v
noncomputable def tail (f : Nat → List W → Bool) (l e n z : Nat) (r : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) (f z r)
      (Bool.rec (motive := fun _ => Bool) (f z r) false (rect l (Nat.xor l (twice l r)) r []))
      (Nat.beq n e))
    (Nat.beq (cov l r) l)
noncomputable def child (f : Nat → List W → Bool) (l g e n : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (st z (fun z => mk (tail f l e n z))) (Nat.beq (Nat.land z g) g)
noncomputable def put (s c : Nat) (v : List W) (h : List W → Bool) : Bool :=
  st s (fun s => Bool.rec (motive := fun _ => Bool) (st c (fun c => ins (s, c) v h)) false (Nat.beq s 0))
noncomputable def kids (ch : Nat → ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false (ch (Nat.succ (Nat.succ n)) mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))
      true
      (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) false (ch (Nat.succ n) (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) oa)
          true
          (Bool.rec (motive := fun _ => Bool) false (ch (Nat.succ n) (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) oc))
        (Nat.ble (Nat.succ n) e)))
    true
    (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (ch n (fun h => mk (fun r => rm a c' r h)) z) oc) oa)
noncomputable def mid (f : Nat → List W → Bool) (l g e n z : Nat) (v : List W) (a c : W) (da dc s ca : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (st (Nat.sub (Nat.add z (Nat.land a.2 c.2)) ca) (fun z =>
      kids (child f l g e) e n z a.2 c.2 a.1 c.1 (Nat.beq da 0) (Nat.beq dc 0) (put s ca v)))
    (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.2 c.2)) ca) g) g)
noncomputable def f0 (h : W → W → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s ca : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false (h a c da dc s ca) (Nat.beq dc 0)) (Nat.beq da 0)
noncomputable def f1 (h : W → W → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s ca : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (h a c da dc s ca) (Nat.beq dc 0)) (h a c da dc s ca) (Nat.beq da 0)
noncomputable def f2 (h : W → W → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s ca : Nat) : Bool := h a c da dc s ca
noncomputable def pair (h : W → W → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun a ua =>
    Prod.rec (motive := fun _ => Bool) (fun c uc =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool)
            (h a c (Nat.xor (Nat.land ua c.1) ua) (Nat.land uc a.1) (Nat.xor c.1 (Nat.land a.1 c.1)) c.2)
            true
            (h a c (Nat.land ua c.1) (Nat.xor (Nat.land uc a.1) uc) (Nat.xor a.1 (Nat.land a.1 c.1)) a.2))
          true
          (h a c (Nat.land ua c.1) (Nat.land uc a.1) (Nat.lor a.1 c.1) (Nat.land a.2 c.2)))
        true
        (h a c (Nat.xor (Nat.land ua c.1) ua) (Nat.xor (Nat.land uc a.1) uc) (Nat.land a.1 c.1) (Nat.lor a.2 c.2))) c) a
noncomputable def scan (p : X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun c _ jh => Bool.rec (motive := fun _ => Bool) jh true (p c)) xs
noncomputable def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true (scan (h a) r)) xs
noncomputable def wst (l : Nat) (v : List W) : Nat := Nat.xor l (twice l v)
noncomputable def node (f : Nat → List W → Bool) (l g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkX l (wst l v) v))
  (mid f l g e (Nat.pred n) z v)
noncomputable def look (l g : Nat) (fuel : Nat) : Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → List W → Bool) (fun _ _ _ => true)
    (fun _ ih k z v => (fun n => Bool.rec (motive := fun _ => Bool)
      (node (ih (Nat.sub k 1)) l g k n z v pairs) true (Nat.ble n 1)) v.length) fuel
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
noncomputable def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.1.1 x.1.1))) r)) xs
noncomputable def topC (l g fuel H k z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (node (look l g fuel (Nat.sub k 1)) l g k v.length z v (pairsC H))
    true (Nat.ble v.length 1)
noncomputable def addS (o : W) (v : List W) : List W := List.rec (motive := fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.1 w.1)) (Nat.ble w.1 o.1)) v
noncomputable def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
noncomputable def mkW (P : List ℕ) (s : ℕ) : W := (s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)))
noncomputable def avl (P : List ℕ) (m : ℕ) (L : List ℕ) : List W := List.rec (motive := fun _ => List W) []
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) 0)) L
noncomputable def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.1 fun s => st w.2 fun c => ih fun r => h ((s, c) :: r)) v
noncomputable def anySub (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (ih h) true (ih fun r => h (w :: r))) v
noncomputable def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.2 ih) v
noncomputable def startv (l g B K H : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l g K H K z r)
      l g (Nat.succ K) v.length (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.succ K))) (Nat.beq (cov l v) l)
def kz (Z : ℕ) : ℕ := (List.range 9).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else x) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
def pr (Z : ℕ) : List (ℕ × ℕ) := (tab3 ++ tab2).filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
def PZ (Z : ℕ) : List ℕ := (pr Z).map (fun e => mz e.1)
noncomputable def chk (Z K H : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B =>
    frc (avl P m rawL) (fun v => anySub v (fun r => st l fun l => st g fun g => st B fun B => startv l g B K H r)))
    (pL ((pr Z).map fun e => 16 + (K - e.2)))) (pL ((pr Z).map fun _ => 16))) (PZ Z)) (mz Z)) (lz Z)

lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl

lemma pairwise_symm_forall {α : Type*} {R : α → α → Prop} {l : List α}
    (hp : l.Pairwise R) (hs : ∀ a b, R a b → R b a)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) : R x y := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 hx with rfl | hx'
    · rcases List.mem_cons.1 hy with rfl | hy'
      · exact absurd rfl hne
      · exact hp.1 _ hy'
    · rcases List.mem_cons.1 hy with rfl | hy'
      · exact hs _ _ (hp.1 _ hx')
      · exact ih hp.2 hx' hy'

lemma sp_bit (l s i : ℕ) : (sp l s).testBit i = (l.testBit i && sepb NN s i) := by
  simp only [sp, sepb, nl, nx, nsr, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight]
  cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl

lemma cov_bit (l i : ℕ) (v : List W) : (cov l v).testBit i = true ↔ ∃ w ∈ v, (sp l w.1).testBit i = true := by
  induction v with
  | nil => simp [cov]
  | cons w v ih =>
    change (Nat.lor (sp l w.1) (cov l v)).testBit i = true ↔ _
    simp [ih]

lemma twice_bit (l i : ℕ) (v : List W) (h : (twice l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp l w.1).testBit i = true ∧ (sp l w'.1).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp l w.1) (cov l v)) (twice l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h

def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map Prod.fst).Nodup ∧ (v.map Prod.fst).toFinset = S

lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.1 = x := by
  rw [← h.2]; simp

lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.1 = w'.1) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e

lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]

lemma uq_of {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp l w.1) (wst l v)).testBit i = true) : l.testBit i = true ∧ Uq NN S w.1 i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit l i v ht
  have := pairwise_symm_forall hp (fun a b h h' => h h'.symm) hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this

def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG : AA &&& TG = AA := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt : TG < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt : AA < 2 ^ NN := by decide +kernel
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good : rawL.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true := by decide +kernel

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
  | true => rw [h1] at h; simp only [Bool.cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [Bool.cond_true, Bool.cond_false, Bool.false_eq_true] at h
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

lemma rect_false {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag l o b) (flag l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag l o w) e = false) → rect l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect l o v (flag l o w :: m)) true (hits (flag l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he

lemma Live.pos {T k : ℕ} {S : Finset ℕ} (h : Live T k S) : 0 < S.card := by
  cases k with
  | zero => change S = {T} at h; subst h; simp
  | succ k => obtain ⟨_, _, _, _, _, _, rfl, _⟩ := h; exact Finset.card_pos.2 (Finset.insert_nonempty _ _)

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

def fl (w : W) (j : ℕ) : ℕ := (w.2.testBit (5 * j)).toNat
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.2.testBit (5 * j) <;> simp
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq

def WOk (P : List ℕ) (w : W) : Prop :=
  isPk P.length w.2 ∧ ∀ j < P.length, w.2.testBit (5 * j) = true → w.1 &&& P.getD j 0 = 0

lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.2.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.1 :=
  h.2 j hj hf

def Cl (P : List ℕ) (T k : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  ∀ j < P.length, ∀ q, q + b j < k → ¬ Sol (T &&& P.getD j 0) q (C (Im (P.getD j 0) S))

def StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop :=
  Rep v S ∧ (∀ w ∈ v, WOk P w) ∧ (∀ w ∈ v, Good l w.1) ∧
  ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)

def Ctx (P : List ℕ) (l g T : ℕ) : Prop :=
  (∀ i, l.testBit i = true → Lg NN T i ∧ AA.testBit i = true) ∧
  (∀ j < P.length, T &&& P.getD j 0 ≠ 0) ∧
  g = pk P.length (fun _ => 16)

lemma cnt_le {P : List ℕ} {l g T k k' : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ}
    (hctx : Ctx P l g T) (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k b S) (hm : Min T k' S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨q, hq, hs⟩ := hm.const (hctx.2.1 j hj)
  have hqb : ¬ q + b j < k := fun h => hc j hj q h hs
  have : cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
    have e : cnt v j = (v.filter (fun w => w.2.testBit (5 * j))).length := by
      clear hr hw
      induction v with
      | nil => rfl
      | cons w v ih =>
        rw [cnt_cons, ih, List.filter_cons, fl]
        cases w.2.testBit (5 * j) <;> simp; omega
    rw [e, ← List.length_map Prod.fst, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
    apply Finset.card_le_card
    intro x hx
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
    obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
    rw [Finset.mem_filter]
    exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
  omega

lemma cov_ok {P : List ℕ} {l g T k' : ℕ} {r : List W} {S : Finset ℕ}
    (hctx : Ctx P l g T) (hrep : Rep r S) (hl : Live T k' S) :
    Nat.beq (cov l r) l = true := by
  rw [Nat.beq_eq]
  apply Nat.eq_of_testBit_eq; intro i
  cases hli : l.testBit i with
  | false =>
    by_contra hc
    obtain ⟨w, _, hw⟩ := (cov_bit l i r).1 (by simpa using hc)
    rw [sp_bit, hli] at hw; simp at hw
  | true =>
    rw [cov_bit]
    obtain ⟨⟨t1, t2⟩, _⟩ := hctx.1 i hli
    obtain ⟨w, hw, hs⟩ := Live.cov t1 t2 hl
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, hs]; rfl⟩

lemma tail_sound {P : List ℕ} {l g T : ℕ} (hctx : Ctx P l g T)
    {f : ℕ → List W → Bool} {e n z k k' : ℕ} {r : List W} {S : Finset ℕ}
    (hr : StOk P T l k z r S) (hm : Min T k' S) (hk : k' ≤ k) (hn : n = r.length)
    (he : e = k + 1) (h : tail f l e n z r = false) : f z r = false := by
  simp only [tail, bR, cov_ok hctx hr.1 hm.1] at h
  by_cases hne : n = e
  · have hb : Nat.beq n e = true := by simpa using hne
    rw [hb, Bool.cond_true] at h
    cases hrect : rect l (Nat.xor l (twice l r)) r [] with
    | false => rw [hrect] at h; simpa using h
    | true =>
      exfalso
      have hs := hm.size
      have hcard := hr.1.card
      have htight : S.card = k' + 1 := by omega
      rw [rect_false (o := Nat.xor l (twice l r))] at hrect; · simp at hrect
      · have hnd : r.Pairwise (fun a b => a.1 ≠ b.1) := List.pairwise_map.1 hr.1.1
        refine hnd.imp_of_mem fun {a b} ha hb' hab => ?_
        by_contra hhit
        rw [Bool.not_eq_false] at hhit
        obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec hhit
        have hu : ∀ w, ∀ i, (Nat.land (sp l w) (wst l r)).testBit i = true → AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (hctx.1 i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.1) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.1) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.1) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.1) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.1 ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.1 hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.1 ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.1 hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.1.mem.1 hw
          exact (hr.2.2.1 w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.1.mem.1 hw
          exact (hr.2.2.1 w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
        have ma := hr.1.mem.2 ⟨a, ha, rfl⟩
        have mb := hr.1.mem.2 ⟨b, hb', rfl⟩
        exact rect1 hm.1 hm.2 htight (hctx.1 _ l1).1 (hctx.1 _ l2).1 (hctx.1 _ l3).1 (hctx.1 _ l4).1
          ma mb hab g1 g2 u1 u2 u3 u4
      · simp
  · have hb : Nat.beq n e = false := Bool.eq_false_iff.2 fun h => hne (Nat.eq_of_beq_eq_true h)
    rw [hb, Bool.cond_false] at h; exact h

lemma guard_ok {P : List ℕ} {l g T k k' z : ℕ} (hctx : Ctx P l g T)
    {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min T k' S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.2.2.2
  have hle := cnt_le hctx hr.1 hr.2.1 hc hm hk
  rw [nl, hz, hctx.2.2, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega

lemma child_sound {P : List ℕ} {l g T : ℕ} (hctx : Ctx P l g T)
    {f : ℕ → List W → Bool} {e n z k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k z r S) (hm : Min T k' S) (hk : k' ≤ k) (hn : n = r.length)
    (he : e = k + 1) (h : child f l g e n mk z = false) : f z r = false := by
  simp only [child, st_eq, guard_ok hctx hr hm hk, hmk] at h
  exact tail_sound hctx hr hm hk hn he h

lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.1 x || Nat.beq w.1 y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.1 y)) (rm x y v h) (Nat.beq w.1 x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.1 x <;> cases Nat.beq w.1 y <;> simp

lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.1 ≠ o.1) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.1 o.1 then (bif Nat.beq o.1 w.1 then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.1 w.1)) (Nat.ble w.1 o.1) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.1 o.1 with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.1 w.1 = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl

lemma filter_perm {v : List W} (hv : (v.map Prod.fst).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.1 a.1)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.1 a.1) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.1 a.1 (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, ite_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)

lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.1 x || Nat.beq w.1 y)) =
    (v.filter (fun w => !Nat.beq w.1 x)).filter (fun w => !Nat.beq w.1 y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.1 x <;> cases Nat.beq w.1 y <;> rfl

lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.1 x || Nat.beq w.1 x)) = v.filter (fun w => !Nat.beq w.1 x) := by
  congr 1; funext w; cases Nat.beq w.1 x <;> rfl

def Shape (o a c : W) (v : List W) (ka kc : Bool) (r : List W) : Prop :=
  match ka, kc with
  | false, false => (a :: c :: r).Perm (o :: v)
  | true,  false => (c :: r).Perm (o :: v)
  | false, true  => (a :: r).Perm (o :: v)
  | true,  true  => r.Perm (o :: v)

lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases ka <;> cases kc <;> simp only [Shape] at h
  · have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  · have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  · have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  · have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega

lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases ka <;> cases kc <;> simp only [Shape] at h
    · exact h.subset (by simp [hw])
    · exact h.subset (by simp [hw])
    · exact h.subset (by simp [hw])
    · exact h.subset (by simp [hw])
  simpa using this

lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases ka <;> cases kc <;> simp only [Shape] at h
  · have := h.length_eq; simp at this ⊢; omega
  · have := h.length_eq; simp at this ⊢; omega
  · have := h.length_eq; simp at this ⊢; omega
  · have := h.length_eq; simp at this ⊢; omega

lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (_hac : a.1 ≠ c.1) (ho : o.1 ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.1 ∨ (x ∈ S ∧ (x = a.1 → ka = true) ∧ (x = c.1 → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map Prod.fst).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map Prod.fst ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map Prod.fst ↔ x = o.1 ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.1).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.1).1 (List.mem_map_of_mem hc)
  have hao : a.1 ≠ o.1 := fun e => ho (e ▸ haS)
  have hco : c.1 ≠ o.1 := fun e => ho (e ▸ hcS)
  cases ka <;> cases kc <;> simp only [Shape] at h
  · have hn := (h.map Prod.fst).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map Prod.fst).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.1 := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.1 := fun e => hn.2.1 (e ▸ h1)
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
  · have hn := (h.map Prod.fst).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map Prod.fst).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.1 := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  · have hn := (h.map Prod.fst).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map Prod.fst).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.1 := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  · have hn := (h.map Prod.fst).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map Prod.fst).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp

lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.1 ≠ o.1) (hp : r.Perm (o :: v)) (hv : (v.map Prod.fst).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.1 ≠ c.1) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.1 a.1 || Nat.beq w.1 c.1))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.1 c.1 || Nat.beq w.1 c.1))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.1 a.1 || Nat.beq w.1 a.1))) ∧ Shape o a c v true true r := by
  have hnd : (r.map Prod.fst).Nodup := by
    refine (hp.map Prod.fst).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨?_, ?_, ?_, hp⟩
  · change (a :: c :: r.filter (fun w => !(Nat.beq w.1 a.1 || Nat.beq w.1 c.1))).Perm (o :: v)
    rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.1 a.1) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · change (c :: r.filter (fun w => !(Nat.beq w.1 c.1 || Nat.beq w.1 c.1))).Perm (o :: v)
    rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · change (a :: r.filter (fun w => !(Nat.beq w.1 a.1 || Nat.beq w.1 a.1))).Perm (o :: v)
    rw [filter1]; exact (filter_perm hnd har).trans hp

lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map Prod.fst).Nodup) (hac : a.1 ≠ c.1) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.1 a.1) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega

lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map Prod.fst).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega

def opW (d : ℕ) (a c : W) : W :=
  match d with
  | 0 => (a.1 &&& c.1, a.2 ||| c.2)
  | 1 => (a.1 ||| c.1, a.2 &&& c.2)
  | 2 => (a.1 ^^^ (a.1 &&& c.1), a.2)
  | _ => (c.1 ^^^ (a.1 &&& c.1), c.2)

lemma opW_s (d : ℕ) (a c : W) : (opW d a c).1 = op d a.1 c.1 := by
  rcases d with _ | _ | _ | d <;> rfl

lemma opW_ok {P : List ℕ} {a c : W} (d : ℕ) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  rcases d with _ | _ | _ | d
  · refine ⟨isPk_or ha.1 hc.1, fun j hj h => ?_⟩
    have h : (a.2 ||| c.2).testBit (5 * j) = true := h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    rw [opW_s, and_op]
    rcases h with h | h
    · rw [ha.2 j hj h]; simp [op]
    · rw [hc.2 j hj h]; simp [op]
  · refine ⟨isPk_and ha.1, fun j hj h => ?_⟩
    have h : (a.2 &&& c.2).testBit (5 * j) = true := h
    rw [Nat.testBit_and, Bool.and_eq_true] at h
    rw [opW_s, and_op, ha.2 j hj h.1, hc.2 j hj h.2]; simp [op]
  · refine ⟨ha.1, fun j hj h => ?_⟩
    rw [opW_s, and_op, ha.2 j hj h]; simp [op]
  · refine ⟨hc.1, fun j hj h => ?_⟩
    rw [opW_s, and_op, hc.2 j hj h]; simp [op]

lemma op_good {l x y : ℕ} (d : ℕ) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]

lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.2 &&& c.2 = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.2) ha.1)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.2.testBit (5 * j) <;> cases c.2.testBit (5 * j) <;> rfl

lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.2 = pk P.length (fl a) := pk_of ha.1

lemma bi_st {P : List ℕ} {l g T : ℕ} (hctx : Ctx P l g T) {k k' z : ℕ} {v r : List W} {S S' : Finset ℕ}
    {d' : ℕ} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min T (k' + 1) S) (hk : k' ≤ k) (hb : Bi d' a.1 c.1 S S')
    (hl : Live T k' S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.1 ∈ S')) (hkc : kc = decide (c.1 ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k (z + (a.2 &&& c.2) - (opW d' a c).2 - (bif ka then a.2 else 0) - (bif kc then c.2 else 0)) r S' ∧
    Nat.beq (Nat.land (z + (a.2 &&& c.2) - (opW d' a c).2) g) g = true := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.2.2.2
  have hle := cnt_le hctx hs.1 hs.2.1 hcl hm (by omega)
  have hab : a.1 ≠ c.1 := hb.2.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).1 ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ (by simpa using h))
  have wa := hs.2.1 a ha; have wc := hs.2.1 c hc
  have wo := opW_ok d' wa wc
  have hrep : Rep r S' := by
    refine hsh.rep hs.1 ha hc hab hfS fun x => ?_
    obtain ⟨_, _, U, e1, e2⟩ := hb
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
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hsh.mem hw).elim (fun e => e ▸ wo) (hs.2.1 w)
  have hgood : ∀ w ∈ r, Good l w.1 := fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s]; exact op_good _ (hs.2.2.1 a ha) (hs.2.2.1 c hc)
    · exact hs.2.2.1 w h
  let b' : ℕ → ℕ := fun j => b j - max (fl a j) (fl c j)
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.1.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.2.testBit (5 * j) = true ∨ c.2.testBit (5 * j) = true
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
  have hle' := cnt_le hctx hrep hwok hcl' hmin hk
  have num : ∀ j < P.length, 1 ≤ 16 + b j - cnt v j + fl a j * fl c j ∧ fl (opW d' a c) j ≤ 1 ∧
      16 ≤ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j ∧ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j < 32 ∧
      16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (bif ka then fl a j else 0) - (bif kc then fl c j else 0) = 16 + b' j - cnt r j := by
    intro j hj
    have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_two ha hc hs.1.1 hab j; have q4 := hb15 j hj
    have q5 := hsh.cnt j; have q6 := fl_le a j; have q7 := fl_le c j; have q8 := fl_le (opW d' a c) j
    simp only [b'] at q2 ⊢
    generalize fl a j = fa at *; generalize fl c j = fc at *; generalize fl (opW d' a c) j = fo at *
    interval_cases fa <;> interval_cases fc <;> cases ka <;> cases kc <;> simp at q2 q3 q5 ⊢ <;> omega
  have e1 : z + (a.2 &&& c.2) - (opW d' a c).2 = pk P.length (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, fl_pk wo, pk_add, pk_sub]
    intro j hj; have := num j hj; omega
  refine ⟨⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩, ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · rw [e1]
    have ea : (bif ka then a.2 else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have ec : (bif kc then c.2 else 0) = pk P.length (fun j => bif kc then fl c j else 0) := by
      cases kc
      · simp [pk]
      · exact fl_pk wc
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    have le2 : ∀ j, (bif kc then fl c j else 0) ≤ 1 := fun j => by cases kc <;> simp [fl_le]
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (num j hj).2.2.2.2
    · intro j hj; have := num j hj; have := le1 j; have := le2 j; omega
    · intro j hj; have := num j hj; have := le1 j; omega
  · rw [e1, nl, hctx.2.2, pk_guard]; · simp
    intro j hj; have := num j hj; omega

lemma drop_ok {P : List ℕ} {l g T : ℕ} (hctx : Ctx P l g T) {k' : ℕ} {v : List W} {S S' : Finset ℕ}
    {d' : ℕ} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi d' a.1 c.1 S S') (hl : Live T k' S') (ha : a ∈ v) (hk : a.1 ∉ S')
    (hu : (Nat.land (sp l a.1) (wst l v)).testBit i = true) :
    (d' = 0 → c.1.testBit i = true) ∧ (d' = 1 → c.1.testBit i = false) ∧
    (d' = 2 → c.1.testBit i = false) ∧ (d' = 3 → c.1.testBit i = true) := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨t1, t2⟩, _⟩ := hctx.1 i hli
  obtain ⟨w, hw, hs⟩ := Live.cov t1 t2 hl
  have hac : c.1 ≠ a.1 := hb.2.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb NN (op d' a.1 c.1) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.1 hb.sub.2.1 hac
  have hd' := hb.1
  rcases d' with _ | _ | _ | d'
  · revert hg hcn u1; unfold sepb; simp only [op_bit, bOp]
    cases a.1.testBit i <;> cases a.1.testBit (NN + i) <;> cases c.1.testBit i <;> cases c.1.testBit (NN + i) <;> simp
  · revert hg hcn u1; unfold sepb; simp only [op_bit, bOp]
    cases a.1.testBit i <;> cases a.1.testBit (NN + i) <;> cases c.1.testBit i <;> cases c.1.testBit (NN + i) <;> simp
  · revert hg hcn u1; unfold sepb; simp only [op_bit, bOp]
    cases a.1.testBit i <;> cases a.1.testBit (NN + i) <;> cases c.1.testBit i <;> cases c.1.testBit (NN + i) <;> simp
  · have : d' = 0 := by omega
    subst this
    revert hg hcn u1; unfold sepb; simp only [op_bit, bOp]
    cases a.1.testBit i <;> cases a.1.testBit (NN + i) <;> cases c.1.testBit i <;> cases c.1.testBit (NN + i) <;> simp

noncomputable def mkx (l o : ℕ) (w : W) : X := (w, Nat.land (sp l w.1) o)

lemma mkX_eq (l o : ℕ) (v : List W) : mkX l o v = v.map (mkx l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX l o v = _; rw [ih]; rfl

noncomputable def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0

lemma node_eq (f : ℕ → List W → Bool) (l g e n z : ℕ) (v : List W) (go : (X → X → Bool) → List X → Bool) :
    node f l g e n z v go = go (pair (modeF n e (mid f l g e (Nat.pred n) z v))) (v.map (mkx l (wst l v))) := by
  rw [← mkX_eq]; unfold node modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl

lemma modeF_false {n e : ℕ} {h : W → W → ℕ → ℕ → ℕ → ℕ → Bool} {a c : W} {da dc s ca : ℕ}
    (hf : modeF n e h a c da dc s ca = false) (h0 : ¬ n ≤ e → da = 0 ∧ dc = 0) (h1 : ¬ n + 1 ≤ e → da = 0 ∨ dc = 0) :
    h a c da dc s ca = false := by
  unfold modeF at hf
  cases b1 : Nat.ble n e with
  | false =>
    have := h0 (fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1)
    rw [b1, this.1, this.2] at hf; rw [this.1, this.2]; exact hf
  | true =>
    cases b2 : Nat.ble (Nat.succ n) e with
    | false =>
      have := h1 (fun h => by rw [Nat.ble_eq_true_of_le h] at b2; simp at b2)
      rw [b1, b2] at hf
      simp only [Bool.cond_true, Bool.cond_false, f1, bR] at hf
      rcases this with h2 | h2
      · simp [h2] at hf; simp [h2, hf]
      · cases ha : Nat.beq da 0 <;> simp [ha, h2] at hf ⊢ <;> exact hf
    | true => rw [b1, b2] at hf; exact hf

noncomputable def dfc (d' l o : ℕ) (a c : W) : ℕ :=
  let u := Nat.land (sp l a.1) o
  match d' with
  | 0 => Nat.xor (Nat.land u c.1) u
  | 1 => Nat.land u c.1
  | 2 => Nat.land u c.1
  | _ => Nat.xor (Nat.land u c.1) u

def swapOp (d : ℕ) : ℕ :=
  match d with
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | _ => 2

lemma Bi.swap {d a b : ℕ} {S S' : Finset ℕ} (h : Bi d a b S S') : Bi (swapOp d) b a S S' := by
  obtain ⟨hd, hab, U, rfl, rfl⟩ := h
  rcases d with _ | _ | _ | d
  · exact ⟨by decide, hab.symm, U, Finset.insert_comm _ _ _, by simp [swapOp, op, Nat.and_comm]⟩
  · exact ⟨by decide, hab.symm, U, Finset.insert_comm _ _ _, by simp [swapOp, op, Nat.or_comm]⟩
  · exact ⟨by decide, hab.symm, U, Finset.insert_comm _ _ _, by simp [swapOp, op, Nat.and_comm]⟩
  · exact ⟨by simp [swapOp], hab.symm, U, Finset.insert_comm _ _ _, by simp [swapOp, op, Nat.and_comm]⟩

lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → Bool} {l o : ℕ} {a c : W}
    (hp : pair h (mkx l o a) (mkx l o c) = false) {d' : ℕ} (hd' : d' < 4) :
    h a c (dfc d' l o a c) (dfc (swapOp d') l o c a) (opW d' a c).1 (opW d' a c).2 = false := by
  simp only [pair, mkx, bR] at hp
  rcases d' with _ | _ | _ | d'
  · cases h0 : h a c (Nat.xor (Nat.land (Nat.land (sp l a.1) o) c.1) (Nat.land (sp l a.1) o))
        (Nat.xor (Nat.land (Nat.land (sp l c.1) o) a.1) (Nat.land (sp l c.1) o)) (Nat.land a.1 c.1) (Nat.lor a.2 c.2) with
    | true => rw [h0] at hp; simp at hp
    | false => exact h0
  · revert hp
    cases h0 : h a c _ _ (Nat.land a.1 c.1) (Nat.lor a.2 c.2)
    · cases h1 : h a c (Nat.land (Nat.land (sp l a.1) o) c.1) (Nat.land (Nat.land (sp l c.1) o) a.1) (Nat.lor a.1 c.1) (Nat.land a.2 c.2)
      · intro _; exact h1
      · simp
    · simp
  · revert hp
    cases h0 : h a c _ _ (Nat.land a.1 c.1) (Nat.lor a.2 c.2)
    · cases h1 : h a c _ _ (Nat.lor a.1 c.1) (Nat.land a.2 c.2)
      · cases h2 : h a c (Nat.land (Nat.land (sp l a.1) o) c.1) (Nat.xor (Nat.land (Nat.land (sp l c.1) o) a.1) (Nat.land (sp l c.1) o))
            (Nat.xor a.1 (Nat.land a.1 c.1)) a.2
        · intro _; exact h2
        · simp
      · simp
    · simp
  · have : d' = 0 := by omega
    subst this
    revert hp
    cases h0 : h a c _ _ (Nat.land a.1 c.1) (Nat.lor a.2 c.2)
    · cases h1 : h a c _ _ (Nat.lor a.1 c.1) (Nat.land a.2 c.2)
      · cases h2 : h a c _ _ (Nat.xor a.1 (Nat.land a.1 c.1)) a.2
        · exact id
        · simp
      · simp
    · simp

lemma put_eq {o : W} {v : List W} (h0 : o.1 ≠ 0) (h : List W → Bool) :
    put o.1 o.2 v h = ins o v h := by
  have hb0 : Nat.beq o.1 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  simp only [put, st_eq, hb0]

lemma mid_false {f : ℕ → List W → Bool} {l g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : ℕ}
    (h : mid f l g e n z v a c da dc (opW d' a c).1 (opW d' a c).2 = false)
    (hg : Nat.beq (Nat.land (z + (a.2 &&& c.2) - (opW d' a c).2) g) g = true) :
    kids (child f l g e) e n (z + (a.2 &&& c.2) - (opW d' a c).2) a.2 c.2 a.1 c.1 (Nat.beq da 0) (Nat.beq dc 0)
      (put (opW d' a c).1 (opW d' a c).2 v) = false := by
  simp only [mid, st_eq, bR] at h
  have hg' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.2 c.2)) (opW d' a c).2) g) g = true := hg
  rw [hg', Bool.cond_true] at h
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

lemma gate_sound {P : List ℕ} {l g T : ℕ} (hctx : Ctx P l g T)
    {f : ℕ → List W → Bool} {e n z k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : ℕ}
    (hs : StOk P T l (k + 1) z v S) (hm : Min T (k' + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (he : e = k + 1) (hb : Bi d' a.1 c.1 S S') (hl : Live T k' S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f l g e (Nat.pred n) z v)) (mkx l (wst l v) a) (mkx l (wst l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' := by
  subst hn
  have hd' : d' < 4 := hb.1
  have hmin := hb.min hl hm.2
  have hsz := hmin.size
  have hpos := hl.pos
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.1 ≠ (opW d' a c).1 := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ (by simpa using hs.1.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).1 ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.1.1 ha hc hb.2.1
  have hp := pair_false hp hd'
  generalize hoa : dfc d' l (wst l v) a c = da at hp
  generalize hoc : dfc (swapOp d') l (wst l v) c a = dc at hp
  have dfc_zero : ∀ {q : ℕ} {x y : W} {Sx : Finset ℕ}, q < 4 → Rep v S → Bi q x.1 y.1 S Sx →
      Live T k' Sx → x ∈ v → x.1 ∉ Sx → dfc q l (wst l v) x y = 0 := by
    intro q x y Sx hq hr hbx hlx hx hxn
    unfold dfc
    generalize hu : Nat.land (sp l x.1) (wst l v) = u
    have hdrop : ∀ i, u.testBit i = true → (q = 0 → y.1.testBit i = true) ∧ (q = 1 → y.1.testBit i = false) ∧
        (q = 2 → y.1.testBit i = false) ∧ (q = 3 → y.1.testBit i = true) :=
      fun i hi => drop_ok hctx hr hbx hlx hx hxn (hu ▸ hi)
    rcases q with _ | _ | _ | q
    · apply Nat.eq_of_testBit_eq; intro i
      simp only [nl, nx, Nat.testBit_xor, Nat.testBit_and, Nat.zero_testBit]
      cases hi : u.testBit i
      · simp
      · simp [(hdrop i hi).1 rfl]
    · apply Nat.eq_of_testBit_eq; intro i
      simp only [nl, Nat.testBit_and, Nat.zero_testBit]
      cases hi : u.testBit i
      · simp
      · simp [(hdrop i hi).2.1 rfl]
    · apply Nat.eq_of_testBit_eq; intro i
      simp only [nl, Nat.testBit_and, Nat.zero_testBit]
      cases hi : u.testBit i
      · simp
      · simp [(hdrop i hi).2.2.1 rfl]
    · have : q = 0 := by omega
      subst this
      apply Nat.eq_of_testBit_eq; intro i
      simp only [nl, nx, Nat.testBit_xor, Nat.testBit_and, Nat.zero_testBit]
      cases hi : u.testBit i
      · simp
      · simp [(hdrop i hi).2.2.2 rfl]
  have fa : a.1 ∉ S' → da = 0 := fun h => by
    rw [← hoa]; exact dfc_zero hd' hs.1 hb hl ha h
  have fc : c.1 ∉ S' → dc = 0 := fun h => by
    rw [← hoc]
    have hsw : swapOp d' < 4 := by rcases d' with _ | _ | _ | d' <;> simp [swapOp]
    exact dfc_zero hsw hs.1 hb.swap hl hc h
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put (opW d' a c).1 (opW d' a c).2 v h = h r0 := fun h => by
    rw [put_eq ho0, hins]
  have hv2 : 2 ≤ v.length := by
    rw [← hs.1.card]
    have : ({a.1, c.1} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hb.2.1] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.1 ∈ S') → kc = decide (c.1 ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ S'.card ≤ e ∧ StOk P T l k (z + (a.2 &&& c.2) - (opW d' a c).2 - (bif ka then a.2 else 0) - (bif kc then c.2 else 0)) r S' := by
    intro ka kc r h1 h2 h3
    have := (bi_st hctx hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.1.card.symm, by omega, this⟩
  have hguard : Nat.beq (Nat.land (z + (a.2 &&& c.2) - (opW d' a c).2) g) g = true := by
    by_cases q1 : a.1 ∈ S' <;> by_cases q2 : c.1 ∈ S'
    · exact (bi_st hctx hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st hctx hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st hctx hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exact (bi_st hctx hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s1).2
  have fin : ∀ {n z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k z' r S' → n = r.length →
      child f l g e n mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' :=
    fun {n z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound hctx h1 h2 hmin hk h3 he h4, h2⟩
  by_cases q1 : a.1 ∈ S' <;> by_cases q2 : c.1 ∈ S'
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

lemma node_bi {P : List ℕ} {l g T : ℕ} (hctx : Ctx P l g T)
    {f : ℕ → List W → Bool} {e n z k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : ℕ}
    {go : (X → X → Bool) → List X → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min T (k' + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (he : e = k + 1) (hb : Bi d' x y S S') (hl : Live T k' S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.1 = x → c.1 = y → xs = v.map (mkx l (wst l v)) →
      h (mkx l (wst l v) a) (mkx l (wst l v) c) = false ∨ h (mkx l (wst l v) c) (mkx l (wst l v) a) = false)
    (hp : node f l g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.1.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.1.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · exact gate_sound hctx hs hm hk hn he hb hl ha hc h
  · exact gate_sound hctx hs hm hk hn he hb.symm.choose_spec hl hc ha h

lemma look_sound {P : List ℕ} {l g T : ℕ} (hctx : Ctx P l g T) :
    ∀ (fuel k z : ℕ) (v : List W) (S : Finset ℕ), look l g fuel k z v = false → StOk P T l k z v S →
    ∀ k' ≤ k, ¬ Min T k' S := by
  intro fuel
  induction fuel with
  | zero => intro k z v S h; simp [look] at h
  | succ fuel ih =>
    intro k z v S h hs k' hk hm
    change (Bool.rec (motive := fun _ => Bool)
      (node (look l g fuel (Nat.sub k 1)) l g k v.length z v pairs) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, Bool.cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hc2 : 2 ≤ S.card := by rw [hs.1.card]; exact hlen
      cases k' with
      | zero =>
        obtain ⟨hl, _⟩ := hm
        change S = {T} at hl
        subst hl; simp at hc2
      | succ k0 =>
        obtain ⟨d, hd, a, b, U, hab, hS, hl⟩ := hm.1
        have hb : Bi d a b S (insert (op d a b) U) := ⟨hd, hab, U, hS, rfl⟩
        obtain ⟨k1, rfl⟩ : ∃ k1, k = k1 + 1 := ⟨k - 1, by omega⟩
        have hnode : node (look l g fuel k1) l g (k1 + 1) v.length z v pairs = false := h
        obtain ⟨z', r, hf, hst⟩ := node_bi hctx hs hm (by omega) rfl rfl hb hl (fun h xs hp ca cc hca hcc hax hcy hxs => by
          subst hxs
          have hpw := pairs_false hp
          refine pairwise_symm_forall (hpw.imp fun h => Or.inl h) (fun _ _ h => h.symm)
            (List.mem_map_of_mem hca) (List.mem_map_of_mem hcc) ?_
          intro e
          have : ca.1 = cc.1 := congrArg (fun x : X => x.1.1) e
          exact hab (by rw [← hax, ← hcy, this])) hnode
        exact ih _ _ _ _ hf hst k0 (by omega) (hb.min hl hm.2)

lemma pairsC_false {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.1.1 + b.1.1) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.1.1 x.1.1))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.1.1 x.1.1))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.1.1 x.1.1))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.1.1 b.1.1) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp

lemma topC_succ {l g fuel H k z : ℕ} {v : List W} (h : topC l g fuel H k z v = false) :
    2 ≤ v.length ∧ node (look l g fuel (k - 1)) l g k v.length z v (pairsC H) = false := by
  simp only [topC, bR] at h
  cases h0 : Nat.ble v.length 1 with
  | true => rw [h0] at h; simp at h
  | false =>
    rw [h0, Bool.cond_false] at h
    have hlen : 2 ≤ v.length := by
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
    exact ⟨hlen, h⟩

lemma topC_sound {P : List ℕ} {l g T : ℕ} (hctx : Ctx P l g T) {fuel k z : ℕ} {v : List W} {S : Finset ℕ} {M : List ℕ}
    (h : ∀ H ∈ M, topC l g fuel H k z v = false)
    (hcov : ∀ x, ∃ H ∈ M, hb H x = true)
    (hs : StOk P T l k z v S) : ∀ k' ≤ k, ¬ Min T k' S := by
  intro k' hk hm
  have hM : M ≠ [] := by
    intro he
    obtain ⟨H, hmem, _⟩ := hcov 0
    rw [he] at hmem; simp at hmem
  obtain ⟨H0, hH0⟩ := List.exists_mem_of_ne_nil M hM
  have hlen := (topC_succ (h H0 hH0)).1
  have hc2 : 2 ≤ S.card := by rw [hs.1.card]; exact hlen
  cases k' with
  | zero =>
    obtain ⟨hl, _⟩ := hm
    change S = {T} at hl
    subst hl; simp at hc2
  | succ k0 =>
    obtain ⟨d, hd, a, b, U, hab, hS, hl⟩ := hm.1
    have hbi : Bi d a b S (insert (op d a b) U) := ⟨hd, hab, U, hS, rfl⟩
    obtain ⟨H, hHM, hH⟩ := hcov (a + b)
    obtain ⟨k1, rfl⟩ : ∃ k1, k = k1 + 1 := ⟨k - 1, by omega⟩
    have hnode := (topC_succ (h H hHM)).2
    obtain ⟨z', r, hf, hst⟩ := node_bi hctx hs hm (by omega) rfl rfl hbi hl (fun h xs hp ca cc hca hcc hax hcy hxs => by
      subst hxs
      have hpw := pairsC_false hp
      have : ∀ x y : X, (hb H (x.1.1 + y.1.1) = true → h x y = false ∨ h y x = false) →
          (hb H (y.1.1 + x.1.1) = true → h y x = false ∨ h x y = false) := by
        intro x y h' e; exact (h' (by rwa [Nat.add_comm])).symm
      refine pairwise_symm_forall (hpw.imp fun h e => Or.inl (h e)) this
        (List.mem_map_of_mem hca) (List.mem_map_of_mem hcc) ?_ ?_
      · intro e
        have : ca.1 = cc.1 := congrArg (fun x : X => x.1.1) e
        exact hab (by rw [← hax, ← hcy, this])
      · change hb H (ca.1 + cc.1) = true; rw [hax, hcy]; exact hH) hnode
    exact look_sound hctx fuel _ _ _ _ hf hst k0 (by omega) (hbi.min hl hm.2)

lemma frc_eq (v : List W) : ∀ h, frc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.1 (fun s => st w.2 fun c => frc v fun r => h ((s, c) :: r)) = _
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

lemma addS_cons (o w : W) (t : List W) : addS o (w :: t) = bif Nat.ble w.1 o.1 then (bif Nat.beq o.1 w.1 then w :: t else o :: w :: t) else w :: addS o t := by
  change Bool.rec (motive := fun _ => List W) (w :: addS o t) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.1 w.1)) (Nat.ble w.1 o.1) = _
  cases Nat.ble w.1 o.1 <;> cases Nat.beq o.1 w.1 <;> rfl

def Srt (v : List W) : Prop := v.Pairwise (fun a b => b.1 < a.1)

lemma addS_spec {o : W} {v : List W} (hv : Srt v) : Srt (addS o v) ∧ (∀ w ∈ addS o v, w = o ∨ w ∈ v) ∧
    (∃ w ∈ addS o v, w.1 = o.1) ∧ ∀ w ∈ v, w ∈ addS o v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addS], ⟨o, by simp [addS], rfl⟩, by simp⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2, i3, i4⟩ := ih hp.2
    rw [addS_cons]
    cases h1 : Nat.ble x.1 o.1 with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o.1 x.1 with
      | true => exact ⟨hv, fun w hw => Or.inr hw, ⟨x, by simp, (Nat.eq_of_beq_eq_true h2).symm⟩, fun w hw => hw⟩
      | false =>
        have hne : o.1 ≠ x.1 := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w hw => by simpa using hw, ⟨o, by simp, rfl⟩, fun w hw => by simp at hw ⊢; tauto⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o.1 < x.1 := by
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
    ∀ x ∈ L, x &&& m ≠ 0 → ∃ w ∈ avl P m L, w.1 = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl], by simp⟩
  | cons y L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have e : avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else addS (mkW P (Nat.land y m)) (avl P m L) := by
      change Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> rfl
    have old : ∀ w ∈ avl P m L, ∃ x ∈ y :: L, w = mkW P (x &&& m) := fun w hw => by
      obtain ⟨x, hx, e⟩ := i2 w hw; exact ⟨x, by simp [hx], e⟩
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      refine ⟨i1, old, fun x hx h2 => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd (Nat.eq_of_beq_eq_true h1) h2
      · exact i3 x hx h2
    | false =>
      obtain ⟨j1, j2, j3, j4⟩ := addS_spec (o := mkW P (Nat.land y m)) i1
      refine ⟨j1, fun w hw => ?_, fun x hx h2 => ?_⟩
      · rcases j2 w hw with rfl | h
        · exact ⟨y, by simp, rfl⟩
        · exact old w h
      · simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact j3
        · obtain ⟨w, hw, e⟩ := i3 x hx h2; exact ⟨w, j4 w hw, e⟩

lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg NN (tz Z) i ∧ AA.testBit i = true := by
  have hA : AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, h]
  refine ⟨⟨?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl

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
    have m1 : (mz Z).testBit i = true := by simp [mz, h1]
    have m2 : (mz Z).testBit j = true := by simp [mz, h2]
    rw [Nat.testBit_and, Nat.testBit_and, this, m1, m2]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    have m1 : (mz Z).testBit (NN + i) = true := by
      simp only [mz, no, Nat.testBit_or, Bool.or_eq_true]
      right
      change (lz Z <<< NN).testBit (NN + i) = true
      rw [Nat.testBit_shiftLeft]; simp [h1]
    have m2 : (mz Z).testBit (NN + j) = true := by
      simp only [mz, no, Nat.testBit_or, Bool.or_eq_true]
      right
      change (lz Z <<< NN).testBit (NN + j) = true
      rw [Nat.testBit_shiftLeft]; simp [h2]
    rw [Nat.testBit_and, Nat.testBit_and, this, m1, m2]

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
  refine ⟨?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0); rwa [List.length_map] at this
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)

lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]

def WZ (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL, x = w &&& mz Z}
def Imp (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol (tz Z) q (C (WZ Z))

lemma Im_WZ {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ Z) : Im (mz Z') S ⊆ WZ Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩

lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.2 + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]

lemma pk16 (Z K : ℕ) : pL ((pr Z).map fun e => 16 + (K - e.2)) = pk (PZ Z).length (fun j => 16 + (K - ((pr Z).getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl

def pOk (Z : ℕ) : Bool := !Nat.beq (tz Z) 0 && (pr Z).all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) && !Nat.beq (tz e.1) 0)
noncomputable def okT (Z L : ℕ) : Bool := !chk Z (L - 1) FF
noncomputable def okE (e : ℕ × ℕ) : Bool := pOk e.1 && Nat.ble e.2 15 && ((pr e.1).any (fun x => Nat.ble e.2 x.2) || okT e.1 e.2)

lemma or_all_ones {M : List ℕ} (hM : M.foldr (· ||| ·) 0 = FF) (x : ℕ) : ∃ H ∈ M, hb H x = true := by
  have hx : x % MM < MM := Nat.mod_lt _ (by decide)
  have hbF : (M.foldr (· ||| ·) 0).testBit (x % MM) = true := by
    rw [hM]; change (2 ^ MM - 1).testBit (x % MM) = true
    rw [Nat.testBit_two_pow_sub_one]; simpa using hx
  have key : ∀ {L : List ℕ}, (L.foldr (· ||| ·) 0).testBit (x % MM) = true → ∃ H ∈ L, H.testBit (x % MM) = true := by
    intro L hL
    induction L with
    | nil => simp at hL
    | cons H L ih =>
      simp only [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true] at hL
      rcases hL with h1 | h1
      · exact ⟨H, by simp, h1⟩
      · obtain ⟨H', hmem, hbit⟩ := ih h1
        exact ⟨H', by simp [hmem], hbit⟩
  obtain ⟨H, hmem, hbit⟩ := key hbF
  refine ⟨H, hmem, ?_⟩
  unfold hb
  rw [Nat.beq_eq]
  change (H >>> (x % MM)) &&& 1 = 1
  rw [Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (H >>> (x % MM)) with h0 | h0
  · have ht : (H >>> (x % MM)).testBit 0 = false := by simp [Nat.testBit_zero, h0]
    rw [Nat.testBit_shiftRight, Nat.add_zero, hbit] at ht
    cases ht
  · exact h0

theorem imp_of {Z L : ℕ} (hp : pOk Z = true) (hL : L ≤ 15) (hI : ∀ e ∈ pr Z, Imp e.1 e.2)
    (hb : (∃ e ∈ pr Z, L ≤ e.2) ∨ ∃ M : List ℕ, M.foldr (· ||| ·) 0 = FF ∧ ∀ H ∈ M, chk Z (L - 1) H = false) : Imp Z L := by
  intro q hq hsol
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨hp0, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  classical
  have hex : ∃ q, Sol (tz Z) q (C (WZ Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, S, hS, hl⟩ := (Nat.find_spec hex).live (nb hp0)
  have hCS : C (S : Set ℕ) ⊆ C (WZ Z) := C_mono hS
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl (hS.trans (sub_C _))))
  have hm : Min (tz Z) k S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have h0 : 0 ∉ S := hm.nonzero (nb hp0)
  have hproj : ∀ e ∈ pr Z, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 := by
    intro e he
    obtain ⟨a, b⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b⟩
  have hno : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ WZ Z → ∀ e ∈ pr Z, ∀ q < e.2, ¬ Sol (tz Z &&& mz e.1) q (C (Im (mz e.1) S)) := by
    intro S hSW e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  rcases hb with ⟨e, he, hle⟩ | ⟨M, hMF, hchk⟩
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const (by rw [tz_sub h3.1]; exact h3.2)
    exact hno S hS e he q' (by omega) hs'
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Z) (mz Z) rawL
  set v := (avl (PZ Z) (mz Z) rawL).filter (fun w => decide (w.1 ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Z) (mz Z) rawL) := List.filter_sublist
  have hnd : (v.map Prod.fst).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hS hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Z) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hgood : ∀ w ∈ v, Good (lz Z) w.1 := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good hx Z
  have hPlen : (PZ Z).length = (pr Z).length := by simp [PZ]
  have hPget : ∀ j < (PZ Z).length, (PZ Z).getD j 0 = mz ((pr Z).getD j (0, L - 1)).1 ∧ (pr Z).getD j (0, L - 1) ∈ pr Z := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have hctx : Ctx (PZ Z) (lz Z) (pL ((pr Z).map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3.2
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Z) (tz Z) (L - 1) (fun j => L - 1 - ((pr Z).getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - ((pr Z).getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno S hS _ e2 q (by omega)
  have hle := cnt_le hctx hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Z) (tz Z) (lz Z) (L - 1) (pL ((pr Z).map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : Nat.beq (cov (lz Z) v) (lz Z) = true := cov_ok hctx hrep hl
  have hsz := hm.size
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.succ (L - 1)) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1; omega)
  have all : ∀ H ∈ M, topC (lz Z) (pL ((pr Z).map fun _ => 16)) (L - 1) H (L - 1) (pL ((pr Z).map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro H hHM
    have h2 := hchk H hHM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false h2 v hsub
    simp only [startv, hcov, hble] at h3
    exact child_sound hctx (fun h => rfl) hst hm (by omega) rfl rfl h3
  exact topC_sound hctx all (or_all_ones hMF) hst k (by omega) hm

lemma imp_okE {e : ℕ × ℕ} (h : okE e = true) (hI : ∀ e' ∈ pr e.1, Imp e'.1 e'.2) : Imp e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true'] at h
  refine imp_of h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) fun h => ?_)
  exact ⟨[FF], by decide, fun H hH => by simp only [List.mem_singleton] at hH; subst hH; exact h⟩


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr3 : tab3.all (fun e => (pr e.1).isEmpty) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr2 : tab2.all (fun e => (pr e.1).all (fun x => tab3.contains x)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pr16 : (pr 16).all (fun x => tab2.contains x || tab3.contains x) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c3 : tab3.all okE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c2l : ([(18, 9), (20, 9), (48, 9), (272, 9)] : List (ℕ × ℕ)).all okE = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c17 : okE (17, 11) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p24 : pOk 24 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma m24_ok : M24.foldr (· ||| ·) 0 = FF := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c24_0 : chk 24 10 0x7fbf7ffeffffff7effdfffdfffffffff73fffffdfffffdef = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c24_1 : chk 24 10 0x4080010000008100200020000000008c00000200000210 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p80 : pOk 80 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma m80_ok : M80.foldr (· ||| ·) 0 = FF := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c80_0 : chk 80 10 0x7ebffbffff7fff3ffffffffffcfff5fffffffffff7ffff5f = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c80_1 : chk 80 10 0x1400400008000c00000000003000a0000000000080000a0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p144 : pOk 144 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma m144_ok : M144.foldr (· ||| ·) 0 = FF := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c144_0 : chk 144 10 0x7ffbfffffffffbbffbbffffffffebfbfffffefffffeeffff = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c144_1 : chk 144 10 0x400000000044004400000000140400000100000110000 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma p16 : pOk 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma m16_ok : M16.foldr (· ||| ·) 0 = FF := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c16_0 : chk 16 12 0x7ffffffffffb7fefffffffffffed6edfffffffffffee7fff = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c16_1 : chk 16 12 0x200000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c16_2 : chk 16 12 0x10000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c16_3 : chk 16 12 0x8000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c16_4 : chk 16 12 0x80000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c16_5 : chk 16 12 0x1000000000000000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c16_6 : chk 16 12 0x1000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c16_7 : chk 16 12 0x200000000000000100000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c16_8 : chk 16 12 0x800000000000001000000000000000000000 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c16_9 : chk 16 12 0x4000000000000000000000000000000010000 = false := by decide +kernel

theorem i3 : ∀ e ∈ tab3, Imp e.1 e.2 := fun e he => by
  refine imp_okE (List.all_eq_true.1 c3 e he) fun x hx => ?_
  have := List.all_eq_true.1 pr3 e he
  simp only [List.isEmpty_iff] at this
  rw [this] at hx
  simp at hx

lemma i2_pr {e : ℕ × ℕ} (he : e ∈ tab2) : ∀ x ∈ pr e.1, Imp x.1 x.2 := fun x hx =>
  i3 x (by simpa using List.all_eq_true.1 (List.all_eq_true.1 pr2 e he) x hx)

theorem i24 : Imp 24 11 := by
  refine imp_of p24 (by decide) (i2_pr (e := (24, 11)) (by decide)) (Or.inr ⟨M24, m24_ok, fun H hH => ?_⟩)
  simp only [M24, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl
  · exact c24_0
  · exact c24_1

theorem i80 : Imp 80 11 := by
  refine imp_of p80 (by decide) (i2_pr (e := (80, 11)) (by decide)) (Or.inr ⟨M80, m80_ok, fun H hH => ?_⟩)
  simp only [M80, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl
  · exact c80_0
  · exact c80_1

theorem i144 : Imp 144 11 := by
  refine imp_of p144 (by decide) (i2_pr (e := (144, 11)) (by decide)) (Or.inr ⟨M144, m144_ok, fun H hH => ?_⟩)
  simp only [M144, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl
  · exact c144_0
  · exact c144_1

theorem i2 : ∀ e ∈ tab2, Imp e.1 e.2 := by
  intro e he
  have hpr := i2_pr he
  simp only [tab2, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact imp_okE c17 hpr
  · exact i24
  · exact i80
  · exact i144
  · exact imp_okE (List.all_eq_true.1 c2l (18, 9) (by simp)) hpr
  · exact imp_okE (List.all_eq_true.1 c2l (20, 9) (by simp)) hpr
  · exact imp_okE (List.all_eq_true.1 c2l (48, 9) (by simp)) hpr
  · exact imp_okE (List.all_eq_true.1 c2l (272, 9) (by simp)) hpr

theorem i16 : Imp 16 13 := by
  refine imp_of p16 (by decide) (fun x hx => ?_) (Or.inr ⟨M16, m16_ok, fun H hH => ?_⟩)
  · have := List.all_eq_true.1 pr16 x hx
    rw [Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem] at this
    exact this.elim (i2 x) (i3 x)
  · simp only [M16, List.mem_cons, List.not_mem_nil, or_false] at hH
    rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact c16_0
    · exact c16_1
    · exact c16_2
    · exact c16_3
    · exact c16_4
    · exact c16_5
    · exact c16_6
    · exact c16_7
    · exact c16_8
    · exact c16_9

def edgeF (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def initBool (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 0 || x 1, Bool.false]

lemma wires_getD_lt (gs : List PEqualNP.MetaComplexity.BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_agree_ne4 (gs : List PEqualNP.MetaComplexity.BinaryGate) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
    (∀ i ≠ 4, w1.getD i false = w2.getD i false) →
    (∀ g ∈ gs, g.left ≠ 4 ∧ g.right ≠ 4) →
    ∀ i ≠ 4,
      (gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) w1).getD i false =
      (gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ h _; exact h
  | cons g gs ih =>
    intro w1 w2 hlen h hw i hi
    obtain ⟨hl, hr⟩ := hw g List.mem_cons_self
    have hg : g.op (w1.getD g.left false) (w1.getD g.right false) =
              g.op (w2.getD g.left false) (w2.getD g.right false) := by
      rw [h _ hl, h _ hr]
    refine ih _ _ (by simp [hlen]) (fun j hj => ?_) (fun x hx => hw x (List.mem_cons_of_mem _ hx)) i hi
    simp only [List.getD_eq_getElem?_getD]
    by_cases hlt : j < w1.length
    · rw [List.getElem?_append_left hlt, List.getElem?_append_left (hlen ▸ hlt)]
      exact h j hj
    · have hle : w1.length ≤ j := by omega
      simp only [List.getD_eq_getElem?_getD] at hg
      rw [List.getElem?_append_right hle, List.getElem?_append_right (hlen ▸ hle), hlen, hg]

lemma exists_reads_4 (circ : PEqualNP.MetaComplexity.BinaryCircuit) (p : Bool)
    (hEval : ∀ x : Fin 9 → Bool, (circ.eval (initBool x) != p) = edgeF x) :
    circ.output ≠ 4 ∧ ∃ g ∈ circ.gates, g.left = 4 ∨ g.right = 4 := by
  have hne4 : circ.output ≠ 4 := by
    intro ho
    let z0 : Fin 9 → Bool := fun _ => false
    let z01 : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
    have h0 := hEval z0
    have h01 := hEval z01
    have hw : ∀ x : Fin 9 → Bool, circ.eval (initBool x) = x 4 := by
      intro x
      simp only [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires, ho]
      rw [wires_getD_lt _ _ 4 (by simp [initBool])]
      simp [initBool, List.getD_eq_getElem?_getD]
    rw [hw] at h0 h01
    have f0 : edgeF z0 = false := by decide
    have f01 : edgeF z01 = true := by decide
    have v0 : z0 4 = false := rfl
    have v01 : z01 4 = false := by decide
    rw [v0, f0] at h0
    rw [v01, f01] at h01
    cases p <;> simp at h0 h01
  refine ⟨hne4, ?_⟩
  by_contra hno
  push Not at hno
  let xA : Fin 9 → Bool := fun i => decide (i = 0)
  let xB : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 4)
  have hA := hEval xA
  have hB := hEval xB
  have fA : edgeF xA = false := by decide
  have fB : edgeF xB = true := by decide
  have heq : circ.eval (initBool xA) = circ.eval (initBool xB) := by
    refine wires_agree_ne4 circ.gates (initBool xA) (initBool xB) (by simp [initBool]) (fun i hi => ?_) hno circ.output hne4
    have hi0 : (xA 0 || xA 1) = (xB 0 || xB 1) := by decide
    simp only [initBool, List.getD_eq_getElem?_getD]
    by_cases h9 : i < 9
    · rw [List.getElem?_append_left (by simp [h9]), List.getElem?_append_left (by simp [h9])]
      simp only [List.getElem?_ofFn, h9, dite_eq_left, Option.getD_some, xA, xB]
      have hne4' : (⟨i, h9⟩ : Fin 9) ≠ 4 := fun h4 => hi (congrArg Fin.val h4)
      simp [hne4']
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp [hi0]
  rw [heq, fA] at hA
  rw [fB] at hB
  rw [hA] at hB
  cases hB

abbrev Wire := Bool × ℕ

def read (b : ℕ) (w : Wire) : Bool := w.1 != w.2.testBit b

def signedGate (a b : Bool) (u v : Wire) : Wire :=
  bif (u.1 == a) then (bif (v.1 == b) then (true, op 1 u.2 v.2) else (false, op 3 u.2 v.2))
  else (bif (v.1 == b) then (false, op 2 u.2 v.2) else (false, op 0 u.2 v.2))

def gateStep (w : List Wire) (g : PEqualNP.MetaComplexity.BinaryGate) : Wire :=
  signedGate (g.op true true || g.op true false) (g.op true true || g.op false true)
    (w.getD g.left (false, 0)) (w.getD g.right (false, 0))

def exec (gs : List PEqualNP.MetaComplexity.BinaryGate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w ++ [gateStep w g]) w

lemma read_signedGate (k : ℕ) (a b : Bool) (u v : Wire) :
    read k (signedGate a b u v) = ((read k u == a) && (read k v == b)) := by
  rcases u with ⟨u1, u2⟩; rcases v with ⟨v1, v2⟩
  cases a <;> cases b <;> cases u1 <;> cases v1 <;>
    simp [read, signedGate, op, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases u2.testBit k <;> cases v2.testBit k <;> simp

lemma signedGate_op (a b : Bool) (u v : Wire) : ∃ d < 4, (signedGate a b u v).2 = op d u.2 v.2 := by
  cases h1 : (u.1 == a) <;> cases h2 : (v.1 == b) <;> simp only [signedGate, h1, h2, Bool.cond_true, Bool.cond_false]
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨3, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩

lemma signedGate_zero_left {a b : Bool} {u v : Wire} (hu : u.2 = 0) :
    (signedGate a b u v).2 = 0 ∨ (signedGate a b u v).2 = v.2 := by
  obtain ⟨d, _, hd⟩ := signedGate_op a b u v
  rw [hd, hu]; exact op_zero_left d v.2

lemma signedGate_zero_right {a b : Bool} {u v : Wire} (hv : v.2 = 0) :
    (signedGate a b u v).2 = 0 ∨ (signedGate a b u v).2 = u.2 := by
  obtain ⟨d, _, hd⟩ := signedGate_op a b u v
  rw [hd, hv]; exact op_zero_right d u.2

lemma signedGate_params (g : PEqualNP.MetaComplexity.BinaryGate)
    (hg : ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) :
    g.op = fun x y => (x == (g.op true true || g.op true false)) && (y == (g.op true true || g.op false true)) := by
  obtain ⟨a, b, hop⟩ := hg
  rw [hop]
  cases a <;> cases b <;> rfl

lemma getD_map_read (w : List Wire) (b i : ℕ) : (w.map (read b)).getD i false = read b (w.getD i (false, 0)) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [read]

lemma exec_read (b : ℕ) (gs : List PEqualNP.MetaComplexity.BinaryGate) : ∀ (w : List Wire),
    (∀ g ∈ gs, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
    (exec gs w).map (read b) =
      gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) (w.map (read b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    have hg0 := signedGate_params g (hg g List.mem_cons_self)
    rw [exec, List.foldl_cons, List.foldl_cons]
    have hstep : read b (gateStep w g) = g.op ((w.map (read b)).getD g.left false) ((w.map (read b)).getD g.right false) := by
      rw [gateStep, read_signedGate, getD_map_read, getD_map_read]
      conv_rhs => rw [hg0]
    have := ih (w ++ [gateStep w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append, List.map_singleton, hstep] at this
    exact this

lemma exec_inv (m : ℕ) (gs : List PEqualNP.MetaComplexity.BinaryGate) : ∀ (w : List Wire),
    (∀ x ∈ w, x.2 &&& m = x.2 ∧ x.2.testBit 0 = false) →
    ∀ x ∈ exec gs w, x.2 &&& m = x.2 ∧ x.2.testBit 0 = false := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih _ fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · have rd : ∀ i, (w.getD i (false, 0)).2 &&& m = (w.getD i (false, 0)).2 ∧ (w.getD i (false, 0)).2.testBit 0 = false := by
        intro i
        rw [List.getD_eq_getElem?_getD]
        by_cases hi : i < w.length
        · rw [List.getElem?_eq_getElem hi]; exact hw _ (List.getElem_mem hi)
        · rw [List.getElem?_eq_none (by omega)]; simp
      obtain ⟨d, _, hd⟩ := signedGate_op (g.op true true || g.op true false) (g.op true true || g.op false true)
        (w.getD g.left (false, 0)) (w.getD g.right (false, 0))
      change (gateStep w g).2 &&& m = (gateStep w g).2 ∧ (gateStep w g).2.testBit 0 = false
      unfold gateStep; rw [hd, and_op, (rd g.left).1, (rd g.right).1]
      refine ⟨rfl, ?_⟩
      rw [op_bit, (rd g.left).2, (rd g.right).2]
      rcases d with _ | _ | _ | d <;> rfl

lemma exec_sol (gs : List PEqualNP.MetaComplexity.BinaryGate) : ∀ (w : List Wire) (S : Set ℕ) (out : ℕ),
    4 < w.length → (w.getD 4 (false, 0)).2 = 0 →
    (∀ x ∈ w, x.2 ∈ S) → 0 ∈ S →
    Sol ((exec gs w).getD out (false, 0)).2 (gs.countP (fun g => g.left != 4 && g.right != 4)) S := by
  induction gs with
  | nil =>
    intro w S out _ _ hw h0
    change Sol (w.getD out (false, 0)).2 0 S
    rw [List.getD_eq_getElem?_getD]
    by_cases hi : out < w.length
    · rw [List.getElem?_eq_getElem hi]; exact hw _ (List.getElem_mem hi)
    · rw [List.getElem?_eq_none (by omega)]; exact h0
  | cons g gs ih =>
    intro w S out hlen hw4 hw h0
    have hl4 : ((w ++ [gateStep w g]).getD 4 (false, 0)).2 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
      simpa [List.getD_eq_getElem?_getD] using hw4
    have rd : ∀ i, (w.getD i (false, 0)).2 ∈ S := fun i => by
      rw [List.getD_eq_getElem?_getD]
      by_cases hi : i < w.length
      · rw [List.getElem?_eq_getElem hi]; exact hw _ (List.getElem_mem hi)
      · rw [List.getElem?_eq_none (by omega)]; exact h0
    by_cases h4 : g.left = 4 ∨ g.right = 4
    · have hkeep : (gateStep w g).2 ∈ S := by
        unfold gateStep
        rcases h4 with h4 | h4
        · have hz : (w.getD g.left (false, 0)).2 = 0 := h4 ▸ hw4
          rcases signedGate_zero_left hz with e | e <;> rw [e]
          · exact h0
          · exact rd g.right
        · have hz : (w.getD g.right (false, 0)).2 = 0 := h4 ▸ hw4
          rcases signedGate_zero_right hz with e | e <;> rw [e]
          · exact h0
          · exact rd g.left
      have hcnt : (g :: gs).countP (fun g => g.left != 4 && g.right != 4) =
                  gs.countP (fun g => g.left != 4 && g.right != 4) := by
        rw [List.countP_cons]
        rcases h4 with h4 | h4 <;> simp [h4]
      rw [hcnt]
      exact ih (w ++ [gateStep w g]) S out (by simp; omega) hl4 (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact hkeep) h0
    · push Not at h4
      have hcnt : (g :: gs).countP (fun g => g.left != 4 && g.right != 4) =
                  gs.countP (fun g => g.left != 4 && g.right != 4) + 1 := by
        rw [List.countP_cons]; simp [h4.1, h4.2]
      rw [hcnt]
      obtain ⟨d, hd, hdg⟩ := signedGate_op (g.op true true || g.op true false) (g.op true true || g.op false true)
        (w.getD g.left (false, 0)) (w.getD g.right (false, 0))
      refine Or.inr ⟨d, hd, (w.getD g.left (false, 0)).2, rd g.left, (w.getD g.right (false, 0)).2, rd g.right, ?_⟩
      change Sol ((exec gs (w ++ [gateStep w g])).getD out (false, 0)).2 _ (insert (op d _ _) S)
      rw [← show (gateStep w g).2 = op d (w.getD g.left (false, 0)).2 (w.getD g.right (false, 0)).2 from hdg]
      exact ih (w ++ [gateStep w g]) _ out (by simp; omega) hl4 (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0)

def EF : ℕ := (([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (ℕ × ℕ)).map
  (fun e => rawP.getD e.1 0 &&& rawP.getD e.2 0)).foldr (· ||| ·) 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 16 = tz 16 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mz16_bit0 : (mz 16).testBit 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rawL_bit0 : rawL.all (fun w => !w.testBit 0) = true := by decide +kernel


lemma rawP_len : rawP.length = 9 := rfl

lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 9 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl

def initWires : List Wire :=
  (rawP.map (fun x => (false, x &&& mz 16))) ++ [(false, (rawP.getD 0 0 ||| rawP.getD 1 0) &&& mz 16), (false, 0)]

theorem final : ∀ (circ : PEqualNP.MetaComplexity.BinaryCircuit) (p : Bool),
    (∀ g ∈ circ.gates, ∃ (a b : Bool), g.op = fun x y => x == a && y == b) →
    (∀ x : Fin 9 → Bool, (circ.eval (initBool x) != p) = edgeF x) →
    14 ≤ circ.size := by
  intro circ p hgates hEval
  by_contra hsz
  have hlen : circ.gates.length ≤ 13 := by
    change ¬ 14 ≤ circ.gates.length at hsz; omega
  obtain ⟨_, g4, hg4, hg4r⟩ := exists_reads_4 circ p hEval
  have hcnt_lt : circ.gates.countP (fun g => g.left != 4 && g.right != 4) < circ.gates.length := by
    have hle := List.countP_le_length (p := fun g : PEqualNP.MetaComplexity.BinaryGate => g.left != 4 && g.right != 4) (l := circ.gates)
    by_contra hge
    have heq : circ.gates.countP (fun g => g.left != 4 && g.right != 4) = circ.gates.length := by omega
    have hall := List.countP_eq_length.1 heq g4 hg4
    rcases hg4r with h | h <;> simp [h] at hall
  have hcnt12 : circ.gates.countP (fun g => g.left != 4 && g.right != 4) ≤ 12 := by omega
  let row : ℕ → Fin 9 → Bool := fun b v => (rawP.getD v.val 0).testBit b
  have hrow : ∀ b, List.ofFn (row b) = rawP.map (fun x => x.testBit b) := row_list
  have hinv_init : ∀ x ∈ initWires, x.2 &&& mz 16 = x.2 ∧ x.2.testBit 0 = false := by
    intro x hx
    simp only [initWires, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ⟨y, hy, rfl⟩ | rfl | rfl
    · have hb0 : y.testBit 0 = false := by
        have := List.all_eq_true.1 rawL_bit0 y (List.mem_append_left _ hy)
        simpa using this
      exact ⟨by rw [Nat.and_assoc, Nat.and_self], by simp only [Nat.testBit_and, hb0, Bool.false_and]⟩
    · have hy : rawP.getD 0 0 ||| rawP.getD 1 0 ∈ rawL := List.mem_append_right _ (by simp)
      have hb0 : (rawP.getD 0 0 ||| rawP.getD 1 0).testBit 0 = false := by
        have := List.all_eq_true.1 rawL_bit0 _ hy
        simpa using this
      exact ⟨by rw [Nat.and_assoc, Nat.and_self], by simp only [Nat.testBit_and, hb0, Bool.false_and]⟩
    · simp
  have hinv_out := exec_inv (mz 16) circ.gates initWires hinv_init
  let outW : Wire := (exec circ.gates initWires).getD circ.output (false, 0)
  have hout_inv : outW.2 &&& mz 16 = outW.2 ∧ outW.2.testBit 0 = false := by
    dsimp [outW]
    rw [List.getD_eq_getElem?_getD]
    by_cases hi : circ.output < (exec circ.gates initWires).length
    · rw [List.getElem?_eq_getElem hi]; exact hinv_out _ (List.getElem_mem hi)
    · rw [List.getElem?_eq_none (by omega)]; simp
  have hinit_map : ∀ b, (mz 16).testBit b = true → initWires.map (read b) = initBool (row b) := by
    intro b hb
    simp only [initWires, initBool, hrow b, List.map_append, List.map_map, List.map_cons, List.map_nil]
    congr 1
    · apply List.map_congr_left
      intro x _
      simp [Function.comp, read, Nat.testBit_and, hb]
    · simp only [read, Nat.testBit_and, hb, Bool.and_true, Bool.false_bne, Nat.testBit_or, Nat.zero_testBit]
      have h0 : row b 0 = (rawP.getD 0 0).testBit b := rfl
      have h1 : row b 1 = (rawP.getD 1 0).testBit b := rfl
      rw [h0, h1]
  have heval_b : ∀ b, (mz 16).testBit b = true → read b outW = circ.eval (initBool (row b)) := by
    intro b hb
    dsimp [outW]
    rw [← getD_map_read, exec_read b circ.gates initWires hgates, hinit_map b hb]
    rfl
  have hp_eq : outW.1 = p := by
    have h0 := hEval (row 0)
    rw [← heval_b 0 mz16_bit0] at h0
    have hr0 : read 0 outW = outW.1 := by
      simp [read, hout_inv.2]
    have hf0 : edgeF (row 0) = false := by
      have hb0 : ∀ i : Fin 9, row 0 i = false := by
        intro i
        have hi : rawP.getD i.val 0 ∈ rawL := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [rawP_len]; exact i.isLt)]
          exact List.mem_append_left _ (List.getElem_mem _)
        have := List.all_eq_true.1 rawL_bit0 _ hi
        simpa [row] using this
      simp [edgeF, hb0]
    rw [hr0, hf0] at h0
    cases h1 : outW.1 <;> cases h2 : p <;> simp [h1, h2] at h0 ⊢
  have hout2 : outW.2 = tz 16 := by
    apply Nat.eq_of_testBit_eq
    intro b
    cases hb : (mz 16).testBit b with
    | false =>
      have e1 := congrArg (fun x => x.testBit b) hout_inv.1
      have e2 : (tz 16).testBit b = false := by simp [tz, Nat.testBit_and, hb]
      simp only [Nat.testBit_and, hb, Bool.and_false] at e1
      rw [← e1, e2]
    | true =>
      have h := hEval (row b)
      rw [← heval_b b hb] at h
      have hl : (read b outW != p) = outW.2.testBit b := by
        simp only [read, hp_eq]
        cases p <;> cases outW.2.testBit b <;> rfl
      have hr : edgeF (row b) = (tz 16).testBit b := by
        rw [← EF_ok, Nat.testBit_and, hb, Bool.and_true]
        simp only [EF, edgeF, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          Nat.testBit_or, Nat.testBit_and, Nat.zero_testBit, Bool.or_false]
        simp only [Bool.or_assoc]; rfl
      rw [← hl, ← hr, h]
  have hmem : ∀ x ∈ initWires, x.2 ∈ C (WZ 16) := by
    intro x hx
    simp only [initWires, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ⟨y, hy, rfl⟩ | rfl | rfl
    · exact Or.inr ⟨y, List.mem_append_left _ hy, rfl⟩
    · exact Or.inr ⟨rawP.getD 0 0 ||| rawP.getD 1 0, List.mem_append_right _ (by simp), rfl⟩
    · exact Or.inl rfl
  have hw4 : (initWires.getD 4 (false, 0)).2 = 0 := by
    have : (initWires.getD 4 (false, 0)).2 = 0 &&& mz 16 := rfl
    rw [this, Nat.zero_and]
  have hsol := exec_sol circ.gates initWires (C (WZ 16)) circ.output (by simp [initWires, rawP_len]) hw4 hmem (Or.inl rfl)
  rw [show ((exec circ.gates initWires).getD circ.output (false, 0)).2 = tz 16 from hout2] at hsol
  exact i16 _ (by omega) hsol

end PEqualNP.Outside.L_meta_2828

theorem PEqualNP.Outside.L_meta_2828 : ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size :=
  PEqualNP.Outside.L_meta_2828.final

import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Range

namespace PEqualNP.Outside.L_meta_4970_aux

lemma pointCentre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hno : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (Q : Finset (Fin l)) (hQ : 2 ≤ Q.card) {a a' : Fin p}
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  by_contra hne
  obtain ⟨b, hb, b', hb', hbb'⟩ :=
    Finset.one_lt_card.mp (lt_of_lt_of_le (by decide : 1 < 2) hQ)
  exact hno a a' b b' hne hbb' ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩

lemma lineCentre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hno : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (P : Finset (Fin p)) (hP : 2 ≤ P.card) {b b' : Fin l}
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P, (a, b') ∈ E) : b = b' := by
  by_contra hne
  obtain ⟨a, ha, a', ha', haa'⟩ :=
    Finset.one_lt_card.mp (lt_of_lt_of_le (by decide : 1 < 2) hP)
  exact hno a a' b b' haa' hne ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩

lemma orSupport_unique {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (S T : Finset α)
    (h : ∀ x : β → Bool,
      decide (∃ a ∈ S, x (f a) = true) = decide (∃ a ∈ T, x (f a) = true)) : S = T := by
  ext a
  have ht := h (fun b => decide (b = f a))
  have hS : (∃ a' ∈ S, decide (f a' = f a) = true) ↔ a ∈ S := by
    simp [hf.eq_iff]
  have hT : (∃ a' ∈ T, decide (f a' = f a) = true) ↔ a ∈ T := by
    simp [hf.eq_iff]
  have hd : decide (a ∈ S) = decide (a ∈ T) := by
    simpa only [hS, hT] using ht
  have hd' : (decide (a ∈ S) = true) ↔ (decide (a ∈ T) = true) := by rw [hd]
  simpa only [decide_eq_true_eq] using hd'

lemma lineOrSupport_unique {p l : ℕ} (Q Q' : Finset (Fin l))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
      decide (∃ b ∈ Q', x (Fin.natAdd p b) = true)) : Q = Q' := by
  have hi : Function.Injective (Fin.natAdd p : Fin l → Fin (p + l)) := by
    intro a b hab
    apply Fin.ext
    have hval := congrArg (fun z : Fin (p + l) => z.val) hab
    exact Nat.add_left_cancel hval
  apply orSupport_unique (Fin.natAdd p) hi Q Q'
  intro x
  simpa only [decide_eq_decide] using h x

lemma pointOrSupport_unique {p l : ℕ} (P P' : Finset (Fin p))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
      decide (∃ a ∈ P', x (Fin.castAdd l a) = true)) : P = P' := by
  have hi : Function.Injective (Fin.castAdd l : Fin p → Fin (p + l)) := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun z : Fin (p + l) => z.val) hab
  apply orSupport_unique (Fin.castAdd l) hi P P'
  intro x
  simpa only [decide_eq_decide] using h x

lemma pointLineOr_distinct {p l : ℕ} (P : Finset (Fin p))
    (Q : Finset (Fin l)) (hQ : Q.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) := by
  obtain ⟨b, hb⟩ := hQ
  have hne (a : Fin p) : Fin.castAdd l a ≠ Fin.natAdd p b := by
    intro h
    have hv : (a : ℕ) = p + (b : ℕ) := congrArg Fin.val h
    have hpa : p ≤ (a : ℕ) := by
      rw [hv]
      exact Nat.le_add_right p b
    exact Nat.not_le_of_lt a.isLt hpa
  intro h
  have ht := h (fun k => decide (k = Fin.natAdd p b))
  have hP : decide (∃ a ∈ P, decide (Fin.castAdd l a = Fin.natAdd p b) = true) =
      false := by simp [hne]
  have hQ' : decide (∃ b' ∈ Q, decide (Fin.natAdd p b' = Fin.natAdd p b) = true) =
      true := by
    simp only [decide_eq_true_eq]
    exact ⟨b, hb, rfl⟩
  rw [hP, hQ'] at ht
  cases ht

def MonotoneBool {α : Type*} (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def BelowOr {α : Type*} (Q : Finset α) (f : (α → Bool) → Bool) : Prop :=
  ∀ x, f x = true → ∃ i ∈ Q, x i = true

def outsideInput {α : Type*} [DecidableEq α] (Q : Finset α) : α → Bool :=
  fun i => decide (i ∉ Q)

lemma belowOr_iff_outside_false {α : Type*} [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool) (hm : MonotoneBool f) :
    BelowOr Q f ↔ f (outsideInput Q) = false := by
  constructor
  · intro h
    cases hf : f (outsideInput Q) with
    | false => rfl
    | true =>
      obtain ⟨i, hi, hx⟩ := h _ hf
      simp [outsideInput, hi] at hx
  · intro h x hx
    by_contra hn
    have hle : ∀ i, x i = true → outsideInput Q i = true := by
      intro i hi
      have hni : i ∉ Q := fun hmem => hn ⟨i, hmem, hi⟩
      simp [outsideInput, hni]
    have := hm x (outsideInput Q) hle hx
    simp [h] at this

lemma belowOr_and {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : MonotoneBool f) (hg : MonotoneBool g)
    (h : BelowOr Q (fun x => f x && g x)) : BelowOr Q f ∨ BelowOr Q g := by
  have hm : MonotoneBool (fun x => f x && g x) := by
    intro x y hxy hx
    simp only [Bool.and_eq_true] at hx ⊢
    exact ⟨hf x y hxy hx.1, hg x y hxy hx.2⟩
  have hz := (belowOr_iff_outside_false Q _ hm).mp h
  rw [belowOr_iff_outside_false Q f hf, belowOr_iff_outside_false Q g hg]
  cases hfv : f (outsideInput Q) <;> cases hgv : g (outsideInput Q) <;>
    simp_all

lemma belowOr_or {α : Type*} (Q : Finset α) (f g : (α → Bool) → Bool)
    (h : BelowOr Q (fun x => f x || g x)) : BelowOr Q f ∧ BelowOr Q g := by
  constructor
  · intro x hx
    exact h x (by simp [hx])
  · intro x hx
    exact h x (by simp [hx])

lemma and_eq_or_imp_operand_eq {α : Type*} [Fintype α] [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : MonotoneBool f) (hg : MonotoneBool g)
    (h : ∀ x, (f x && g x) = decide (∃ i ∈ Q, x i = true)) :
    (∀ x, f x = decide (∃ i ∈ Q, x i = true)) ∨
    (∀ x, g x = decide (∃ i ∈ Q, x i = true)) := by
  have hb : BelowOr Q (fun x => f x && g x) := by
    intro x hx
    change (f x && g x) = true at hx
    rw [h x] at hx
    exact of_decide_eq_true hx
  rcases belowOr_and Q f g hf hg hb with hb | hb
  · left
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      exact decide_eq_true (hb x hx)
    · intro hx
      have hp : (f x && g x) = true := (h x).trans hx
      simp only [Bool.and_eq_true] at hp
      exact hp.1
  · right
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      exact decide_eq_true (hb x hx)
    · intro hx
      have hp : (f x && g x) = true := (h x).trans hx
      simp only [Bool.and_eq_true] at hp
      exact hp.2

open Classical

lemma leaf_count_bypass {α : Type*} [DecidableEq α]
    (cls branch : ℕ → Prop) (T : ℕ → Finset α)
    (h : ∀ w, cls w → (T w).card ≤ 1 ∨
      (branch w ∧ ∃ a b, a < w ∧ b < w ∧ cls a ∧ cls b ∧ T w = T a ∪ T b) ∨
      ∃ a, a < w ∧ cls a ∧ T w ⊆ T a) :
    ∀ M (W : Finset ℕ), (∀ w ∈ W, w < M ∧ cls w) →
      (W.biUnion T).card ≤ W.card +
        ((Finset.range M).filter (fun k => cls k ∧ branch k ∧ 2 ≤ (T k).card)).card := by
  intro M
  induction M with
  | zero =>
    intro W hW
    have : W = ∅ := by
      ext w
      simp only [Finset.notMem_empty, iff_false]
      intro hw
      exact absurd (hW w hw).1 (by omega)
    subst this
    simp
  | succ M ih =>
    intro W hW
    have hmono :
        ((Finset.range M).filter (fun k => cls k ∧ branch k ∧ 2 ≤ (T k).card)).card ≤
        ((Finset.range (M + 1)).filter (fun k => cls k ∧ branch k ∧ 2 ≤ (T k).card)).card := by
      apply Finset.card_le_card
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by omega, hk.2⟩
    by_cases hM : M ∈ W
    · have hWe : W = insert M (W.erase M) := (Finset.insert_erase hM).symm
      have hW' : ∀ w ∈ W.erase M, w < M ∧ cls w := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have := hW w hw.2
        exact ⟨by omega, this.2⟩
      have hcard : W.card = (W.erase M).card + 1 := by
        rw [Finset.card_erase_of_mem hM]
        have := Finset.card_pos.mpr ⟨M, hM⟩
        omega
      have hU : W.biUnion T = T M ∪ (W.erase M).biUnion T := by
        conv_lhs => rw [hWe]
        rw [Finset.biUnion_insert]
      by_cases h1 : (T M).card ≤ 1
      · have ih1 := ih (W.erase M) hW'
        have hu := Finset.card_union_le (T M) ((W.erase M).biUnion T)
        rw [hU]
        omega
      · rcases h M (hW M hM).2 with h2 | ⟨hbranch, a, b, ha, hb, ca, cb, hT⟩ |
            ⟨a, ha, ca, hT⟩
        · exact absurd h2 h1
        · let W2 := insert a (insert b (W.erase M))
          have hW2 : ∀ w ∈ W2, w < M ∧ cls w := by
            intro w hw
            simp only [W2, Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hw
            · exact ⟨ha, ca⟩
            · exact ⟨hb, cb⟩
            · exact hW' w hw
          have hU2 : W2.biUnion T = W.biUnion T := by
            rw [show W2 = insert a (insert b (W.erase M)) from rfl,
              Finset.biUnion_insert, Finset.biUnion_insert, hU, hT, Finset.union_assoc]
          have hc2 : W2.card ≤ (W.erase M).card + 2 := by
            have e1 := Finset.card_insert_le a (insert b (W.erase M))
            have e2 := Finset.card_insert_le b (W.erase M)
            dsimp only [W2]
            omega
          have ih2 := ih W2 hW2
          rw [hU2] at ih2
          have hsplit : (Finset.range (M + 1)).filter
              (fun k => cls k ∧ branch k ∧ 2 ≤ (T k).card) =
              insert M ((Finset.range M).filter
                (fun k => cls k ∧ branch k ∧ 2 ≤ (T k).card)) := by
            rw [Finset.range_add_one, Finset.filter_insert, ite_eq_left]
            exact ⟨(hW M hM).2, hbranch, by omega⟩
          rw [hsplit, Finset.card_insert_of_notMem (by simp)]
          omega
        · let W1 := insert a (W.erase M)
          have hW1 : ∀ w ∈ W1, w < M ∧ cls w := by
            intro w hw
            simp only [W1, Finset.mem_insert] at hw
            rcases hw with rfl | hw
            · exact ⟨ha, ca⟩
            · exact hW' w hw
          have hU1 : W.biUnion T ⊆ W1.biUnion T := by
            rw [hU, show W1 = insert a (W.erase M) from rfl, Finset.biUnion_insert]
            exact Finset.union_subset_union hT (by intro x hx; exact hx)
          have hc1 : W1.card ≤ W.card := by
            have := Finset.card_insert_le a (W.erase M)
            dsimp only [W1]
            omega
          have ih1 := ih W1 hW1
          have huc := Finset.card_le_card hU1
          omega
    · have hW' : ∀ w ∈ W, w < M ∧ cls w := by
        intro w hw
        have := hW w hw
        have hne : w ≠ M := fun he => hM (he ▸ hw)
        exact ⟨by omega, this.2⟩
      have := ih W hW'
      omega

lemma belowOr_finset_conj_factor {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (Q : Finset α) (I : Finset ι) (f : ι → (α → Bool) → Bool)
    (hm : ∀ i ∈ I, MonotoneBool (f i))
    (hb : BelowOr Q (fun x => decide (∀ i ∈ I, f i x = true))) :
    ∃ i ∈ I, BelowOr Q (f i) := by
  by_contra hn
  have hall : ∀ i ∈ I, f i (outsideInput Q) = true := by
    intro i hi
    cases hfi : f i (outsideInput Q) with
    | false =>
      exact False.elim (hn ⟨i, hi, (belowOr_iff_outside_false Q (f i) (hm i hi)).mpr hfi⟩)
    | true => rfl
  obtain ⟨a, ha, hax⟩ := hb (outsideInput Q) (decide_eq_true hall)
  simp [outsideInput, ha] at hax

lemma or_finset_conj_eq_or_factors {α ι κ : Type*}
    [DecidableEq α] [DecidableEq ι] [DecidableEq κ]
    (Q : Finset α) (I : Finset ι) (J : Finset κ)
    (f : ι → (α → Bool) → Bool) (g : κ → (α → Bool) → Bool)
    (hf : ∀ i ∈ I, MonotoneBool (f i)) (hg : ∀ j ∈ J, MonotoneBool (g j))
    (h : ∀ x,
      (decide (∀ i ∈ I, f i x = true) || decide (∀ j ∈ J, g j x = true)) =
        decide (∃ a ∈ Q, x a = true)) :
    ∃ i ∈ I, ∃ j ∈ J, BelowOr Q (f i) ∧ BelowOr Q (g j) ∧
      ∀ x, (f i x || g j x) = decide (∃ a ∈ Q, x a = true) := by
  have hb : BelowOr Q (fun x =>
      decide (∀ i ∈ I, f i x = true) || decide (∀ j ∈ J, g j x = true)) := by
    intro x hx
    change (decide (∀ i ∈ I, f i x = true) || decide (∀ j ∈ J, g j x = true)) = true at hx
    rw [h x] at hx
    exact of_decide_eq_true hx
  obtain ⟨hI, hJ⟩ := belowOr_or Q _ _ hb
  obtain ⟨i, hi, hfi⟩ := belowOr_finset_conj_factor Q I f hf hI
  obtain ⟨j, hj, hgj⟩ := belowOr_finset_conj_factor Q J g hg hJ
  refine ⟨i, hi, j, hj, hfi, hgj, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    simp only [Bool.or_eq_true] at hx
    rcases hx with hfx | hgx
    · exact decide_eq_true (hfi x hfx)
    · exact decide_eq_true (hgj x hgx)
  · intro hx
    have hc : (decide (∀ i ∈ I, f i x = true) || decide (∀ j ∈ J, g j x = true)) = true :=
      (h x).trans hx
    simp only [Bool.or_eq_true] at hc ⊢
    rcases hc with hfx | hgx
    · exact Or.inl ((of_decide_eq_true hfx) i hi)
    · exact Or.inr ((of_decide_eq_true hgx) j hj)


def unitInput {α : Type*} [DecidableEq α] (u : α) : α → Bool :=
  fun i => decide (i = u)

def pairInput {α : Type*} [DecidableEq α] (u v : α) : α → Bool :=
  fun i => decide (i = u ∨ i = v)

lemma unitInput_le_pairInput_left {α : Type*} [DecidableEq α] (u v : α) :
    ∀ i, unitInput u i = true → pairInput u v i = true := by
  intro i hi
  simp only [unitInput, decide_eq_true_eq] at hi
  simp only [pairInput, decide_eq_true_eq]
  exact Or.inl hi

lemma unitInput_le_pairInput_right {α : Type*} [DecidableEq α] (u v : α) :
    ∀ i, unitInput v i = true → pairInput u v i = true := by
  intro i hi
  simp only [unitInput, decide_eq_true_eq] at hi
  simp only [pairInput, decide_eq_true_eq]
  exact Or.inr hi

lemma pairContext_singleton_centre {α : Type*} [DecidableEq α]
    (Adj : α → α → Prop)
    (hno : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (Adj a b ∧ Adj a b' ∧ Adj a' b ∧ Adj a' b'))
    (g h : (α → Bool) → Bool) (hgm : MonotoneBool g) (hhm : MonotoneBool h)
    (hPair : ∀ u v, (g (pairInput u v) && h (pairInput u v)) = true → Adj u v)
    {c q1 q2 : α} (hq : q1 ≠ q2) (hc1 : Adj c q1) (hc2 : Adj c q2)
    (hg1 : g (unitInput q1) = true) (hg2 : g (unitInput q2) = true) :
    ∀ v, h (unitInput v) = true → v = c := by
  intro v hv
  have hvq (q : α) (hgq : g (unitInput q) = true) : Adj v q := by
    apply hPair v q
    simp only [Bool.and_eq_true]
    exact ⟨hgm _ _ (unitInput_le_pairInput_right v q) hgq,
      hhm _ _ (unitInput_le_pairInput_left v q) hv⟩
  by_contra hvc
  exact hno c v q1 q2 (Ne.symm hvc) hq ⟨hc1, hc2, hvq q1 hg1, hvq q2 hg2⟩

def PairMinterm {α : Type*} [DecidableEq α]
    (f : (α → Bool) → Bool) (u v : α) : Prop :=
  f (pairInput u v) = true ∧ f (unitInput u) = false ∧ f (unitInput v) = false

lemma pairContext_inherited_off_centre {α : Type*} [DecidableEq α]
    (g h : (α → Bool) → Bool) (c : α)
    (hc : ∀ v, h (unitInput v) = true → v = c)
    {u v : α} (hu : u ≠ c) (hv : v ≠ c)
    (hp : (g (pairInput u v) && h (pairInput u v)) = true) :
    PairMinterm h u v := by
  have hp' : g (pairInput u v) = true ∧ h (pairInput u v) = true := by
    simpa only [Bool.and_eq_true] using hp
  refine ⟨hp'.2, ?_, ?_⟩
  · cases he : h (unitInput u) with
    | false => rfl
    | true => exact False.elim (hu (hc u he))
  · cases he : h (unitInput v) with
    | false => rfl
    | true => exact False.elim (hv (hc v he))

lemma pairContext_inherited_at_centre {α : Type*} [DecidableEq α]
    (g h : (α → Bool) → Bool) {c b : α}
    (hc : g (unitInput c) = false) (hb : g (unitInput b) = false)
    (hp : (g (pairInput c b) && h (pairInput c b)) = true) :
    PairMinterm g c b := by
  have hp' : g (pairInput c b) = true ∧ h (pairInput c b) = true := by
    simpa only [Bool.and_eq_true] using hp
  exact ⟨hp'.1, hc, hb⟩

lemma pairContext_minterm_or_star {α : Type*} [DecidableEq α]
    (g h : (α → Bool) → Bool) (c : α)
    (hc : ∀ v, h (unitInput v) = true → v = c)
    (hgc : g (unitInput c) = false)
    {u v : α} (hp : (g (pairInput u v) && h (pairInput u v)) = true) :
    PairMinterm h u v ∨ PairMinterm g u v ∨
      (u = c ∧ g (unitInput v) = true ∧ h (unitInput u) = true) ∨
      (v = c ∧ g (unitInput u) = true ∧ h (unitInput v) = true) := by
  have hp' : g (pairInput u v) = true ∧ h (pairInput u v) = true := by
    simpa only [Bool.and_eq_true] using hp
  obtain ⟨hgp, hhp⟩ := hp'
  cases hhu : h (unitInput u) with
  | false =>
    cases hhv : h (unitInput v) with
    | false => exact Or.inl ⟨hhp, hhu, hhv⟩
    | true =>
      have hvc := hc v hhv
      cases hgu : g (unitInput u) with
      | false =>
        exact Or.inr (Or.inl ⟨hgp, hgu, hvc.symm ▸ hgc⟩)
      | true => exact Or.inr (Or.inr (Or.inr ⟨hvc, rfl, rfl⟩))
  | true =>
    have huc := hc u hhu
    cases hgv : g (unitInput v) with
    | false =>
      exact Or.inr (Or.inl ⟨hgp, huc.symm ▸ hgc, hgv⟩)
    | true => exact Or.inr (Or.inr (Or.inl ⟨huc, rfl, rfl⟩))



def insertTrueInput {α : Type*} [DecidableEq α] (x : α → Bool) (q : α) : α → Bool :=
  fun i => if i = q then true else x i

lemma input_le_insertTrueInput {α : Type*} [DecidableEq α] (x : α → Bool) (q : α) :
    ∀ i, x i = true → insertTrueInput x q i = true := by
  intro i hi
  by_cases he : i = q <;> simp [insertTrueInput, he, hi]

lemma context_false_on_star_support {α : Type*} (Adj : α → α → Prop)
    (Q : Finset α) (h : (α → Bool) → Bool)
    (hsafe : ∀ x, (∃ q ∈ Q, x q = true) → h x = true →
      ∃ a b, Adj a b ∧ x a = true ∧ x b = true)
    {x : α → Bool} (hx : h x = true)
    (hfalse : ¬ ∃ a b, Adj a b ∧ x a = true ∧ x b = true) :
    ∀ q ∈ Q, x q = false := by
  intro q hq
  cases he : x q with
  | false => rfl
  | true => exact False.elim (hfalse (hsafe x ⟨q, hq, he⟩ hx))

lemma context_false_input_neighbours {α : Type*} [DecidableEq α]
    (Adj : α → α → Prop)
    (hsymm : ∀ a b, Adj a b → Adj b a) (hirr : ∀ a, ¬ Adj a a)
    (Q : Finset α) (h : (α → Bool) → Bool) (hm : MonotoneBool h)
    (hsafe : ∀ x, (∃ q ∈ Q, x q = true) → h x = true →
      ∃ a b, Adj a b ∧ x a = true ∧ x b = true)
    {x : α → Bool} (hx : h x = true)
    (hfalse : ¬ ∃ a b, Adj a b ∧ x a = true ∧ x b = true) :
    ∀ q ∈ Q, ∃ a, Adj a q ∧ x a = true := by
  intro q hq
  have hy : h (insertTrueInput x q) = true :=
    hm x (insertTrueInput x q) (input_le_insertTrueInput x q) hx
  obtain ⟨a, b, hab, ha, hb⟩ :=
    hsafe (insertTrueInput x q) ⟨q, hq, by simp [insertTrueInput]⟩ hy
  by_cases haq : a = q
  · subst a
    have hbq : b ≠ q := by
      intro he
      subst b
      exact hirr q hab
    exact ⟨b, hsymm q b hab, by simpa [insertTrueInput, hbq] using hb⟩
  · have hxa : x a = true := by simpa [insertTrueInput, haq] using ha
    by_cases hbq : b = q
    · subst b
      exact ⟨a, hab, hxa⟩
    · have hxb : x b = true := by simpa [insertTrueInput, hbq] using hb
      exact False.elim (hfalse ⟨a, b, hab, hxa, hxb⟩)

lemma context_true_support_card {α : Type*} [Fintype α] [DecidableEq α]
    (Adj : α → α → Prop)
    (hsymm : ∀ a b, Adj a b → Adj b a) (hirr : ∀ a, ¬ Adj a a)
    (hno : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (Adj a b ∧ Adj a b' ∧ Adj a' b ∧ Adj a' b'))
    (Q : Finset α) (c : α) (hc : ∀ q ∈ Q, Adj c q)
    (h : (α → Bool) → Bool) (hm : MonotoneBool h)
    (hsafe : ∀ x, (∃ q ∈ Q, x q = true) → h x = true →
      ∃ a b, Adj a b ∧ x a = true ∧ x b = true)
    {x : α → Bool} (hx : h x = true)
    (hfalse : ¬ ∃ a b, Adj a b ∧ x a = true ∧ x b = true)
    (hxc : x c = false) :
    Q.card ≤ (Finset.univ.filter (fun a => x a = true)).card := by
  classical
  have hneigh := context_false_input_neighbours Adj hsymm hirr Q h hm hsafe hx hfalse
  have hex (q : α) : ∃ a, q ∈ Q → Adj a q ∧ x a = true := by
    by_cases hq : q ∈ Q
    · obtain ⟨a, ha, hxa⟩ := hneigh q hq
      exact ⟨a, fun _ => ⟨ha, hxa⟩⟩
    · exact ⟨c, fun hq' => False.elim (hq hq')⟩
  choose f hf using hex
  apply Finset.card_le_card_of_injOn f
  · intro q hq
    change f q ∈ Finset.univ.filter (fun a => x a = true)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf q hq).2⟩
  · intro q hq q' hq' he
    by_contra hqq'
    have hfc : c ≠ f q := by
      intro hcf
      have hxf := (hf q hq).2
      rw [← hcf, hxc] at hxf
      cases hxf
    have hfq' : Adj (f q) q' := by rw [he]; exact (hf q' hq').1
    exact hno c (f q) q q' hfc hqq'
      ⟨hc q hq, hc q' hq', (hf q hq).1, hfq'⟩

lemma context_off_centre_pair_safe {α : Type*} [Fintype α] [DecidableEq α]
    (Adj : α → α → Prop)
    (hsymm : ∀ a b, Adj a b → Adj b a) (hirr : ∀ a, ¬ Adj a a)
    (hno : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (Adj a b ∧ Adj a b' ∧ Adj a' b ∧ Adj a' b'))
    (Q : Finset α) (c : α) (hc : ∀ q ∈ Q, Adj c q) (hQ : 3 ≤ Q.card)
    (h : (α → Bool) → Bool) (hm : MonotoneBool h)
    (hsafe : ∀ x, (∃ q ∈ Q, x q = true) → h x = true →
      ∃ a b, Adj a b ∧ x a = true ∧ x b = true)
    {u v : α} (hu : u ≠ c) (hv : v ≠ c) (hp : h (pairInput u v) = true) :
    Adj u v := by
  classical
  by_contra hnadj
  have hfalse : ¬ ∃ a b, Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true := by
    rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hirr u (by simpa only [ha, hb] using hab)
    · exact hnadj (by simpa only [ha, hb] using hab)
    · exact hnadj (hsymm v u (by simpa only [ha, hb] using hab))
    · exact hirr v (by simpa only [ha, hb] using hab)
  have hxc : pairInput u v c = false := by
    simp [pairInput, Ne.symm hu, Ne.symm hv]
  have hcard := context_true_support_card Adj hsymm hirr hno Q c hc h hm hsafe hp hfalse hxc
  have hs : (Finset.univ.filter (fun a => pairInput u v a = true)) = {u, v} := by
    ext a
    simp [pairInput]
  rw [hs] at hcard
  have hp2 : ({u, v} : Finset α).card ≤ 2 := Finset.card_le_two
  omega


namespace SemanticNormal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def pr {n : ℕ} (u v : Fin n) : Fin n → Bool := fun c => decide (c = u ∨ c = v)
lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]


section cl

open Classical

-- abstract leaf count: a family closed under unions of two earlier members
lemma leaf_count {α : Type*} [DecidableEq α] (cls : ℕ → Prop) (T : ℕ → Finset α)
    (h : ∀ w, cls w → (T w).card ≤ 1 ∨ ∃ a b, a < w ∧ b < w ∧ cls a ∧ cls b ∧ T w = T a ∪ T b) :
    ∀ M (W : Finset ℕ), (∀ w ∈ W, w < M ∧ cls w) →
      (W.biUnion T).card ≤ W.card +
        ((Finset.range M).filter (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ W.biUnion T)).card := by
  intro M
  induction M with
  | zero =>
    intro W hW
    have : W = ∅ := by
      ext w
      simp only [Finset.notMem_empty, iff_false]
      intro hw
      exact absurd (hW w hw).1 (by omega)
    subst this
    simp
  | succ M ih =>
    intro W hW
    have hmono : ∀ U U' : Finset α, U ⊆ U' →
        ((Finset.range M).filter (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ U)).card ≤
        ((Finset.range (M + 1)).filter (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ U')).card := by
      intro U U' hU
      apply Finset.card_le_card
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by omega, hk.2.1, hk.2.2.1, hk.2.2.2.trans hU⟩
    by_cases hM : M ∈ W
    · have hWe : W = insert M (W.erase M) := (Finset.insert_erase hM).symm
      have hW' : ∀ w ∈ W.erase M, w < M ∧ cls w := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have := hW w hw.2
        exact ⟨by omega, this.2⟩
      have hnot : M ∉ W.erase M := Finset.notMem_erase M W
      have hcard : W.card = (W.erase M).card + 1 := by
        rw [Finset.card_erase_of_mem hM]
        have := Finset.card_pos.mpr ⟨M, hM⟩
        omega
      have hU : W.biUnion T = T M ∪ (W.erase M).biUnion T := by
        conv_lhs => rw [hWe]
        rw [Finset.biUnion_insert]
      by_cases h1 : (T M).card ≤ 1
      · have ih1 := ih (W.erase M) hW'
        have hsub : (W.erase M).biUnion T ⊆ W.biUnion T := by
          rw [hU]; exact Finset.subset_union_right
        have := hmono _ _ hsub
        have hu := Finset.card_union_le (T M) ((W.erase M).biUnion T)
        rw [hU] at this ⊢
        omega
      · rcases h M (hW M hM).2 with h2 | ⟨a, b, ha, hb, ca, cb, hT⟩
        · exact absurd h2 h1
        · set W2 := insert a (insert b (W.erase M)) with hW2
          have hW2' : ∀ w ∈ W2, w < M ∧ cls w := by
            intro w hw
            rw [hW2, Finset.mem_insert, Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hw
            · exact ⟨ha, ca⟩
            · exact ⟨hb, cb⟩
            · exact hW' w hw
          have hU2 : W2.biUnion T = W.biUnion T := by
            rw [hW2, Finset.biUnion_insert, Finset.biUnion_insert, hU, hT, Finset.union_assoc]
          have hc2 : W2.card ≤ (W.erase M).card + 2 := by
            rw [hW2]
            have e1 := Finset.card_insert_le a (insert b (W.erase M))
            have e2 := Finset.card_insert_le b (W.erase M)
            omega
          have ih2 := ih W2 hW2'
          rw [hU2] at ih2
          have hsplit : (Finset.range (M + 1)).filter
              (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ W.biUnion T) =
              insert M ((Finset.range M).filter
                (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ W.biUnion T)) := by
            rw [Finset.range_add_one, Finset.filter_insert, if_pos]
            refine ⟨(hW M hM).2, by omega, ?_⟩
            rw [hU]; exact Finset.subset_union_left
          rw [hsplit, Finset.card_insert_of_notMem (by simp)]
          omega
    · have hW' : ∀ w ∈ W, w < M ∧ cls w := by
        intro w hw
        have := hW w hw
        have hne : w ≠ M := fun he => hM (he ▸ hw)
        exact ⟨by omega, this.2⟩
      have := ih W hW'
      have := hmono (W.biUnion T) (W.biUnion T) le_rfl
      omega


section circ

variable (n : ℕ) (C : Circuit)

lemma gv (hC : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) (h1 : n ≤ w) (h2 : w < n + C.gates.length) :
    ∃ a b, (gateAt C (w - n)).inputs = [a, b] ∧ a < w ∧ b < w ∧
      ((gateAt C (w - n)).op = GateOp.and ∨ (gateAt C (w - n)).op = GateOp.or) ∧
      ∀ x : Fin n → Bool, val C.gates x w =
        (gateAt C (w - n)).op.eval [val C.gates x a, val C.gates x b] := by
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  have hk : k < C.gates.length := by omega
  have e : n + k - n = k := by omega
  rw [e]
  obtain ⟨hAO, hRB, hL⟩ := hC
  have hmem := List.getElem_mem hk
  have h2 := hL _ hmem
  have hop := hAO _ hmem
  rw [← gateAt_eq C k hk] at h2 hop
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
  have ha := hRB k hk a (by rw [hab]; simp)
  have hb := hRB k hk b (by rw [hab]; simp)
  refine ⟨a, b, hab, ha, hb, hop, fun x => ?_⟩
  rw [val_gate C.gates x k hk, ← gateAt_eq C k hk, hab]
  simp [ha, hb]

lemma ev_and (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by simp [GateOp.eval]

lemma ev_or (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by simp [GateOp.eval]

def S (w : ℕ) : Finset (Fin n) := Finset.univ.filter (fun v => val C.gates (eof v) w = true)

lemma mem_S (w : ℕ) (v : Fin n) : v ∈ S n C w ↔ val C.gates (eof v) w = true := by simp [S]

lemma S_inp (w : ℕ) (hw : w < n) : S n C w = {⟨w, hw⟩} := by
  ext v
  rw [mem_S, val_lt C.gates _ w hw]
  simp only [eof, decide_eq_true_eq, Finset.mem_singleton]
  exact eq_comm

lemma S_or (a b w : ℕ)
    (hv : ∀ x : Fin n → Bool, val C.gates x w = (val C.gates x a || val C.gates x b)) :
    S n C w = S n C a ∪ S n C b := by
  ext v
  simp only [Finset.mem_union, mem_S, hv, Bool.or_eq_true]

def Z (w : ℕ) : Prop :=
  n ≤ w ∧ w < n + C.gates.length ∧ ∀ v : Fin n, val C.gates (eof v) w = false

lemma z_struct (hC : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) (hz : Z n C w) :
    (gateAt C (w - n)).op = GateOp.and ∨ ((gateAt C (w - n)).op = GateOp.or ∧
      ∃ a b, (gateAt C (w - n)).inputs = [a, b] ∧ a < w ∧ b < w ∧ Z n C a ∧ Z n C b ∧
        ∀ x : Fin n → Bool, val C.gates x w = (val C.gates x a || val C.gates x b)) := by
  obtain ⟨h1, h2, h3⟩ := hz
  obtain ⟨a, b, hab, ha, hb, hop, hv⟩ := gv n C hC w h1 h2
  rcases hop with hop | hop
  · exact Or.inl hop
  · right
    have hv' : ∀ x : Fin n → Bool, val C.gates x w = (val C.gates x a || val C.gates x b) := by
      intro x; rw [hv x, hop, ev_or]
    have hza : ∀ c, c < w → (∀ v : Fin n, val C.gates (eof v) w = false → val C.gates (eof v) c = false) →
        Z n C c := by
      intro c hc hcv
      refine ⟨?_, by omega, fun v => hcv v (h3 v)⟩
      by_contra hlt
      push_neg at hlt
      have := hcv ⟨c, hlt⟩ (h3 _)
      rw [val_lt C.gates _ c hlt] at this
      simp [eof] at this
    refine ⟨hop, a, b, hab, ha, hb, hza a ha ?_, hza b hb ?_, hv'⟩
    · intro v hv0; rw [hv'] at hv0; simp only [Bool.or_eq_false_iff] at hv0; exact hv0.1
    · intro v hv0; rw [hv'] at hv0; simp only [Bool.or_eq_false_iff] at hv0; exact hv0.2

def Reach (j w : ℕ) : Prop :=
  n ≤ j ∧ j < n + C.gates.length ∧ (gateAt C (j - n)).op = GateOp.and ∧
    Relation.ReflTransGen (fun a w : ℕ =>
      n ≤ w ∧ w < n + C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or ∧
        a ∈ (gateAt C (w - n)).inputs) j w

lemma Reach.self {n : ℕ} {C : Circuit} (w : ℕ)
    (h1 : n ≤ w) (h2 : w < n + C.gates.length)
    (h3 : (gateAt C (w - n)).op = GateOp.and) : Reach n C w w :=
  ⟨h1, h2, h3, Relation.ReflTransGen.refl⟩

lemma Reach.up {n : ℕ} {C : Circuit} (j w a : ℕ)
    (h1 : n ≤ w) (h2 : w < n + C.gates.length)
    (h3 : (gateAt C (w - n)).op = GateOp.or)
    (h4 : a ∈ (gateAt C (w - n)).inputs) (h : Reach n C j a) : Reach n C j w :=
  ⟨h.1, h.2.1, h.2.2.1, Relation.ReflTransGen.tail h.2.2.2 ⟨h1, h2, h3, h4⟩⟩

lemma reach_and (hC : PEqualNP.TopForm.IsAO2 n C) (j w : ℕ) (h : Reach n C j w) :
    n ≤ j ∧ j < n + C.gates.length ∧ (gateAt C (j - n)).op = GateOp.and ∧ j ≤ w := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  have hp := h.2.2.2
  clear h
  induction hp with
  | refl => exact le_rfl
  | @tail b c hpath hstep ih =>
    obtain ⟨h1, h2, _, hmem⟩ := hstep
    obtain ⟨a', b', hab, ha, hb, _, _⟩ := gv n C hC c h1 h2
    rw [hab] at hmem
    have hbc : b < c := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> assumption
    exact le_trans ih (Nat.le_of_lt hbc)

lemma reach_val (hC : PEqualNP.TopForm.IsAO2 n C) (j w : ℕ) (h : Reach n C j w) :
    ∀ x : Fin n → Bool, val C.gates x j = true → val C.gates x w = true := by
  intro x hx
  have hp := h.2.2.2
  clear h
  induction hp with
  | refl => exact hx
  | @tail b c hpath hstep ih =>
    obtain ⟨h1, h2, hop, hmem⟩ := hstep
    obtain ⟨a', b', hab, _, _, _, hv⟩ := gv n C hC c h1 h2
    rw [hv x, hop, ev_or, Bool.or_eq_true]
    rw [hab] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact Or.inl ih
    · exact Or.inr ih

lemma z_sem (hC : PEqualNP.TopForm.IsAO2 n C) : ∀ w, Z n C w → ∀ x : Fin n → Bool,
    val C.gates x w = true → ∃ j, Reach n C j w ∧ val C.gates x j = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hz x hx
    rcases z_struct n C hC w hz with hop | ⟨hop, a, b, hab, ha, hb, za, zb, hv⟩
    · exact ⟨w, Reach.self w hz.1 hz.2.1 hop, hx⟩
    · rw [hv, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · obtain ⟨j, hj, hjx⟩ := ih a ha za x hx
        exact ⟨j, Reach.up j w a hz.1 hz.2.1 hop (by rw [hab]; simp) hj, hjx⟩
      · obtain ⟨j, hj, hjx⟩ := ih b hb zb x hx
        exact ⟨j, Reach.up j w b hz.1 hz.2.1 hop (by rw [hab]; simp) hj, hjx⟩

lemma reach_inv (j w : ℕ) (h : Reach n C j w) :
    (j = w ∧ n ≤ w ∧ w < n + C.gates.length ∧ (gateAt C (w - n)).op = GateOp.and) ∨
    (n ≤ w ∧ w < n + C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or ∧
      ∃ a ∈ (gateAt C (w - n)).inputs, Reach n C j a) := by
  rcases Relation.ReflTransGen.cases_tail h.2.2.2 with heq | ⟨a, ha, hstep⟩
  · subst w
    exact Or.inl ⟨rfl, h.1, h.2.1, h.2.2.1⟩
  · obtain ⟨h1, h2, hop, hmem⟩ := hstep
    exact Or.inr ⟨h1, h2, hop, a, hmem, h.1, h.2.1, h.2.2.1, ha⟩

noncomputable def A (w : ℕ) : Finset ℕ :=
  (Finset.range (n + C.gates.length)).filter (fun j => Reach n C j w)

lemma mem_A (hC : PEqualNP.TopForm.IsAO2 n C) (j w : ℕ) : j ∈ A n C w ↔ Reach n C j w := by
  unfold A
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(reach_and n C hC j w h).2.1, h⟩

lemma A_and (hC : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) (h1 : n ≤ w)
    (h2 : w < n + C.gates.length) (hop : (gateAt C (w - n)).op = GateOp.and) :
    A n C w = {w} := by
  ext j
  rw [mem_A n C hC, Finset.mem_singleton]
  constructor
  · intro h
    rcases reach_inv n C j w h with ⟨h0, _⟩ | ⟨_, _, h3, _⟩
    · exact h0
    · rw [hop] at h3; exact absurd h3 (by simp)
  · rintro rfl
    exact Reach.self j h1 h2 hop

lemma z_cls (hC : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) (hz : Z n C w) :
    (A n C w).card ≤ 1 ∨ ∃ a b, a < w ∧ b < w ∧ Z n C a ∧ Z n C b ∧ A n C w = A n C a ∪ A n C b := by
  rcases z_struct n C hC w hz with hop | ⟨hop, a, b, hab, ha, hb, za, zb, _⟩
  · left; rw [A_and n C hC w hz.1 hz.2.1 hop]; simp
  · right
    refine ⟨a, b, ha, hb, za, zb, ?_⟩
    ext j
    rw [Finset.mem_union, mem_A n C hC, mem_A n C hC, mem_A n C hC]
    constructor
    · intro h
      rcases reach_inv n C j w h with ⟨_, _, _, h3⟩ | ⟨_, _, _, a0, h4, h5⟩
      · rw [hop] at h3; exact absurd h3 (by simp)
      · rw [hab] at h4
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
        rcases h4 with rfl | rfl
        · exact Or.inl h5
        · exact Or.inr h5
    · rintro (h | h)
      · exact Reach.up j w a hz.1 hz.2.1 hop (by rw [hab]; simp) h
      · exact Reach.up j w b hz.1 hz.2.1 hop (by rw [hab]; simp) h


def Pure (w : ℕ) : Prop := ∀ x : Fin n → Bool,
  val C.gates x w = decide (∃ v ∈ S n C w, x v = true)

lemma pure_sem (w : ℕ) (hp : Pure n C w) (u v : Fin n) :
    val C.gates (pr u v) w = true ↔ u ∈ S n C w ∨ v ∈ S n C w := by
  rw [hp, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hx⟩
    simp only [pr, decide_eq_true_eq] at hx
    rcases hx with rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (hu | hv)
    · exact ⟨u, hu, by simp [pr]⟩
    · exact ⟨v, hv, by simp [pr]⟩

lemma val_ones (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∀ w, w < n + C.gates.length → val C.gates (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_lt C.gates _ w hn]
    · obtain ⟨a, b, _, ha, hb, hop, hv⟩ := gv n C hC w (by omega) hw
      rw [hv, ih a ha (by omega), ih b hb (by omega)]
      rcases hop with hop | hop <;> simp [hop, GateOp.eval]

lemma val_monotone (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∀ w, w < n + C.gates.length → MonotoneBool (fun x : Fin n → Bool => val C.gates x w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw x y hxy hx
    change val C.gates x w = true at hx
    change val C.gates y w = true
    by_cases hn : w < n
    · rw [val_lt C.gates _ w hn] at hx ⊢
      exact hxy _ hx
    · obtain ⟨a, b, _, ha, hb, hop, hv⟩ := gv n C hC w (by omega) hw
      rcases hop with hop | hop
      · rw [hv, hop, ev_and, Bool.and_eq_true] at hx ⊢
        exact ⟨ih a ha (by omega) x y hxy hx.1, ih b hb (by omega) x y hxy hx.2⟩
      · rw [hv, hop, ev_or, Bool.or_eq_true] at hx ⊢
        exact hx.imp (ih a ha (by omega) x y hxy) (ih b hb (by omega) x y hxy)

lemma pure_ne (hC : PEqualNP.TopForm.IsAO2 n C) (w : ℕ)
    (hw : w < n + C.gates.length) (hp : Pure n C w) : (S n C w).Nonempty := by
  have h := val_ones n C hC w hw
  rw [hp, decide_eq_true_eq] at h
  obtain ⟨v, hv, _⟩ := h
  exact ⟨v, hv⟩

lemma below_support (Q : Finset (Fin n)) (w : ℕ)
    (hb : BelowOr Q (fun x : Fin n → Bool => val C.gates x w)) : S n C w ⊆ Q := by
  intro v hv
  obtain ⟨i, hi, hx⟩ := hb (eof v) ((mem_S n C w v).mp hv)
  simp only [eof, decide_eq_true_eq] at hx
  rwa [hx] at hi

def BC (Q : Finset (Fin n)) (w : ℕ) : Prop :=
  w < n + C.gates.length ∧ BelowOr Q (fun x : Fin n → Bool => val C.gates x w)

def IsOr (w : ℕ) : Prop :=
  n ≤ w ∧ w < n + C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or

lemma bc_class (hC : PEqualNP.TopForm.IsAO2 n C) (Q : Finset (Fin n)) (w : ℕ)
    (hw : BC n C Q w) :
    (S n C w).card ≤ 1 ∨
      (IsOr n C w ∧ ∃ a b, a < w ∧ b < w ∧ BC n C Q a ∧ BC n C Q b ∧
        S n C w = S n C a ∪ S n C b) ∨
      ∃ a, a < w ∧ BC n C Q a ∧ S n C w ⊆ S n C a := by
  by_cases hn : w < n
  · left
    rw [S_inp n C w hn]
    simp
  · obtain ⟨a, b, _, ha, hb, hop, hv⟩ := gv n C hC w (by omega) hw.1
    have ham : MonotoneBool (fun x : Fin n → Bool => val C.gates x a) :=
      val_monotone n C hC a (by have := hw.1; omega)
    have hbm : MonotoneBool (fun x : Fin n → Bool => val C.gates x b) :=
      val_monotone n C hC b (by have := hw.1; omega)
    rcases hop with hop | hop
    · have hv' : ∀ x : Fin n → Bool, val C.gates x w = (val C.gates x a && val C.gates x b) := by
        intro x
        rw [hv, hop, ev_and]
      have hbound : BelowOr Q (fun x : Fin n → Bool => val C.gates x a && val C.gates x b) := by
        intro x hx
        exact hw.2 x ((hv' x).trans hx)
      right; right
      rcases belowOr_and Q _ _ ham hbm hbound with hba | hbb
      · refine ⟨a, ha, ⟨by have := hw.1; omega, hba⟩, ?_⟩
        intro v hvv
        rw [mem_S, hv', Bool.and_eq_true] at hvv
        exact (mem_S n C a v).mpr hvv.1
      · refine ⟨b, hb, ⟨by have := hw.1; omega, hbb⟩, ?_⟩
        intro v hvv
        rw [mem_S, hv', Bool.and_eq_true] at hvv
        exact (mem_S n C b v).mpr hvv.2
    · have hv' : ∀ x : Fin n → Bool, val C.gates x w = (val C.gates x a || val C.gates x b) := by
        intro x
        rw [hv, hop, ev_or]
      have hbound : BelowOr Q (fun x : Fin n → Bool => val C.gates x a || val C.gates x b) := by
        intro x hx
        exact hw.2 x ((hv' x).trans hx)
      obtain ⟨hba, hbb⟩ := belowOr_or Q _ _ hbound
      exact Or.inr (Or.inl ⟨⟨by omega, hw.1, hop⟩, a, b, ha, hb,
        ⟨by have := hw.1; omega, hba⟩, ⟨by have := hw.1; omega, hbb⟩, S_or n C a b w hv'⟩)

end circ

def ia (C : Circuit) (n j : ℕ) : ℕ := (gateAt C (j - n)).inputs.getD 0 0

def ib (C : Circuit) (n j : ℕ) : ℕ := (gateAt C (j - n)).inputs.getD 1 0

def Good (n : ℕ) (C : Circuit) (adj : Fin n → Fin n → Prop) : Prop :=
  PEqualNP.TopForm.IsAO2 n C ∧
  (∀ j, Reach n C j C.output → Pure n C (ia C n j) ∧ Pure n C (ib C n j)) ∧
  (∀ v, ¬ adj v v) ∧ (∀ u v, adj u v → adj v u) ∧
  (∀ c c' y y' : Fin n, c ≠ c' → y ≠ y' → adj c y → adj c y' → adj c' y → adj c' y' → False) ∧
  (∀ u v : Fin n, val C.gates (pr u v) C.output = true ↔ adj u v)

section stars

variable (n : ℕ) (C : Circuit) (adj : Fin n → Fin n → Prop)

lemma pr_self (v : Fin n) : pr v v = eof v := by
  funext c; simp [pr, eof]

lemma out_Z (hG : Good n C adj) (hex : ∃ u v, adj u v) : Z n C C.output := by
  obtain ⟨_, _, hirr, _, _, hout⟩ := hG
  have hf : ∀ v : Fin n, val C.gates (eof v) C.output = false := by
    intro v
    rw [← pr_self]
    cases hv : val C.gates (pr v v) C.output
    · rfl
    · rw [hout] at hv; exact absurd hv (hirr v)
  refine ⟨?_, ?_, hf⟩
  · by_contra h
    push_neg at h
    have := hf ⟨C.output, h⟩
    rw [val_lt C.gates _ _ h] at this
    simp [eof] at this
  · by_contra h
    push_neg at h
    obtain ⟨u, v, huv⟩ := hex
    have h1 := (hout u v).mpr huv
    rw [val_ge C.gates _ _ h] at h1
    exact absurd h1 (by simp)

lemma star (hG : Good n C adj) (j : ℕ) (hj : Reach n C j C.output) :
    Pure n C (ia C n j) ∧ Pure n C (ib C n j) ∧ ia C n j < j ∧ ib C n j < j ∧
      ∀ u v : Fin n, (val C.gates (pr u v) j = true ↔
        (u ∈ S n C (ia C n j) ∨ v ∈ S n C (ia C n j)) ∧
        (u ∈ S n C (ib C n j) ∨ v ∈ S n C (ib C n j))) := by
  have hC := hG.1
  obtain ⟨qa, qb⟩ := hG.2.1 j hj
  obtain ⟨h1, h2, hop, _⟩ := reach_and n C hC j _ hj
  obtain ⟨a, b, hab, ha, hb, _, hv⟩ := gv n C hC j h1 h2
  have ea : ia C n j = a := by simp [ia, hab]
  have eb : ib C n j = b := by simp [ib, hab]
  rw [ea] at qa
  rw [eb] at qb
  rw [ea, eb]
  refine ⟨qa, qb, ha, hb, fun u v => ?_⟩
  rw [hv, hop, ev_and, Bool.and_eq_true, pure_sem n C a qa, pure_sem n C b qb]

lemma star2 (hG : Good n C adj) (j : ℕ) (hj : Reach n C j C.output) :
    (∀ v, ¬ (v ∈ S n C (ia C n j) ∧ v ∈ S n C (ib C n j))) ∧
    (∀ u ∈ S n C (ia C n j), ∀ v ∈ S n C (ib C n j), adj u v) ∧
    ((S n C (ia C n j)).card = 1 ∨ (S n C (ib C n j)).card = 1) := by
  obtain ⟨la, lb, haa, hbb, hs⟩ := star n C adj hG j hj
  obtain ⟨hC, _, hirr, _, hcom, hout⟩ := hG
  have hadj : ∀ u v, val C.gates (pr u v) j = true → adj u v := by
    intro u v h
    exact (hout u v).mp (reach_val n C hC j _ hj _ h)
  have hd : ∀ v, ¬ (v ∈ S n C (ia C n j) ∧ v ∈ S n C (ib C n j)) := by
    rintro v ⟨h1, h2⟩
    exact hirr v (hadj v v ((hs v v).mpr ⟨Or.inl h1, Or.inl h2⟩))
  have hc : ∀ u ∈ S n C (ia C n j), ∀ v ∈ S n C (ib C n j), adj u v :=
    fun u hu v hv => hadj u v ((hs u v).mpr ⟨Or.inl hu, Or.inr hv⟩)
  refine ⟨hd, hc, ?_⟩
  by_contra hne
  push_neg at hne
  have hjb := (reach_and n C hC j _ hj).2.1
  have n1 := (pure_ne n C hC _ (lt_trans haa hjb) la).card_pos
  have n2 := (pure_ne n C hC _ (lt_trans hbb hjb) lb).card_pos
  obtain ⟨p1, hp1, p2, hp2, hp⟩ :=
    Finset.one_lt_card.mp (show 1 < (S n C (ia C n j)).card by omega)
  obtain ⟨q1, hq1, q2, hq2, hq⟩ :=
    Finset.one_lt_card.mp (show 1 < (S n C (ib C n j)).card by omega)
  exact hcom p1 p2 q1 q2 hp hq (hc p1 hp1 q1 hq1) (hc p1 hp1 q2 hq2) (hc p2 hp2 q1 hq1)
    (hc p2 hp2 q2 hq2)

def cw (j : ℕ) : ℕ := if (S n C (ia C n j)).card = 1 then ia C n j else ib C n j

def lw (j : ℕ) : ℕ := if (S n C (ia C n j)).card = 1 then ib C n j else ia C n j

lemma cw_facts (hG : Good n C adj) (j : ℕ) (hj : Reach n C j C.output) :
    (S n C (cw n C j)).card = 1 ∧ Pure n C (lw n C j) ∧ lw n C j < j ∧
      (∀ c ∈ S n C (cw n C j), ∀ y ∈ S n C (lw n C j), adj c y) := by
  obtain ⟨la, lb, ha, hb, _⟩ := star n C adj hG j hj
  obtain ⟨_, hc, h1⟩ := star2 n C adj hG j hj
  have hsymm := hG.2.2.2.1
  by_cases h : (S n C (ia C n j)).card = 1
  · simp only [cw, lw, if_pos h]
    exact ⟨h, lb, hb, hc⟩
  · simp only [cw, lw, if_neg h]
    refine ⟨h1.resolve_left h, la, ha, fun c hc' y hy => ?_⟩
    exact hsymm _ _ (hc y hy c hc')

lemma cover (hG : Good n C adj) (u v : Fin n) (huv : adj u v) :
    ∃ j, Reach n C j C.output ∧ ((u ∈ S n C (cw n C j) ∧ v ∈ S n C (lw n C j)) ∨
      (v ∈ S n C (cw n C j) ∧ u ∈ S n C (lw n C j))) := by
  have hC := hG.1
  have hout := hG.2.2.2.2.2
  obtain ⟨j, hj, hv⟩ := z_sem n C hC _ (out_Z n C adj hG ⟨u, v, huv⟩) _ ((hout u v).mpr huv)
  refine ⟨j, hj, ?_⟩
  obtain ⟨_, _, _, _, hs⟩ := star n C adj hG j hj
  obtain ⟨hd, _, _⟩ := star2 n C adj hG j hj
  have h := (hs u v).mp hv
  have hu := hd u
  have hv' := hd v
  by_cases hc : (S n C (ia C n j)).card = 1
  · simp only [cw, lw, if_pos hc]
    tauto
  · simp only [cw, lw, if_neg hc]
    tauto

end stars

section count

variable (n : ℕ) (C : Circuit) (adj : Fin n → Fin n → Prop)

lemma dbl (s : Finset ℕ) (T : ℕ → Finset (Fin n)) (h : ∀ j ∈ s, (T j).card = 1) :
    ∑ c : Fin n, (s.filter (fun j => c ∈ T j)).card = s.card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ j ∈ s, ∑ c : Fin n, (if c ∈ T j then 1 else 0) = 1 := by
    intro j hj
    rw [Finset.sum_boole]
    simp [Finset.filter_mem_eq_inter, h j hj]
  rw [Finset.sum_congr rfl this]
  simp

noncomputable def G (c : Fin n) : Finset ℕ :=
  (A n C C.output).filter (fun j => c ∈ S n C (cw n C j))

noncomputable def D (c : Fin n) : Finset (Fin n) := (G n C c).biUnion (fun j => S n C (lw n C j))


noncomputable def N (c : Fin n) : Finset (Fin n) := Finset.univ.filter (adj c)

noncomputable def Lc (c : Fin n) : Finset ℕ :=
  (Finset.range (n + C.gates.length)).filter
    (fun k => BC n C (N n adj c) k ∧ IsOr n C k ∧ 2 ≤ (S n C k).card)

noncomputable def LL : Finset ℕ := (Finset.range (n + C.gates.length)).filter
  (fun k => IsOr n C k ∧ 2 ≤ (S n C k).card)

noncomputable def PU : Finset ℕ := (Finset.range (n + C.gates.length)).filter
  (fun k => Z n C k ∧ 2 ≤ (A n C k).card ∧ A n C k ⊆ A n C C.output)

lemma memG (c : Fin n) (j : ℕ) : j ∈ G n C c ↔ j ∈ A n C C.output ∧ c ∈ S n C (cw n C j) := by
  simp [G]

lemma memD (c y : Fin n) : y ∈ D n C c ↔ ∃ j ∈ G n C c, y ∈ S n C (lw n C j) := by
  simp [D]

lemma dn (hG : Good n C adj) (c : Fin n) : ∀ y ∈ D n C c, adj c y := by
  intro y hy
  obtain ⟨j, hjG, hy⟩ := (memD n C c y).mp hy
  obtain ⟨hjA, hc⟩ := (memG n C c j).mp hjG
  exact (cw_facts n C adj hG j ((mem_A n C hG.1 j _).mp hjA)).2.2.2 c hc y hy


lemma dc_le (hG : Good n C adj) (c : Fin n) :
    (D n C c).card ≤ (G n C c).card + (Lc n C adj c).card := by
  have hC := hG.1
  have hW : ∀ w ∈ (G n C c).image (lw n C),
      w < n + C.gates.length ∧ BC n C (N n adj c) w := by
    intro w hw
    obtain ⟨j, hjG, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hjA, hc⟩ := (memG n C c j).mp hjG
    have hr := (mem_A n C hC j _).mp hjA
    obtain ⟨_, hp, hlt, hadj⟩ := cw_facts n C adj hG j hr
    have hjb := (reach_and n C hC j _ hr).2.1
    refine ⟨by omega, ⟨by omega, ?_⟩⟩
    intro x hx
    change val C.gates x (lw n C j) = true at hx
    rw [hp, decide_eq_true_eq] at hx
    obtain ⟨v, hv, hxv⟩ := hx
    refine ⟨v, ?_, hxv⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj c hc v hv⟩
  have h := leaf_count_bypass (BC n C (N n adj c)) (IsOr n C) (S n C)
    (bc_class n C hC (N n adj c)) (n + C.gates.length) ((G n C c).image (lw n C)) hW
  rw [Finset.image_biUnion] at h
  have hi : ((G n C c).image (lw n C)).card ≤ (G n C c).card := Finset.card_image_le
  have h' : (D n C c).card ≤ ((G n C c).image (lw n C)).card + (Lc n C adj c).card := h
  omega

lemma lsum (hG : Good n C adj) : ∑ c : Fin n, (Lc n C adj c).card ≤ (LL n C).card := by
  have hcom := hG.2.2.2.2.1
  have hdisj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (Lc n C adj) := by
    intro c _ c' _ hne
    show Disjoint (Lc n C adj c) (Lc n C adj c')
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Lc, Finset.mem_filter] at hk hk'
    obtain ⟨y1, hy1, y2, hy2, hy⟩ := Finset.one_lt_card.mp
      (show 1 < (S n C k).card by omega)
    have hsub := below_support n C (N n adj c) k hk.2.1.2
    have hsub' := below_support n C (N n adj c') k hk'.2.1.2
    have a1 := (Finset.mem_filter.mp (hsub hy1)).2
    have a2 := (Finset.mem_filter.mp (hsub hy2)).2
    have b1 := (Finset.mem_filter.mp (hsub' hy1)).2
    have b2 := (Finset.mem_filter.mp (hsub' hy2)).2
    exact hcom c c' y1 y2 hne hy a1 a2 b1 b2
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_biUnion] at hk
  obtain ⟨c, _, hk⟩ := hk
  simp only [Lc, LL, Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.2⟩

lemma gsum (hG : Good n C adj) : ∑ c : Fin n, (G n C c).card = (A n C C.output).card :=
  dbl n (A n C C.output) (fun j => S n C (cw n C j))
    (fun j hj => (cw_facts n C adj hG j ((mem_A n C hG.1 j _).mp hj)).1)

lemma cov (hG : Good n C adj) (u v : Fin n) (huv : adj u v) :
    ((G n C u).Nonempty ∧ v ∈ D n C u) ∨ ((G n C v).Nonempty ∧ u ∈ D n C v) := by
  obtain ⟨j, hj, h⟩ := cover n C adj hG u v huv
  have hjA : j ∈ A n C C.output := (mem_A n C hG.1 j _).mpr hj
  rcases h with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · exact Or.inl ⟨⟨j, (memG n C _ _).mpr ⟨hjA, hu⟩⟩,
      (memD n C _ _).mpr ⟨j, (memG n C _ _).mpr ⟨hjA, hu⟩, hv⟩⟩
  · exact Or.inr ⟨⟨j, (memG n C _ _).mpr ⟨hjA, hv⟩⟩,
      (memD n C _ _).mpr ⟨j, (memG n C _ _).mpr ⟨hjA, hv⟩, hu⟩⟩

lemma kcard (hG : Good n C adj) :
    (Finset.univ.filter (fun c : Fin n => (G n C c).Nonempty)).card ≤ (A n C C.output).card := by
  rw [← gsum n C adj hG, Finset.card_eq_sum_ones]
  calc ∑ c ∈ Finset.univ.filter (fun c : Fin n => (G n C c).Nonempty), 1
      ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin n => (G n C c).Nonempty), (G n C c).card :=
        Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2.card_pos)
    _ ≤ ∑ c : Fin n, (G n C c).card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma pu_le (hG : Good n C adj) (hex : ∃ u v, adj u v) :
    (A n C C.output).card ≤ 1 + (PU n C).card := by
  have hz := out_Z n C adj hG hex
  have h := leaf_count (Z n C) (A n C) (z_cls n C hG.1) (n + C.gates.length) {C.output} (by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact ⟨hz.2.1, hz⟩)
  rw [Finset.singleton_biUnion, Finset.card_singleton] at h
  exact h

lemma size_le (hG : Good n C adj) :
    (LL n C).card + (A n C C.output).card + (PU n C).card ≤ C.gates.length := by
  have hC := hG.1
  have hLL : ∀ k ∈ LL n C, n ≤ k ∧ k < n + C.gates.length ∧
      (gateAt C (k - n)).op = GateOp.or := by
    intro k hk
    simp only [LL, Finset.mem_filter] at hk
    exact hk.2.1
  have hAA : ∀ k ∈ A n C C.output, n ≤ k ∧ k < n + C.gates.length ∧
      (gateAt C (k - n)).op = GateOp.and := by
    intro k hk
    obtain ⟨h1, h2, h3, _⟩ := reach_and n C hC k _ ((mem_A n C hC k _).mp hk)
    exact ⟨h1, h2, h3⟩
  have hPP : ∀ k ∈ PU n C, Z n C k ∧ 2 ≤ (A n C k).card := by
    intro k hk
    simp only [PU, Finset.mem_filter] at hk
    exact ⟨hk.2.1, hk.2.2.1⟩
  have d1 : Disjoint (LL n C) (A n C C.output) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have := (hLL k h1).2.2
    rw [(hAA k h2).2.2] at this
    exact absurd this (by simp)
  have d2 : Disjoint (LL n C ∪ A n C C.output) (PU n C) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    obtain ⟨hz, h2c⟩ := hPP k h2
    rcases Finset.mem_union.mp h1 with h1 | h1
    · simp only [LL, Finset.mem_filter] at h1
      have : S n C k = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro v hv
        rw [mem_S, hz.2.2 v] at hv
        exact absurd hv (by simp)
      rw [this] at h1
      simp at h1
    · obtain ⟨a1, a2, a3⟩ := hAA k h1
      rw [A_and n C hC k a1 a2 a3, Finset.card_singleton] at h2c
      omega
  have hsub : LL n C ∪ A n C C.output ∪ PU n C ⊆ Finset.Ico n (n + C.gates.length) := by
    intro k hk
    rw [Finset.mem_Ico]
    rcases Finset.mem_union.mp hk with hk | hk
    · rcases Finset.mem_union.mp hk with hk | hk
      · exact ⟨(hLL k hk).1, (hLL k hk).2.1⟩
      · exact ⟨(hAA k hk).1, (hAA k hk).2.1⟩
    · exact ⟨(hPP k hk).1.1, (hPP k hk).1.2.1⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1, Nat.card_Ico] at this
  omega

lemma core (hG : Good n C adj) (hex : ∃ u v, adj u v) :
    ∃ (K : Finset (Fin n)) (Dm : Fin n → Finset (Fin n)), (∀ u v, adj u v → u ∈ K ∨ v ∈ K) ∧
      (∀ u v, adj u v → v ∈ Dm u ∨ u ∈ Dm v) ∧
      (∑ c, (Dm c).card) + K.card ≤ C.gates.length + 1 := by
  refine ⟨Finset.univ.filter (fun c : Fin n => (G n C c).Nonempty), D n C, ?_, ?_, ?_⟩
  · intro u v huv
    rcases cov n C adj hG u v huv with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩)
  · intro u v huv
    rcases cov n C adj hG u v huv with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  · have e2 : ∑ c : Fin n, (D n C c).card ≤ (A n C C.output).card + (LL n C).card := by
      calc ∑ c : Fin n, (D n C c).card ≤ ∑ c : Fin n, ((G n C c).card + (Lc n C adj c).card) :=
            Finset.sum_le_sum (fun c _ => dc_le n C adj hG c)
        _ = ∑ c : Fin n, (G n C c).card + ∑ c : Fin n, (Lc n C adj c).card := Finset.sum_add_distrib
        _ ≤ (A n C C.output).card + (LL n C).card := by
            rw [gsum n C adj hG]
            exact Nat.add_le_add_left (lsum n C adj hG) _
    have e3 := kcard n C adj hG
    have e4 := pu_le n C adj hG hex
    have e5 := size_le n C adj hG
    omega

end count
end cl

lemma ca_ne_na {x1 x2 : ℕ} (p : Fin x1) (l : Fin x2) : Fin.castAdd x2 p ≠ Fin.natAdd x1 l := by
  intro h
  have h1 : p.val = x1 + l.val := congrArg Fin.val h
  have := p.isLt
  omega

lemma ca_inj {x1 x2 : ℕ} {p p' : Fin x1} (h : Fin.castAdd x2 p = Fin.castAdd x2 p') : p = p' := by
  have h1 := congrArg Fin.val h
  exact Fin.ext h1

lemma na_inj {x1 x2 : ℕ} {l l' : Fin x2} (h : Fin.natAdd x1 l = Fin.natAdd x1 l') : l = l' := by
  have h1 : x1 + l.val = x1 + l'.val := congrArg Fin.val h
  exact Fin.ext (by omega)

def adjI {x1 x2 : ℕ} (I : Fin x1 → Fin x2 → Prop) (u v : Fin (x1 + x2)) : Prop :=
  ∃ p l, I p l ∧ ((u = Fin.castAdd x2 p ∧ v = Fin.natAdd x1 l) ∨
    (u = Fin.natAdd x1 l ∧ v = Fin.castAdd x2 p))

lemma good_of (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) (C : Circuit)
    (hno : ∀ (a a' : Fin x1) (b b' : Fin x2), a ≠ a' → b ≠ b' →
      ¬ (I a b ∧ I a b' ∧ I a' b ∧ I a' b'))
    (hC : PEqualNP.TopForm.IsAO2 (x1 + x2) C)
    (hF : ∀ x : Fin (x1 + x2) → Bool, circuitFun (x1 + x2) C x = true ↔
      ∃ p l, I p l ∧ x (Fin.castAdd x2 p) = true ∧ x (Fin.natAdd x1 l) = true)
    (hPure : ∀ j, Reach (x1 + x2) C j C.output →
      Pure (x1 + x2) C (ia C (x1 + x2) j) ∧ Pure (x1 + x2) C (ib C (x1 + x2) j)) :
    Good (x1 + x2) C (adjI I) := by
  refine ⟨hC, hPure, ?_, ?_, ?_, ?_⟩
  · intro v hv
    unfold adjI at hv
    obtain ⟨p, l, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hv
    · exact ca_ne_na p l (h1.symm.trans h2)
    · exact ca_ne_na p l (h2.symm.trans h1)
  · intro u v h
    unfold adjI at h ⊢
    obtain ⟨p, l, i, h | h⟩ := h
    · exact ⟨p, l, i, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨p, l, i, Or.inl ⟨h.2, h.1⟩⟩
  · intro c c' y y' hc hy h1 h2 h3 h4
    unfold adjI at h1 h2 h3 h4
    obtain ⟨p1, l1, i1, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h1
    · obtain ⟨p2, l2, i2, ⟨e1, rfl⟩ | ⟨e1, _⟩⟩ := h2
      · obtain ⟨p3, l3, i3, ⟨rfl, e3⟩ | ⟨_, e3⟩⟩ := h3
        · obtain ⟨p4, l4, i4, ⟨e4, e5⟩ | ⟨e4, _⟩⟩ := h4
          · rw [← ca_inj e1] at i2
            rw [← na_inj e3] at i3
            rw [← ca_inj e4, ← na_inj e5] at i4
            exact hno p1 p3 l1 l2 (fun h => hc (by rw [h])) (fun h => hy (by rw [h]))
              ⟨i1, i2, i3, i4⟩
          · exact ca_ne_na _ _ e4
        · exact ca_ne_na _ _ e3.symm
      · exact ca_ne_na _ _ e1
    · obtain ⟨p2, l2, i2, ⟨e1, _⟩ | ⟨e1, rfl⟩⟩ := h2
      · exact ca_ne_na _ _ e1.symm
      · obtain ⟨p3, l3, i3, ⟨_, e3⟩ | ⟨rfl, e3⟩⟩ := h3
        · exact ca_ne_na _ _ e3
        · obtain ⟨p4, l4, i4, ⟨e4, _⟩ | ⟨e4, e5⟩⟩ := h4
          · exact ca_ne_na _ _ e4.symm
          · rw [← na_inj e1] at i2
            rw [← ca_inj e3] at i3
            rw [← na_inj e4, ← ca_inj e5] at i4
            exact hno p1 p2 l1 l3 (fun h => hy (by rw [h])) (fun h => hc (by rw [h]))
              ⟨i1, i3, i2, i4⟩
  · intro u v
    have e : val C.gates (pr u v) C.output = circuitFun (x1 + x2) C (pr u v) := rfl
    rw [e, hF]
    simp only [pr, decide_eq_true_eq, adjI]
    constructor
    · rintro ⟨p, l, i, h1, h2⟩
      refine ⟨p, l, i, ?_⟩
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) (ca_ne_na p l)
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
      · exact absurd (h1.trans h2.symm) (ca_ne_na p l)
    · rintro ⟨p, l, i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨p, l, i, Or.inl rfl, Or.inr rfl⟩
      · exact ⟨p, l, i, Or.inr rfl, Or.inl rfl⟩

lemma inj_count {x1 x2 : ℕ} (I : Fin x1 → Fin x2 → Prop)
    (Dm : Fin (x1 + x2) → Finset (Fin (x1 + x2)))
    (hD : ∀ p l, I p l →
      Fin.natAdd x1 l ∈ Dm (Fin.castAdd x2 p) ∨ Fin.castAdd x2 p ∈ Dm (Fin.natAdd x1 l)) :
    (PEqualNP.ReadTwo.incid I).card ≤ ∑ c, (Dm c).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn
    (fun e => if Fin.natAdd x1 e.2 ∈ Dm (Fin.castAdd x2 e.1) then
      (⟨Fin.castAdd x2 e.1, Fin.natAdd x1 e.2⟩ : Σ _ : Fin (x1 + x2), Fin (x1 + x2))
      else ⟨Fin.natAdd x1 e.2, Fin.castAdd x2 e.1⟩) ?_ ?_
  · intro e he
    have he' : I e.1 e.2 := by simpa [PEqualNP.ReadTwo.incid] using he
    by_cases h : Fin.natAdd x1 e.2 ∈ Dm (Fin.castAdd x2 e.1)
    · simp [h]
    · rcases hD _ _ he' with h' | h'
      · exact absurd h' h
      · simp [h, h']
  · intro e _ e' _ hee
    dsimp only at hee
    by_cases h1 : Fin.natAdd x1 e.2 ∈ Dm (Fin.castAdd x2 e.1) <;>
      by_cases h2 : Fin.natAdd x1 e'.2 ∈ Dm (Fin.castAdd x2 e'.1)
    · rw [if_pos h1, if_pos h2] at hee
      obtain ⟨a, b⟩ := Sigma.mk.inj_iff.mp hee
      exact Prod.ext (ca_inj a) (na_inj (eq_of_heq b))
    · rw [if_pos h1, if_neg h2] at hee
      exact absurd (Sigma.mk.inj_iff.mp hee).1 (ca_ne_na _ _)
    · rw [if_neg h1, if_pos h2] at hee
      exact absurd (Sigma.mk.inj_iff.mp hee).1.symm (ca_ne_na _ _)
    · rw [if_neg h1, if_neg h2] at hee
      obtain ⟨a, b⟩ := Sigma.mk.inj_iff.mp hee
      exact Prod.ext (ca_inj (eq_of_heq b)) (na_inj a)

lemma main (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I] (C : Circuit)
    (hno : ∀ (a a' : Fin x1) (b b' : Fin x2), a ≠ a' → b ≠ b' →
      ¬ (I a b ∧ I a b' ∧ I a' b ∧ I a' b'))
    (hC : PEqualNP.TopForm.IsAO2 (x1 + x2) C)
    (hF : ∀ x : Fin (x1 + x2) → Bool, circuitFun (x1 + x2) C x =
      decide (∃ p l, I p l ∧ x (Fin.castAdd x2 p) = true ∧ x (Fin.natAdd x1 l) = true))
    (hPure : ∀ j, Reach (x1 + x2) C j C.output →
      Pure (x1 + x2) C (ia C (x1 + x2) j) ∧ Pure (x1 + x2) C (ib C (x1 + x2) j)) :
    ∃ K : Finset (Fin (x1 + x2)),
      (∀ p l, I p l → Fin.castAdd x2 p ∈ K ∨ Fin.natAdd x1 l ∈ K) ∧
      (PEqualNP.ReadTwo.incid I).card + K.card ≤ C.size + 1 := by
  classical
  have hF' : ∀ x : Fin (x1 + x2) → Bool, circuitFun (x1 + x2) C x = true ↔
      ∃ p l, I p l ∧ x (Fin.castAdd x2 p) = true ∧ x (Fin.natAdd x1 l) = true := by
    intro x
    rw [hF x, decide_eq_true_eq]
  have hG := good_of x1 x2 I C hno hC hF' hPure
  have hadj : ∀ p l, I p l → adjI I (Fin.castAdd x2 p) (Fin.natAdd x1 l) := by
    intro p l h
    exact ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩
  by_cases hex : ∃ p l, I p l
  · obtain ⟨p0, l0, h0⟩ := hex
    obtain ⟨K, Dm, hK, hD, hcnt⟩ := core (x1 + x2) C _ hG ⟨_, _, hadj p0 l0 h0⟩
    refine ⟨K, fun p l h => hK _ _ (hadj p l h), ?_⟩
    have := inj_count I Dm (fun p l h => hD _ _ (hadj p l h))
    show _ ≤ C.gates.length + 1
    omega
  · refine ⟨∅, fun p l h => absurd ⟨p, l, h⟩ hex, ?_⟩
    have : PEqualNP.ReadTwo.incid I = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e he
      simp only [PEqualNP.ReadTwo.incid, Finset.mem_filter] at he
      exact hex ⟨e.1, e.2, he.2⟩
    rw [this]
    simp

lemma main_finset (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hno : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hC : PEqualNP.TopForm.IsAO2 (p + l) C)
    (hF : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ a b, (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hPure : ∀ j, Reach (p + l) C j C.output →
      Pure (p + l) C (ia C (p + l) j) ∧ Pure (p + l) C (ib C (p + l) j)) :
    ∃ K : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ K ∨ Fin.natAdd p b ∈ K) ∧
      E.card + K.card ≤ C.size + 1 := by
  have h := main p l (fun a b => (a, b) ∈ E) C hno hC hF hPure
  have hE : PEqualNP.ReadTwo.incid (fun a b => (a, b) ∈ E) = E := by
    ext e
    simp [PEqualNP.ReadTwo.incid]
  simpa only [hE] using h

lemma pure_of_disjunction (n : ℕ) (C : Circuit) (w : ℕ) (T : Finset (Fin n))
    (h : ∀ x : Fin n → Bool, val C.gates x w = decide (∃ v ∈ T, x v = true)) :
    Pure n C w := by
  have hS : S n C w = T := by
    ext v
    rw [mem_S, h, decide_eq_true_eq]
    simp [eof]
  intro x
  rw [h, hS]

end SemanticNormal

end PEqualNP.Outside.L_meta_4970_aux

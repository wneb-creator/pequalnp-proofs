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


end PEqualNP.Outside.L_meta_4970_aux

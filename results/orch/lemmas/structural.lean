import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PEqualNP.Outside.L_meta_4970_aux.Structural

def IsIncreasing {α : Type*} (f : (α → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

lemma below_or_of_complement {α : Type*} [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool)
    (hf : IsIncreasing f)
    (hzero : f (fun i => decide (i ∉ Q)) ≠ true) :
    ∀ x, f x = true → ∃ i ∈ Q, x i = true := by
  intro x hx
  by_contra hn
  apply hzero
  apply hf x (fun i => decide (i ∉ Q)) _ hx
  intro i hi
  simp only [decide_eq_true_eq]
  intro hiQ
  exact hn ⟨i, hiQ, hi⟩

lemma and_below_or_child {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : IsIncreasing f) (hg : IsIncreasing g)
    (hbound : ∀ x, (f x && g x) = true → ∃ i ∈ Q, x i = true) :
    (∀ x, f x = true → ∃ i ∈ Q, x i = true) ∨
      (∀ x, g x = true → ∃ i ∈ Q, x i = true) := by
  let z : α → Bool := fun i => decide (i ∉ Q)
  have hz : ¬ (f z = true ∧ g z = true) := by
    intro h
    obtain ⟨i, hiQ, hiz⟩ := hbound z (by simp [h.1, h.2])
    simp [z, hiQ] at hiz
  by_cases h : f z = true
  · exact Or.inr (below_or_of_complement Q g hg (fun h' => hz ⟨h, h'⟩))
  · exact Or.inl (below_or_of_complement Q f hf h)

lemma and_eq_or_child {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : IsIncreasing f) (hg : IsIncreasing g)
    (heq : ∀ x, (f x && g x) = decide (∃ i ∈ Q, x i = true)) :
    (∀ x, f x = decide (∃ i ∈ Q, x i = true)) ∨
      (∀ x, g x = decide (∃ i ∈ Q, x i = true)) := by
  have hb : ∀ x, (f x && g x) = true → ∃ i ∈ Q, x i = true := by
    intro x hx
    rw [heq x] at hx
    exact of_decide_eq_true hx
  rcases and_below_or_child Q f g hf hg hb with h | h
  · left
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · exact h x
    · intro hx
      have hx' : (f x && g x) = true := by
        rw [heq x]
        exact decide_eq_true hx
      rw [Bool.and_eq_true] at hx'
      exact hx'.1
  · right
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · exact h x
    · intro hx
      have hx' : (f x && g x) = true := by
        rw [heq x]
        exact decide_eq_true hx
      rw [Bool.and_eq_true] at hx'
      exact hx'.2

lemma countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

lemma pure_or_rt_count {α : Type*} [DecidableEq α] [Fintype α]
    (k N : ℕ) (Q : Finset α)
    (W : ℕ → (α → Bool) → Bool) (S : ℕ → Finset α)
    (a b : ℕ → ℕ) (isAnd : ℕ → Bool)
    (hmono : ∀ w < N, IsIncreasing (W w))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hsupport : ∀ w < N, ∀ i,
      i ∈ S w ↔ W w (fun j => decide (j = i)) = true)
    (heval : ∀ w, k ≤ w → w < N → ∀ x,
      W w x = if isAnd w then (W (a w) x && W (b w) x)
        else (W (a w) x || W (b w) x))
    (R : Finset ℕ)
    (hR : ∀ w ∈ R, w < N ∧ (∀ x, W w x = true → ∃ i ∈ Q, x i = true)) :
    (R.biUnion S).card ≤ R.card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ isAnd w = false ∧
        1 < (S w).card ∧ ∀ x, W w x = true → ∃ i ∈ Q, x i = true)).card := by
  classical
  let below (w : ℕ) := ∀ x, W w x = true → ∃ i ∈ Q, x i = true
  let F (w : ℕ) := if w < N ∧ below w then S w else ∅
  let paid := (Finset.range N).filter fun w =>
    k ≤ w ∧ isAnd w = false ∧ 1 < (S w).card ∧ below w
  have hstep : ∀ w < N, 1 < (F w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ F w ⊆ cs.biUnion F ∧
        cs.card ≤ 1 + (if w ∈ paid then 1 else 0) := by
    intro w hw hlarge
    have hgood : w < N ∧ below w := by
      by_contra hn
      simp [F, hn] at hlarge
    have hF : F w = S w := ite_eq_left hgood
    have hk : k ≤ w := by
      by_contra hn
      have ht := hsmall w (by omega)
      rw [hF] at hlarge
      omega
    have ⟨ha, hb⟩ := hparents w hk hw
    cases hop : isAnd w with
    | true =>
      have hbound : ∀ x, (W (a w) x && W (b w) x) = true → ∃ i ∈ Q, x i = true := by
        intro x hx
        apply hgood.2 x
        simpa [heval w hk hw x, hop] using hx
      have hchoice := and_below_or_child Q (W (a w)) (W (b w))
        (hmono _ (ha.trans hw)) (hmono _ (hb.trans hw)) hbound
      have hsubA : S w ⊆ S (a w) := by
        intro i hi
        apply (hsupport _ (ha.trans hw) i).mpr
        have ht := (hsupport w hw i).mp hi
        rw [heval w hk hw, hop] at ht
        simp only [ite_true, Bool.and_eq_true] at ht
        exact ht.1
      have hsubB : S w ⊆ S (b w) := by
        intro i hi
        apply (hsupport _ (hb.trans hw) i).mpr
        have ht := (hsupport w hw i).mp hi
        rw [heval w hk hw, hop] at ht
        simp only [ite_true, Bool.and_eq_true] at ht
        exact ht.2
      rcases hchoice with hA | hB
      · have hFA : F (a w) = S (a w) := ite_eq_left ⟨ha.trans hw, hA⟩
        refine ⟨{a w}, by simpa using ha, ?_, by simp⟩
        simpa [hF, hFA] using hsubA
      · have hFB : F (b w) = S (b w) := ite_eq_left ⟨hb.trans hw, hB⟩
        refine ⟨{b w}, by simpa using hb, ?_, by simp⟩
        simpa [hF, hFB] using hsubB
    | false =>
      have hA : below (a w) := by
        intro x hx
        apply hgood.2 x
        simp [heval w hk hw x, hop, hx]
      have hB : below (b w) := by
        intro x hx
        apply hgood.2 x
        simp [heval w hk hw x, hop, hx]
      have hFA : F (a w) = S (a w) := ite_eq_left ⟨ha.trans hw, hA⟩
      have hFB : F (b w) = S (b w) := ite_eq_left ⟨hb.trans hw, hB⟩
      have hsub : S w ⊆ S (a w) ∪ S (b w) := by
        intro i hi
        have ht := (hsupport w hw i).mp hi
        rw [heval w hk hw, hop] at ht
        simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true] at ht
        rcases ht with ht | ht
        · exact Finset.mem_union_left _ ((hsupport _ (ha.trans hw) i).mpr ht)
        · exact Finset.mem_union_right _ ((hsupport _ (hb.trans hw) i).mpr ht)
      have hp : w ∈ paid := by
        simp only [paid, Finset.mem_filter, Finset.mem_range]
        exact ⟨hw, hk, hop, hF ▸ hlarge, hgood.2⟩
      refine ⟨{a w, b w}, ?_, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hv]
          exact Finset.mem_range.mpr hb
      · simpa [hF, hFA, hFB] using hsub
      · simp only [hp, ite_true]
        exact Finset.card_le_two
  have hRrange : R ⊆ Finset.range N := by
    intro w hw
    exact Finset.mem_range.mpr (hR w hw).1
  have hroots : R.biUnion F = R.biUnion S := by
    apply Finset.biUnion_congr rfl
    intro w hw
    exact ite_eq_left (hR w hw)
  have hpaid : Finset.range N ∩ paid = paid := by
    exact Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
  have hc := countUnion F paid N hstep R hRrange
  simpa only [hroots, hpaid] using hc

end PEqualNP.Outside.L_meta_4970_aux.Structural

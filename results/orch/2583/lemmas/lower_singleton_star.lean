import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def singletonTrace {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => f (pairInput u u) = true

theorem graphFun_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  have hzero : (decide (∃ a ∈ (∅ : Finset (Fin n)), pairInput u v a = true) : Bool) = false := by simp
  unfold graphFun
  rw [hzero]
  simp only [Bool.false_or, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have ha' : a = u ∨ a = v := of_decide_eq_true ha
    have hb' : b = u ∨ b = v := of_decide_eq_true hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact (by simpa using hab : False).elim
    · exact hab
    · exact hab.symm
    · exact (by simpa using hab : False).elim
  · intro huv
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

theorem singleton_le_pair_left {n : ℕ} (u v : Fin n) :
    pairInput u u ≤ pairInput u v := by
  intro w
  by_cases h : w = u <;> simp [pairInput, h]

theorem singleton_le_pair_right {n : ℕ} (u v : Fin n) :
    pairInput v v ≤ pairInput u v := by
  intro w
  by_cases h : w = v <;> simp [pairInput, h]

theorem clean_factor_cross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : (Fin n → Bool) → Bool) (ha : Monotone a) (hb : Monotone b)
    (hclean : ∀ x, a x = true → b x = true → graphFun G ∅ x = true)
    {u v : Fin n} (hu : u ∈ singletonTrace a) (hv : v ∈ singletonTrace b) :
    G.Adj u v := by
  have hua : a (pairInput u u) = true := (Finset.mem_filter.mp hu).2
  have hvb : b (pairInput v v) = true := (Finset.mem_filter.mp hv).2
  have hap : a (pairInput u v) = true := by
    have h := ha (singleton_le_pair_left u v)
    cases he : a (pairInput u v) <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) h
  have hbp : b (pairInput u v) = true := by
    have h := hb (singleton_le_pair_right u v)
    cases he : b (pairInput u v) <;> simp_all
    exact (by decide : ¬ (true : Bool) ≤ false) h
  exact (graphFun_pair_iff G u v).mp (hclean _ hap hbp)

theorem rectangle_is_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hnofour : NoFourCycle G) (A B : Finset (Fin n))
    (hcross : ∀ u ∈ A, ∀ v ∈ B, G.Adj u v) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases hA : A.card ≤ 1
  · exact Or.inl hA
  · right
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    apply le_trans (Finset.card_le_card (s := B) (t := Finset.univ.filter
      fun w => G.Adj u w ∧ G.Adj v w) ?_) (hnofour u v huv)
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcross u hu w hw, hcross v hv w hw⟩

theorem clean_factor_singletons_disjoint {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (a b : (Fin n → Bool) → Bool)
    (ha : Monotone a) (hb : Monotone b)
    (hclean : ∀ x, a x = true → b x = true → graphFun G ∅ x = true) :
    Disjoint (singletonTrace a) (singletonTrace b) := by
  apply Finset.disjoint_left.mpr
  intro u hu hv
  have h := clean_factor_cross G a b ha hb hclean hu hv
  simpa using h

theorem clean_factor_singletons_star {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hnofour : NoFourCycle G)
    (a b : (Fin n → Bool) → Bool) (ha : Monotone a) (hb : Monotone b)
    (hclean : ∀ x, a x = true → b x = true → graphFun G ∅ x = true) :
    (singletonTrace a).card ≤ 1 ∨ (singletonTrace b).card ≤ 1 := by
  apply rectangle_is_star G hnofour
  intro u hu v hv
  exact clean_factor_cross G a b ha hb hclean hu hv

end PEqualNP.Outside.L_meta_2583_aux

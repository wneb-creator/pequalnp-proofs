import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.NestedJoint

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

lemma nested_joint_guarded {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (g h : ℕ) (R S : Finset (Fin n)) (a b : Bool)
    (hsem : ∀ x : Fin n → Bool, gateVal n C h x =
      ((decide (∃ r ∈ R, x r = true) || (a && gateVal n C g x)) &&
        (decide (∃ s ∈ S, x s = true) || (b && gateVal n C g x))))
    (hjoint : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C h x = true → graphFun G ∅ x = true)
    (hused : a = true ∨ b = true) (u v : Fin n)
    (hguv : gateVal n C g (pairInput u v) = true)
    (hhuv : gateVal n C h (pairInput u v) = true) :
    u ∈ wmax G C g ∨ v ∈ wmax G C g := by
  have hR (ha : a = false) (hb : b = true) (r : Fin n) (hr : r ∈ R) :
      r ∈ wmax G C g := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ r, ?_⟩
    intro x hgx hrx
    apply hjoint x hgx
    rw [hsem]
    have hRx : decide (∃ r ∈ R, x r = true) = true := decide_eq_true ⟨r, hr, hrx⟩
    simp [ha, hb, hgx, hRx]
  have hS (ha : a = true) (hb : b = false) (s : Fin n) (hs : s ∈ S) :
      s ∈ wmax G C g := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ s, ?_⟩
    intro x hgx hsx
    apply hjoint x hgx
    rw [hsem]
    have hSx : decide (∃ s ∈ S, x s = true) = true := decide_eq_true ⟨s, hs, hsx⟩
    simp [ha, hb, hgx, hSx]
  cases ha : a with
  | false =>
    have hb : b = true := hused.resolve_left (by simp [ha])
    have hh := hhuv
    rw [hsem] at hh
    simp only [ha, hb, hguv, Bool.false_and, Bool.or_false, Bool.true_and,
      Bool.or_true, Bool.and_true, decide_eq_true_eq] at hh
    obtain ⟨r, hr, hrv⟩ := hh
    have hrw := hR ha hb r hr
    simp only [pairInput, decide_eq_true_eq] at hrv
    rcases hrv with rfl | rfl <;> simp [hrw]
  | true =>
    cases hb : b with
    | false =>
      have hh := hhuv
      rw [hsem] at hh
      simp only [ha, hb, hguv, Bool.false_and, Bool.or_false, Bool.true_and,
        Bool.or_true, decide_eq_true_eq] at hh
      obtain ⟨s, hs, hsv⟩ := hh
      have hsw := hS ha hb s hs
      simp only [pairInput, decide_eq_true_eq] at hsv
      rcases hsv with rfl | rfl <;> simp [hsw]
    | true =>
      left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ u, ?_⟩
      intro x hgx _
      apply hjoint x hgx
      rw [hsem]
      simp [ha, hb, hgx]

lemma nested_joint_unguarded_coefficients {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (g h : ℕ) (R S : Finset (Fin n)) (a b : Bool)
    (hsem : ∀ x : Fin n → Bool, gateVal n C h x =
      ((decide (∃ r ∈ R, x r = true) || (a && gateVal n C g x)) &&
        (decide (∃ s ∈ S, x s = true) || (b && gateVal n C g x))))
    (hjoint : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C h x = true → graphFun G ∅ x = true)
    (u v : Fin n) (hguv : gateVal n C g (pairInput u v) = true)
    (hhuv : gateVal n C h (pairInput u v) = true)
    (hfree : u ∉ wmax G C g ∧ v ∉ wmax G C g) : a = false ∧ b = false := by
  have hnot : ¬ (a = true ∨ b = true) := by
    intro hused
    exact (nested_joint_guarded g h R S a b hsem hjoint hused u v hguv hhuv).elim
      hfree.1 hfree.2
  cases a <;> cases b <;> simp_all

end PEqualNP.Outside.L_meta_5012.NestedJoint

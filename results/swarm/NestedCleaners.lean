import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.NestedCleaners

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

lemma bool_eq_of_ne {p q r : Bool} (hp : p ≠ r) (hq : q ≠ r) : p = q := by
  cases p <;> cases q <;> cases r <;> simp_all

lemma wmax_two_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (a b : Fin n) (hab : ¬ G.Adj a b)
    (hmono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      gateVal n C g x = true → gateVal n C g y = true)
    (hg : gateVal n C g (pairInput a b) = true) :
    ∀ w ∈ wmax G C g, G.Adj a w ∨ G.Adj b w := by
  intro w hw
  let x : Fin n → Bool := fun i => decide (i = a ∨ i = b ∨ i = w)
  have hgx : gateVal n C g x = true := hmono (pairInput a b) x (by
    intro i hi
    simp only [pairInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl <;> simp [x]) hg
  have hf := (Finset.mem_filter.mp hw).2 x hgx (by simp [x])
  have he : ∃ u v, G.Adj u v ∧ (u = a ∨ u = b ∨ u = w) ∧
      (v = a ∨ v = b ∨ v = w) := by
    simpa [graphFun, x] using hf
  obtain ⟨u, v, huv, hu, hv⟩ := he
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  all_goals first
    | exact False.elim (G.irrefl huv)
    | exact False.elim (hab huv)
    | exact False.elim (hab huv.symm)
    | (have hsym := huv.symm; tauto)

lemma dirty_pair_endpoints_not_wmax {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (g : ℕ) (a b : Fin n)
    (hg : gateVal n C g (pairInput a b) = true)
    (hf : graphFun G ∅ (pairInput a b) = false) :
    a ∉ wmax G C g ∧ b ∉ wmax G C g := by
  constructor
  · intro ha
    have hh := (Finset.mem_filter.mp ha).2 (pairInput a b) hg (by simp [pairInput])
    rw [hf] at hh
    cases hh
  · intro hb
    have hh := (Finset.mem_filter.mp hb).2 (pairInput a b) hg (by simp [pairInput])
    rw [hf] at hh
    cases hh

lemma two_star_degree_same_color {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (W : Finset (Fin n))
    (a b v : Fin n) (hab : s a ≠ s b) (hva : v ≠ a) (hsv : s v = s a)
    (hW : ∀ w ∈ W, G.Adj a w ∨ G.Adj b w) :
    (W.filter fun w => G.Adj v w).card ≤ 1 := by
  have hsub : (W.filter fun w => G.Adj v w) ⊆
      Finset.univ.filter (fun w => G.Adj v w ∧ G.Adj a w) := by
    intro w hw
    obtain ⟨hwW, hvw⟩ := Finset.mem_filter.mp hw
    have haw : G.Adj a w := by
      rcases hW w hwW with haw | hbw
      · exact haw
      · have heq : s v = s b := bool_eq_of_ne (hbip v w hvw) (hbip b w hbw)
        exact False.elim (hab (hsv.symm.trans heq))
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hvw, haw⟩
  exact (Finset.card_le_card hsub).trans (h4 v a hva)

lemma two_star_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (W : Finset (Fin n))
    (a b v : Fin n) (hab : s a ≠ s b) (hva : v ≠ a) (hvb : v ≠ b)
    (hW : ∀ w ∈ W, G.Adj a w ∨ G.Adj b w) :
    (W.filter fun w => G.Adj v w).card ≤ 1 := by
  by_cases hs : s v = s a
  · exact two_star_degree_same_color G h4 s hbip W a b v hab hva hs hW
  · have hsv : s v = s b := bool_eq_of_ne hs (Ne.symm hab)
    exact two_star_degree_same_color G h4 s hbip W b a v (Ne.symm hab) hvb hsv
      (fun w hw => (hW w hw).symm)

lemma dirty_cross_pair_wmax_degree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (C : Circuit) (g : ℕ)
    (a b : Fin n) (hab : ¬ G.Adj a b) (hsab : s a ≠ s b)
    (hmono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      gateVal n C g x = true → gateVal n C g y = true)
    (hg : gateVal n C g (pairInput a b) = true) :
    ∀ v : Fin n, v ≠ a → v ≠ b →
      ((wmax G C g).filter fun w => G.Adj v w).card ≤ 1 := by
  intro v hva hvb
  exact two_star_degree G h4 s hbip (wmax G C g) a b v hsab hva hvb
    (wmax_two_star G C g a b hab hmono hg)

lemma dirty_cross_pair_wmax_induced_degree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (C : Circuit) (g : ℕ)
    (a b : Fin n) (hab : ¬ G.Adj a b) (hsab : s a ≠ s b)
    (hmono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      gateVal n C g x = true → gateVal n C g y = true)
    (hg : gateVal n C g (pairInput a b) = true)
    (hf : graphFun G ∅ (pairInput a b) = false) :
    ∀ v ∈ wmax G C g, ((wmax G C g).filter fun w => G.Adj v w).card ≤ 1 := by
  intro v hv
  obtain ⟨ha, hb⟩ := dirty_pair_endpoints_not_wmax G C g a b hg hf
  exact dirty_cross_pair_wmax_degree G h4 s hbip C g a b hab hsab hmono hg v
    (fun he => ha (he ▸ hv)) (fun he => hb (he ▸ hv))

end PEqualNP.Outside.L_meta_5012.NestedCleaners

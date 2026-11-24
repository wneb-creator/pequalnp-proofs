import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5349_aux

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

lemma neighbor_cover_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (A S : Finset (Fin n)) (v : Fin n)
    (hv : v ∉ S) (hadj : ∀ u ∈ A, G.Adj u v)
    (hcover : ∀ u ∈ A, ∃ w ∈ S, G.Adj u w) : A.card ≤ S.card := by
  classical
  choose w hwS hwa using hcover
  let f : A → S := fun u => ⟨w u.val u.property, hwS u.val u.property⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro u z heq
  apply Subtype.ext
  by_contra hne
  have hbound := h4 u.val z.val hne
  have hw : w u.val u.property = w z.val z.property := congrArg Subtype.val heq
  have hfirst : v ∈ Finset.univ.filter (fun t => G.Adj u.val t ∧ G.Adj z.val t) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hadj u.val u.property, hadj z.val z.property⟩
  have hsecond : w u.val u.property ∈
      Finset.univ.filter (fun t => G.Adj u.val t ∧ G.Adj z.val t) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hwa u.val u.property, hw.symm ▸ hwa z.val z.property⟩
  have he := Finset.card_le_one.mp hbound v hfirst (w u.val u.property) hsecond
  exact hv (he.symm ▸ hwS u.val u.property)

lemma wmax_dirty_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (S : Finset (Fin n))
    (hmono : ∀ (x y : Fin n → Bool), (∀ v, x v = true → y v = true) →
      gateVal n C g x = true → gateVal n C g y = true)
    (hS : ∀ p ∈ S, ∀ q ∈ S, ¬ G.Adj p q)
    (hg : gateVal n C g (fun p => decide (p ∈ S)) = true)
    {u : Fin n} (hu : u ∈ wmax G C g) : ∃ w ∈ S, G.Adj u w := by
  let x : Fin n → Bool := fun p => decide (p ∈ S ∨ p = u)
  have hx : gateVal n C g x = true := hmono _ x (by
    intro p hp
    simp only [decide_eq_true_eq] at hp
    simp only [x, decide_eq_true_eq]
    exact Or.inl hp) hg
  have hF := (Finset.mem_filter.mp hu).2 x hx (by simp [x])
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨p, q, hpq, hp, hq⟩ := hF
  simp only [x, decide_eq_true_eq] at hp hq
  rcases hp with hp | rfl <;> rcases hq with hq | rfl
  · exact (hS p hp q hq hpq).elim
  · exact ⟨p, hp, hpq.symm⟩
  · exact ⟨q, hq, hpq⟩
  · exact (G.irrefl hpq).elim

lemma dirty_witness_fiber_card {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (g : ℕ) (A S : Finset (Fin n)) (v : Fin n)
    (h4 : NoFourCycle G)
    (hmono : ∀ (x y : Fin n → Bool), (∀ z, x z = true → y z = true) →
      gateVal n C g x = true → gateVal n C g y = true)
    (hS : ∀ p ∈ S, ∀ q ∈ S, ¬ G.Adj p q)
    (hg : gateVal n C g (fun p => decide (p ∈ S)) = true)
    (hv : v ∉ S) (hA : A ⊆ wmax G C g)
    (hadj : ∀ u ∈ A, G.Adj u v) : A.card ≤ S.card := by
  exact neighbor_cover_card G h4 A S v hv hadj
    (fun u hu => wmax_dirty_cover G C g S hmono hS hg (hA hu))

end PEqualNP.Outside.L_meta_5349_aux

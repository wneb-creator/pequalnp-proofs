import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1770_aux

lemma distinct_junk_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hcard : (PEqualNP.TopForm.junk G C).card ≤ 1)
    {g h : ℕ} (hg : g ∈ PEqualNP.TopForm.junk G C)
    (hh : h ∈ PEqualNP.TopForm.junk G C) (hne : g ≠ h) : False := by
  exact hne (Finset.card_le_one.mp hcard g hg h hh)

lemma residual_empty_of_junk_card_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hcard : (PEqualNP.TopForm.junk G C).card ≤ 1) :
    {x9 ∈ PEqualNP.TopForm.Ustar G C | (¬∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops G C, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk G C, x10 ∈ PEqualNP.TopForm.side C x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true) ∧ ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops G C, ∃ x13 ∈ PEqualNP.TopForm.junk G C, ∃ x14 ∈ PEqualNP.TopForm.junk G C, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal n C x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true} = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  rw [Finset.mem_filter] at he
  obtain ⟨_, _, u, v, _, a, ha, g, hg, h, hh, hne, _⟩ := he
  exact distinct_junk_impossible G C hcard hg hh hne

end PEqualNP.Outside.L_meta_1770_aux

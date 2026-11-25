import Mathlib

namespace PEqualNP.Outside.L_meta_2056_aux.RectangleCover

open scoped BigOperators

lemma star_weight {r : Nat} (hr : r ≤ 4) : 5 * r ≤ 4 * (r + 1) := by
  omega

lemma proper_weight {r c : Nat}
    (h : (r ≤ 3 ∧ 4 ≤ c) ∨ (r ≤ 4 ∧ 5 ≤ c)) : 5 * r ≤ 4 * c := by
  rcases h with h | h <;> omega

lemma cover_cost_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pieces : ι → Finset (Fin 52)) (cost : ι → Nat)
    (hall : Finset.univ.biUnion pieces = Finset.univ)
    (hcost : ∀ i, 5 * (pieces i).card ≤ 4 * cost i) :
    65 ≤ ∑ i, cost i := by
  have hcard : 52 ≤ ∑ i, (pieces i).card := by
    have h := Finset.card_biUnion_le (s := Finset.univ) (t := pieces)
    simpa [hall] using h
  have hsum : (∑ i, 5 * (pieces i).card) ≤ ∑ i, 4 * cost i :=
    Finset.sum_le_sum (fun i _ => hcost i)
  simp only [← Finset.mul_sum] at hsum
  omega

lemma no_cover_cost_at_most_sixty_four {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pieces : ι → Finset (Fin 52)) (cost : ι → Nat)
    (hall : Finset.univ.biUnion pieces = Finset.univ)
    (hcost : ∀ i, 5 * (pieces i).card ≤ 4 * cost i)
    (small : (∑ i, cost i) ≤ 64) : False := by
  have h := cover_cost_lower pieces cost hall hcost
  omega

end PEqualNP.Outside.L_meta_2056_aux.RectangleCover

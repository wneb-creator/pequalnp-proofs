import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031

lemma common_neighbor_nonadjacent {α : Type*} (G : SimpleGraph α)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    {a b c : α} (hac : G.Adj a c) (hbc : G.Adj b c) : ¬ G.Adj a b := by
  intro hab
  exact htri a b c hab hbc hac.symm

abbrev fiveCycle : SimpleGraph (Fin 5) :=
  PEqualNP.EdgeOwnership.edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

lemma fiveCycle_no_triangles :
    ∀ a b c : Fin 5, fiveCycle.Adj a b → fiveCycle.Adj b c → ¬ fiveCycle.Adj c a := by
  decide

lemma fiveCycle_no_four_cycles :
    ∀ a b c d : Fin 5, fiveCycle.Adj a b → fiveCycle.Adj b c →
      fiveCycle.Adj c d → fiveCycle.Adj d a → a = c ∨ b = d := by
  decide

lemma two_common_neighbor_steps_do_not_force_nonadjacency :
    ¬ (∀ a b c d e : Fin 5,
      fiveCycle.Adj a b → fiveCycle.Adj b c → fiveCycle.Adj c d →
      fiveCycle.Adj d e → ¬ fiveCycle.Adj e a) := by
  intro h
  exact h 0 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)

end PEqualNP.Outside.L_meta_1031

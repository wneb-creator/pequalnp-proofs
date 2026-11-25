import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux

abbrev fiveCycle : SimpleGraph (Fin 5) :=
  PEqualNP.EdgeOwnership.edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

lemma fiveCycle_triangleFree :
    ∀ a b c : Fin 5, fiveCycle.Adj a b → fiveCycle.Adj b c → ¬ fiveCycle.Adj c a := by
  decide

lemma fiveCycle_noFourCycle : PEqualNP.TopForm.NoFourCycle fiveCycle := by
  decide

lemma fiveCycle_parityObstruction :
    fiveCycle.Adj 0 1 ∧ fiveCycle.Adj 2 1 ∧ fiveCycle.Adj 2 3 ∧
      fiveCycle.Adj 4 3 ∧ fiveCycle.Adj 0 4 := by
  decide

lemma triangleFree_noFourCycle_doesNotExcludeOddClosedWalk :
    ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      PEqualNP.TopForm.NoFourCycle G →
      ∀ a b c d e : Fin n, G.Adj a c → G.Adj b c → G.Adj b d →
        G.Adj e d → ¬ G.Adj a e) := by
  intro h
  obtain ⟨h01, h21, h23, h43, h04⟩ := fiveCycle_parityObstruction
  exact h 5 fiveCycle fiveCycle_triangleFree fiveCycle_noFourCycle 0 2 1 3 4
    h01 h21 h23 h43 h04

end PEqualNP.Outside.L_meta_1772_aux

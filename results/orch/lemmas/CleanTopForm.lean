import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.CleanTopForm

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover

lemma singleton_false (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : graphFun G ∅ (PEqualNP.SplitCount.unitInput v) = false := by
  simp [graphFun, PEqualNP.SplitCount.unitInput]

lemma no_nested_and (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (htop : TopForm G C)
    (hclean : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i) :
    ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and → ¬ InCone n C i j := by
  intro i hi j hj hopi hopj
  exact htop i hi j hj hopi (hclean i hi hopi) hopj

lemma and_singleton_false (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (hclean : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i) :
    ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → ∀ v : Fin n,
      gateVal n C i (PEqualNP.SplitCount.unitInput v) = false := by
  intro i hi hop v
  cases hv : gateVal n C i (PEqualNP.SplitCount.unitInput v) with
  | false => rfl
  | true =>
    have h := hclean i hi hop (PEqualNP.SplitCount.unitInput v) hv
    rw [singleton_false n G v] at h
    cases h

end PEqualNP.Outside.L_meta_2585.CleanTopForm

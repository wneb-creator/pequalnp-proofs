import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.CleanJunk

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover

lemma all_and_below_of_junk_empty (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hJ : junk G C = ∅) :
    ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i := by
  intro i hi hop x hx
  cases hF : graphFun G ∅ x with
  | true => rfl
  | false =>
    have hmem : i ∈ junk G C := by
      simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨hi, hop, hi, x, hx, hF⟩
    have hnot : i ∉ junk G C := by simp [hJ]
    exact False.elim (hnot hmem)

end PEqualNP.Outside.L_meta_2585.CleanJunk

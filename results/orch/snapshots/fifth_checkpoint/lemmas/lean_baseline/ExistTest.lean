import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650
lemma edge_case_test (x : Fin 26 → Bool) :
    (∃ u v : Fin 26, (u.val, v.val) = (0, 13) ∧ x u = true ∧ x v = true) ↔
    x 0 = true ∧ x 13 = true := by
  simp [Prod.mk.injEq, Fin.exists_iff]
end PEqualNP.Outside.L_meta_650

import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231_aux

def edgeEnds : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def canonicalEdges : Fin 3 → Fin 3 → Fin 6 :=
  ![![0,1,2], ![0,1,3], ![0,3,5]]

def SameUnorderedEnds (a b : Fin 4 × Fin 4) : Prop :=
  (a.1 = b.1 ∧ a.2 = b.2) ∨ (a.1 = b.2 ∧ a.2 = b.1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem three_edge_orbits :
    ∀ pick : Fin 3 → Fin 6, Function.Injective pick →
      ∃ p : Equiv.Perm (Fin 4), ∃ q : Equiv.Perm (Fin 3), ∃ kind : Fin 3,
        ∀ k : Fin 3, SameUnorderedEnds
          (p (edgeEnds (pick (q k))).1, p (edgeEnds (pick (q k))).2)
          (edgeEnds (canonicalEdges kind k)) := by
  unfold SameUnorderedEnds
  decide

end PEqualNP.Outside.L_gct_231_aux

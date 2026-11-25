import PrunedCopyFixture0Initial
import PrunedSound

namespace PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0

theorem completed_live_exclusion : Impossible false graph 12 (roots0.image nodeRaw0) := by
  intro k bound run
  obtain ⟨label, part, entries, traces, supports⟩ := initial_certificate
  have cap : k + 1 ≤ (roots0.image nodeRaw0).card + 1 := by
    rw [raw_card]
    omega
  exact pruned_node_exclusion_state (pairColumn false) (pairColumn false graph) false graph
    (pairColumn_gate false) (pairColumn_cover false graph) k
    (Fin 12) roots0 nodeRaw0 (entryCert entries0) 1 completedPrunedNode
    (roots0.image nodeRaw0) run cap label part entries traces supports

end PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0

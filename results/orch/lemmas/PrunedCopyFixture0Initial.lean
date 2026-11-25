import PrunedCopyFixture0Node
import InitialRawState
import PairColumnSemantics

namespace PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem raw_distinct : Set.InjOn nodeRaw0 (↑roots0 : Set (Fin 12)) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem raw_card : (roots0.image nodeRaw0).card = 12 := by
  decide +kernel

theorem initial_certificate : ∃ label : Sig → Finset (Fin 12),
    LabelPartition roots0 (roots0.image nodeRaw0) label ∧
    (∀ v ∈ roots0.image nodeRaw0, entryCert entries0 (label v) v) ∧
    (∀ v ∈ roots0.image nodeRaw0, ReadOnce nodeRaw0 false (label v) v) ∧
    (∀ v ∈ roots0.image nodeRaw0, ColumnSupport nodeRaw0 (pairColumn false) (label v) v) :=
  initial_raw_state roots0 nodeRaw0 (pairColumn false) (entryCert entries0) false
    raw_distinct (entryLeafCheck_sound checkedLeaves0)

end PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0

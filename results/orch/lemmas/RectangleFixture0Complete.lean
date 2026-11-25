import RectangleFixture0Children
import EntryTableAdapters
import InitialRawState
import PairColumnSemantics
import PrunedSound

namespace PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0

def rootLabels0 : List (Fin 12) := [0,1,2,3,4,5,6,7,8,9,10,11]
def roots0 : Finset (Fin 12) := rootLabels0.toFinset
def nodeRaw0 : Fin 12 → Sig := RectangleFixture0Children.baseRaw
def entries0 : List (Entry (Fin 12)) := RectangleFixture0Children.entries
def cuts0 : List (Entry (Fin 12)) := []
def rows0 : List (Row × Row) :=
  [(17,116),(6,773),(24,104),(12,773),(528,116),(640,773),
   (132,201),(17,402),(33,201),(288,116),(6,116),(640,385),
   (6,50),(24,208),(66,201),(320,385),(24,138),(264,201)]

theorem roots_eq : roots0 = RectangleFixture0Children.baseRoots := by decide +kernel

theorem cutsSound0 : ∀ A v, (A,v) ∈ cuts0 →
    BudgetRunCut (compressRoots roots0 A) (duplicateRaw nodeRaw0 v) false graph 1 := by
  intro A v h
  simp [cuts0] at h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves0 : entryLeafCheck rootLabels0 nodeRaw0 entries0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates0 :
    entryGateCheck false graph rootLabels0 nodeRaw0 entries0 cuts0 rows0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing0 : (roots0, graph) ∉ entries0 := by decide +kernel

theorem completedPrunedNode :
    PrunedNode (pairColumn false) (pairColumn false graph) false graph 1
      (Fin 12) roots0 nodeRaw0 (entryCert entries0) := by
  refine ⟨entryLeafCheck_sound checkedLeaves0,
    entryGateCheck_sound cutsSound0 checkedGates0, checkedMissing0, ?_⟩
  intro A w sub hp member
  apply Or.inl
  simpa only [roots_eq, nodeRaw0] using RectangleFixture0Children.entry_cuts member

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem raw_distinct : Set.InjOn nodeRaw0 (↑roots0 : Set (Fin 12)) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem raw_card : (roots0.image nodeRaw0).card = 12 := by decide +kernel

theorem initial_certificate : ∃ label : Sig → Finset (Fin 12),
    LabelPartition roots0 (roots0.image nodeRaw0) label ∧
    (∀ v ∈ roots0.image nodeRaw0, entryCert entries0 (label v) v) ∧
    (∀ v ∈ roots0.image nodeRaw0, ReadOnce nodeRaw0 false (label v) v) ∧
    (∀ v ∈ roots0.image nodeRaw0, ColumnSupport nodeRaw0 (pairColumn false) (label v) v) :=
  initial_raw_state roots0 nodeRaw0 (pairColumn false) (entryCert entries0) false
    raw_distinct (entryLeafCheck_sound checkedLeaves0)

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

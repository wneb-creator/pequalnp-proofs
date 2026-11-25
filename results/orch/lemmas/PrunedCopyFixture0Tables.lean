import EntryTableAdapters
import PrunedCopyFixture0Cuts

namespace PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0

abbrev ChildLabel := Sum (Fin 12) Bool

def rootLabels0 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def roots0 : Finset (Fin 12) := rootLabels0.toFinset
def nodeRaw0 (i : Fin 12) : Sig := [s1, s11, s3, s4, s5, s14, s6, s7, s15, s8, s16, s9].getD i.val zero
def entries0 : List (Entry (Fin 12)) := [({0}, s1), ({1}, s11), ({2}, s3), ({3}, s4), ({4}, s5), ({5}, s14), ({6}, s6), ({7}, s7), ({8}, s15), ({9}, s8), ({10}, s16), ({11}, s9), ({5, 8}, s18)]
def cuts0 : List (Entry (Fin 12)) := []
def rows0 : List (Row × Row) := [(17, 116), (6, 773), (24, 104), (12, 773), (528, 116), (640, 773), (132, 201), (17, 402), (33, 201), (288, 116), (6, 116), (640, 385), (6, 50), (24, 208), (66, 201), (320, 385), (24, 138), (264, 201)]

theorem cutsSound0 : ∀ A v, (A, v) ∈ cuts0 →
    BudgetRunCut (compressRoots roots0 A) (duplicateRaw nodeRaw0 v) false graph 1 := by
  intro A v h
  simp [cuts0] at h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves0 : entryLeafCheck rootLabels0 nodeRaw0 entries0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates0 : entryGateCheck false graph rootLabels0 nodeRaw0 entries0 cuts0 rows0 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing0 : (roots0, graph) ∉ entries0 := by
  decide +kernel

theorem closed0 : PrunedGateClosed roots0 nodeRaw0 (pairColumn false)
    (pairColumn false graph) (entryCert entries0) false graph 1 :=
  entryGateCheck_sound cutsSound0 checkedGates0

def rootLabels1 : List (ChildLabel) := [(Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]
def roots1 : Finset (ChildLabel) := rootLabels1.toFinset
def nodeRaw1 : ChildLabel → Sig := duplicateRaw nodeRaw0 s1
def entries1 : List (Entry (ChildLabel)) := [({(Sum.inl 1)}, s11), ({(Sum.inl 2)}, s3), ({(Sum.inl 3)}, s4), ({(Sum.inl 4)}, s5), ({(Sum.inl 5)}, s14), ({(Sum.inl 6)}, s6), ({(Sum.inl 7)}, s7), ({(Sum.inl 8)}, s15), ({(Sum.inl 9)}, s8), ({(Sum.inl 10)}, s16), ({(Sum.inl 11)}, s9), ({(Sum.inr false)}, s1), ({(Sum.inr true)}, s1), ({(Sum.inl 5), (Sum.inl 8)}, s18), ({(Sum.inl 4), (Sum.inr false)}, s19), ({(Sum.inl 7), (Sum.inr false)}, s20), ({(Sum.inl 9), (Sum.inr false)}, s21), ({(Sum.inl 10), (Sum.inr false)}, s23), ({(Sum.inl 4), (Sum.inr true)}, s19), ({(Sum.inl 7), (Sum.inr true)}, s20), ({(Sum.inl 9), (Sum.inr true)}, s21), ({(Sum.inl 10), (Sum.inr true)}, s23)]
def cuts1 : List (Entry (ChildLabel)) := [({(Sum.inl 10), (Sum.inr false)}, s22), ({(Sum.inl 10), (Sum.inr true)}, s22), ({(Sum.inl 9), (Sum.inl 10), (Sum.inr false)}, s24), ({(Sum.inl 9), (Sum.inl 10), (Sum.inr true)}, s24)]
def rows1 : List (Row × Row) := [(132, 773), (33, 385), (17, 402), (288, 116), (24, 402), (24, 138), (17, 116), (528, 402), (12, 201), (320, 402), (6, 50), (33, 554), (528, 116), (12, 69), (24, 104), (33, 201), (12, 773), (17, 208), (264, 201)]

theorem budgetCut2 : BudgetRunCut (compressRoots roots1 {(Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw1 s22) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs2 (by decide) (by decide) (by rfl)
    false graph 0 11 (by decide)
  exact fun k bound => cutRun2 bound

theorem budgetCut3 : BudgetRunCut (compressRoots roots1 {(Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw1 s22) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs3 (by decide) (by decide) (by rfl)
    false graph 0 11 (by decide)
  exact fun k bound => cutRun3 bound

theorem budgetCut4 : BudgetRunCut (compressRoots roots1 {(Sum.inl 9), (Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw1 s24) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs4 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun4 bound

theorem budgetCut5 : BudgetRunCut (compressRoots roots1 {(Sum.inl 9), (Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw1 s24) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs5 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun5 bound

theorem cutsSound1 : ∀ A v, (A, v) ∈ cuts1 →
    BudgetRunCut (compressRoots roots1 A) (duplicateRaw nodeRaw1 v) false graph 0 := by
  intro A v h
  simp only [cuts1, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1 | h2 | h3
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    exact budgetCut2
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact budgetCut3
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact budgetCut4
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    exact budgetCut5

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves1 : entryLeafCheck rootLabels1 nodeRaw1 entries1 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates1 : entryGateCheck false graph rootLabels1 nodeRaw1 entries1 cuts1 rows1 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing1 : (roots1, graph) ∉ entries1 := by
  decide +kernel

theorem closed1 : PrunedGateClosed roots1 nodeRaw1 (pairColumn false)
    (pairColumn false graph) (entryCert entries1) false graph 0 :=
  entryGateCheck_sound cutsSound1 checkedGates1

theorem childNode1 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots1 nodeRaw1 (entryCert entries1) :=
  prunedNode_zero_of_checks rootLabels1 nodeRaw1 false graph entries1 cuts1 rows1
    cutsSound1 checkedLeaves1 checkedGates1 checkedMissing1

def rootLabels2 : List (ChildLabel) := [(Sum.inl 0), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]
def roots2 : Finset (ChildLabel) := rootLabels2.toFinset
def nodeRaw2 : ChildLabel → Sig := duplicateRaw nodeRaw0 s11
def entries2 : List (Entry (ChildLabel)) := [({(Sum.inl 0)}, s1), ({(Sum.inl 2)}, s3), ({(Sum.inl 3)}, s4), ({(Sum.inl 4)}, s5), ({(Sum.inl 5)}, s14), ({(Sum.inl 6)}, s6), ({(Sum.inl 7)}, s7), ({(Sum.inl 8)}, s15), ({(Sum.inl 9)}, s8), ({(Sum.inl 10)}, s16), ({(Sum.inl 11)}, s9), ({(Sum.inr false)}, s11), ({(Sum.inr true)}, s11), ({(Sum.inl 5), (Sum.inl 8)}, s18), ({(Sum.inl 5), (Sum.inr false)}, s25), ({(Sum.inl 10), (Sum.inr false)}, s26), ({(Sum.inl 10), (Sum.inr false)}, s27), ({(Sum.inl 5), (Sum.inr true)}, s25), ({(Sum.inl 10), (Sum.inr true)}, s26), ({(Sum.inl 10), (Sum.inr true)}, s27)]
def cuts2 : List (Entry (ChildLabel)) := [({(Sum.inl 5), (Sum.inl 8), (Sum.inr false)}, s28), ({(Sum.inl 5), (Sum.inl 10), (Sum.inr false)}, s29), ({(Sum.inl 0), (Sum.inl 10), (Sum.inr false)}, s30), ({(Sum.inl 5), (Sum.inl 8), (Sum.inr true)}, s28), ({(Sum.inl 5), (Sum.inl 10), (Sum.inr true)}, s29), ({(Sum.inl 0), (Sum.inl 10), (Sum.inr true)}, s30)]
def rows2 : List (Row × Row) := [(17, 402), (33, 116), (24, 116), (528, 116), (528, 773), (640, 773), (33, 69), (3, 773), (576, 773), (320, 69), (66, 104), (12, 773), (640, 385), (288, 385), (24, 104), (24, 138), (24, 208), (66, 201), (66, 402)]

theorem budgetCut6 : BudgetRunCut (compressRoots roots2 {(Sum.inl 5), (Sum.inl 8), (Sum.inr false)})
    (duplicateRaw nodeRaw2 s28) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 10)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs6 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun6 bound

theorem budgetCut7 : BudgetRunCut (compressRoots roots2 {(Sum.inl 5), (Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw2 s29) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs7 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun7 bound

theorem budgetCut8 : BudgetRunCut (compressRoots roots2 {(Sum.inl 0), (Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw2 s30) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs8 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun8 bound

theorem budgetCut9 : BudgetRunCut (compressRoots roots2 {(Sum.inl 5), (Sum.inl 8), (Sum.inr true)})
    (duplicateRaw nodeRaw2 s28) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 10)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs9 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun9 bound

theorem budgetCut10 : BudgetRunCut (compressRoots roots2 {(Sum.inl 5), (Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw2 s29) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs10 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun10 bound

theorem budgetCut11 : BudgetRunCut (compressRoots roots2 {(Sum.inl 0), (Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw2 s30) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs11 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun11 bound

theorem cutsSound2 : ∀ A v, (A, v) ∈ cuts2 →
    BudgetRunCut (compressRoots roots2 A) (duplicateRaw nodeRaw2 v) false graph 0 := by
  intro A v h
  simp only [cuts2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1 | h2 | h3 | h4 | h5
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    exact budgetCut6
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact budgetCut7
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact budgetCut8
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    exact budgetCut9
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
    exact budgetCut10
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
    exact budgetCut11

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves2 : entryLeafCheck rootLabels2 nodeRaw2 entries2 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates2 : entryGateCheck false graph rootLabels2 nodeRaw2 entries2 cuts2 rows2 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing2 : (roots2, graph) ∉ entries2 := by
  decide +kernel

theorem closed2 : PrunedGateClosed roots2 nodeRaw2 (pairColumn false)
    (pairColumn false graph) (entryCert entries2) false graph 0 :=
  entryGateCheck_sound cutsSound2 checkedGates2

theorem childNode2 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots2 nodeRaw2 (entryCert entries2) :=
  prunedNode_zero_of_checks rootLabels2 nodeRaw2 false graph entries2 cuts2 rows2
    cutsSound2 checkedLeaves2 checkedGates2 checkedMissing2

def rootLabels3 : List (ChildLabel) := [(Sum.inl 0), (Sum.inl 1), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]
def roots3 : Finset (ChildLabel) := rootLabels3.toFinset
def nodeRaw3 : ChildLabel → Sig := duplicateRaw nodeRaw0 s3
def entries3 : List (Entry (ChildLabel)) := [({(Sum.inl 0)}, s1), ({(Sum.inl 1)}, s11), ({(Sum.inl 3)}, s4), ({(Sum.inl 4)}, s5), ({(Sum.inl 5)}, s14), ({(Sum.inl 6)}, s6), ({(Sum.inl 7)}, s7), ({(Sum.inl 8)}, s15), ({(Sum.inl 9)}, s8), ({(Sum.inl 10)}, s16), ({(Sum.inl 11)}, s9), ({(Sum.inr false)}, s3), ({(Sum.inr true)}, s3), ({(Sum.inl 5), (Sum.inl 8)}, s18), ({(Sum.inl 5), (Sum.inr false)}, s31), ({(Sum.inl 6), (Sum.inr false)}, s32), ({(Sum.inl 10), (Sum.inr false)}, s34), ({(Sum.inl 5), (Sum.inr true)}, s31), ({(Sum.inl 6), (Sum.inr true)}, s32), ({(Sum.inl 10), (Sum.inr true)}, s34)]
def cuts3 : List (Entry (ChildLabel)) := [({(Sum.inl 10), (Sum.inr false)}, s33), ({(Sum.inl 10), (Sum.inr true)}, s33), ({(Sum.inl 5), (Sum.inl 8), (Sum.inr false)}, s35), ({(Sum.inl 6), (Sum.inl 10), (Sum.inr false)}, s36), ({(Sum.inl 5), (Sum.inl 8), (Sum.inr true)}, s35), ({(Sum.inl 6), (Sum.inl 10), (Sum.inr true)}, s36)]
def rows3 : List (Row × Row) := [(17, 208), (66, 402), (6, 773), (132, 201), (640, 201), (528, 554), (33, 201), (33, 104), (132, 773), (320, 201), (17, 385), (288, 773), (6, 402), (66, 104), (528, 276), (640, 521), (66, 201)]

theorem budgetCut12 : BudgetRunCut (compressRoots roots3 {(Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw3 s33) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs12 (by decide) (by decide) (by rfl)
    false graph 0 11 (by decide)
  exact fun k bound => cutRun12 bound

theorem budgetCut13 : BudgetRunCut (compressRoots roots3 {(Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw3 s33) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs13 (by decide) (by decide) (by rfl)
    false graph 0 11 (by decide)
  exact fun k bound => cutRun13 bound

theorem budgetCut14 : BudgetRunCut (compressRoots roots3 {(Sum.inl 5), (Sum.inl 8), (Sum.inr false)})
    (duplicateRaw nodeRaw3 s35) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 10)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs14 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun14 bound

theorem budgetCut15 : BudgetRunCut (compressRoots roots3 {(Sum.inl 6), (Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw3 s36) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs15 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun15 bound

theorem budgetCut16 : BudgetRunCut (compressRoots roots3 {(Sum.inl 5), (Sum.inl 8), (Sum.inr true)})
    (duplicateRaw nodeRaw3 s35) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 10)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs16 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun16 bound

theorem budgetCut17 : BudgetRunCut (compressRoots roots3 {(Sum.inl 6), (Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw3 s36) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs17 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun17 bound

theorem cutsSound3 : ∀ A v, (A, v) ∈ cuts3 →
    BudgetRunCut (compressRoots roots3 A) (duplicateRaw nodeRaw3 v) false graph 0 := by
  intro A v h
  simp only [cuts3, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1 | h2 | h3 | h4 | h5
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    exact budgetCut12
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact budgetCut13
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact budgetCut14
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    exact budgetCut15
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
    exact budgetCut16
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
    exact budgetCut17

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves3 : entryLeafCheck rootLabels3 nodeRaw3 entries3 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates3 : entryGateCheck false graph rootLabels3 nodeRaw3 entries3 cuts3 rows3 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing3 : (roots3, graph) ∉ entries3 := by
  decide +kernel

theorem closed3 : PrunedGateClosed roots3 nodeRaw3 (pairColumn false)
    (pairColumn false graph) (entryCert entries3) false graph 0 :=
  entryGateCheck_sound cutsSound3 checkedGates3

theorem childNode3 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots3 nodeRaw3 (entryCert entries3) :=
  prunedNode_zero_of_checks rootLabels3 nodeRaw3 false graph entries3 cuts3 rows3
    cutsSound3 checkedLeaves3 checkedGates3 checkedMissing3

def rootLabels4 : List (ChildLabel) := [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]
def roots4 : Finset (ChildLabel) := rootLabels4.toFinset
def nodeRaw4 : ChildLabel → Sig := duplicateRaw nodeRaw0 s4
def entries4 : List (Entry (ChildLabel)) := [({(Sum.inl 0)}, s1), ({(Sum.inl 1)}, s11), ({(Sum.inl 2)}, s3), ({(Sum.inl 4)}, s5), ({(Sum.inl 5)}, s14), ({(Sum.inl 6)}, s6), ({(Sum.inl 7)}, s7), ({(Sum.inl 8)}, s15), ({(Sum.inl 9)}, s8), ({(Sum.inl 10)}, s16), ({(Sum.inl 11)}, s9), ({(Sum.inr false)}, s4), ({(Sum.inr true)}, s4), ({(Sum.inl 5), (Sum.inl 8)}, s18), ({(Sum.inl 4), (Sum.inr false)}, s37), ({(Sum.inl 5), (Sum.inr false)}, s38), ({(Sum.inl 7), (Sum.inr false)}, s39), ({(Sum.inl 10), (Sum.inr false)}, s40), ({(Sum.inl 10), (Sum.inr false)}, s41), ({(Sum.inl 4), (Sum.inr true)}, s37), ({(Sum.inl 5), (Sum.inr true)}, s38), ({(Sum.inl 7), (Sum.inr true)}, s39), ({(Sum.inl 10), (Sum.inr true)}, s40), ({(Sum.inl 10), (Sum.inr true)}, s41), ({(Sum.inl 4), (Sum.inl 5), (Sum.inr false)}, s42), ({(Sum.inl 4), (Sum.inl 10), (Sum.inr false)}, s43), ({(Sum.inl 7), (Sum.inl 10), (Sum.inr false)}, s44), ({(Sum.inl 5), (Sum.inl 10), (Sum.inr false)}, s45), ({(Sum.inl 4), (Sum.inl 5), (Sum.inr true)}, s42), ({(Sum.inl 4), (Sum.inl 10), (Sum.inr true)}, s43), ({(Sum.inl 7), (Sum.inl 10), (Sum.inr true)}, s44), ({(Sum.inl 5), (Sum.inl 10), (Sum.inr true)}, s45)]
def cuts4 : List (Entry (ChildLabel)) := []
def rows4 : List (Row × Row) := [(17, 402), (33, 201), (132, 773), (33, 116), (6, 50), (6, 116), (528, 116), (24, 116), (288, 116), (66, 402), (288, 385), (12, 773), (640, 385), (17, 208), (132, 208), (24, 104), (3, 773), (24, 138), (24, 402), (66, 201), (264, 201)]

theorem cutsSound4 : ∀ A v, (A, v) ∈ cuts4 →
    BudgetRunCut (compressRoots roots4 A) (duplicateRaw nodeRaw4 v) false graph 0 := by
  intro A v h
  simp [cuts4] at h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves4 : entryLeafCheck rootLabels4 nodeRaw4 entries4 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates4 : entryGateCheck false graph rootLabels4 nodeRaw4 entries4 cuts4 rows4 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing4 : (roots4, graph) ∉ entries4 := by
  decide +kernel

theorem closed4 : PrunedGateClosed roots4 nodeRaw4 (pairColumn false)
    (pairColumn false graph) (entryCert entries4) false graph 0 :=
  entryGateCheck_sound cutsSound4 checkedGates4

theorem childNode4 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots4 nodeRaw4 (entryCert entries4) :=
  prunedNode_zero_of_checks rootLabels4 nodeRaw4 false graph entries4 cuts4 rows4
    cutsSound4 checkedLeaves4 checkedGates4 checkedMissing4

def rootLabels5 : List (ChildLabel) := [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]
def roots5 : Finset (ChildLabel) := rootLabels5.toFinset
def nodeRaw5 : ChildLabel → Sig := duplicateRaw nodeRaw0 s5
def entries5 : List (Entry (ChildLabel)) := [({(Sum.inl 0)}, s1), ({(Sum.inl 1)}, s11), ({(Sum.inl 2)}, s3), ({(Sum.inl 3)}, s4), ({(Sum.inl 5)}, s14), ({(Sum.inl 6)}, s6), ({(Sum.inl 7)}, s7), ({(Sum.inl 8)}, s15), ({(Sum.inl 9)}, s8), ({(Sum.inl 10)}, s16), ({(Sum.inl 11)}, s9), ({(Sum.inr false)}, s5), ({(Sum.inr true)}, s5), ({(Sum.inl 6), (Sum.inr false)}, s46), ({(Sum.inl 7), (Sum.inr false)}, s47), ({(Sum.inl 10), (Sum.inr false)}, s49), ({(Sum.inl 6), (Sum.inr true)}, s46), ({(Sum.inl 7), (Sum.inr true)}, s47), ({(Sum.inl 10), (Sum.inr true)}, s49)]
def cuts5 : List (Entry (ChildLabel)) := [({(Sum.inl 5), (Sum.inl 8)}, s18), ({(Sum.inl 5), (Sum.inl 8)}, s18), ({(Sum.inl 10), (Sum.inr false)}, s48), ({(Sum.inl 10), (Sum.inr true)}, s48), ({(Sum.inl 6), (Sum.inl 10), (Sum.inr false)}, s50), ({(Sum.inl 6), (Sum.inl 10), (Sum.inr true)}, s50)]
def rows5 : List (Row × Row) := [(132, 69), (576, 773), (6, 116), (24, 116), (528, 116), (24, 104), (6, 50), (17, 116), (320, 116), (17, 208), (264, 402), (528, 402), (66, 201), (264, 201), (3, 773), (6, 402), (12, 773), (24, 138)]

theorem budgetCut0 : BudgetRunCut (compressRoots roots5 {(Sum.inl 5), (Sum.inl 8)})
    (duplicateRaw nodeRaw5 s18) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 10)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs0 (by decide) (by decide) (by rfl)
    false graph 0 11 (by decide)
  exact fun k bound => cutRun0 bound

theorem budgetCut18 : BudgetRunCut (compressRoots roots5 {(Sum.inl 5), (Sum.inl 8)})
    (duplicateRaw nodeRaw5 s18) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 10)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs18 (by decide) (by decide) (by rfl)
    false graph 0 11 (by decide)
  exact fun k bound => cutRun18 bound

theorem budgetCut19 : BudgetRunCut (compressRoots roots5 {(Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw5 s48) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs19 (by decide) (by decide) (by rfl)
    false graph 0 11 (by decide)
  exact fun k bound => cutRun19 bound

theorem budgetCut20 : BudgetRunCut (compressRoots roots5 {(Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw5 s48) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs20 (by decide) (by decide) (by rfl)
    false graph 0 11 (by decide)
  exact fun k bound => cutRun20 bound

theorem budgetCut21 : BudgetRunCut (compressRoots roots5 {(Sum.inl 6), (Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw5 s50) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs21 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun21 bound

theorem budgetCut22 : BudgetRunCut (compressRoots roots5 {(Sum.inl 6), (Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw5 s50) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs22 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun22 bound

theorem cutsSound5 : ∀ A v, (A, v) ∈ cuts5 →
    BudgetRunCut (compressRoots roots5 A) (duplicateRaw nodeRaw5 v) false graph 0 := by
  intro A v h
  simp only [cuts5, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1 | h2 | h3 | h4 | h5
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    exact budgetCut0
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact budgetCut18
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact budgetCut19
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    exact budgetCut20
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
    exact budgetCut21
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
    exact budgetCut22

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves5 : entryLeafCheck rootLabels5 nodeRaw5 entries5 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates5 : entryGateCheck false graph rootLabels5 nodeRaw5 entries5 cuts5 rows5 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing5 : (roots5, graph) ∉ entries5 := by
  decide +kernel

theorem closed5 : PrunedGateClosed roots5 nodeRaw5 (pairColumn false)
    (pairColumn false graph) (entryCert entries5) false graph 0 :=
  entryGateCheck_sound cutsSound5 checkedGates5

theorem childNode5 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots5 nodeRaw5 (entryCert entries5) :=
  prunedNode_zero_of_checks rootLabels5 nodeRaw5 false graph entries5 cuts5 rows5
    cutsSound5 checkedLeaves5 checkedGates5 checkedMissing5

def rootLabels6 : List (ChildLabel) := [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]
def roots6 : Finset (ChildLabel) := rootLabels6.toFinset
def nodeRaw6 : ChildLabel → Sig := duplicateRaw nodeRaw0 s14
def entries6 : List (Entry (ChildLabel)) := [({(Sum.inl 0)}, s1), ({(Sum.inl 1)}, s11), ({(Sum.inl 2)}, s3), ({(Sum.inl 3)}, s4), ({(Sum.inl 4)}, s5), ({(Sum.inl 6)}, s6), ({(Sum.inl 7)}, s7), ({(Sum.inl 8)}, s15), ({(Sum.inl 9)}, s8), ({(Sum.inl 10)}, s16), ({(Sum.inl 11)}, s9), ({(Sum.inr false)}, s14), ({(Sum.inr true)}, s14), ({(Sum.inl 8), (Sum.inr false)}, s18), ({(Sum.inl 10), (Sum.inr false)}, s51), ({(Sum.inl 10), (Sum.inr false)}, s52), ({(Sum.inl 8), (Sum.inr true)}, s18), ({(Sum.inl 10), (Sum.inr true)}, s51), ({(Sum.inl 10), (Sum.inr true)}, s52)]
def cuts6 : List (Entry (ChildLabel)) := [({(Sum.inl 8), (Sum.inl 10), (Sum.inr false)}, s53), ({(Sum.inl 8), (Sum.inl 10), (Sum.inr true)}, s53)]
def rows6 : List (Row × Row) := [(17, 116), (6, 773), (24, 104), (640, 201), (132, 69), (24, 116), (132, 201), (264, 201), (33, 773), (576, 773), (264, 385), (6, 116), (6, 402), (528, 276), (17, 385), (33, 201), (66, 201)]

theorem budgetCut23 : BudgetRunCut (compressRoots roots6 {(Sum.inl 8), (Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw6 s53) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs23 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun23 bound

theorem budgetCut24 : BudgetRunCut (compressRoots roots6 {(Sum.inl 8), (Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw6 s53) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs24 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun24 bound

theorem cutsSound6 : ∀ A v, (A, v) ∈ cuts6 →
    BudgetRunCut (compressRoots roots6 A) (duplicateRaw nodeRaw6 v) false graph 0 := by
  intro A v h
  simp only [cuts6, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    exact budgetCut23
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact budgetCut24

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves6 : entryLeafCheck rootLabels6 nodeRaw6 entries6 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates6 : entryGateCheck false graph rootLabels6 nodeRaw6 entries6 cuts6 rows6 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing6 : (roots6, graph) ∉ entries6 := by
  decide +kernel

theorem closed6 : PrunedGateClosed roots6 nodeRaw6 (pairColumn false)
    (pairColumn false graph) (entryCert entries6) false graph 0 :=
  entryGateCheck_sound cutsSound6 checkedGates6

theorem childNode6 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots6 nodeRaw6 (entryCert entries6) :=
  prunedNode_zero_of_checks rootLabels6 nodeRaw6 false graph entries6 cuts6 rows6
    cutsSound6 checkedLeaves6 checkedGates6 checkedMissing6

def rootLabels7 : List (ChildLabel) := [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]
def roots7 : Finset (ChildLabel) := rootLabels7.toFinset
def nodeRaw7 : ChildLabel → Sig := duplicateRaw nodeRaw0 s6
def entries7 : List (Entry (ChildLabel)) := [({(Sum.inl 0)}, s1), ({(Sum.inl 1)}, s11), ({(Sum.inl 2)}, s3), ({(Sum.inl 3)}, s4), ({(Sum.inl 4)}, s5), ({(Sum.inl 5)}, s14), ({(Sum.inl 7)}, s7), ({(Sum.inl 8)}, s15), ({(Sum.inl 9)}, s8), ({(Sum.inl 10)}, s16), ({(Sum.inl 11)}, s9), ({(Sum.inr false)}, s6), ({(Sum.inr true)}, s6), ({(Sum.inl 5), (Sum.inl 8)}, s18)]
def cuts7 : List (Entry (ChildLabel)) := []
def rows7 : List (Row × Row) := [(17, 116), (24, 104), (528, 116), (6, 69), (12, 69), (132, 201), (264, 201), (17, 208), (33, 201), (132, 69), (528, 402), (6, 50), (320, 116), (6, 116), (24, 402), (640, 201), (3, 773), (24, 138), (66, 201)]

theorem cutsSound7 : ∀ A v, (A, v) ∈ cuts7 →
    BudgetRunCut (compressRoots roots7 A) (duplicateRaw nodeRaw7 v) false graph 0 := by
  intro A v h
  simp [cuts7] at h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves7 : entryLeafCheck rootLabels7 nodeRaw7 entries7 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates7 : entryGateCheck false graph rootLabels7 nodeRaw7 entries7 cuts7 rows7 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing7 : (roots7, graph) ∉ entries7 := by
  decide +kernel

theorem closed7 : PrunedGateClosed roots7 nodeRaw7 (pairColumn false)
    (pairColumn false graph) (entryCert entries7) false graph 0 :=
  entryGateCheck_sound cutsSound7 checkedGates7

theorem childNode7 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots7 nodeRaw7 (entryCert entries7) :=
  prunedNode_zero_of_checks rootLabels7 nodeRaw7 false graph entries7 cuts7 rows7
    cutsSound7 checkedLeaves7 checkedGates7 checkedMissing7

def rootLabels8 : List (ChildLabel) := [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]
def roots8 : Finset (ChildLabel) := rootLabels8.toFinset
def nodeRaw8 : ChildLabel → Sig := duplicateRaw nodeRaw0 s7
def entries8 : List (Entry (ChildLabel)) := [({(Sum.inl 0)}, s1), ({(Sum.inl 1)}, s11), ({(Sum.inl 2)}, s3), ({(Sum.inl 3)}, s4), ({(Sum.inl 4)}, s5), ({(Sum.inl 5)}, s14), ({(Sum.inl 6)}, s6), ({(Sum.inl 8)}, s15), ({(Sum.inl 9)}, s8), ({(Sum.inl 10)}, s16), ({(Sum.inl 11)}, s9), ({(Sum.inr false)}, s7), ({(Sum.inr true)}, s7), ({(Sum.inl 10), (Sum.inr false)}, s55), ({(Sum.inl 10), (Sum.inr true)}, s55)]
def cuts8 : List (Entry (ChildLabel)) := [({(Sum.inl 5), (Sum.inl 8)}, s18), ({(Sum.inl 5), (Sum.inl 8)}, s18), ({(Sum.inl 10), (Sum.inr false)}, s54), ({(Sum.inl 10), (Sum.inr true)}, s54)]
def rows8 : List (Row × Row) := [(6, 402), (24, 201), (528, 402), (24, 402), (6, 116), (33, 201), (17, 208), (17, 116), (264, 201), (6, 554), (66, 201), (66, 402), (576, 104), (12, 69), (320, 116), (3, 773), (12, 201), (24, 104)]

theorem budgetCut1 : BudgetRunCut (compressRoots roots8 {(Sum.inl 5), (Sum.inl 8)})
    (duplicateRaw nodeRaw8 s18) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 10)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs1 (by decide) (by decide) (by rfl)
    false graph 0 11 (by decide)
  exact fun k bound => cutRun1 bound

theorem budgetCut25 : BudgetRunCut (compressRoots roots8 {(Sum.inl 5), (Sum.inl 8)})
    (duplicateRaw nodeRaw8 s18) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 10)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs25 (by decide) (by decide) (by rfl)
    false graph 0 11 (by decide)
  exact fun k bound => cutRun25 bound

theorem budgetCut26 : BudgetRunCut (compressRoots roots8 {(Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw8 s54) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs26 (by decide) (by decide) (by rfl)
    false graph 0 11 (by decide)
  exact fun k bound => cutRun26 bound

theorem budgetCut27 : BudgetRunCut (compressRoots roots8 {(Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw8 s54) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 8)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs27 (by decide) (by decide) (by rfl)
    false graph 0 11 (by decide)
  exact fun k bound => cutRun27 bound

theorem cutsSound8 : ∀ A v, (A, v) ∈ cuts8 →
    BudgetRunCut (compressRoots roots8 A) (duplicateRaw nodeRaw8 v) false graph 0 := by
  intro A v h
  simp only [cuts8, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1 | h2 | h3
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    exact budgetCut1
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact budgetCut25
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact budgetCut26
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    exact budgetCut27

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves8 : entryLeafCheck rootLabels8 nodeRaw8 entries8 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates8 : entryGateCheck false graph rootLabels8 nodeRaw8 entries8 cuts8 rows8 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing8 : (roots8, graph) ∉ entries8 := by
  decide +kernel

theorem closed8 : PrunedGateClosed roots8 nodeRaw8 (pairColumn false)
    (pairColumn false graph) (entryCert entries8) false graph 0 :=
  entryGateCheck_sound cutsSound8 checkedGates8

theorem childNode8 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots8 nodeRaw8 (entryCert entries8) :=
  prunedNode_zero_of_checks rootLabels8 nodeRaw8 false graph entries8 cuts8 rows8
    cutsSound8 checkedLeaves8 checkedGates8 checkedMissing8

def rootLabels9 : List (ChildLabel) := [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]
def roots9 : Finset (ChildLabel) := rootLabels9.toFinset
def nodeRaw9 : ChildLabel → Sig := duplicateRaw nodeRaw0 s15
def entries9 : List (Entry (ChildLabel)) := [({(Sum.inl 0)}, s1), ({(Sum.inl 1)}, s11), ({(Sum.inl 2)}, s3), ({(Sum.inl 3)}, s4), ({(Sum.inl 4)}, s5), ({(Sum.inl 5)}, s14), ({(Sum.inl 6)}, s6), ({(Sum.inl 7)}, s7), ({(Sum.inl 9)}, s8), ({(Sum.inl 10)}, s16), ({(Sum.inl 11)}, s9), ({(Sum.inr false)}, s15), ({(Sum.inr true)}, s15), ({(Sum.inl 5), (Sum.inr false)}, s18), ({(Sum.inl 10), (Sum.inr false)}, s56), ({(Sum.inl 10), (Sum.inr false)}, s57), ({(Sum.inl 5), (Sum.inr true)}, s18), ({(Sum.inl 10), (Sum.inr true)}, s56), ({(Sum.inl 10), (Sum.inr true)}, s57)]
def cuts9 : List (Entry (ChildLabel)) := [({(Sum.inl 4), (Sum.inl 10), (Sum.inr false)}, s58), ({(Sum.inl 5), (Sum.inl 10), (Sum.inr false)}, s59), ({(Sum.inl 4), (Sum.inl 10), (Sum.inr true)}, s58), ({(Sum.inl 5), (Sum.inl 10), (Sum.inr true)}, s59)]
def rows9 : List (Row × Row) := [(17, 402), (24, 201), (528, 402), (6, 402), (12, 773), (6, 69), (33, 201), (576, 773), (320, 208), (132, 69), (24, 208), (12, 521), (288, 773), (640, 201), (6, 116), (66, 201), (3, 773), (24, 104)]

theorem budgetCut28 : BudgetRunCut (compressRoots roots9 {(Sum.inl 4), (Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw9 s58) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs28 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun28 bound

theorem budgetCut29 : BudgetRunCut (compressRoots roots9 {(Sum.inl 5), (Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw9 s59) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs29 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun29 bound

theorem budgetCut30 : BudgetRunCut (compressRoots roots9 {(Sum.inl 4), (Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw9 s58) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 5)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs30 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun30 bound

theorem budgetCut31 : BudgetRunCut (compressRoots roots9 {(Sum.inl 5), (Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw9 s59) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs31 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun31 bound

theorem cutsSound9 : ∀ A v, (A, v) ∈ cuts9 →
    BudgetRunCut (compressRoots roots9 A) (duplicateRaw nodeRaw9 v) false graph 0 := by
  intro A v h
  simp only [cuts9, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1 | h2 | h3
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    exact budgetCut28
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact budgetCut29
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact budgetCut30
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    exact budgetCut31

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves9 : entryLeafCheck rootLabels9 nodeRaw9 entries9 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates9 : entryGateCheck false graph rootLabels9 nodeRaw9 entries9 cuts9 rows9 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing9 : (roots9, graph) ∉ entries9 := by
  decide +kernel

theorem closed9 : PrunedGateClosed roots9 nodeRaw9 (pairColumn false)
    (pairColumn false graph) (entryCert entries9) false graph 0 :=
  entryGateCheck_sound cutsSound9 checkedGates9

theorem childNode9 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots9 nodeRaw9 (entryCert entries9) :=
  prunedNode_zero_of_checks rootLabels9 nodeRaw9 false graph entries9 cuts9 rows9
    cutsSound9 checkedLeaves9 checkedGates9 checkedMissing9

def rootLabels10 : List (ChildLabel) := [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]
def roots10 : Finset (ChildLabel) := rootLabels10.toFinset
def nodeRaw10 : ChildLabel → Sig := duplicateRaw nodeRaw0 s8
def entries10 : List (Entry (ChildLabel)) := [({(Sum.inl 0)}, s1), ({(Sum.inl 1)}, s11), ({(Sum.inl 2)}, s3), ({(Sum.inl 3)}, s4), ({(Sum.inl 4)}, s5), ({(Sum.inl 5)}, s14), ({(Sum.inl 6)}, s6), ({(Sum.inl 7)}, s7), ({(Sum.inl 8)}, s15), ({(Sum.inl 10)}, s16), ({(Sum.inl 11)}, s9), ({(Sum.inr false)}, s8), ({(Sum.inr true)}, s8), ({(Sum.inl 5), (Sum.inl 8)}, s18), ({(Sum.inl 8), (Sum.inr false)}, s60), ({(Sum.inl 8), (Sum.inr true)}, s60)]
def cuts10 : List (Entry (ChildLabel)) := [({(Sum.inl 5), (Sum.inl 8), (Sum.inr false)}, s61), ({(Sum.inl 5), (Sum.inl 8), (Sum.inr true)}, s61)]
def rows10 : List (Row × Row) := [(17, 116), (6, 773), (528, 773), (24, 402), (640, 201), (17, 402), (12, 201), (33, 773), (66, 402), (132, 773), (6, 770), (12, 69), (33, 201), (6, 116), (528, 276), (24, 104), (24, 138), (17, 208), (66, 201)]

theorem budgetCut32 : BudgetRunCut (compressRoots roots10 {(Sum.inl 5), (Sum.inl 8), (Sum.inr false)})
    (duplicateRaw nodeRaw10 s61) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 10)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs32 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun32 bound

theorem budgetCut33 : BudgetRunCut (compressRoots roots10 {(Sum.inl 5), (Sum.inl 8), (Sum.inr true)})
    (duplicateRaw nodeRaw10 s61) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 10)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs33 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun33 bound

theorem cutsSound10 : ∀ A v, (A, v) ∈ cuts10 →
    BudgetRunCut (compressRoots roots10 A) (duplicateRaw nodeRaw10 v) false graph 0 := by
  intro A v h
  simp only [cuts10, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    exact budgetCut32
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact budgetCut33

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves10 : entryLeafCheck rootLabels10 nodeRaw10 entries10 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates10 : entryGateCheck false graph rootLabels10 nodeRaw10 entries10 cuts10 rows10 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing10 : (roots10, graph) ∉ entries10 := by
  decide +kernel

theorem closed10 : PrunedGateClosed roots10 nodeRaw10 (pairColumn false)
    (pairColumn false graph) (entryCert entries10) false graph 0 :=
  entryGateCheck_sound cutsSound10 checkedGates10

theorem childNode10 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots10 nodeRaw10 (entryCert entries10) :=
  prunedNode_zero_of_checks rootLabels10 nodeRaw10 false graph entries10 cuts10 rows10
    cutsSound10 checkedLeaves10 checkedGates10 checkedMissing10

def rootLabels11 : List (ChildLabel) := [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]
def roots11 : Finset (ChildLabel) := rootLabels11.toFinset
def nodeRaw11 : ChildLabel → Sig := duplicateRaw nodeRaw0 s16
def entries11 : List (Entry (ChildLabel)) := [({(Sum.inl 0)}, s1), ({(Sum.inl 1)}, s11), ({(Sum.inl 2)}, s3), ({(Sum.inl 3)}, s4), ({(Sum.inl 4)}, s5), ({(Sum.inl 5)}, s14), ({(Sum.inl 6)}, s6), ({(Sum.inl 7)}, s7), ({(Sum.inl 8)}, s15), ({(Sum.inl 9)}, s8), ({(Sum.inl 11)}, s9), ({(Sum.inr false)}, s16), ({(Sum.inr true)}, s16), ({(Sum.inl 5), (Sum.inl 8)}, s18)]
def cuts11 : List (Entry (ChildLabel)) := []
def rows11 : List (Row × Row) := [(17, 116), (6, 773), (24, 104), (12, 773), (528, 116), (640, 773), (132, 201), (17, 402), (33, 201), (288, 116), (6, 116), (640, 385), (6, 50), (24, 208), (66, 201), (320, 385), (24, 138), (264, 201)]

theorem cutsSound11 : ∀ A v, (A, v) ∈ cuts11 →
    BudgetRunCut (compressRoots roots11 A) (duplicateRaw nodeRaw11 v) false graph 0 := by
  intro A v h
  simp [cuts11] at h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves11 : entryLeafCheck rootLabels11 nodeRaw11 entries11 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates11 : entryGateCheck false graph rootLabels11 nodeRaw11 entries11 cuts11 rows11 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing11 : (roots11, graph) ∉ entries11 := by
  decide +kernel

theorem closed11 : PrunedGateClosed roots11 nodeRaw11 (pairColumn false)
    (pairColumn false graph) (entryCert entries11) false graph 0 :=
  entryGateCheck_sound cutsSound11 checkedGates11

theorem childNode11 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots11 nodeRaw11 (entryCert entries11) :=
  prunedNode_zero_of_checks rootLabels11 nodeRaw11 false graph entries11 cuts11 rows11
    cutsSound11 checkedLeaves11 checkedGates11 checkedMissing11

def rootLabels12 : List (ChildLabel) := [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 5), (Sum.inl 6), (Sum.inl 7), (Sum.inl 8), (Sum.inl 9), (Sum.inl 10), (Sum.inr false), (Sum.inr true)]
def roots12 : Finset (ChildLabel) := rootLabels12.toFinset
def nodeRaw12 : ChildLabel → Sig := duplicateRaw nodeRaw0 s9
def entries12 : List (Entry (ChildLabel)) := [({(Sum.inl 0)}, s1), ({(Sum.inl 1)}, s11), ({(Sum.inl 2)}, s3), ({(Sum.inl 3)}, s4), ({(Sum.inl 4)}, s5), ({(Sum.inl 5)}, s14), ({(Sum.inl 6)}, s6), ({(Sum.inl 7)}, s7), ({(Sum.inl 8)}, s15), ({(Sum.inl 9)}, s8), ({(Sum.inl 10)}, s16), ({(Sum.inr false)}, s9), ({(Sum.inr true)}, s9), ({(Sum.inl 5), (Sum.inl 8)}, s18), ({(Sum.inl 5), (Sum.inr false)}, s62), ({(Sum.inl 9), (Sum.inr false)}, s63), ({(Sum.inl 10), (Sum.inr false)}, s64), ({(Sum.inl 10), (Sum.inr false)}, s65), ({(Sum.inl 5), (Sum.inr true)}, s62), ({(Sum.inl 9), (Sum.inr true)}, s63), ({(Sum.inl 10), (Sum.inr true)}, s64), ({(Sum.inl 10), (Sum.inr true)}, s65), ({(Sum.inl 9), (Sum.inl 10), (Sum.inr false)}, s67), ({(Sum.inl 5), (Sum.inl 10), (Sum.inr false)}, s68), ({(Sum.inl 8), (Sum.inl 10), (Sum.inr false)}, s69), ({(Sum.inl 5), (Sum.inl 8), (Sum.inl 10), (Sum.inr false)}, s70), ({(Sum.inl 9), (Sum.inl 10), (Sum.inr true)}, s67), ({(Sum.inl 5), (Sum.inl 10), (Sum.inr true)}, s68), ({(Sum.inl 8), (Sum.inl 10), (Sum.inr true)}, s69), ({(Sum.inl 5), (Sum.inl 8), (Sum.inl 10), (Sum.inr true)}, s70)]
def cuts12 : List (Entry (ChildLabel)) := [({(Sum.inl 5), (Sum.inl 8), (Sum.inr false)}, s66), ({(Sum.inl 5), (Sum.inl 8), (Sum.inr true)}, s66), ({(Sum.inl 5), (Sum.inl 8), (Sum.inl 10), (Sum.inr false)}, s71), ({(Sum.inl 5), (Sum.inl 8), (Sum.inl 10), (Sum.inr false)}, s72), ({(Sum.inl 5), (Sum.inl 8), (Sum.inl 10), (Sum.inr true)}, s71), ({(Sum.inl 5), (Sum.inl 8), (Sum.inl 10), (Sum.inr true)}, s72)]
def rows12 : List (Row × Row) := [(17, 402), (264, 201), (33, 554), (6, 770), (12, 773), (17, 773), (33, 773), (320, 773), (3, 773), (132, 773), (24, 104), (17, 116), (640, 385), (66, 104), (33, 201), (24, 138), (24, 208), (6, 50), (66, 201), (66, 402)]

theorem budgetCut34 : BudgetRunCut (compressRoots roots12 {(Sum.inl 5), (Sum.inl 8), (Sum.inr false)})
    (duplicateRaw nodeRaw12 s66) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 10)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs34 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun34 bound

theorem budgetCut35 : BudgetRunCut (compressRoots roots12 {(Sum.inl 5), (Sum.inl 8), (Sum.inr true)})
    (duplicateRaw nodeRaw12 s66) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 10)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs35 (by decide) (by decide) (by rfl)
    false graph 0 10 (by decide)
  exact fun k bound => cutRun35 bound

theorem budgetCut36 : BudgetRunCut (compressRoots roots12 {(Sum.inl 5), (Sum.inl 8), (Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw12 s71) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs36 (by decide) (by decide) (by rfl)
    false graph 0 9 (by decide)
  exact fun k bound => cutRun36 bound

theorem budgetCut37 : BudgetRunCut (compressRoots roots12 {(Sum.inl 5), (Sum.inl 8), (Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw12 s72) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs37 (by decide) (by decide) (by rfl)
    false graph 0 9 (by decide)
  exact fun k bound => cutRun37 bound

theorem budgetCut38 : BudgetRunCut (compressRoots roots12 {(Sum.inl 5), (Sum.inl 8), (Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw12 s71) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs38 (by decide) (by decide) (by rfl)
    false graph 0 9 (by decide)
  exact fun k bound => cutRun38 bound

theorem budgetCut39 : BudgetRunCut (compressRoots roots12 {(Sum.inl 5), (Sum.inl 8), (Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw12 s72) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 4)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs39 (by decide) (by decide) (by rfl)
    false graph 0 9 (by decide)
  exact fun k bound => cutRun39 bound

theorem cutsSound12 : ∀ A v, (A, v) ∈ cuts12 →
    BudgetRunCut (compressRoots roots12 A) (duplicateRaw nodeRaw12 v) false graph 0 := by
  intro A v h
  simp only [cuts12, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1 | h2 | h3 | h4 | h5
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    exact budgetCut34
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact budgetCut35
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact budgetCut36
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    exact budgetCut37
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
    exact budgetCut38
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
    exact budgetCut39

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves12 : entryLeafCheck rootLabels12 nodeRaw12 entries12 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates12 : entryGateCheck false graph rootLabels12 nodeRaw12 entries12 cuts12 rows12 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing12 : (roots12, graph) ∉ entries12 := by
  decide +kernel

theorem closed12 : PrunedGateClosed roots12 nodeRaw12 (pairColumn false)
    (pairColumn false graph) (entryCert entries12) false graph 0 :=
  entryGateCheck_sound cutsSound12 checkedGates12

theorem childNode12 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots12 nodeRaw12 (entryCert entries12) :=
  prunedNode_zero_of_checks rootLabels12 nodeRaw12 false graph entries12 cuts12 rows12
    cutsSound12 checkedLeaves12 checkedGates12 checkedMissing12

def rootLabels13 : List (ChildLabel) := [(Sum.inl 0), (Sum.inl 1), (Sum.inl 2), (Sum.inl 3), (Sum.inl 4), (Sum.inl 6), (Sum.inl 7), (Sum.inl 9), (Sum.inl 10), (Sum.inl 11), (Sum.inr false), (Sum.inr true)]
def roots13 : Finset (ChildLabel) := rootLabels13.toFinset
def nodeRaw13 : ChildLabel → Sig := duplicateRaw nodeRaw0 s18
def entries13 : List (Entry (ChildLabel)) := [({(Sum.inl 0)}, s1), ({(Sum.inl 1)}, s11), ({(Sum.inl 2)}, s3), ({(Sum.inl 3)}, s4), ({(Sum.inl 4)}, s5), ({(Sum.inl 6)}, s6), ({(Sum.inl 7)}, s7), ({(Sum.inl 9)}, s8), ({(Sum.inl 10)}, s16), ({(Sum.inl 11)}, s9), ({(Sum.inr false)}, s18), ({(Sum.inr true)}, s18), ({(Sum.inl 10), (Sum.inr false)}, s73), ({(Sum.inl 10), (Sum.inr false)}, s74), ({(Sum.inl 10), (Sum.inr true)}, s73), ({(Sum.inl 10), (Sum.inr true)}, s74)]
def cuts13 : List (Entry (ChildLabel)) := [({(Sum.inl 4), (Sum.inl 10), (Sum.inr false)}, s58), ({(Sum.inl 4), (Sum.inl 10), (Sum.inr true)}, s58)]
def rows13 : List (Row × Row) := [(6, 773), (132, 201), (24, 201), (132, 773), (640, 201), (24, 402), (33, 201), (264, 201), (320, 385), (12, 69), (288, 276), (6, 116), (6, 402), (528, 116), (17, 385), (66, 201), (528, 276)]

theorem budgetCut40 : BudgetRunCut (compressRoots roots13 {(Sum.inl 4), (Sum.inl 10), (Sum.inr false)})
    (duplicateRaw nodeRaw13 s58) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr true)), (Sum.inr false)] cutWs40 (by decide) (by decide) (by rfl)
    false graph 0 9 (by decide)
  exact fun k bound => cutRun40 bound

theorem budgetCut41 : BudgetRunCut (compressRoots roots13 {(Sum.inl 4), (Sum.inl 10), (Sum.inr true)})
    (duplicateRaw nodeRaw13 s58) false graph 0 := by
  apply budgetRunCut_of_list _ _ [(Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), (Sum.inl (Sum.inl 2)), (Sum.inl (Sum.inl 3)), (Sum.inl (Sum.inl 6)), (Sum.inl (Sum.inl 7)), (Sum.inl (Sum.inl 9)), (Sum.inl (Sum.inl 11)), (Sum.inl (Sum.inr false)), (Sum.inr false)] cutWs41 (by decide) (by decide) (by rfl)
    false graph 0 9 (by decide)
  exact fun k bound => cutRun41 bound

theorem cutsSound13 : ∀ A v, (A, v) ∈ cuts13 →
    BudgetRunCut (compressRoots roots13 A) (duplicateRaw nodeRaw13 v) false graph 0 := by
  intro A v h
  simp only [cuts13, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h0 | h1
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    exact budgetCut40
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    exact budgetCut41

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedLeaves13 : entryLeafCheck rootLabels13 nodeRaw13 entries13 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedGates13 : entryGateCheck false graph rootLabels13 nodeRaw13 entries13 cuts13 rows13 = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem checkedMissing13 : (roots13, graph) ∉ entries13 := by
  decide +kernel

theorem closed13 : PrunedGateClosed roots13 nodeRaw13 (pairColumn false)
    (pairColumn false graph) (entryCert entries13) false graph 0 :=
  entryGateCheck_sound cutsSound13 checkedGates13

theorem childNode13 : PrunedNode (pairColumn false) (pairColumn false graph)
    false graph 0 ChildLabel roots13 nodeRaw13 (entryCert entries13) :=
  prunedNode_zero_of_checks rootLabels13 nodeRaw13 false graph entries13 cuts13 rows13
    cutsSound13 checkedLeaves13 checkedGates13 checkedMissing13

end PEqualNP.Outside.L_meta_2373.Live1024.PrunedCopyFixture0

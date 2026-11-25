import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.FiveOwnerNegatives

def edgePairs : Finset (Fin 16 × Fin 16) := {(0, 5), (0, 6), (0, 8), (0, 13), (1, 5), (1, 7), (1, 12), (1, 15), (2, 6), (2, 11), (2, 14), (2, 15), (3, 9), (3, 12), (3, 13), (3, 14), (4, 7), (4, 10), (4, 11), (4, 13)}

def dirtyPairs : Finset (Fin 16 × Fin 16) := {(1, 13), (2, 13), (5, 11), (5, 13), (5, 14), (6, 7), (6, 12), (6, 13), (7, 13), (7, 14), (11, 12), (11, 13), (12, 13), (13, 14), (13, 15)}

abbrev allowed (u v : Fin 16) : Prop :=
  (u,v) ∈ edgePairs ∨ (v,u) ∈ edgePairs ∨ (u,v) ∈ dirtyPairs ∨ (v,u) ∈ dirtyPairs

abbrev hasEdge (U : Finset (Fin 16)) : Prop := ∃ e ∈ edgePairs, e.1 ∈ U ∧ e.2 ∈ U

def negativeList : List (Finset (Fin 16)) :=
  [{0, 1, 2, 3, 4}, {1, 2, 3, 4, 8}, {2, 3, 4, 5, 8}, {1, 3, 4, 6, 8}, {0, 1, 2, 4, 9}, {1, 2, 4, 8, 9}, {0, 1, 2, 3, 10}, {0, 2, 3, 7, 10}, {1, 2, 3, 8, 10}, {2, 3, 5, 7, 8, 10}, {0, 1, 2, 9, 10}, {0, 1, 3, 10, 11}, {1, 3, 6, 8, 10, 11}, {0, 2, 4, 9, 12}, {2, 4, 5, 8, 9, 12}, {0, 2, 7, 9, 10, 12}, {1, 2, 8, 9, 10, 13}, {2, 5, 7, 8, 9, 10, 12, 13}, {0, 1, 4, 9, 14}, {1, 4, 6, 8, 9, 14}, {0, 1, 9, 10, 11, 14}, {1, 6, 8, 9, 10, 11, 13, 14}, {0, 3, 4, 15}, {3, 4, 5, 6, 8, 15}, {0, 3, 7, 10, 11, 15}, {3, 5, 6, 7, 8, 10, 11, 15}, {0, 4, 9, 12, 14, 15}, {4, 5, 6, 8, 9, 12, 14, 15}, {0, 7, 9, 10, 11, 12, 14, 15}, {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}]

def family : Finset (Finset (Fin 16)) := negativeList.toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem family_card : family.card = 30 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem negative_check : negativeList.all (fun U => decide (¬hasEdge U)) = true := by decide +kernel

theorem family_negative (U : Finset (Fin 16)) (hU : U ∈ family) : ¬hasEdge U := by
  have hu : U ∈ negativeList := by simpa [family] using hU
  exact decide_eq_true_eq.mp (List.all_eq_true.mp negative_check U hu)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem pair_check : negativeList.all (fun U => negativeList.all
    (fun V => decide (U = V ∨ hasEdge (U ∪ V)))) = true := by decide +kernel

theorem pair_positive (U V : Finset (Fin 16)) (hU : U ∈ family) (hV : V ∈ family)
    (hne : U ≠ V) : hasEdge (U ∪ V) := by
  have hu : U ∈ negativeList := by simpa [family] using hU
  have hv : V ∈ negativeList := by simpa [family] using hV
  have h := List.all_eq_true.mp (List.all_eq_true.mp pair_check U hu) V hv
  exact (decide_eq_true_eq.mp h).resolve_left hne

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem singleton_count : ∀ v : Fin 16, 4 ≤ (family.filter fun U => v ∈ U).card := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem forbidden_pair_count : ∀ u v : Fin 16, ¬allowed u v →
    3 ≤ (family.filter fun U => u ∈ U ∧ v ∈ U).card := by decide +kernel

def dirtyTemplates : List (Fin 16 × Finset (Fin 16) × Finset (Fin 16)) :=
  [(1, {1}, {5, 7, 12, 13, 15}), (2, {2}, {6, 11, 13, 14, 15}), (1, {1, 13}, {5, 7, 12, 15}), (2, {2, 13}, {6, 11, 14, 15})]

def badOwner (k : Fin 4) : Fin 16 := (dirtyTemplates[k.val]?.getD (0,∅,∅)).1

def badLeft (k : Fin 4) : Finset (Fin 16) := (dirtyTemplates[k.val]?.getD (0,∅,∅)).2.1

def badRight (k : Fin 4) : Finset (Fin 16) := (dirtyTemplates[k.val]?.getD (0,∅,∅)).2.2

def badFamilies : List (List (Finset (Fin 16))) :=
  [[{1, 2, 8, 9, 10, 13}, {1, 6, 8, 9, 10, 11, 13, 14}], [{1, 2, 8, 9, 10, 13}, {2, 5, 7, 8, 9, 10, 12, 13}], [{2, 5, 7, 8, 9, 10, 12, 13}, {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}], [{1, 6, 8, 9, 10, 11, 13, 14}, {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}]]

def badList (k : Fin 4) : List (Finset (Fin 16)) := badFamilies[k.val]?.getD []

def badFamily (k : Fin 4) : Finset (Finset (Fin 16)) := (badList k).toFinset

def witnesses : List (List (Finset (Fin 16))) :=
  [[{1, 2, 8, 9, 10, 13}, ∅, {1, 6, 8, 9, 10, 11, 13, 14}, {1, 2, 8, 9, 10, 13}, {1, 2, 8, 9, 10, 13}], [{1, 2, 8, 9, 10, 13}, {2, 5, 7, 8, 9, 10, 12, 13}, ∅, {1, 2, 8, 9, 10, 13}, {1, 2, 8, 9, 10, 13}], [{2, 5, 7, 8, 9, 10, 12, 13}, ∅, {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}, {2, 5, 7, 8, 9, 10, 12, 13}, {2, 5, 7, 8, 9, 10, 12, 13}], [{1, 6, 8, 9, 10, 11, 13, 14}, {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}, ∅, {1, 6, 8, 9, 10, 11, 13, 14}, {1, 6, 8, 9, 10, 11, 13, 14}]]

def witness (k : Fin 4) (j : Fin 5) : Finset (Fin 16) :=
  ((witnesses[k.val]?.getD [])[j.val]?).getD ∅

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bad_card : ∀ k : Fin 4, (badFamily k).card = 2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bad_check : ∀ k : Fin 4, (badList k).all (fun U => decide
    (U ∈ family ∧ (∃ u ∈ badLeft k, u ∈ U) ∧ (∃ v ∈ badRight k, v ∈ U))) = true := by
  decide +kernel

theorem dirty_family_check : ∀ k : Fin 4,
    (badFamily k).card = 2 ∧ badFamily k ⊆ family ∧
    ∀ U ∈ badFamily k, (∃ u ∈ badLeft k, u ∈ U) ∧ (∃ v ∈ badRight k, v ∈ U) := by
  intro k
  have data : ∀ U ∈ badFamily k, U ∈ family ∧
      (∃ u ∈ badLeft k, u ∈ U) ∧ (∃ v ∈ badRight k, v ∈ U) := by
    intro U hU
    have hlist : U ∈ badList k := by simpa [badFamily] using hU
    exact decide_eq_true_eq.mp (List.all_eq_true.mp (bad_check k) U hlist)
  exact ⟨bad_card k,fun U hU => (data U hU).1,fun U hU => (data U hU).2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem other_owner_witness : ∀ (k : Fin 4) (j : Fin 5),
    (Fin.castAdd 11 j : Fin 16) ≠ badOwner k →
    witness k j ∈ badFamily k ∧ Fin.castAdd 11 j ∉ witness k j ∧
      ∃ l : Fin 16, (Fin.castAdd 11 j,l) ∈ edgePairs ∧ l ∈ witness k j := by decide +kernel

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerNegatives

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_meta_9033_aux

def edges : List (Fin 256) := [65, 129, 10, 34, 20, 132, 40, 136, 48, 80, 96]

def negatives : List (Fin 256) := [7, 13, 19, 25, 37, 70, 76, 146, 160, 194]

def columns : List Nat := [2147418115, 663661903884, 34144976944,
  21653750532, 103293914128, 414195942664, 581968119809, 1065151898146]

def rows : List (Fin 256) := [65, 129, 10, 34, 20, 132, 0, 0, 40, 136,
  48, 80, 0, 128, 64, 96, 7, 13, 19, 25, 7, 13, 19, 25, 7, 13,
  19, 25, 37, 37, 37, 70, 76, 70, 76, 146, 146, 160, 160, 194]

abbrev submask (a b : Fin 256) : Prop := a.val &&& b.val = a.val

def edgeFunction (x : Fin 256) : Bool := edges.any fun e => decide (submask e x)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma column_rows : ∀ (i : Fin 8) (k : Fin 40),
    (columns.getD i.val 0).testBit k.val =
      (rows.getD k.val 0).val.testBit i.val := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma target_rows : ∀ k : Fin 40,
    edgeFunction (rows.getD k.val 0) = (36671 : Nat).testBit k.val := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma negatives_appear : ∀ n ∈ negatives,
    ∃ k : Fin 24, rows.getD (16 + k.val) 0 = n := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma independent_covered : ∀ x : Fin 256, edgeFunction x = false →
    ∃ y ∈ negatives, submask x y := by
  decide +kernel

lemma monotone_table_unique (f : Fin 256 → Bool)
    (mono : ∀ a b, submask a b → f a = true → f b = true)
    (positive : ∀ e ∈ edges, f e = true)
    (negative : ∀ n ∈ negatives, f n = false) :
    ∀ x, f x = edgeFunction x := by
  intro x
  cases hx : edgeFunction x with
  | false =>
    obtain ⟨n, hn, hxn⟩ := independent_covered x hx
    cases hfx : f x with
    | false => rfl
    | true =>
      have hntrue := mono x n hxn hfx
      rw [negative n hn] at hntrue
      contradiction
  | true =>
    obtain ⟨e, he, hex⟩ := List.any_eq_true.mp hx
    exact mono e x (of_decide_eq_true hex) (positive e he)

namespace CoreMIM

abbrev G (n : Nat) := List (Fin n × Fin n)

def noLoop {n : Nat} (E : G n) : Bool := E.all fun e => e.1 != e.2

def isIM {n : Nat} (E : G n) (m : Nat) : Bool :=
  E.all fun e => !(m.testBit e.1.val && m.testBit e.2.val)

def isMIM (n : Nat) (E : G n) (m : Nat) : Bool :=
  isIM E m && (List.finRange n).all fun v =>
    m.testBit v.val || !isIM E (Nat.lor m (1 <<< v.val))

def mIMs (n : Nat) (E : G n) : List Nat :=
  (List.range (2 ^ n)).filter (isMIM n E)

def coreEdges : G 5 := [(0, 2), (0, 4), (1, 2), (1, 3), (2, 3)]

set_option maxRecDepth 10000 in
lemma core_loopless : noLoop coreEdges = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma core_maximal_independent_sets : mIMs 5 coreEdges = [3, 9, 18, 20, 24] := by
  decide +kernel

lemma core_mk3_premise : noLoop coreEdges = true ∧ 5 ≤ (mIMs 5 coreEdges).length := by
  rw [core_maximal_independent_sets]
  exact ⟨core_loopless, by decide⟩

end CoreMIM


namespace UnionCatalog

def bases : List Nat := [0, 1, 2, 4, 8, 16, 32, 64, 128]

def locallyConstructible (family : List Nat) (extra : Nat) : Bool :=
  let pool := bases ++ family ++ [extra]
  (family ++ [extra]).all fun target =>
    bases.contains target || pool.any (fun a =>
      decide (a < target) && pool.any (fun b =>
        decide (b < target) && (Nat.lor a b == target)))



def family4_0 : List Nat := [17, 90, 176, 192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_0_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_0 extra) = true := by
  decide +kernel

def family4_1 : List Nat := [17, 91, 144, 192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_1_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_1 extra) = true := by
  decide +kernel

def family4_2 : List Nat := [18, 176, 192, 226]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_2_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_2 extra) = true := by
  decide +kernel

def family4_3 : List Nat := [26, 176, 192, 194]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_3_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_3 extra) = true := by
  decide +kernel

def family4_4 : List Nat := [26, 176, 192, 226]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_4_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_4 extra) = true := by
  decide +kernel

def family4_5 : List Nat := [66, 144, 178, 224]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_5_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_5 extra) = true := by
  decide +kernel

def family4_6 : List Nat := [68, 90, 144, 224]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_6_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_6 extra) = true := by
  decide +kernel

def family4_7 : List Nat := [68, 94, 144, 192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_7_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_7 extra) = true := by
  decide +kernel

def family4_8 : List Nat := [74, 144, 146, 224]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_8_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_8 extra) = true := by
  decide +kernel

def family4_9 : List Nat := [74, 144, 178, 224]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_9_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_9 extra) = true := by
  decide +kernel

def family4_10 : List Nat := [82, 144, 178, 224]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_10_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_10 extra) = true := by
  decide +kernel

def family4_11 : List Nat := [82, 176, 192, 226]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_11_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_11 extra) = true := by
  decide +kernel

def family4_12 : List Nat := [83, 144, 178, 192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_12_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_12 extra) = true := by
  decide +kernel

def family4_13 : List Nat := [86, 144, 192, 226]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_13_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_13 extra) = true := by
  decide +kernel

def family4_14 : List Nat := [90, 144, 146, 224]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_14_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_14 extra) = true := by
  decide +kernel

def family4_15 : List Nat := [90, 144, 178, 224]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_15_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_15 extra) = true := by
  decide +kernel

def family4_16 : List Nat := [90, 176, 192, 194]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_16_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_16 extra) = true := by
  decide +kernel

def family4_17 : List Nat := [90, 176, 192, 226]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_17_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_17 extra) = true := by
  decide +kernel

def family4_18 : List Nat := [91, 144, 146, 192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_18_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_18 extra) = true := by
  decide +kernel

def family4_19 : List Nat := [91, 144, 178, 192]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_19_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_19 extra) = true := by
  decide +kernel

def family4_20 : List Nat := [94, 144, 192, 194]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_20_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_20 extra) = true := by
  decide +kernel

def family4_21 : List Nat := [94, 144, 192, 226]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma family4_21_obstruction : (List.range 256).all (fun extra => !locallyConstructible family4_21 extra) = true := by
  decide +kernel

def fiveFamilies : List (List Nat) := [
  [5, 40, 41, 176, 228],
  [5, 40, 44, 177, 224],
  [5, 40, 57, 164, 176],
  [5, 40, 57, 176, 228],
  [5, 40, 108, 161, 224],
  [5, 40, 108, 177, 224],
  [9, 18, 40, 144, 224],
  [9, 18, 40, 176, 224],
  [9, 18, 66, 144, 224],
  [9, 18, 74, 144, 224],
  [9, 18, 82, 144, 224],
  [9, 18, 90, 144, 192],
  [9, 18, 90, 144, 224],
  [9, 18, 144, 176, 224],
  [9, 40, 68, 144, 224],
  [9, 40, 144, 160, 177],
  [9, 40, 144, 176, 224],
  [9, 40, 144, 177, 224],
  [9, 50, 66, 144, 224],
  [9, 50, 74, 144, 224],
  [9, 50, 82, 144, 192],
  [9, 50, 82, 144, 224],
  [9, 50, 90, 144, 192],
  [9, 50, 90, 144, 224],
  [9, 66, 144, 146, 224],
  [9, 66, 144, 178, 224],
  [9, 68, 82, 144, 224],
  [9, 68, 90, 144, 192],
  [9, 68, 90, 144, 224],
  [9, 74, 144, 146, 224],
  [9, 74, 144, 178, 224],
  [9, 82, 144, 146, 224],
  [9, 82, 144, 178, 192],
  [9, 82, 144, 178, 224],
  [9, 90, 144, 146, 192],
  [9, 90, 144, 146, 224],
  [9, 90, 144, 178, 192],
  [9, 90, 144, 178, 224],
  [12, 17, 40, 176, 192],
  [12, 17, 82, 176, 192],
  [12, 17, 90, 144, 192],
  [12, 17, 90, 176, 192],
  [12, 18, 66, 176, 192],
  [12, 18, 98, 176, 192],
  [12, 18, 176, 192, 194],
  [12, 18, 176, 192, 226],
  [12, 26, 66, 176, 192],
  [12, 26, 98, 176, 192],
  [12, 26, 176, 192, 194],
  [12, 26, 176, 192, 226],
  [12, 40, 66, 176, 192],
  [12, 40, 66, 176, 224],
  [12, 40, 160, 192, 228],
  [12, 40, 176, 192, 224],
  [12, 40, 176, 192, 228],
  [12, 66, 82, 176, 192],
  [12, 66, 90, 144, 192],
  [12, 66, 90, 176, 192],
  [12, 66, 176, 192, 224],
  [12, 82, 98, 144, 192],
  [12, 82, 98, 176, 192],
  [12, 82, 144, 192, 226],
  [12, 82, 176, 192, 194],
  [12, 82, 176, 192, 226],
  [12, 90, 98, 144, 192],
  [12, 90, 98, 176, 192],
  [12, 90, 144, 192, 194],
  [12, 90, 144, 192, 226],
  [12, 90, 176, 192, 194],
  [12, 90, 176, 192, 226],
  [13, 40, 41, 48, 228],
  [13, 40, 41, 176, 228],
  [13, 40, 44, 96, 177],
  [13, 40, 44, 177, 224],
  [13, 40, 48, 57, 164],
  [13, 40, 48, 57, 228],
  [13, 40, 57, 164, 176],
  [13, 40, 57, 176, 228],
  [13, 40, 96, 108, 161],
  [13, 40, 96, 108, 177],
  [13, 40, 108, 161, 224],
  [13, 40, 108, 177, 224],
  [17, 34, 82, 176, 192],
  [17, 34, 83, 144, 192],
  [17, 34, 90, 176, 192],
  [17, 34, 91, 144, 192],
  [17, 40, 88, 176, 192],
  [17, 40, 89, 144, 192],
  [17, 40, 90, 176, 192],
  [17, 40, 91, 144, 192],
  [17, 40, 92, 144, 192],
  [17, 66, 90, 144, 192],
  [17, 82, 98, 144, 192],
  [17, 82, 144, 192, 226],
  [17, 82, 162, 176, 192],
  [17, 82, 176, 192, 224],
  [17, 83, 144, 162, 192],
  [17, 83, 144, 176, 192],
  [17, 90, 98, 144, 192],
  [17, 90, 130, 176, 192],
  [17, 90, 144, 192, 194],
  [17, 90, 144, 192, 226],
  [17, 90, 162, 176, 192],
  [17, 90, 176, 192, 224],
  [17, 91, 130, 144, 192],
  [17, 91, 144, 162, 192],
  [17, 91, 144, 176, 192],
  [18, 68, 90, 144, 192],
  [18, 144, 176, 178, 224],
  [19, 144, 176, 178, 192],
  [21, 33, 40, 108, 224],
  [21, 36, 40, 57, 176],
  [21, 40, 41, 100, 176],
  [21, 40, 44, 49, 224],
  [21, 40, 49, 108, 224],
  [21, 40, 57, 100, 176],
  [22, 144, 176, 192, 226],
  [26, 144, 146, 176, 224],
  [26, 144, 176, 178, 224],
  [27, 144, 146, 176, 192],
  [27, 144, 176, 178, 192],
  [29, 33, 40, 96, 108],
  [29, 33, 40, 108, 224],
  [29, 36, 40, 48, 57],
  [29, 36, 40, 57, 176],
  [29, 40, 41, 48, 100],
  [29, 40, 41, 100, 176],
  [29, 40, 44, 49, 96],
  [29, 40, 44, 49, 224],
  [29, 40, 48, 57, 100],
  [29, 40, 49, 96, 108],
  [29, 40, 49, 108, 224],
  [29, 40, 57, 100, 176],
  [30, 144, 176, 192, 194],
  [30, 144, 176, 192, 226],
  [33, 40, 69, 108, 224],
  [33, 40, 77, 96, 108],
  [33, 40, 77, 108, 224],
  [33, 40, 85, 108, 224],
  [33, 40, 93, 96, 108],
  [33, 40, 93, 108, 224],
  [34, 68, 82, 144, 224],
  [34, 68, 86, 144, 192],
  [34, 68, 90, 144, 224],
  [34, 68, 94, 144, 192],
  [36, 40, 48, 57, 77],
  [36, 40, 48, 57, 93],
  [36, 40, 57, 69, 176],
  [36, 40, 57, 77, 176],
  [36, 40, 57, 85, 176],
  [36, 40, 57, 93, 176],
  [40, 41, 48, 77, 100],
  [40, 41, 48, 93, 100],
  [40, 41, 69, 100, 176],
  [40, 41, 77, 100, 176],
  [40, 41, 85, 100, 176],
  [40, 41, 93, 100, 176],
  [40, 44, 49, 69, 224],
  [40, 44, 49, 77, 96],
  [40, 44, 49, 77, 224],
  [40, 44, 49, 85, 224],
  [40, 44, 49, 93, 96],
  [40, 44, 49, 93, 224],
  [40, 48, 57, 77, 100],
  [40, 48, 57, 93, 100],
  [40, 49, 69, 108, 224],
  [40, 49, 77, 96, 108],
  [40, 49, 77, 108, 224],
  [40, 49, 85, 108, 224],
  [40, 49, 93, 96, 108],
  [40, 49, 93, 108, 224],
  [40, 57, 69, 100, 176],
  [40, 57, 77, 100, 176],
  [40, 57, 85, 100, 176],
  [40, 57, 93, 100, 176],
  [40, 68, 88, 144, 224],
  [40, 68, 89, 144, 192],
  [40, 68, 90, 144, 224],
  [40, 68, 92, 144, 192],
  [40, 68, 94, 144, 192],
  [50, 68, 82, 144, 192],
  [50, 68, 90, 144, 192],
  [66, 176, 192, 224, 226],
  [67, 144, 178, 192, 224],
  [68, 82, 144, 162, 224],
  [68, 82, 144, 176, 224],
  [68, 82, 144, 178, 192],
  [68, 86, 144, 162, 192],
  [68, 86, 144, 192, 224],
  [68, 90, 130, 144, 224],
  [68, 90, 144, 146, 192],
  [68, 90, 144, 162, 224],
  [68, 90, 144, 176, 224],
  [68, 90, 144, 178, 192],
  [68, 94, 130, 144, 192],
  [68, 94, 144, 162, 192],
  [68, 94, 144, 192, 224],
  [70, 144, 192, 224, 226],
  [74, 176, 192, 194, 224],
  [74, 176, 192, 224, 226],
  [75, 144, 146, 192, 224],
  [75, 144, 178, 192, 224],
  [78, 144, 192, 194, 224],
  [78, 144, 192, 224, 226],
  [82, 144, 176, 178, 224],
  [82, 144, 176, 192, 226],
  [82, 144, 178, 192, 224],
  [82, 176, 192, 224, 226],
  [83, 144, 176, 178, 192],
  [83, 144, 178, 192, 224],
  [86, 144, 176, 192, 226],
  [86, 144, 192, 224, 226],
  [90, 144, 146, 176, 224],
  [90, 144, 146, 192, 224],
  [90, 144, 176, 178, 224],
  [90, 144, 176, 192, 194],
  [90, 144, 176, 192, 226],
  [90, 144, 178, 192, 224],
  [90, 176, 192, 194, 224],
  [90, 176, 192, 224, 226],
  [91, 144, 146, 176, 192],
  [91, 144, 146, 192, 224],
  [91, 144, 176, 178, 192],
  [91, 144, 178, 192, 224],
  [94, 144, 176, 192, 194],
  [94, 144, 176, 192, 226],
  [94, 144, 192, 194, 224],
  [94, 144, 192, 224, 226]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma five_families_obstruction : fiveFamilies.all (fun family => !locallyConstructible family 0) = true := by
  decide +kernel

def checkedCatalog : Prop :=
  ((List.range 256).all (fun extra => !locallyConstructible family4_0 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_1 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_2 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_3 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_4 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_5 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_6 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_7 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_8 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_9 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_10 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_11 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_12 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_13 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_14 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_15 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_16 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_17 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_18 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_19 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_20 extra) = true) ∧
  ((List.range 256).all (fun extra => !locallyConstructible family4_21 extra) = true) ∧
  (fiveFamilies.all (fun family => !locallyConstructible family 0) = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma checkedCatalog_proof : checkedCatalog :=
  ⟨family4_0_obstruction, family4_1_obstruction, family4_2_obstruction, family4_3_obstruction, family4_4_obstruction, family4_5_obstruction, family4_6_obstruction, family4_7_obstruction, family4_8_obstruction, family4_9_obstruction, family4_10_obstruction, family4_11_obstruction, family4_12_obstruction, family4_13_obstruction, family4_14_obstruction, family4_15_obstruction, family4_16_obstruction, family4_17_obstruction, family4_18_obstruction, family4_19_obstruction, family4_20_obstruction, family4_21_obstruction, five_families_obstruction⟩


lemma locallyConstructible_iff (family : List Nat) (extra : Nat) :
    locallyConstructible family extra = true ↔
      ∀ target ∈ family ++ [extra], target ∈ bases ∨
        ∃ a ∈ bases ++ family ++ [extra], a < target ∧
          ∃ b ∈ bases ++ family ++ [extra], b < target ∧ Nat.lor a b = target := by
  simp only [locallyConstructible, List.all_eq_true, Bool.or_eq_true,
    List.contains_iff_mem, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq]

end UnionCatalog

namespace PreservedMaskBudget

lemma value_origin {α : Type} [DecidableEq α]
    (n : Nat) (value : Nat → α) (base : Finset α) (eligible : Nat → Bool)
    (preserved : ∀ i, i < n → eligible i = false →
      value i ∈ base ∨ ∃ j, j < i ∧ value j = value i) :
    ∀ i, i < n → value i ∈ base ∨
      ∃ j, j < n ∧ eligible j = true ∧ value j = value i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    cases he : eligible i with
    | true => exact Or.inr ⟨i, hi, he, rfl⟩
    | false =>
      rcases preserved i hi he with hb | ⟨j, hji, hjv⟩
      · exact Or.inl hb
      · rcases ih j hji (Nat.lt_trans hji hi) with hb | ⟨k, hk, hke, hkv⟩
        · exact Or.inl (hjv ▸ hb)
        · exact Or.inr ⟨k, hk, hke, hkv.trans hjv⟩

lemma distinct_values_le_eligible {α : Type} [DecidableEq α]
    (n : Nat) (value : Nat → α) (base : Finset α) (eligible : Nat → Bool)
    (preserved : ∀ i, i < n → eligible i = false →
      value i ∈ base ∨ ∃ j, j < i ∧ value j = value i) :
    ((Finset.range n).image value \ base).card ≤
      ((Finset.range n).filter fun i => eligible i = true).card := by
  calc
    ((Finset.range n).image value \ base).card ≤
        (((Finset.range n).filter fun i => eligible i = true).image value).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hx, hxb⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hx
      rcases value_origin n value base eligible preserved i (Finset.mem_range.mp hi) with
        hb | ⟨j, hj, hje, hjv⟩
      · exact False.elim (hxb (hiv ▸ hb))
      · exact Finset.mem_image.mpr
          ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hje⟩, hjv.trans hiv⟩
    _ ≤ ((Finset.range n).filter fun i => eligible i = true).card := Finset.card_image_le

end PreservedMaskBudget


namespace CleanRectangle

def adjacent (a b : Fin 8) : Bool :=
  (edges.map Fin.val).contains (Nat.lor (2 ^ a.val) (2 ^ b.val))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma no_complete_two_by_two : ∀ a b c d : Fin 8,
    a ≠ b → c ≠ d →
      ¬(adjacent a c = true ∧ adjacent a d = true ∧ adjacent b c = true ∧ adjacent b d = true) := by
  decide +kernel

lemma rectangle_star (S T : Finset (Fin 8))
    (cross : ∀ a ∈ S, ∀ b ∈ T, adjacent a b = true) :
    S.card ≤ 1 ∨ T.card ≤ 1 := by
  by_contra h
  have hs : 1 < S.card := Nat.lt_of_not_ge (fun hS => h (Or.inl hS))
  have ht : 1 < T.card := Nat.lt_of_not_ge (fun hT => h (Or.inr hT))
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hs
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp ht
  exact no_complete_two_by_two a b c d hab hcd
    ⟨cross a ha c hc, cross a ha d hd, cross b hb c hc, cross b hb d hd⟩

end CleanRectangle

namespace RawPairClassification

def graphEdges : List Nat := edges.map Fin.val

def maximalIndependent : List Nat := negatives.map Fin.val

def allowedNegatives (v : Fin 3) : List Nat :=
  [[25, 37], [146, 194], [37, 76]].getD v.val []

def criticalPairs (v : Fin 3) : List Nat :=
  [[24, 36], [144, 192], [33, 72]].getD v.val []

def pairMask (i j : Fin 8) : Nat := Nat.lor (1 <<< i.val) (1 <<< j.val)

lemma pairMask_lt : ∀ i j : Fin 8, pairMask i j < 256 := by
  decide +kernel

def pairAssignment (i j : Fin 8) : Fin 256 := ⟨pairMask i j, pairMask_lt i j⟩

def hitsForbidden (v : Fin 3) (p : Nat) : Bool :=
  maximalIndependent.any fun n =>
    !(allowedNegatives v).contains n && (p &&& n == p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma outside_pair_characterization : ∀ (v : Fin 3) (i j : Fin 8),
    i ≠ j → i.val ≠ v.val → j.val ≠ v.val →
    (hitsForbidden v (pairMask i j) = false ↔
      pairMask i j ∈ graphEdges ∨ pairMask i j ∈ criticalPairs v) := by
  decide +kernel


lemma permitted_pair_of_monotone (v : Fin 3) (q : Fin 256 → Bool)
    (mono : ∀ a b, submask a b → q a = true → q b = true)
    (negative : ∀ n ∈ negatives, (allowedNegatives v).contains n.val = false →
      q n = false)
    (i j : Fin 8) (hij : i ≠ j) (hiv : i.val ≠ v.val) (hjv : j.val ≠ v.val)
    (accepted : q (pairAssignment i j) = true) :
    pairMask i j ∈ graphEdges ∨ pairMask i j ∈ criticalPairs v := by
  apply (outside_pair_characterization v i j hij hiv hjv).mp
  cases hh : hitsForbidden v (pairMask i j) with
  | false => rfl
  | true =>
    exfalso
    change (maximalIndependent.any fun n =>
      !(allowedNegatives v).contains n && (pairMask i j &&& n == pairMask i j)) = true at hh
    obtain ⟨n, hn, h⟩ := List.any_eq_true.mp hh
    simp only [Bool.and_eq_true] at h
    obtain ⟨ha, hm⟩ := h
    have hblocked : (allowedNegatives v).contains n = false := by simpa using ha
    have hsub : pairMask i j &&& n = pairMask i j := beq_iff_eq.mp hm
    change n ∈ negatives.map Fin.val at hn
    obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hn
    have htrue := mono (pairAssignment i j) N hsub accepted
    rw [negative N hN hblocked] at htrue
    contradiction

end RawPairClassification

namespace RawPairClassification

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma singleton_forbidden_witness : ∀ (v : Fin 3) (i : Fin 8),
    ∃ n ∈ negatives, (allowedNegatives v).contains n.val = false ∧
      submask (pairAssignment i i) n := by
  decide +kernel

lemma singleton_false_of_monotone (v : Fin 3) (q : Fin 256 → Bool)
    (mono : ∀ a b, submask a b → q a = true → q b = true)
    (negative : ∀ n ∈ negatives,
      (allowedNegatives v).contains n.val = false → q n = false)
    (i : Fin 8) : q (pairAssignment i i) = false := by
  obtain ⟨n, hn, hblocked, hsub⟩ := singleton_forbidden_witness v i
  cases hq : q (pairAssignment i i) with
  | false => rfl
  | true =>
      have htrue := mono (pairAssignment i i) n hsub hq
      rw [negative n hn hblocked] at htrue
      contradiction

end RawPairClassification

namespace CleanRectangle

open RawPairClassification

lemma pair_submask : ∀ i j : Fin 8,
    submask (pairAssignment i i) (pairAssignment i j) ∧
      submask (pairAssignment j j) (pairAssignment i j) := by
  decide +kernel

lemma pair_graph : ∀ i j : Fin 8,
    edgeFunction (pairAssignment i j) = adjacent i j := by
  decide +kernel

lemma clean_function_below_graph (q : Fin 256 → Bool)
    (mono : ∀ a b, submask a b → q a = true → q b = true)
    (negative : ∀ n ∈ negatives, q n = false) :
    ∀ x, q x = true → edgeFunction x = true := by
  intro x hq
  cases hx : edgeFunction x with
  | true => rfl
  | false =>
    obtain ⟨n, hn, hxn⟩ := independent_covered x hx
    have hqn := mono x n hxn hq
    rw [negative n hn] at hqn
    contradiction

lemma clean_and_star (f g : Fin 256 → Bool)
    (mf : ∀ a b, submask a b → f a = true → f b = true)
    (mg : ∀ a b, submask a b → g a = true → g b = true)
    (negative : ∀ n ∈ negatives, (f n && g n) = false) :
    ((Finset.univ : Finset (Fin 8)).filter fun i => f (pairAssignment i i) = true).card ≤ 1 ∨
      ((Finset.univ : Finset (Fin 8)).filter fun i => g (pairAssignment i i) = true).card ≤ 1 := by
  apply rectangle_star
  intro i hi j hj
  have hfi := (Finset.mem_filter.mp hi).2
  have hgj := (Finset.mem_filter.mp hj).2
  have hf := mf _ _ (pair_submask i j).1 hfi
  have hg := mg _ _ (pair_submask i j).2 hgj
  have monoAnd : ∀ a b, submask a b →
      (f a && g a) = true → (f b && g b) = true := by
    intro a b hab h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨mf a b hab h.1, mg a b hab h.2⟩
  have he := clean_function_below_graph (fun x => f x && g x) monoAnd negative
    (pairAssignment i j) (by simp only [hf, hg, Bool.and_self])
  exact (pair_graph i j).symm.trans he

end CleanRectangle

namespace PreservedMaskBudget

lemma proper_union_of_trace (n : Nat) (value : Nat → Nat) (base : Finset Nat)
    (trace : ∀ i, i < n → value i ∈ base ∨
      ∃ a b, a < i ∧ b < i ∧ (value a ||| value b) = value i) :
    ∀ i, i < n → value i ∉ base →
      ∃ a b, a < n ∧ b < n ∧ value a < value i ∧ value b < value i ∧
        (value a ||| value b) = value i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi hnon
    rcases trace i hi with hb | ⟨a, b, hai, hbi, hab⟩
    · exact False.elim (hnon hb)
    · by_cases ha : value a = value i
      · simpa only [ha] using ih a hai (Nat.lt_trans hai hi) (by simpa only [ha] using hnon)
      by_cases hb : value b = value i
      · simpa only [hb] using ih b hbi (Nat.lt_trans hbi hi) (by simpa only [hb] using hnon)
      have hla : value a ≤ value i := hab ▸ Nat.left_le_or
      have hlb : value b ≤ value i := hab ▸ Nat.right_le_or
      exact ⟨a, b, Nat.lt_trans hai hi, Nat.lt_trans hbi hi, by omega, by omega, hab⟩

lemma trace_nonbase_closed (n : Nat) (value : Nat → Nat) (base : Finset Nat)
    (trace : ∀ i, i < n → value i ∈ base ∨
      ∃ a b, a < i ∧ b < i ∧ (value a ||| value b) = value i) :
    let S := (Finset.range n).image value \ base
    ∀ x ∈ S, ∃ a ∈ S ∪ base, ∃ b ∈ S ∪ base,
      a < x ∧ b < x ∧ (a ||| b) = x := by
  intro S x hx
  obtain ⟨hx, hxb⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hx
  obtain ⟨a, b, ha, hb, hax, hbx, hab⟩ :=
    proper_union_of_trace n value base trace i (Finset.mem_range.mp hi)
      (by simpa only [hiv] using hxb)
  have member : ∀ j, j < n → value j ∈ S ∪ base := by
    intro j hj
    by_cases hbase : value j ∈ base
    · exact Finset.mem_union_right S hbase
    · exact Finset.mem_union_left base (Finset.mem_sdiff.mpr
        ⟨Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩, hbase⟩)
  exact ⟨value a, member a ha, value b, member b hb,
    hiv ▸ hax, hiv ▸ hbx, hab.trans hiv⟩

end PreservedMaskBudget

namespace CleanForestCount

lemma binary_forest_count {ι : Type} [DecidableEq ι]
    (clean leaves : Finset ι) (hleaves : leaves ⊆ clean)
    (out : ι) (hout : out ∈ clean) (reads : ι → ι → Nat)
    (incoming : ∀ i ∈ clean, (∑ j ∈ clean, reads i j) =
      if i ∈ leaves then 0 else 2)
    (outgoing : ∀ j ∈ clean, (∑ i ∈ clean, reads i j) =
      if j = out then 0 else 1) :
    (clean \ leaves).card + 1 = leaves.card := by
  have htotal : (∑ i ∈ clean, if i ∈ leaves then 0 else 2) =
      ∑ j ∈ clean, if j = out then 0 else 1 := by
    calc
      _ = ∑ i ∈ clean, ∑ j ∈ clean, reads i j := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (incoming i hi).symm
      _ = ∑ j ∈ clean, ∑ i ∈ clean, reads i j := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        exact outgoing
  have hrow : (∑ i ∈ clean, if i ∈ leaves then 0 else 2) =
      (clean \ leaves).card * 2 := by
    have hf : clean.filter (fun i => i ∉ leaves) = clean \ leaves := by
      ext i
      simp
    calc
      _ = ∑ i ∈ clean.filter (fun i => i ∉ leaves), 2 := by
        rw [Finset.sum_filter]
        simp
      _ = _ := by rw [hf]; simp
  have hcol : (∑ j ∈ clean, if j = out then 0 else 1) = clean.card - 1 := by
    have hf : clean.filter (fun j => j ≠ out) = clean.erase out := by
      ext j
      simp [and_comm]
    calc
      _ = ∑ j ∈ clean.filter (fun j => j ≠ out), 1 := by
        rw [Finset.sum_filter]
        simp
      _ = _ := by rw [hf]; simp [Finset.card_erase_of_mem hout]
  rw [hrow, hcol] at htotal
  have hd := Finset.card_sdiff_of_subset hleaves
  have hp : 0 < clean.card := Finset.card_pos.mpr ⟨out, hout⟩
  have hl := Finset.card_le_card hleaves
  omega

end CleanForestCount

namespace RawPairClassification

def ownVariable (v : Fin 3) : Fin 8 := ⟨v.val, by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma pair_in_negative_not_graph : ∀ n ∈ negatives, ∀ i j : Fin 8,
    submask (pairAssignment i i) n → submask (pairAssignment j j) n →
      pairMask i j ∉ graphEdges := by
  decide +kernel

lemma critical_pair_of_negative_linear (v : Fin 3) (f g : Fin 256 → Bool)
    (mf : ∀ a b, submask a b → f a = true → f b = true)
    (mg : ∀ a b, submask a b → g a = true → g b = true)
    (negative : ∀ n ∈ negatives,
      (allowedNegatives v).contains n.val = false → (f n && g n) = false)
    (ownF : f (pairAssignment (ownVariable v) (ownVariable v)) = false)
    (ownG : g (pairAssignment (ownVariable v) (ownVariable v)) = false)
    (linearF : ∀ n ∈ negatives, (f n && g n) = true →
      ∃ i : Fin 8, submask (pairAssignment i i) n ∧ f (pairAssignment i i) = true)
    (linearG : ∀ n ∈ negatives, (f n && g n) = true →
      ∃ j : Fin 8, submask (pairAssignment j j) n ∧ g (pairAssignment j j) = true)
    (dirty : ∃ n ∈ negatives, (f n && g n) = true) :
    ∃ i j : Fin 8, f (pairAssignment i i) = true ∧
      g (pairAssignment j j) = true ∧ pairMask i j ∈ criticalPairs v := by
  have monoAnd : ∀ a b, submask a b →
      (f a && g a) = true → (f b && g b) = true := by
    intro a b hab h
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨mf a b hab h.1, mg a b hab h.2⟩
  obtain ⟨n, hn, hdirty⟩ := dirty
  obtain ⟨i, hsubi, hfi⟩ := linearF n hn hdirty
  obtain ⟨j, hsubj, hgj⟩ := linearG n hn hdirty
  have hiv : i.val ≠ v.val := by
    intro he
    have hi : i = ownVariable v := Fin.ext he
    rw [hi, ownF] at hfi
    contradiction
  have hjv : j.val ≠ v.val := by
    intro he
    have hj : j = ownVariable v := Fin.ext he
    rw [hj, ownG] at hgj
    contradiction
  have hij : i ≠ j := by
    intro he
    subst j
    have hfalse := singleton_false_of_monotone v (fun x => f x && g x)
      monoAnd negative i
    simp only [hfi, hgj, Bool.and_self] at hfalse
    contradiction
  have accepted : (f (pairAssignment i j) && g (pairAssignment i j)) = true := by
    have hf := mf _ _ (CleanRectangle.pair_submask i j).1 hfi
    have hg := mg _ _ (CleanRectangle.pair_submask i j).2 hgj
    simp only [hf, hg, Bool.and_self]
  rcases permitted_pair_of_monotone v (fun x => f x && g x) monoAnd negative
    i j hij hiv hjv accepted with hgraph | hcritical
  · exact False.elim ((pair_in_negative_not_graph n hn i j hsubi hsubj) hgraph)
  · exact ⟨i, j, hfi, hgj, hcritical⟩

end RawPairClassification

namespace SingletonMaskBridge

lemma high_bit_false (mask : Fin 256) (i : Nat) (hi : 8 ≤ i) :
    mask.val.testBit i = false := by
  have hp : 2 ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le mask.isLt hp)

lemma disjoint_of_bits (left right : Fin 256)
    (h : ∀ i : Fin 8, (left.val.testBit i.val && right.val.testBit i.val) = false) :
    left.val &&& right.val = 0 := by
  apply Nat.zero_of_testBit_eq_false
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 8
  · exact h ⟨i, hi⟩
  · rw [high_bit_false left i (Nat.le_of_not_lt hi)]
    rfl

lemma submask_of_bits (mask : Fin 256) (available : Nat)
    (h : ∀ i : Fin 8, mask.val.testBit i.val = true → available.testBit i.val = true) :
    mask.val &&& available = mask.val := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 8
  · cases hm : mask.val.testBit i with
    | false => rfl
    | true => rw [h ⟨i, hi⟩ hm]; rfl
  · rw [high_bit_false mask i (Nat.le_of_not_lt hi)]
    rfl

lemma disjoint_of_encoded_singletons (f g : Fin 256 → Bool) (left right : Fin 256)
    (hl : ∀ i : Fin 8, left.val.testBit i.val = f (RawPairClassification.pairAssignment i i))
    (hr : ∀ i : Fin 8, right.val.testBit i.val = g (RawPairClassification.pairAssignment i i))
    (hz : ∀ i : Fin 8,
      (f (RawPairClassification.pairAssignment i i) &&
        g (RawPairClassification.pairAssignment i i)) = false) :
    left.val &&& right.val = 0 := by
  apply disjoint_of_bits
  intro i
  rw [hl i, hr i]
  exact hz i

end SingletonMaskBridge

end PEqualNP.Outside.L_meta_9033_aux

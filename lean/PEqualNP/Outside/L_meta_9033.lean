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


end PEqualNP.Outside.L_meta_9033_aux

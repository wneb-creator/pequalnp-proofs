-- Kernel verification did not complete; two attempts were killed.
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884_aux.Structural

open PEqualNP.CircuitLowerBounds

def columnExample : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [10, 12]⟩, ⟨.not, [13]⟩,
    ⟨.or, [14, 7]⟩, ⟨.and, [15, 5]⟩, ⟨.or, [16, 8]⟩, ⟨.or, [17, 7]⟩,
    ⟨.or, [18, 6]⟩, ⟨.or, [19, 3]⟩, ⟨.and, [20, 2]⟩, ⟨.or, [21, 6]⟩,
    ⟨.or, [22, 2]⟩, ⟨.or, [23, 20]⟩, ⟨.and, [24, 9]⟩, ⟨.or, [25, 3]⟩,
    ⟨.and, [26, 19]⟩, ⟨.and, [27, 9]⟩], 28⟩

def columnCodes : List ℕ :=
  [8098112054, 7024370231, 7876514230, 7876514238,
    8394239046, 8394243142, 8167830598, 8167863366]

def columnInput (code row : ℕ) : List Bool :=
  (List.range 11).map fun i => (row + 128).testBit (code / 8 ^ i % 8)

def columnCount (C : Circuit) (code : ℕ) : ℕ :=
  ((List.range (11 + C.size)).map fun w =>
    (List.range 64).map fun row =>
      (C.wires (columnInput code row)).getD w false).toFinset.card

def chosenWires : List (List ℕ) :=
  [
    [0, 2, 3, 6, 7, 8, 9, 10, 18, 19, 20, 21, 22, 23, 24, 25],
    [0, 1, 2, 3, 6, 7, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25],
    [0, 3, 4, 5, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 20, 25],
    [0, 1, 3, 4, 5, 7, 8, 9, 16, 17, 18, 20, 25, 26, 27, 28],
    [0, 1, 2, 5, 6, 7, 8, 10, 12, 14, 15, 16, 17, 18, 19, 21],
    [0, 1, 2, 4, 5, 6, 7, 8, 16, 17, 18, 19, 21, 22, 23, 24],
    [0, 1, 2, 3, 4, 6, 9, 10, 11, 14, 20, 21, 22, 23, 24, 25],
    [0, 1, 2, 3, 4, 5, 6, 9, 11, 20, 21, 22, 23, 24, 25, 26]
  ]

def separatingRows : List (List (List ℕ)) :=
  [
    [
      [0, 1, 2, 8, 32, 4, 16, 0, 4, 4, 2, 3, 3, 1, 1, 17],
      [1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 8, 2, 1],
      [2, 1, 0, 2, 2, 2, 2, 0, 2, 2, 4, 2, 2, 1, 1, 2],
      [8, 1, 2, 0, 8, 4, 8, 0, 4, 4, 2, 3, 3, 1, 1, 8],
      [32, 1, 2, 8, 0, 4, 16, 0, 4, 4, 2, 3, 3, 1, 1, 17],
      [4, 1, 2, 4, 4, 0, 4, 0, 32, 8, 2, 3, 3, 1, 1, 4],
      [16, 1, 2, 8, 16, 4, 0, 0, 4, 4, 2, 3, 3, 1, 1, 16],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [4, 1, 2, 4, 4, 32, 4, 0, 0, 8, 2, 3, 3, 1, 1, 4],
      [4, 1, 2, 4, 4, 8, 4, 0, 8, 0, 2, 3, 3, 1, 1, 4],
      [2, 1, 4, 2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 1, 1, 2],
      [3, 1, 2, 3, 3, 3, 3, 0, 3, 3, 2, 0, 8, 1, 1, 3],
      [3, 1, 2, 3, 3, 3, 3, 0, 3, 3, 2, 8, 0, 1, 1, 3],
      [1, 8, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 2, 1],
      [1, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 2, 0, 1],
      [17, 1, 2, 8, 17, 4, 16, 0, 4, 4, 2, 3, 3, 1, 1, 0]
    ],
    [
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [0, 0, 1, 2, 8, 32, 4, 16, 4, 4, 2, 3, 3, 1, 1, 17],
      [0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1],
      [0, 2, 1, 0, 2, 2, 2, 2, 2, 2, 4, 2, 2, 1, 1, 2],
      [0, 8, 1, 2, 0, 8, 4, 8, 4, 4, 2, 3, 3, 1, 1, 8],
      [0, 32, 1, 2, 8, 0, 4, 16, 4, 4, 2, 3, 3, 1, 1, 17],
      [0, 4, 1, 2, 4, 4, 0, 4, 32, 8, 2, 3, 3, 1, 1, 4],
      [0, 16, 1, 2, 8, 16, 4, 0, 4, 4, 2, 3, 3, 1, 1, 16],
      [0, 4, 1, 2, 4, 4, 32, 4, 0, 8, 2, 3, 3, 1, 1, 4],
      [0, 4, 1, 2, 4, 4, 8, 4, 8, 0, 2, 3, 3, 1, 1, 4],
      [0, 2, 1, 4, 2, 2, 2, 2, 2, 2, 0, 2, 2, 1, 1, 2],
      [0, 3, 1, 2, 3, 3, 3, 3, 3, 3, 2, 0, 8, 1, 1, 3],
      [0, 3, 1, 2, 3, 3, 3, 3, 3, 3, 2, 8, 0, 1, 1, 3],
      [0, 1, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 2, 1],
      [0, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 1],
      [0, 17, 1, 2, 8, 17, 4, 16, 4, 4, 2, 3, 3, 1, 1, 0]
    ],
    [
      [0, 1, 2, 16, 8, 32, 4, 0, 2, 0, 0, 24, 24, 8, 1, 5],
      [1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 8, 1],
      [2, 1, 0, 2, 2, 2, 2, 0, 16, 0, 0, 2, 2, 2, 1, 2],
      [16, 1, 2, 0, 8, 16, 4, 0, 2, 0, 0, 16, 16, 8, 1, 5],
      [8, 1, 2, 8, 0, 8, 4, 0, 2, 0, 0, 8, 8, 32, 1, 5],
      [32, 1, 2, 16, 8, 0, 4, 0, 2, 0, 0, 24, 24, 8, 1, 5],
      [4, 1, 2, 4, 4, 4, 0, 0, 2, 0, 0, 4, 4, 4, 1, 4],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0],
      [2, 1, 16, 2, 2, 2, 2, 0, 0, 0, 0, 2, 2, 2, 1, 2],
      [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 10, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 0, 2, 0, 10, 0, 0, 0, 0, 0, 0],
      [24, 1, 2, 16, 8, 24, 4, 0, 2, 0, 0, 0, 32, 8, 1, 5],
      [24, 1, 2, 16, 8, 24, 4, 0, 2, 0, 0, 32, 0, 8, 1, 5],
      [8, 1, 2, 8, 32, 8, 4, 0, 2, 0, 0, 8, 8, 0, 1, 5],
      [1, 8, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1],
      [5, 1, 2, 5, 5, 5, 4, 0, 2, 0, 0, 5, 5, 5, 1, 0]
    ],
    [
      [0, 0, 1, 2, 16, 8, 32, 4, 24, 24, 8, 1, 5, 1, 9, 12],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 12, 1, 1],
      [2, 0, 1, 0, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2],
      [16, 0, 1, 2, 0, 8, 16, 4, 16, 16, 8, 1, 5, 1, 9, 12],
      [8, 0, 1, 2, 8, 0, 8, 4, 8, 8, 32, 1, 5, 1, 8, 8],
      [32, 0, 1, 2, 16, 8, 0, 4, 24, 24, 8, 1, 5, 1, 9, 12],
      [4, 0, 1, 2, 4, 4, 4, 0, 4, 4, 4, 1, 4, 1, 4, 4],
      [24, 0, 1, 2, 16, 8, 24, 4, 0, 32, 8, 1, 5, 1, 9, 12],
      [24, 0, 1, 2, 16, 8, 24, 4, 32, 0, 8, 1, 5, 1, 9, 12],
      [8, 0, 1, 2, 8, 32, 8, 4, 8, 8, 0, 1, 5, 1, 8, 8],
      [1, 0, 8, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 8, 1, 1],
      [5, 0, 1, 2, 5, 5, 5, 4, 5, 5, 5, 1, 0, 1, 5, 5],
      [1, 0, 12, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 0, 1, 1],
      [9, 0, 1, 2, 9, 8, 9, 4, 9, 9, 8, 1, 5, 1, 0, 9],
      [12, 0, 1, 2, 12, 8, 12, 4, 12, 12, 8, 1, 5, 1, 9, 0]
    ],
    [
      [0, 1, 2, 8, 32, 4, 16, 0, 1, 0, 0, 12, 12, 4, 4, 6],
      [1, 0, 1, 1, 1, 1, 1, 0, 8, 0, 0, 1, 1, 1, 1, 1],
      [2, 1, 0, 2, 2, 2, 2, 0, 1, 0, 0, 2, 2, 2, 2, 2],
      [8, 1, 2, 0, 8, 4, 8, 0, 1, 0, 0, 8, 8, 4, 4, 6],
      [32, 1, 2, 8, 0, 4, 16, 0, 1, 0, 0, 12, 12, 4, 4, 6],
      [4, 1, 2, 4, 4, 0, 4, 0, 1, 0, 0, 4, 4, 16, 16, 4],
      [16, 1, 2, 8, 16, 4, 0, 0, 1, 0, 0, 12, 12, 4, 4, 6],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0],
      [1, 8, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1],
      [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 5, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 0, 0, 0, 0],
      [12, 1, 2, 8, 12, 4, 12, 0, 1, 0, 0, 0, 16, 4, 4, 6],
      [12, 1, 2, 8, 12, 4, 12, 0, 1, 0, 0, 16, 0, 4, 4, 6],
      [4, 1, 2, 4, 4, 16, 4, 0, 1, 0, 0, 4, 4, 0, 32, 4],
      [4, 1, 2, 4, 4, 16, 4, 0, 1, 0, 0, 4, 4, 32, 0, 4],
      [6, 1, 2, 6, 6, 4, 6, 0, 1, 0, 0, 6, 6, 4, 4, 0]
    ],
    [
      [0, 1, 2, 0, 8, 32, 4, 16, 12, 12, 4, 4, 6, 6, 2, 2],
      [1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
      [2, 1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 32, 4],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [8, 1, 2, 0, 0, 8, 4, 8, 8, 8, 4, 4, 6, 6, 2, 2],
      [32, 1, 2, 0, 8, 0, 4, 16, 12, 12, 4, 4, 6, 6, 2, 2],
      [4, 1, 2, 0, 4, 4, 0, 4, 4, 4, 16, 16, 4, 4, 2, 2],
      [16, 1, 2, 0, 8, 16, 4, 0, 12, 12, 4, 4, 6, 6, 2, 2],
      [12, 1, 2, 0, 8, 12, 4, 12, 0, 16, 4, 4, 6, 6, 2, 2],
      [12, 1, 2, 0, 8, 12, 4, 12, 16, 0, 4, 4, 6, 6, 2, 2],
      [4, 1, 2, 0, 4, 4, 16, 4, 4, 4, 0, 32, 4, 4, 2, 2],
      [4, 1, 2, 0, 4, 4, 16, 4, 4, 4, 32, 0, 4, 4, 2, 2],
      [6, 1, 2, 0, 6, 6, 4, 6, 6, 6, 4, 4, 0, 32, 2, 2],
      [6, 1, 2, 0, 6, 6, 4, 6, 6, 6, 4, 4, 32, 0, 2, 2],
      [2, 1, 32, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 4],
      [2, 1, 4, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 0]
    ],
    [
      [0, 1, 2, 4, 8, 32, 16, 0, 1, 0, 4, 6, 6, 2, 2, 18],
      [1, 0, 1, 1, 1, 1, 1, 0, 8, 0, 1, 1, 1, 1, 1, 1],
      [2, 1, 0, 2, 2, 2, 2, 0, 1, 0, 2, 2, 2, 32, 4, 2],
      [4, 1, 2, 0, 4, 4, 4, 0, 1, 0, 32, 4, 4, 2, 2, 4],
      [8, 1, 2, 4, 0, 8, 8, 0, 1, 0, 4, 6, 6, 2, 2, 8],
      [32, 1, 2, 4, 8, 0, 16, 0, 1, 0, 4, 6, 6, 2, 2, 18],
      [16, 1, 2, 4, 8, 16, 0, 0, 1, 0, 4, 6, 6, 2, 2, 16],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
      [1, 8, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1],
      [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      [4, 1, 2, 32, 4, 4, 4, 0, 1, 0, 0, 4, 4, 2, 2, 4],
      [6, 1, 2, 4, 6, 6, 6, 0, 1, 0, 4, 0, 32, 2, 2, 6],
      [6, 1, 2, 4, 6, 6, 6, 0, 1, 0, 4, 32, 0, 2, 2, 6],
      [2, 1, 32, 2, 2, 2, 2, 0, 1, 0, 2, 2, 2, 0, 4, 2],
      [2, 1, 4, 2, 2, 2, 2, 0, 1, 0, 2, 2, 2, 4, 0, 2],
      [18, 1, 2, 4, 8, 18, 16, 0, 1, 0, 4, 6, 6, 2, 2, 0]
    ],
    [
      [0, 1, 2, 4, 8, 0, 32, 16, 1, 4, 6, 6, 2, 2, 18, 4],
      [1, 0, 1, 1, 1, 0, 1, 1, 8, 1, 1, 1, 1, 1, 1, 1],
      [2, 1, 0, 2, 2, 0, 2, 2, 1, 2, 2, 2, 32, 4, 2, 2],
      [4, 1, 2, 0, 4, 0, 4, 4, 1, 32, 4, 4, 2, 2, 4, 18],
      [8, 1, 2, 4, 0, 0, 8, 8, 1, 4, 6, 6, 2, 2, 8, 4],
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [32, 1, 2, 4, 8, 0, 0, 16, 1, 4, 6, 6, 2, 2, 18, 4],
      [16, 1, 2, 4, 8, 0, 16, 0, 1, 4, 6, 6, 2, 2, 16, 4],
      [1, 8, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1],
      [4, 1, 2, 32, 4, 0, 4, 4, 1, 0, 4, 4, 2, 2, 4, 18],
      [6, 1, 2, 4, 6, 0, 6, 6, 1, 4, 0, 32, 2, 2, 6, 4],
      [6, 1, 2, 4, 6, 0, 6, 6, 1, 4, 32, 0, 2, 2, 6, 4],
      [2, 1, 32, 2, 2, 0, 2, 2, 1, 2, 2, 2, 0, 4, 2, 2],
      [2, 1, 4, 2, 2, 0, 2, 2, 1, 2, 2, 2, 4, 0, 2, 2],
      [18, 1, 2, 4, 8, 0, 18, 16, 1, 4, 6, 6, 2, 2, 0, 4],
      [4, 1, 2, 18, 4, 0, 4, 4, 1, 18, 4, 4, 2, 2, 4, 0]
    ]
  ]

def chosenWire (t : Fin 8) (a : Fin 16) : ℕ :=
  ((chosenWires.getD t.val []).getD a.val 0)

def separatingRow (t : Fin 8) (a b : Fin 16) : ℕ :=
  (((separatingRows.getD t.val []).getD a.val []).getD b.val 0)

lemma columnExample_model :
    PEqualNP.MetaComplexity.FanInTwo columnExample ∧ columnExample.size = 18 ∧
    (∀ g ∈ columnExample.gates, 0 ∉ g.inputs) ∧
    columnExample.gates.countP (fun g => decide (g.op = .not)) = 1 ∧
    columnExample.gates.countP (fun g => g.inputs.contains 10) = 1 := by
  decide +kernel

lemma columnExample_chain : columnExample.output = 28 ∧
    ∀ j ∈ List.range 17,
      11 + j ∈ (columnExample.gates.getD (j + 1) ⟨.or, []⟩).inputs := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma chosenWire_lt : ∀ (t : Fin 8) (a : Fin 16), chosenWire t a < 29 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma separatingRow_lt : ∀ (t : Fin 8) (a b : Fin 16), separatingRow t a b < 64 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma columnExample_separates : ∀ (t : Fin 8) (a b : Fin 16), a ≠ b →
    (columnExample.wires
      (columnInput (columnCodes.getD t.val 0) (separatingRow t a b))).getD (chosenWire t a) false ≠
    (columnExample.wires
      (columnInput (columnCodes.getD t.val 0) (separatingRow t a b))).getD (chosenWire t b) false := by
  decide +kernel

lemma columnExample_lower_index (t : Fin 8) :
    16 ≤ columnCount columnExample (columnCodes.getD t.val 0) := by
  classical
  let code := columnCodes.getD t.val 0
  let col : ℕ → List Bool := fun w =>
    (List.range 64).map fun row => (columnExample.wires (columnInput code row)).getD w false
  let S : Finset (List Bool) := ((List.range 29).map col).toFinset
  have hmem (a : Fin 16) : col (chosenWire t a) ∈ S := by
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨chosenWire t a, List.mem_range.mpr (chosenWire_lt t a), rfl⟩
  have hinj : Function.Injective (fun a : Fin 16 => col (chosenWire t a)) := by
    intro a b heq
    by_contra hab
    have hh := congrArg (fun l : List Bool => l.getD (separatingRow t a b) false) heq
    have hr := separatingRow_lt t a b
    have heval (w : ℕ) : (col w).getD (separatingRow t a b) false =
        (columnExample.wires (columnInput code (separatingRow t a b))).getD w false := by
      dsimp only [col]
      rw [List.getD_eq_getElem _ _ (by simpa using hr), List.getElem_map, List.getElem_range]
    rw [heval, heval] at hh
    exact columnExample_separates t a b hab hh
  let f : Fin 16 → {l // l ∈ S} := fun a => ⟨col (chosenWire t a), hmem a⟩
  have hf : Function.Injective f := by
    intro a b heq
    exact hinj (congrArg Subtype.val heq)
  have hc := Fintype.card_le_of_injective f hf
  simpa [f, S, col, code, columnCount, columnExample, Circuit.size] using hc

lemma columnExample_lower : ∀ code ∈ columnCodes, 16 ≤ columnCount columnExample code := by
  intro code hcode
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcode
  have hi8 : i < 8 := by simpa [columnCodes] using hi
  have h := columnExample_lower_index ⟨i, hi8⟩
  rwa [List.getD_eq_getElem _ _ hi] at h

lemma columnExample_trace :
    (columnExample.wires (List.replicate 10 false ++ [true])).getD 13 false = false ∧
    ∀ i ∈ ([1, 4, 5] : List (Fin 10)),
      (columnExample.wires
        (List.ofFn (fun j : Fin 10 => decide (j = i)) ++ [true])).getD 14 false = false ∧
      (columnExample.wires
        (List.ofFn (fun j : Fin 10 => decide (j = 0 ∨ j = i)) ++ [false])).getD 14 false = true := by
  decide +kernel

lemma columnExample_misses_edge :
    columnExample.eval
      (List.ofFn (fun j : Fin 10 => decide (j = 0 ∨ j = 1)) ++ [false]) = false := by
  decide +kernel

def petersenExpression (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma columnExample_not_petersen :
    let x : Fin 10 → Bool := fun j => decide (j = 0 ∨ j = 1)
    columnExample.eval (List.ofFn x ++ [!x 0]) ≠ petersenExpression x := by
  decide +kernel

end PEqualNP.Outside.L_meta_1884_aux.Structural

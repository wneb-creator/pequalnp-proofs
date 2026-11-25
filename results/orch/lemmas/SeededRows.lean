import Mathlib.Data.Nat.Bitwise

namespace PEqualNP.Outside.L_meta_2592_aux.SeededRows

def rows : List Nat := [0, 63, 3, 12, 48, 21, 22, 25, 26, 37, 38, 41, 42]

def seeds : List Nat :=
  [0, 8191, 2726, 5446, 1642, 6538, 498, 7698,
    6142, 7166, 7934, 8158, 7630, 2042, 7802, 6650]

def seedValues (r : Nat) : List Bool :=
  let a := r.testBit 0
  let b := r.testBit 1
  let c := r.testBit 2
  let d := r.testBit 3
  let e := r.testBit 4
  let f := r.testBit 5
  [false, true, a, b, c, d, e, f,
    b || c || e, a || d || e, a || c || f, b || d || f,
    b || d, c || e, c || f, d || e]

def matching (r : Nat) : Bool :=
  (r.testBit 0 && r.testBit 1) ||
  (r.testBit 2 && r.testBit 3) ||
  (r.testBit 4 && r.testBit 5)

lemma seeds_semantics :
    ∀ r : Fin 13,
      seeds.map (fun mask => mask.testBit r.val) = seedValues (rows.getD r.val 0) := by
  decide +kernel

lemma target_semantics :
    ∀ r : Fin 13, (30 : Nat).testBit r.val = matching (rows.getD r.val 0) := by
  decide +kernel

lemma rows_distinct : rows.Nodup := by decide +kernel

lemma rows_small : ∀ r ∈ rows, r < 64 := by decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.SeededRows

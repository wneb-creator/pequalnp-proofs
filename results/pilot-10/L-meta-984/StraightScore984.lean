import Mathlib

namespace PEqualNP.Outside.L_meta_984.Straight

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

def row {α : Type} (xs : List α) (p : α → Bool) : Nat :=
  match xs with
  | [] => 0
  | x :: xs => Nat.bit (p x) (row xs p)

def swar (x : Nat) : Nat :=
  let x := x - ((x >>> 1) &&& 21845)
  let x := (x &&& 13107) + ((x >>> 2) &&& 13107)
  let x := (x + (x >>> 4)) &&& 3855
  ((x * 257) >>> 8) &&& 31

def fastDiff (a b : Nat) : Nat := a ^^^ (a &&& b)

def sum6 (a b c d e f : Nat) : Nat :=
  swar (fastDiff b d) + swar (fastDiff c d) + swar (fastDiff a e) + swar (fastDiff a f) -
    swar (fastDiff (a &&& (b ||| c)) (d ||| (e &&& f)))

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def fastEntry (y bw : Nat) (coords masks : List Nat) (code : Nat) : Bool :=
  let a := fld code bw 0
  let b := fld code bw 1
  let c := fld code bw 2
  let d := fld code bw 3
  let e := fld code bw 4
  let f := fld code bw 5
  if a < coords.length ∧ b < coords.length ∧ c < coords.length ∧
      d < coords.length ∧ e < coords.length ∧ f < coords.length then
    sum6 (masks.getD a 0) (masks.getD b 0) (masks.getD c 0)
      (masks.getD d 0) (masks.getD e 0) (masks.getD f 0) <
    eval6 (coords.getD a 0) (coords.getD b 0) (coords.getD c 0)
      (coords.getD d 0) (coords.getD e 0) (coords.getD f 0) y
  else false

def fastScr (y s : Nat) (coords : List Nat) (bw : Nat) (pool : List Nat)
    (ws : List Nat) : Bool :=
  if ws.length = s + 1 ∧ ws.length ≤ 12 then
    let masks := coords.map fun j => row ws (fun w => w.testBit j)
    pool.any (fastEntry y bw coords masks)
  else false

def coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

def pool : List Nat := [2178473, 6426319, 6637691, 5311866, 6577064, 5532551, 4328344, 1059991, 4333470, 5468092, 3296941, 6307806, 3152541, 5328764, 1072761, 3222938, 3283613, 4263631, 4205463, 6556538, 6360472, 1072505]

def straightScore (masks : List Nat) : Bool :=
  (sum6 (masks.getD 9 0) (masks.getD 10 0) (masks.getD 13 0) (masks.getD 3 0) (masks.getD 1 0) (masks.getD 2 0) < 3) ||
    ((sum6 (masks.getD 15 0) (masks.getD 12 0) (masks.getD 14 0) (masks.getD 0 0) (masks.getD 2 0) (masks.getD 6 0) < 3) ||
    ((sum6 (masks.getD 11 0) (masks.getD 7 0) (masks.getD 8 0) (masks.getD 4 0) (masks.getD 5 0) (masks.getD 6 0) < 3) ||
    ((sum6 (masks.getD 10 0) (masks.getD 7 0) (masks.getD 13 0) (masks.getD 0 0) (masks.getD 1 0) (masks.getD 5 0) < 3) ||
    ((sum6 (masks.getD 8 0) (masks.getD 10 0) (masks.getD 11 0) (masks.getD 5 0) (masks.getD 4 0) (masks.getD 6 0) < 3) ||
    ((sum6 (masks.getD 7 0) (masks.getD 8 0) (masks.getD 11 0) (masks.getD 6 0) (masks.getD 4 0) (masks.getD 5 0) < 3) ||
    ((sum6 (masks.getD 8 0) (masks.getD 9 0) (masks.getD 11 0) (masks.getD 0 0) (masks.getD 2 0) (masks.getD 4 0) < 3) ||
    ((sum6 (masks.getD 7 0) (masks.getD 9 0) (masks.getD 12 0) (masks.getD 2 0) (masks.getD 0 0) (masks.getD 1 0) < 3) ||
    ((sum6 (masks.getD 14 0) (masks.getD 9 0) (masks.getD 15 0) (masks.getD 1 0) (masks.getD 2 0) (masks.getD 4 0) < 3) ||
    ((sum6 (masks.getD 12 0) (masks.getD 11 0) (masks.getD 15 0) (masks.getD 6 0) (masks.getD 3 0) (masks.getD 5 0) < 3) ||
    ((sum6 (masks.getD 13 0) (masks.getD 10 0) (masks.getD 14 0) (masks.getD 4 0) (masks.getD 2 0) (masks.getD 3 0) < 3) ||
    ((sum6 (masks.getD 14 0) (masks.getD 13 0) (masks.getD 15 0) (masks.getD 3 0) (masks.getD 0 0) (masks.getD 6 0) < 3) ||
    ((sum6 (masks.getD 13 0) (masks.getD 9 0) (masks.getD 10 0) (masks.getD 1 0) (masks.getD 0 0) (masks.getD 3 0) < 3) ||
    ((sum6 (masks.getD 12 0) (masks.getD 7 0) (masks.getD 15 0) (masks.getD 4 0) (masks.getD 1 0) (masks.getD 5 0) < 3) ||
    ((sum6 (masks.getD 9 0) (masks.getD 7 0) (masks.getD 14 0) (masks.getD 5 0) (masks.getD 0 0) (masks.getD 1 0) < 3) ||
    ((sum6 (masks.getD 10 0) (masks.getD 9 0) (masks.getD 13 0) (masks.getD 2 0) (masks.getD 1 0) (masks.getD 3 0) < 3) ||
    ((sum6 (masks.getD 13 0) (masks.getD 9 0) (masks.getD 10 0) (masks.getD 1 0) (masks.getD 2 0) (masks.getD 3 0) < 3) ||
    ((sum6 (masks.getD 15 0) (masks.getD 12 0) (masks.getD 14 0) (masks.getD 0 0) (masks.getD 1 0) (masks.getD 4 0) < 3) ||
    ((sum6 (masks.getD 7 0) (masks.getD 9 0) (masks.getD 11 0) (masks.getD 2 0) (masks.getD 0 0) (masks.getD 4 0) < 3) ||
    ((sum6 (masks.getD 10 0) (masks.getD 7 0) (masks.getD 11 0) (masks.getD 0 0) (masks.getD 4 0) (masks.getD 6 0) < 3) ||
    ((sum6 (masks.getD 8 0) (masks.getD 9 0) (masks.getD 13 0) (masks.getD 0 0) (masks.getD 1 0) (masks.getD 6 0) < 3) ||
    ((sum6 (masks.getD 9 0) (masks.getD 7 0) (masks.getD 13 0) (masks.getD 5 0) (masks.getD 0 0) (masks.getD 1 0) < 3) ||
    (false))))))))))))))))))))))

theorem straightScore_eq (masks : List Nat) :
    straightScore masks = pool.any (fastEntry 65408 4 coords masks) := by
  rfl

def straightScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    straightScore (coords.map fun j => row ws (fun w => w.testBit j))
  else false

theorem straightScr_eq (s : Nat) (ws : List Nat) :
    straightScr s ws = fastScr 65408 s coords 4 pool ws := by
  unfold straightScr fastScr
  split
  · rw [straightScore_eq]
  · rfl

end PEqualNP.Outside.L_meta_984.Straight

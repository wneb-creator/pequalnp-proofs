import Mathlib
namespace ForceBenchmark
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

def goal (k:Nat):Nat := ((2^k-1) <<< k)

def fastEntry (k bw : Nat) (coords masks : List Nat) (code : Nat) : Bool :=
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
      (coords.getD d 0) (coords.getD e 0) (coords.getD f 0) (goal k)
  else false

def forceNat {α : Sort _} (x : Nat) (f : Nat → α) : α :=
  match x with
  | 0 => f 0
  | n+1 => f (n+1)

def forceMap {α : Type} {β : Sort _} : List α → (α → Nat) → (List Nat → β) → β
  | [], _, k => k []
  | x :: xs, g, k => forceNat (g x) (fun v => forceMap xs g (fun vs => k (v :: vs)))

def coords : List Nat := [0, 9, 18, 27, 36, 45, 54, 63, 64, 65, 66, 67, 68, 69, 70, 71]
def pool : List Nat := [2178473, 6426319, 6637691, 5311866, 6577064, 5532551, 4328344, 1059991, 4333470, 5468092, 3296941, 6307806, 3152541, 5328764, 1072761, 3222938, 3283613, 4263631, 4205463, 6556538, 6360472, 1072505, 2178473, 6426319]
def ws : List Nat := [0x1e0f0783c1e0f0780001ff00003fe00,0x2412090482412097fc0000ffffc0000,0x5e2f178bc5e2f1780001ff00003fe00,0x6231188c4623118803fe000000001ff,0x9048241209048247fffe00ff8000000,0x188c46231188c4620000000007fc01ff,0x1eaf57abd5eaf57a803fe00007fc01ff,0x24120904824120900000000ffffffe00,0x30180c06030180c07ffffff000000000]
def run : List Bool := forceMap coords (fun j => row ws (fun w => w.testBit j)) (fun masks => pool.map (fastEntry 63 4 coords masks))
theorem check0 : run = List.replicate 24 false := by decide +kernel
theorem check1 : run = List.replicate 24 false := by decide +kernel
theorem check2 : run = List.replicate 24 false := by decide +kernel
theorem check3 : run = List.replicate 24 false := by decide +kernel
theorem check4 : run = List.replicate 24 false := by decide +kernel
theorem check5 : run = List.replicate 24 false := by decide +kernel
theorem check6 : run = List.replicate 24 false := by decide +kernel
theorem check7 : run = List.replicate 24 false := by decide +kernel
theorem check8 : run = List.replicate 24 false := by decide +kernel
theorem check9 : run = List.replicate 24 false := by decide +kernel
theorem check10 : run = List.replicate 24 false := by decide +kernel
theorem check11 : run = List.replicate 24 false := by decide +kernel
theorem check12 : run = List.replicate 24 false := by decide +kernel
theorem check13 : run = List.replicate 24 false := by decide +kernel
theorem check14 : run = List.replicate 24 false := by decide +kernel
theorem check15 : run = List.replicate 24 false := by decide +kernel
theorem check16 : run = List.replicate 24 false := by decide +kernel
theorem check17 : run = List.replicate 24 false := by decide +kernel
theorem check18 : run = List.replicate 24 false := by decide +kernel
theorem check19 : run = List.replicate 24 false := by decide +kernel
theorem check20 : run = List.replicate 24 false := by decide +kernel
theorem check21 : run = List.replicate 24 false := by decide +kernel
theorem check22 : run = List.replicate 24 false := by decide +kernel
theorem check23 : run = List.replicate 24 false := by decide +kernel
theorem check24 : run = List.replicate 24 false := by decide +kernel
theorem check25 : run = List.replicate 24 false := by decide +kernel
theorem check26 : run = List.replicate 24 false := by decide +kernel
theorem check27 : run = List.replicate 24 false := by decide +kernel
theorem check28 : run = List.replicate 24 false := by decide +kernel
theorem check29 : run = List.replicate 24 false := by decide +kernel
end ForceBenchmark

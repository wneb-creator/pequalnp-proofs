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

def patternScore : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15] =>
    (sum6 r9 r10 r13 r3 r1 r2 < 3) ||
      ((sum6 r15 r12 r14 r0 r2 r6 < 3) ||
      ((sum6 r11 r7 r8 r4 r5 r6 < 3) ||
      ((sum6 r10 r7 r13 r0 r1 r5 < 3) ||
      ((sum6 r8 r10 r11 r5 r4 r6 < 3) ||
      ((sum6 r7 r8 r11 r6 r4 r5 < 3) ||
      ((sum6 r8 r9 r11 r0 r2 r4 < 3) ||
      ((sum6 r7 r9 r12 r2 r0 r1 < 3) ||
      ((sum6 r14 r9 r15 r1 r2 r4 < 3) ||
      ((sum6 r12 r11 r15 r6 r3 r5 < 3) ||
      ((sum6 r13 r10 r14 r4 r2 r3 < 3) ||
      ((sum6 r14 r13 r15 r3 r0 r6 < 3) ||
      ((sum6 r13 r9 r10 r1 r0 r3 < 3) ||
      ((sum6 r12 r7 r15 r4 r1 r5 < 3) ||
      ((sum6 r9 r7 r14 r5 r0 r1 < 3) ||
      ((sum6 r10 r9 r13 r2 r1 r3 < 3) ||
      ((sum6 r13 r9 r10 r1 r2 r3 < 3) ||
      ((sum6 r15 r12 r14 r0 r1 r4 < 3) ||
      ((sum6 r7 r9 r11 r2 r0 r4 < 3) ||
      ((sum6 r10 r7 r11 r0 r4 r6 < 3) ||
      ((sum6 r8 r9 r13 r0 r1 r6 < 3) ||
      ((sum6 r9 r7 r13 r5 r0 r1 < 3) ||
      (false))))))))))))))))))))))
  | masks => pool.any (fastEntry 65408 4 coords masks)

theorem patternScore_eq (masks : List Nat) :
    patternScore masks = pool.any (fastEntry 65408 4 coords masks) := by
  unfold patternScore
  split <;> rfl

def patternScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    patternScore (coords.map fun j => row ws (fun w => w.testBit j))
  else false

theorem patternScr_eq (s : Nat) (ws : List Nat) :
    patternScr s ws = fastScr 65408 s coords 4 pool ws := by
  unfold patternScr fastScr
  split
  · rw [patternScore_eq]
  · rfl

def threshold3 (a b c d e f : Nat) : Bool :=
  let xh := fastDiff (b &&& c) d
  let yh := fastDiff a (e ||| f)
  let r := fastDiff (b ||| c) d ||| fastDiff a (e &&& f)
  let q := r &&& (r-1)
  xh &&& yh == 0 && q &&& (q-1) == 0 && (xh ||| yh == 0 || q == 0)

def forceNat {α : Sort _} (x : Nat) (f : Nat → α) : α :=
  match x with
  | 0 => f 0
  | n+1 => f (n+1)

theorem forceNat_eq {α : Sort _} (x : Nat) (f : Nat → α) : forceNat x f = f x := by
  cases x <;> rfl

def thresholdForced (a b c d e f : Nat) : Bool :=
  forceNat (fastDiff (b &&& c) d) fun xh =>
  forceNat (fastDiff a (e ||| f)) fun yh =>
    xh &&& yh == 0 &&
      forceNat (fastDiff (b ||| c) d ||| fastDiff a (e &&& f)) fun r =>
      forceNat (r &&& (r-1)) fun q =>
        q &&& (q-1) == 0 && (xh ||| yh == 0 || q == 0)

theorem thresholdForced_eq (a b c d e f : Nat) :
    thresholdForced a b c d e f = threshold3 a b c d e f := by
  simp only [thresholdForced,forceNat_eq,threshold3,Bool.and_assoc]

def thresholdPattern : List Nat → Bool
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15] =>
    (thresholdForced r9 r10 r13 r3 r1 r2) ||
      ((thresholdForced r15 r12 r14 r0 r2 r6) ||
      ((thresholdForced r11 r7 r8 r4 r5 r6) ||
      ((thresholdForced r10 r7 r13 r0 r1 r5) ||
      ((thresholdForced r8 r10 r11 r5 r4 r6) ||
      ((thresholdForced r7 r8 r11 r6 r4 r5) ||
      ((thresholdForced r8 r9 r11 r0 r2 r4) ||
      ((thresholdForced r7 r9 r12 r2 r0 r1) ||
      ((thresholdForced r14 r9 r15 r1 r2 r4) ||
      ((thresholdForced r12 r11 r15 r6 r3 r5) ||
      ((thresholdForced r13 r10 r14 r4 r2 r3) ||
      ((thresholdForced r14 r13 r15 r3 r0 r6) ||
      ((thresholdForced r13 r9 r10 r1 r0 r3) ||
      ((thresholdForced r12 r7 r15 r4 r1 r5) ||
      ((thresholdForced r9 r7 r14 r5 r0 r1) ||
      ((thresholdForced r10 r9 r13 r2 r1 r3) ||
      ((thresholdForced r13 r9 r10 r1 r2 r3) ||
      ((thresholdForced r15 r12 r14 r0 r1 r4) ||
      ((thresholdForced r7 r9 r11 r2 r0 r4) ||
      ((thresholdForced r10 r7 r11 r0 r4 r6) ||
      ((thresholdForced r8 r9 r13 r0 r1 r6) ||
      ((thresholdForced r9 r7 r13 r5 r0 r1) ||
      (false))))))))))))))))))))))
  | masks => pool.any (fastEntry 65408 4 coords masks)

def thresholdScr (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 ∧ ws.length ≤ 12 then
    thresholdPattern (coords.map fun j => row ws (fun w => w.testBit j))
  else false

def sample : List Nat := [0x792,0x94c,0x1792,0x18a1,0x2468,0x6205,0x7aa5,0x900e,0xc070]

theorem thresholdBenchmark0 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark1 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark2 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark3 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark4 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark5 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark6 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark7 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark8 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark9 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark10 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark11 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark12 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark13 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark14 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark15 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark16 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark17 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark18 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark19 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark20 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark21 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark22 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark23 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark24 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark25 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark26 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark27 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark28 : thresholdScr 8 sample = false := by decide +kernel
theorem thresholdBenchmark29 : thresholdScr 8 sample = false := by decide +kernel
end PEqualNP.Outside.L_meta_984.Straight

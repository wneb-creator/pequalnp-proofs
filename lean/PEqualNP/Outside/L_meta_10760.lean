import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760.CostLUT

def table : Nat := 0xa0601a00aa05000a07a0800000660921900000000000090600060b000000000000000c0860c00000050a00080c00001900000021b000000000000c0721c00000011a00000041c00900000000000000000000000000080b41b005000000000905000000000000000000000c0500000000000000000000000000000000000000031a00000b00080900000000000700031900000000000000000070a01b000000419000000000008709000000000000000000000c06b0601c00cb0500080a41a000

def code (t : Nat) : Nat := (table >>> (12*t)) &&& 4095

def op (o : Nat) (a b : Bool) : Bool :=
  if o == 0 then a && b else if o == 1 then a || b
  else if o == 2 then a ^^ (a && b) else b ^^ (a && b)

def input (a b c : Bool) (i : Nat) : Bool := [a,b,c].getD i false

def evalCode (code : Nat) (a b c : Bool) : Bool :=
  let first := (code &&& 255)-1
  let v := op (first % 4) (input a b c ((first/4)%4)) (input a b c (first/16))
  if code < 256 then v else
    let second := code/256-1
    op (second%4) v (input a b c (second/4))

def bitIndex (a b c : Bool) : Nat := a.toNat + 2*b.toNat + 4*c.toNat

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem code_correct : ∀ (t : Fin 128) (a b c : Bool),
    code t.val != 0 → evalCode (code t.val) a b c = (2*t.val).testBit (bitIndex a b c) := by
  decide +kernel


def natOp (o a b : Nat) : Nat :=
  if o == 0 then a &&& b else if o == 1 then a ||| b
  else if o == 2 then a ^^^ (a &&& b) else b ^^^ (a &&& b)

theorem testBit_natOp (o a b i : Nat) :
    (natOp o a b).testBit i = op o (a.testBit i) (b.testBit i) := by
  by_cases h0 : o = 0
  · simp [natOp, op, h0, Nat.testBit_and]
  · by_cases h1 : o = 1
    · simp [natOp, op, h0, h1, Nat.testBit_or]
    · by_cases h2 : o = 2
      · simp [natOp, op, h0, h1, h2, Nat.testBit_xor, Nat.testBit_and]
      · simp [natOp, op, h0, h1, h2, Nat.testBit_xor, Nat.testBit_and]

def natInput (a b c i : Nat) : Nat := [a,b,c].getD i 0

theorem testBit_natInput (a b c j i : Nat) :
    (natInput a b c j).testBit i = input (a.testBit i) (b.testBit i) (c.testBit i) j := by
  cases j with
  | zero => rfl
  | succ j => cases j with
    | zero => rfl
    | succ j => cases j with
      | zero => rfl
      | succ j => simp [natInput, input, List.getD]

def evalCodeNat (code a b c : Nat) : Nat :=
  let first := (code &&& 255)-1
  let v := natOp (first % 4) (natInput a b c ((first/4)%4)) (natInput a b c (first/16))
  if code < 256 then v else
    let second := code/256-1
    natOp (second%4) v (natInput a b c (second/4))

theorem testBit_evalCodeNat (code a b c i : Nat) :
    (evalCodeNat code a b c).testBit i =
      evalCode code (a.testBit i) (b.testBit i) (c.testBit i) := by
  unfold evalCodeNat evalCode
  split <;> simp only [testBit_natOp, testBit_natInput]

theorem testBit_evalCodeNat_correct (t : Fin 128) (hcode : code t.val != 0)
    (a b c i : Nat) :
    (evalCodeNat (code t.val) a b c).testBit i =
      (2*t.val).testBit (bitIndex (a.testBit i) (b.testBit i) (c.testBit i)) := by
  rw [testBit_evalCodeNat]
  exact code_correct t _ _ _ hcode

theorem evalCodeNat_eq_of_bits (t : Fin 128) (hcode : code t.val != 0)
    (a b c w : Nat)
    (hw : ∀ i, w.testBit i =
      (2*t.val).testBit (bitIndex (a.testBit i) (b.testBit i) (c.testBit i))) :
    evalCodeNat (code t.val) a b c = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_evalCodeNat_correct t hcode, hw]

theorem testBit_evalCodeNat_masked (t : Fin 128) (hcode : code t.val != 0)
    (a b c d i : Nat) (hd : d.testBit i = true) :
    (evalCodeNat (code t.val) (a &&& d) (b &&& d) (c &&& d)).testBit i =
      (2*t.val).testBit (bitIndex (a.testBit i) (b.testBit i) (c.testBit i)) := by
  rw [testBit_evalCodeNat_correct t hcode]
  simp only [Nat.testBit_and, hd, Bool.and_true]

theorem testBit_relativeComplement (w d i : Nat) (hd : d.testBit i = true) :
    (w ^^^ d).testBit i = !(w.testBit i) := by
  simp only [Nat.testBit_xor, hd, Bool.xor_true]

end PEqualNP.Outside.L_meta_10760.CostLUT


import Mathlib.Logic.Function.Basic
abbrev Word := BitVec 512
def fits (mono desired ground sample:Bool):Bool :=
 if mono then if desired then !ground || sample else !sample || ground else ground == sample
def pinMask (mono desired sample:Bool) (w:Word):Word :=
 if fits mono desired false sample then
   if fits mono desired true sample then BitVec.allOnes 512 else ~~~w
 else if fits mono desired true sample then w else 0
def mask (mono desired:Bool):(ws:List Word) → (Fin ws.length → Bool) → Word
 | [], _ => BitVec.allOnes 512
 | w :: ws, x => pinMask mono desired (x 0) w &&& mask mono desired ws (fun i => x i.succ)
def forced (target:Word) (mono desired:Bool) (ws:List Word) (x:Fin ws.length → Bool):Bool :=
 decide ((mask mono desired ws x &&& (if desired then target else ~~~target)) ≠ (0:Word))
def maskUpNat : List Word → Nat → Word
 | [], _ => BitVec.allOnes 512
 | w::ws,a => if a.testBit 0 then w &&& maskUpNat ws (a>>>1) else maskUpNat ws (a>>>1)
def maskDownNat : List Word → Nat → Word
 | [], _ => BitVec.allOnes 512
 | w::ws,a => if a.testBit 0 then maskDownNat ws (a>>>1) else ~~~w &&& maskDownNat ws (a>>>1)
def maskExactNat : List Word → Nat → Word
 | [], _ => BitVec.allOnes 512
 | w::ws,a => (if a.testBit 0 then w else ~~~w) &&& maskExactNat ws (a>>>1)
def maskNat (mono desired:Bool) (ws:List Word) (a:Nat):Word :=
 if mono then if desired then maskDownNat ws a else maskUpNat ws a else maskExactNat ws a
set_option maxRecDepth 4096 in
theorem maskNat_cons (mono desired:Bool) (w:Word) (ws:List Word) (a:Nat):
 maskNat mono desired (w::ws) a = pinMask mono desired (a.testBit 0) w &&& maskNat mono desired ws (a>>>1) := by
 cases mono <;> cases desired <;> cases ha:a.testBit 0 <;> simp [maskNat,maskUpNat,maskDownNat,maskExactNat,pinMask,fits,ha] <;> exact BitVec.allOnes_and.symm
theorem maskNat_eq (mono desired:Bool) (ws:List Word) (a:Nat):
 maskNat mono desired ws a = mask mono desired ws (fun i => a.testBit i.val) := by
 induction ws generalizing a with
 | nil => cases mono <;> cases desired <;> rfl
 | cons w ws ih =>
  rw [maskNat_cons]
  simp only [mask,ih,Nat.testBit_shiftRight,Fin.val_succ,Fin.val_zero,Nat.add_comm]
def putBit (a i:Nat) (b:Bool):Nat := if a.testBit i == b then a else a ^^^ (2^i)
theorem putBit_test (a i j:Nat) (b:Bool):
 (putBit a i b).testBit j = if j=i then b else a.testBit j := by
 by_cases h:j=i
 · subst j
   cases ha:a.testBit i <;> cases b <;> simp [putBit,ha,Nat.testBit_xor,Nat.testBit_two_pow]
 · unfold putBit
   split <;> simp [Nat.testBit_xor,Nat.testBit_two_pow,h,Ne.symm h]
def row {n:Nat} (a:Nat):Fin n → Bool := fun i => a.testBit i.val
def pairInput {n:Nat} (i j:Fin n) (base:Fin n → Bool) (a b:Bool) (k:Fin n):Bool :=
 if k=i then a else if k=j then b else base k
theorem row_put {n:Nat} (a:Nat) (k:Fin n) (b:Bool):
 row (putBit a k.val b) = Function.update (row a) k b := by
 funext j
 simp [row,putBit_test,Function.update,Fin.ext_iff]
theorem row_pair {n:Nat} (a:Nat) (i j:Fin n) (u v:Bool):
 row (putBit (putBit a j.val v) i.val u) = pairInput i j (row a) u v := by
 funext k
 simp [row,pairInput,putBit_test,Fin.ext_iff]
def forcedNat (target:Word) (mono desired:Bool) (ws:List Word) (a:Nat):Bool :=
 decide ((maskNat mono desired ws a &&& (if desired then target else ~~~target)) ≠ (0:Word))
theorem forcedNat_eq (target:Word) (mono desired:Bool) (ws:List Word) (a:Nat):
 forcedNat target mono desired ws a = forced target mono desired ws (row a) := by
 simp only [forcedNat,forced,maskNat_eq]
 rfl
abbrev Rule (n:Nat) := (Fin n × Fin n × Nat × Nat) ⊕ (Fin n × Fin n × Fin n × Nat × Nat × Nat × Bool × Bool)
def checksRule (target:Word) (mono:Bool) (ws:List Word):Rule ws.length → Bool :=
 let checkValue := fun x b => forced target mono b ws x
 fun
 | Sum.inl (i,j,a,o) =>
     [false,true].all fun u => [false,true].all fun v =>
       checkValue (pairInput i j (row a) u v) (u && v) &&
       checkValue (pairInput i j (row o) u v) (u || v)
 | Sum.inr (i,j,k,a,b,c,bit,sign) =>
     let hi m := Function.update (row m) k bit
     ((List.finRange ws.length).all fun v => v == i || v == j ||
       (row a v == row b v && row b v == row c v)) &&
     checkValue (row a) false &&
     checkValue (row b) true &&
     checkValue (hi a) sign &&
     checkValue (hi b) sign &&
     checkValue (hi c) (!sign)
def checksRuleNat (target:Word) (mono:Bool) (ws:List Word):Rule ws.length → Bool :=
 let checkValue := fun x b => forcedNat target mono b ws x
 fun
 | Sum.inl (i,j,a,o) =>
     [false,true].all fun u => [false,true].all fun v =>
       checkValue (putBit (putBit a j.val v) i.val u) (u && v) &&
       checkValue (putBit (putBit o j.val v) i.val u) (u || v)
 | Sum.inr (i,j,k,a,b,c,bit,sign) =>
     let hi m := putBit m k.val bit
     ((List.finRange ws.length).all fun v => v == i || v == j ||
       (row a v == row b v && row b v == row c v)) &&
     checkValue a false &&
     checkValue b true &&
     checkValue (hi a) sign &&
     checkValue (hi b) sign &&
     checkValue (hi c) (!sign)
theorem checksRuleNat_eq (target:Word) (mono:Bool) (ws:List Word):
 checksRuleNat target mono ws = checksRule target mono ws := by
 funext rule
 rcases rule with ⟨i,j,a,o⟩ | ⟨i,j,k,a,b,c,bit,sign⟩
 · simp only [checksRuleNat,checksRule,forcedNat_eq,row_pair]
 · simp only [checksRuleNat,checksRule,forcedNat_eq,row_put]

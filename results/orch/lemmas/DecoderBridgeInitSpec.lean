import Init
namespace Function
universe u v
def update {α:Sort u} {β:α→Sort v} [DecidableEq α]
 (f:∀a,β a) (a':α) (v:β a') (a:α):β a :=
 if h:a=a' then Eq.ndrec v h.symm else f a
end Function
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
def maskUpNat : List Word → Nat → Nat
 | [], _ => (2^512-1)
 | w::ws,a => if a.testBit 0 then w.toNat &&& maskUpNat ws (a>>>1) else maskUpNat ws (a>>>1)
def maskDownNat : List Word → Nat → Nat
 | [], _ => (2^512-1)
 | w::ws,a => if a.testBit 0 then maskDownNat ws (a>>>1) else ((2^512-1) ^^^ w.toNat) &&& maskDownNat ws (a>>>1)
def maskExactNat : List Word → Nat → Nat
 | [], _ => (2^512-1)
 | w::ws,a => (if a.testBit 0 then w.toNat else ((2^512-1) ^^^ w.toNat)) &&& maskExactNat ws (a>>>1)
def maskNat (mono desired:Bool) (ws:List Word) (a:Nat):Nat :=
 if mono then if desired then maskDownNat ws a else maskUpNat ws a else maskExactNat ws a

set_option maxRecDepth 4096 in
theorem maskNat_eq (mono desired:Bool) (ws:List Word) (a:Nat):
 maskNat mono desired ws a = (mask mono desired ws (fun i => a.testBit i.val)).toNat := by
 cases mono <;> cases desired <;>
   simp only [maskNat, Bool.false_eq_true, ite_true, ite_false] <;>
   induction ws generalizing a with
   | nil => rfl
   | cons w ws ih =>
     cases ha:a.testBit 0 <;>
       simp only [maskUpNat,maskDownNat,maskExactNat,mask,Fin.val_zero,pinMask,fits,ha,
         Bool.not_false,Bool.not_true,Bool.false_or,Bool.true_or,Bool.or_false,Bool.or_true,
         Bool.false_beq,Bool.true_beq,Bool.false_eq_true,
         ite_true,ite_false,BitVec.allOnes_and,BitVec.toNat_and,BitVec.not_def,BitVec.toNat_xor,BitVec.toNat_allOnes,ih,
         Nat.testBit_shiftRight,Fin.val_succ,Nat.add_comm]
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
 by_cases h:j=k
 · subst j
   simp [row,putBit_test,Function.update]
 · have hv:j.val≠k.val:=fun eq=>h (Fin.ext eq)
   simp [row,putBit_test,Function.update,h,hv]
theorem row_pair {n:Nat} (a:Nat) (i j:Fin n) (u v:Bool):
 row (putBit (putBit a j.val v) i.val u) = pairInput i j (row a) u v := by
 funext k
 simp [row,pairInput,putBit_test,Fin.ext_iff]
def forcedNat (target:Word) (mono desired:Bool) (ws:List Word) (a:Nat):Bool :=
 decide ((maskNat mono desired ws a &&& (if desired then target.toNat else (2^512-1) ^^^ target.toNat)) ≠ 0)
set_option maxRecDepth 4096 in
theorem forcedNat_eq (target:Word) (mono desired:Bool) (ws:List Word) (a:Nat):
 forcedNat target mono desired ws a = forced target mono desired ws (row a) := by
 cases desired <;>
   simp only [forcedNat,forced,maskNat_eq,ne_eq,←BitVec.toNat_inj,BitVec.toNat_and,
     BitVec.not_def,BitVec.toNat_xor,BitVec.toNat_allOnes,BitVec.toNat_zero,Bool.false_eq_true,ite_false,ite_true]
 all_goals rfl
abbrev Rule (n:Nat) :=
 (Fin n × Fin n × Nat × Nat) ⊕
   (Fin n × Fin n × Fin n × Nat × Nat × Nat × Bool × Bool)
def Rule.square {n:Nat} (i j:Fin n) (a o:Nat):Rule n :=
 Sum.inl (i,j,a,o)
def Rule.cube {n:Nat} (i j k:Fin n) (a b c:Nat) (bit sign:Bool):Rule n :=
 Sum.inr (i,j,k,a,b,c,bit,sign)
def readFin (n x:Nat):Option (Fin n) :=
 if h:x < n then some ⟨x,h⟩ else none
def ruleCode (n w:Nat):Option (Rule n):=do
 let i ← readFin n (w &&& 15)
 let j ← readFin n ((w >>> 4) &&& 15)
 let k:=(w >>> 8) &&& 15
 let pay:=w >>> 12
 let raw:=pay &&& 4095
 if k == 15 then
   return Rule.square i j raw (pay >>> 12)
 else
   let pivot ← readFin n k
   let corner (m:Nat):=raw ||| ((m &&& 1) <<< i.val) ||| (((m >>> 1) &&& 1) <<< j.val)
   return Rule.cube i j pivot (corner (pay >>> 12)) (corner (pay >>> 14))
     (corner (pay >>> 16)) (!(raw.testBit k)) (pay.testBit 18)
def readRules (n:Nat):Nat → Nat → List (Rule n)
 | 0,_=>[]
 | c+1,w =>
   (ruleCode n (w &&& 0xfffffffff)).toList ++ readRules n c (w >>> 36)
def sharedRule {n:Nat}:Rule n → Prop
 | Sum.inl _ => True
 | Sum.inr (i,j,_,a,b,c,_,_) => ∀v:Fin n,v≠i→v≠j→row a v=row b v ∧ row b v=row c v
def checksRule (target:Word) (mono:Bool) (ws:List Word):Rule ws.length → Bool :=
 let checkValue:=fun x b => forced target mono b ws x
 fun
 | Sum.inl (i,j,a,o) =>
     if mono then
       checkValue (pairInput i j (row a) false true) false &&
       checkValue (pairInput i j (row a) true false) false &&
       checkValue (pairInput i j (row a) true true) true &&
       checkValue (pairInput i j (row o) false false) false &&
       checkValue (pairInput i j (row o) false true) true &&
       checkValue (pairInput i j (row o) true false) true
     else
       [false,true].all fun u => [false,true].all fun v =>
         checkValue (pairInput i j (row a) u v) (u && v) &&
         checkValue (pairInput i j (row o) u v) (u || v)
 | Sum.inr (i,j,k,a,b,c,bit,sign) =>
     let hi m:=Function.update (row m) k bit
     ((List.finRange ws.length).all fun v => v == i || v == j ||
       (row a v == row b v && row b v == row c v)) &&
     checkValue (row a) false &&
     checkValue (row b) true &&
     (if mono && !bit && !sign then true else checkValue (hi a) sign) &&
     (if mono && bit && sign then true else checkValue (hi b) sign) &&
     checkValue (hi c) (!sign)
def checksRuleNat (target:Word) (mono:Bool) (ws:List Word):Rule ws.length → Bool :=
 let checkValue:=fun x b => forcedNat target mono b ws x
 fun
 | Sum.inl (i,j,a,o) =>
     if mono then
       checkValue (putBit (putBit a j.val true) i.val false) false &&
       checkValue (putBit (putBit a j.val false) i.val true) false &&
       checkValue (putBit (putBit a j.val true) i.val true) true &&
       checkValue (putBit (putBit o j.val false) i.val false) false &&
       checkValue (putBit (putBit o j.val true) i.val false) true &&
       checkValue (putBit (putBit o j.val false) i.val true) true
     else
       [false,true].all fun u => [false,true].all fun v =>
         checkValue (putBit (putBit a j.val v) i.val u) (u && v) &&
         checkValue (putBit (putBit o j.val v) i.val u) (u || v)
 | Sum.inr (i,j,k,a,b,c,bit,sign) =>
     let hi m:=putBit m k.val bit
     checkValue a false &&
     checkValue b true &&
     (if mono && !bit && !sign then true else checkValue (hi a) sign) &&
     (if mono && bit && sign then true else checkValue (hi b) sign) &&
     checkValue (hi c) (!sign)
theorem checksRuleNat_eq (target:Word) (mono:Bool) (ws:List Word)
 (rule:Rule ws.length) (shared:sharedRule rule):
 checksRuleNat target mono ws rule = checksRule target mono ws rule := by
 rcases rule with ⟨i,j,a,o⟩ | ⟨i,j,k,a,b,c,bit,sign⟩
 · simp only [checksRuleNat,checksRule,forcedNat_eq,row_pair]
 · have hs:((List.finRange ws.length).all fun v=>v==i || v==j ||
       (row a v==row b v && row b v==row c v))=true := by
     apply List.all_eq_true.mpr
     intro v hv
     by_cases hi:v=i
     · simp [hi]
     by_cases hj:v=j
     · simp [hj]
     have hv:=shared v hi hj
     simp only [hv.1,hv.2,beq_self_eq_true,Bool.true_and,Bool.or_true]
   simp only [checksRuleNat,checksRule,forcedNat_eq,row_put,hs,Bool.true_and]
theorem lowBit_shift_other (m i k:Nat) (h:k≠i):
 ((m &&& 1) <<< i).testBit k = false := by
 by_cases hi:i≤k
 · have hb:(1:Nat).testBit (k-i)=false := by
     apply Bool.eq_false_iff.mpr
     intro hbit
     have he:=Nat.testBit_one_eq_true_iff_self_eq_zero.mp hbit
     omega
   simp only [Nat.testBit_shiftLeft,Nat.testBit_and,hi,hb,decide_true,Bool.true_and,Bool.and_false]
 · simp [Nat.testBit_shiftLeft,hi]
theorem corner_other (raw m i j k:Nat) (hi:k≠i) (hj:k≠j):
 (raw ||| ((m &&& 1) <<< i) ||| (((m >>> 1) &&& 1) <<< j)).testBit k = raw.testBit k := by
 simp only [Nat.testBit_or,lowBit_shift_other m i k hi,
   lowBit_shift_other (m>>>1) j k hj,Bool.or_false]
theorem ruleCode_shared {n w:Nat} {r:Rule n} (h:ruleCode n w=some r):sharedRule r := by
 unfold ruleCode at h
 cases hi:readFin n (w &&& 15) with
 | none => simp only [hi] at h; cases h
 | some i =>
   simp only [hi,Option.bind_some] at h
   cases hj:readFin n ((w>>>4) &&& 15) with
   | none => simp only [hj] at h; cases h
   | some j =>
     simp only [hj,Option.bind_some] at h
     split at h
     next hs => cases h; trivial
     next hs =>
       cases hk:readFin n ((w>>>8) &&& 15) with
       | none => simp only [hk] at h; cases h
       | some k =>
         simp only [hk,Option.bind_some] at h
         cases h
         intro v hi hj
         have vi:v.val≠i.val := fun e=>hi (Fin.ext e)
         have vj:v.val≠j.val := fun e=>hj (Fin.ext e)
         have hc (m:Nat):=corner_other ((w>>>12)&&&4095) m i.val j.val v.val vi vj
         constructor <;> simp only [row,hc]
theorem readRules_shared (n count code:Nat):∀r∈readRules n count code,sharedRule r := by
 induction count generalizing code with
 | zero => simp [readRules]
 | succ count ih =>
   intro r hr
   rcases List.mem_append.mp hr with hr|hr
   · exact ruleCode_shared (Option.mem_toList.mp hr)
   · exact ih _ r hr
theorem decodedChecks (target:Word) (mono:Bool) (ws:List Word) (count code:Nat)
 (h:(readRules ws.length count code).all (checksRuleNat target mono ws)=true):
 (readRules ws.length count code).all (checksRule target mono ws)=true := by
 apply List.all_eq_true.mpr
 intro claim hc
 rw [←checksRuleNat_eq target mono ws claim (readRules_shared ws.length count code claim hc)]
 exact List.all_eq_true.mp h _ hc

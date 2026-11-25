import Init
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
abbrev Rule (n:Nat) :=
 (Fin n × Fin n × Nat × Nat) ⊕
   (Fin n × Fin n × Fin n × Nat × Nat × Nat × Bool × Bool)
def Rule.square {n:Nat} (i j:Fin n) (a o:Nat):Rule n :=
 Sum.inl (i,j,a,o)
def Rule.cube {n:Nat} (i j k:Fin n) (a b c:Nat) (bit sign:Bool):Rule n :=
 Sum.inr (i,j,k,a,b,c,bit,sign)
def row {n:Nat} (m:Nat):Fin n → Bool:=fun i=>m.testBit i.val
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

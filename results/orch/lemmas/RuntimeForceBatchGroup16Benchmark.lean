import PEqualNP.Defs

-- The live-wire checker and the smaller graph certificates are adapted from the project proofs
-- L_meta_1667 and L_meta_1677, distributed under Apache-2.0.
-- Each root search considers all nine inputs. Restriction bounds and conflicting truth-table
-- rows eliminate children, and checked graph permutations identify equivalent states.
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_670.Projection
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
abbrev Row := Fin 512
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
abbrev Move := Sig × Sig × Row
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def properB (T : Sig) := T != zero && T != one
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

def defaultDecor : Decor := (zero,0,0)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
noncomputable def force {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n
noncomputable def forcePacked {β : Type} (xs : List PackedSig) : (List PackedSig → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f =>
    force p.1 fun a => force p.2 fun b => ih fun ys => f ((a,b)::ys)) xs

noncomputable def forceBatch {β : Type} (b : Batch) (f : Batch → β) : β :=
  force b.1 fun k => force b.2.1 fun n => force b.2.2.1 fun r =>
  forcePacked b.2.2.2.1 fun ws =>
  force b.2.2.2.2.1 fun c0 => force b.2.2.2.2.2.1 fun c1 => force b.2.2.2.2.2.2 fun c2 =>
  f (k,n,r,ws,c0,c1,c2)

noncomputable def forceMap {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => force (f a) fun x => ih fun xs => k (x::xs)) l
def nmask (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d
noncomputable def anyEq (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l
def nconst (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (nconst d m) (anyEq m pm)) (and u (anyEq (Nat.xor d m) pm))
def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
def nloss (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (nconst d x) 1 0)
abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def forceBool {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b
noncomputable def forcePool {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (p : BoundPool) (f : QS → β) : β :=
  force p.domain.toNat fun d => forceMap (nmask d) p.wires fun pm => forceMap (fun w : Decor => nmask d w.1) ws fun ms =>
  force (ms.countP (nconst d)) fun c => force p.bound fun l => force (Nat.add k p.paid) fun t =>
  force (ms.map fun m => cond (navail u d pm m) 0 1).sum fun v => forceBool u fun u => f (d,c,l,t,v,ms,pm,u)
noncomputable def forcePools {β : Type} (u : Bool) (k : Nat) (ws : List Decor) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => forcePool u k ws p fun q => ih fun qs => f (q::qs)) ps
def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs
noncomputable def fastCost (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (s.2.2.2.2.2.1.getD i 0) fun x => force (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (force (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
noncomputable def linkAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  force (l.2.2.2.2.1.getD i 0) fun x => force (l.2.2.2.2.1.getD j 0) fun y => force (zN op x y) fun z =>
  Option.rec false (fun ys => forceMap (fun v => v) ys fun ys =>
    and (anyEq z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (anyEq v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (anyEq v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
noncomputable def fallbackAt (fl : Nat → Option (List Nat)) (l : Lane) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
def swapIdx (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
noncomputable def decodeN : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => decodeN n (bits >>> 10) (ws++[z])
noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  force (packedAt data (i*(len+(selected g.mask).length+depth)) (len+(selected g.mask).length+depth)) fun rec =>
  selectLive (rec >>> len) (decodeN depth (rec &&& ((1 <<< len)-1)) raw)
noncomputable def linkedFast (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all validSwap) (some (fastState g k pair.1 perm)) none
noncomputable def flOf (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (linkedFast g (k-1))
noncomputable def batchMove (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt fl c i j op ka kb) mask xs

noncomputable def batchPair (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i j op : Nat) :=
  let f := batchMove fl u b xs i j op
  f false false && f true false && f false true && f true true
noncomputable def batchRow (fl : Nat → Option (List Nat)) (u : Bool) (b : Batch) (xs : List Lane) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair fl u b xs i j))
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
noncomputable def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  forceBatch b fun b => forceLanes xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    batchRow (flOf g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
def rootLookup (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 2 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none



def rootSSamples : Array (Bits × Bits) := #[((-0x3b3efc6733ff4e7fef7f80e79e776fc59bfefbdf1499ede4cb986d7fe38e077c08c79),0x4c10098c400b1801080251c4088901a6401042029620009142392800010908115182),((-0x1ef5ad9ef3fbfdf9bcfa6f9f807fff3c7899e73b6c79d39b3f67e00995b1bcf377c01),0x210a526108040206430490602b000040816618c492840420400804162a444304c8254),(0x1c01f2583c181c09e1807e41030c788020071cf9318708e1e308738f840f0fcf8,0x40052583c181c49618054410100288020010029308708e0a348508b840b014a0),(0x600607e0080c000600e01ff800e1c0f8007c0f81f01c1f80f01fc0f83f007f00ff00,0x600002a0080c00060000029000e140f8007c0681f00417805015c02837001900eb00),(0x380c7f80031f001f800ffe0000701ff000f800ffe001fe000ffe000ffc0007fff0000,0x380c7f00031f001f800fda0000700be000f80097c001be000adc000d7c00066ee0000),(0xf800003e0001ffff00000007fe00000ffff000001fffff000000ffffff80000000,0x3e0000ae51000000053200000aa69000001fff6e000000fffed600000040),(0x3ff0000003ffffe000000000007fffffff0000000001fffffffffff00000000000000,0xe50000003e9d4a000000000007fffbf7e0000000001fbdfbff7fbe00000000000000),(0x3ffffffffc00000000000000007ffffffffffffffffe0000000000000000000000000,0x3ffffbffac00000000000000002cdeffd75596feffd60000000000000000000000000),(0x3fffffffffffffffffffffffff8000000000000000000000000000000000000000000,0x31afffd5fc162b551aeffdd6598000000000000000000000000000000000004000000)]
def rootSCols : List ColumnInfo := [(0,1,332,412316861106,8),(0,2,312,824633721541,8),(0,4,305,77309412042,8),(0,8,99,824633721748,8),(0,16,486,521,10),(0,32,30,17179870145,8),(0,64,189,770,10),(0,128,347,548,10),(0,256,23,412316861160,8),(1,0,494,134218256,12),(1,2,312,824633721540,7),(1,16,486,520,9),(1,32,30,17179870144,7),(1,64,156,4294968098,7),(1,128,330,134218292,7),(2,0,445,77309411904,12),(2,1,332,412316861104,7),(2,4,305,77309412040,7),(2,16,480,1049101,7),(2,64,189,768,9),(3,0,428,77443629648,9),(3,16,480,1049100,6),(3,64,156,4294968096,6),(3,128,344,548,6),(4,0,379,824633721472,12),(4,2,312,824633721537,7),(4,8,99,824633721744,7),(4,64,57,824633721730,7),(4,128,347,544,9),(5,0,378,824633721472,8),(5,2,312,824633721536,6),(5,16,354,824633721480,6),(5,128,330,134218288,6),(6,0,313,901943132864,9),(6,16,480,521,6),(6,64,57,824633721728,6),(6,128,281,77309411936,6),(7,0,504,512,7),(8,0,487,33554960,12),(8,4,305,77309412034,7),(8,16,486,513,9),(8,64,165,33555218,7),(8,256,23,412316861152,7),(9,0,486,512,8),(9,16,486,512,8),(10,0,437,77309411904,8),(10,4,305,77309412032,6),(10,64,165,33555216,6),(11,0,480,1049092,5),(12,0,355,824667275920,9),(12,64,177,770,6),(13,0,354,824633721472,5),(14,0,497,512,7),(16,0,495,512,13),(16,1,332,412316861090,7),(16,2,424,581,7),(16,4,353,650,7),(16,32,78,897,7),(16,64,165,6292234,7),(16,256,135,616,7),(17,0,494,512,11),(17,2,424,580,6),(17,32,78,896,6),(18,0,428,77309414977,9),(18,1,332,412316861088,6),(18,4,353,648,6),(19,0,428,77309411904,8),(20,0,355,824652595848,9),(20,2,424,577,6),(20,8,99,824633721728,6),(21,0,490,512,7),(24,0,487,512,11),(24,4,353,642,6),(24,256,135,608,6),(25,0,486,512,8),(28,0,355,824633721472,8),(32,0,351,412316861056,12),(32,1,332,412316861074,7),(32,16,198,15393162789641,7),(32,256,23,412316861128,7),(33,0,334,412451078800,9),(33,128,330,134218260,6),(34,0,349,412316861056,8),(34,1,332,412316861072,6),(35,0,476,512,7),(36,0,347,512,8),(36,128,347,512,8),(37,0,330,134218256,5),(38,0,281,77309411904,5),(40,0,215,15393162789632,8),(40,256,23,412316861120,6),(48,0,334,412316862081,9),(48,1,332,412316861058,6),(48,256,135,584,6),(49,0,334,412316861056,8),(52,0,330,1537,5),(56,0,455,512,7),(64,0,447,512,13),(64,1,396,562,7),(64,2,312,824633721477,7),(64,16,166,13194139534089,7),(64,32,30,897,7),(64,256,23,412316861096,7),(65,0,428,134242834,9),(65,2,312,824633721476,6),(65,32,30,896,6),(66,0,445,512,11),(66,1,396,560,6),(66,4,305,648,6),(67,0,428,134218256,8),(68,0,313,824633729666,9),(68,2,312,824633721473,6),(68,8,163,784,6),(70,0,313,824633721472,8),(72,0,167,13194173088528,9),(72,4,305,642,6),(72,256,23,412316861088,6),(73,0,166,13194139534080,5),(74,0,437,512,7),(80,0,431,512,11),(80,1,396,546,6),(80,2,424,517,6),(80,8,163,772,6),(80,256,135,552,6),(82,0,428,3585,8),(88,0,167,13194139534080,8),(96,0,31,9208409883520,9),(96,1,396,530,6),(96,128,27,8796093022980,6),(96,256,23,412316861064,6),(100,0,27,8796093022976,5),(128,0,383,512,13),(128,1,332,562,7),(128,2,312,581,7),(128,4,305,77309411914,7),(128,8,99,788,7),(128,256,23,616,7),(129,0,334,4966056496,9),(129,2,312,580,6),(129,32,30,17179870016,6),(130,0,313,77309936196,9),(130,1,332,560,6),(130,4,305,77309411912,6),(131,0,312,77309936196,6),(132,0,379,512,11),(132,2,312,577,6),(132,8,99,784,6),(133,0,378,512,7),(134,0,313,77309411904,8),(136,0,355,33817108,9),(136,4,305,77309411906,6),(136,256,23,608,6),(140,0,355,33554960,8),(144,0,367,512,11),(144,1,332,546,6),(144,4,353,522,6),(144,32,78,769,6),(145,0,334,4831838752,8),(148,0,355,18874888,8),(152,0,355,262660,8),(160,0,351,512,11),(160,1,332,530,6),(160,64,29,770,6),(160,256,23,584,6),(161,0,334,134218256,8),(164,0,347,512,8),(176,0,334,1537,8),(192,2,312,517,6),(192,4,305,522,6),(192,32,30,769,6),(192,256,23,552,6),(193,0,318,512,7),(194,0,313,524804,8),(196,0,313,8706,8),(224,0,31,8796093022976,8),(256,0,191,17179869760,12),(256,8,99,824633721492,7),(256,16,166,17179869769,7),(256,32,30,17179869889,7),(256,64,189,514,9),(257,0,190,17179869760,8),(257,32,30,17179869888,6),(258,0,189,512,8),(258,64,189,512,8),(259,0,156,4294967840,5),(260,0,187,17179869760,8),(260,8,99,824633721488,6),(264,0,167,17213424208,9),(265,0,166,17179869760,5),(266,0,165,33554960,5),(268,0,243,512,7),(272,0,167,17186161224,9),(272,8,99,824633721476,6),(272,32,78,641,6),(273,0,238,512,7),(274,0,165,6291976,5),(280,0,167,17179869760,8),(288,0,31,429496730304,9),(288,16,198,521,6),(289,0,222,512,7),(292,0,27,17179869760,5),(296,0,215,512,7),(320,0,191,512,11),(320,8,163,532,6),(320,32,30,641,6),(321,0,190,512,7),(322,0,189,512,8),(324,0,187,512,7),(328,0,167,33554960,8),(336,0,167,6291976,8),(352,0,31,412316861056,8),(384,8,99,532,6),(384,32,30,17179869761,6),(416,0,31,17179869760,8),(448,0,31,536871456,8)]
def rootSAutos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def rootSD14 (i : Nat) : Nat := 0x20d84d72a811e41a8f13ff
def rootSH14 (i : Nat) : Nat := 0x2f0000014edb20106622b8c2510416615140348080
def rootSD13 (i : Nat) : Nat := 0x32898903572a99181643c4d83b08f1aca26098d5caa649a1f61480f16ca2609921caa649a3014c19a878cd97100ffd30ffd20ffd10
def rootSH13 (i : Nat) : Nat := 0x310815207a1a1856a8d3a40000372b480e2304301249142c9b9e8e8724b382c72589335c8f91509a2e05557399451794c982231d89f1adcc108500900e8182cfc5d029a6cccbb35d8b2e2b723c552840469a5a860000cd0048e03402020002888800380004010010c20407400825c0
def rootSD12 (i : Nat) : Nat := 0x931180b34c253186dca48b0ce72a26e0cc48f16a8795a6630251882f4780a321c197450ad41638afd3326c3da051c2514e900b9ca8f192644c1669993148db88c6703ce55211e2d4e72a6af28c90970f49a90d844b6823c64122f69987b94167944c04bb08a74828ed09bca025ca930b7d30a407876095470ba905aa3c83942f24c4a7942169993520b547812b0bb0974ca80a46ef18850be051479ab8372a3c78a01614a216999317c12b951e32135301431431f28ce12b265594c294548f26a641c1897c5b8a1e514ba60daa384a1a47935320ed331814dca0b190f28541b526e0c6f109ae524da6043e564c2a3203688412adca14031f2842d332624e3c5a82558a0e5795a6131b0d20a384a92bc50d304ac98938f1ca09521e6c20c699e5059b5520a3a414063cad3326084250f1909a942d92ba664c3e61ee55211e24350b014f2b4c3489ec6126e0e6a8f1810829e5699931aa3e84ac84d51e2fca3434c29718e0d6a0b1016795a664c6a8f80ed211e2d4a0b3ca357261506d6404244125df95a614c38ec212d20a3a8b7f28a515025e0d261b4424879c1ec3e5741c86d415a0ca1434cc98ac31025a423c7295c1ec313413e5741c86d415a74e72a30aee6ac76a5a7c65d2366171f2dce9acd9017355b943d2c111cfa0dacbe0a8c8e87945f047432017c003ffb02987ff64530ffecc241ffd81483ffaa6907ff64d20ffe98a41ffd91483ffb06887ff60910ffea9221ffd32443ffb26887ff64910fff0ca41ffe39483ffd12907fe4c120ffc902217fd98482ffb26885ff64910bff0ca617fe19482ffc52885ff8e520bff1ca21fbe494c2ffd12905ef92530
def rootSH12 (i : Nat) : Nat := 0x509ba7d9f513e4c102bd116f3216b00c00280ba0c760c00002db7a105d14d91f218702129e92bc0bc0610445a6c0839a293611cec5bb4d8624148066437a119aea21e4c2a4800000014b420210148c644e86850889460795e892a20a2ac0d1bab4a18b89b008114b73f0491ec812978109d50f493537c992a3f819a0aba590bcc194001239d0c1dac837aa8ab00216912a7c95710d40a974383912b455b07184d2b128ccbbf5cdc06680d0a780a066c5279d75bc99700dd034c496e61630796ca380c20249d3d1c5c3092893c2438aae0da416958013002a05c3acd66113f0d9a22ecf610c090a4a8002c7c2a2948831963c05a85e0a58000000242834603b43e23d823813eadba23d10b3ad9745be59653a8281935008017003933caf3a81101f9629b2601a022b1098801980c1a1642bc0fe7b931d8a94156a09214d2f8027476566e024000048232043335a2b4204deb4f89046c8542861aa492135a2988d36138511c3c95856c843882354e48c83212e01140b3941018af6044895be6ecf400b4852003d66e07e03542a412d080d84001c8ea496ce1290cdb24a581241f602da83386c9c3250ba803581ea05e068d0742ca94c082856819d131000858017c8ef0ba1cdd8ea8e9a6bd33d0700d900b5c2514458c48ba6a972000129e5e52f6a1620008425a1e82646800c6a62d330b9db3a0e2f6e01753353600f14b28574302948b0396617160c1a9fdeceac2c4f02681547644bc40a822c04691b60d81b012c127b5859151c811f24082dd87e88c000961800213670e20cc33e0b0000a5dc994590a97b22c15b05a797b406d94338478ad1411216e4b54ec08fe562896b07521a5074030160de6ca305382b983c15806f21c8b100630aa1da41ce87f02589ed0a889bad026a02f60650bf063914d40794f247d06a07410d39e111352da40b2ea62749c0c8d5ba13a59c25080e10785975b120112dd06f1b6200800410002383072904441030000184045060500547950111882400401d0a9c0000004285041894408449886e005091c000100a0800e0200380088400502a038008000821614002001421008000002a29003120d28e305420d164820002a00800c0028000081a217200210014c0006e8003003c0a70c00206000038000140820000b93000004000000011c30685062c01f160090c00ac80000345810000482
def rootSD11 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x3ffd5386520fffa6982443ffe3a60910fff96982443ffea954d20fffa2993483ffe8a64d10fff54e89483ff9a04c520ffe6a130483ff9984c120ffe60530483ff9a54c120ffe65530483ff9514c120ffe68530483ff9914c120ffe61520443ff98348110ffe6a120443ff99848110ffe54d20443ff9a548110ffe65520443ff9a348110ffe64d204437fda166120dff6a5824437fda960520dff6a5524437fd9864d20dff655934837fd8564d10dff6a1934437fd9864530dff609934437fd9864d10dff695934437fd9564530dff549934437fda264d10dff649914c37fd984c520bff6a1914c37fd8364910dff6a1924437fd9864520dff661924437fd5364910dff655924437fda364910dff64d914837fd9364910eff66181482ffda864520bff6a219482ffda88e520bff69593482ffda58e520bff68d91482ffda386520bff68e89483fed8254910bff6a193442ffda864910bff69592442ffda364910ffe82998483ffa0a64530ffe829934437fe1a66120bff86998482ffe1a64d20dff54a194c3ffa194c120ffd606194837fd9886520dff6a2194837fd5386520dff64e194837fda386520bffa6982442ffe9a54910dff8a993442ffe2a64530bff8a9934437fd858a510dff60e294437fd538a510bffa6981482ffe3a66120bff8e982442ffe3a60520bff8e9524437fd988e520dff8e5814837fda88e520dff696394837fd858e510dff60a394437fd528e510dffaa5314837fea94c910fef92993483fbe4a64d10fef925814c2ffe5a60910bff969934837fe5a64d10bff969914c2ffe5a64d10ffe965304837fe5964d20dff965314837fea954910dffaa553483efe6a60520f7f9e952442ffe8a64d20dffa2993442ffe8a64530bffa2993443ffa894c120dff54e894837fe8964d20dffa25314837fda3a2520dffaa5814c37fea960520dffaa5824437fea960d10ffc54520443fe9524c120dfe66130483fd9534c120ff64c5304837f99348110ffa549204427fda864d109ff6a1924427fda8865309ff6a2194827fda88a5109ff6a2394827fda88e5109ff696194c27fda58a5109ff696394827fda58e5109ff68d924427fda3865209ff68e294427fda3a2520bbf69a894827fca954d209ff2a5314827fda2865309ff68a394427fda18e5209ff68689482ffa0a66120dfe82993442ffa0a64530bfe829934427fe1a66120bfe86930483ff21a48110dfd606194837f61a64910bfd869924427fe9a609109ff8a9934427fe3a64910ff68e5304837fa39481109ff8ea19482fbe4a64d20def92993442fbe4a64d10fee929304837be4960530def925914c37bda1925309ff969934427fe5a8e520bbf9a981482dfe7a549109ffa29934427fe8a64910dfea25304836fda6a2520cffa25984827fe8a865209bf69a894827be4a64d10 else 0x612672b1e02538130ce3244986004a6f942dfa60ac0ac24c2307604a9f94078638ac0a6e42b502c40b417427c2a7830db51c12a3e574c1aa1f74836aa8e0951d33930ae189a431e5ca04a8ed414c12809479a403f84017c94780bfc18141960b05385c06891a6286b502c0685f95e0c50e6a0840d0c0ac170a4b941f029e90c78da93f2812853d20da8161be502e0a76413543c04a721fd33931b71660074863c7949029f2817053b218f13502547cae4c14ec863c0da094e0a0678a6b219ab1e0be3f4c04a09c6909e1759ab1e3904f4c19a2c053590cd4d1c12a05d025059d844985308c71741533559068e094dd30280b01a35a849b4704a883bd3387fcaec214f4802c47cae99c60217831742873502c4f83f95e83c802c8da60662ebb0853d200acd463a64a4e316dc15e26c1372bc1a2bad4cb9553021590f062e850d6a056918812c602a40b808bc1b6a0569e3013468d2614a2cb3563c7409126347b0ba0a8e094d9331374ce4d43c5b5af03c6db4863c5cc5863f2b9305502f5328c155cd58f17e4044d260ad83c688ba1478f1e528558600b56431e3ca04a78582e85f05a04af2aa3e904061e99c983a05a3958f34808109209560102d01f395a404084904a87942dc2807212616ab5046474ce4da431e0b72f83f95e83c866a05869a5b331662ecc00975d2d7257a4aa294a128264dbc9659253238a44848338fc31e123a9c7178db71a26313c6588c4f17562d2455d8a43133e244444187f50ea21a5c2f984f7087a0db414e81cd02aa0213fc47ecefc81f513e457c28f6b1ea7bd13796cf139dedbb73762cea35d1839de72ece465c5e386a6fc2dde5b93b6bf6caed791aceb5616a34d245a35b42467a4ce2d9a232e7652ac90d8e831896242c33d833afe95f02bcbd7742e965c9eb7f56db2d645a0eb2a9626ac065752ad5d582aa71543ea7614ce296b521ca299424a7ec4f1e9c9d370266d4bf4967529524d848ca90d11f6a39046508b2d152a25e445a87f10bf210b411a8094fe41f6b3e747bccf459e393bce7654e911caf388e6f50db09aee34ca67c8cba192231a061ccc2118112f265c28b5c16452ba455a8a811484284e4f289bc131b2566495890211a72252433082c8fe61f123c847678e881c40370c6b30d09195831105ee0ba016b22bc45550a5813e0264c4a088ef110e20a83ec07910e681b5c33786280bc21560278048808400f641ad82dd04d408600dd813d01c0020c0238000fff6a5814c3ffd5260530fff549914c3ffd5366120fff54d81483ffda954d20fff64d81483ffd5364520fff2a553483ffda960d10fff69582443ffda360910fff6a582443ffd5360910fff60d52443ffda354910fff6a552443ffd854c910fff6a532443ffd8564d10fff60993443ffd5264d10fff61592443ffd8364910fff54d9244) else (if i < 3 then 0x250de60166fc9a83414e0942e1c0ea091721fc4b0403014478248380ba058170ff281623c1221b42e180408d0800941736a0a6717382429b0f1680502001e403161f8242982c0281000f202a0cc14a73ab502c7210b1002446b6a0a6100129ba67260426bf4863c79407902d81282e11af282305338af7940b84685308c1ace074db85ac1234c1706f0e01802a3a0ad4d1da6dc1a0460a61ac4984039b7068234298460d660840b0538250b8537629c1285c27a04a00d05d63c0e0e4022203863c1481d85d3900570b022a4168b405869837b9004a0790e80548c988452ec83ca0a88154a9064b47b20095e5442405a56e34c3046d35b641a385449afa1e1370481e08060b58602832619e258255cac780b94c98439d60b41705f590cd40971e285085a64c1185be3cd206dd0c985a0340d02c02166a0ad8f0ab292f0be0e611b0c09305c78a0a2412e9033e175a38cead407942f80e8ba05c40982c0398461260b8c0324f0d2296e82a3bca0a880a82f83d4a47211b621025174916030452c6d2fb51dd0025456a05c0786940128b00f40d047182582c11c0cc8108160530604e99c62dba3c067e0e5250f05772915ac5d5183301e0518becd4151d063c50b5022d305a5261421fc16046c7814d63078c2b7c781503866a74017138f0dbba01261b41642c0a68168171d007f33c0b02a05340147401701290608591261fc2305330ba04aa74ead470ece82b501e4d90148158660482ac22ce0940f5264282a4228b5385a2d5a431e0b636c078ff2b9345432025864055cd58f0aaab8784fc12078d704017d51f483ca505d15f83d2803d1a6f2b1e0ba482d1a78f1e50a41741b415c2c180a17413c1580af06740d302579510940cc2d42c17c14c2589379551c12a80f0c99122a9a3dca88532812e3cd2016980ce166184bc2045f3ca12751c12a85f3af16e097482a614751c3b56a03cb17d7283a0461260942d1c36d6a16e28c221b70d07ad42dc36825146124db86840251362041711368a33a01149f2b930256981539aa6a03c1b42e5905c3c063da92b02c85815be507f05ce82a3b21e0be04da4029bcaa8e7e6a0742cb4cec22ebbb82c0a7a4150f05d05304a0d00f040059a41b5281a0180582e812853cd4d1ec827e51560ac14c1282e8799a9d02403004c1fe0e9307e13c16848bcac78b00c0945307d0b56431e66a41b7f06293c80711475a81620648930f816b4863cad4716f8f05204b0b4126c806d402ec122903e85a04ba41e55474c2c1a5e0c4c0ba146f2821238c0d50e2e806a56a0587169c985a8980da10ac80544056c300bb048cdec227c6602574151d62d05a89f04be0c36d470a880080d0128d10a62985d590cd58f1402c0ee091743543e053d20d1eb5282a0b405c294210c0b201b5006b048a41a216812b47d21729244fa672 else 0x2b16c6ddbba2c07a1ace6ddc1cb74ad8d4ab42c4595a93cd40d4142ac0ac2582e85828536bc2d0b504f8240e8ba09a864d826b505a36f2dc0f1c2b01d058165cc84d01874586dc2150fc128c41281e0d6904f05287e09842094269e9305903ad8400003c1270282dc160bb3a0908c55a8c2147407145c802393164d460dd80217c2e8e2dc5c8004da094ac9a8c05404a2e82d18ddd83577158ab2148287f066950a00c262154ab011405534a5582a00c142094ed30e2d1858b0c498a1482880589081a02521c58850b0000542c428580b80002529568840661602e04a284f0521080004a404b084000542053c3102610d0f03a0b8e0019a81104a4b5e6ed93027172094d6bce2b4c09e2e4b4980e81a04e1642680c38338582f85d54700060610b0dd8b0a8e000cc9b04caf0b57280e980a50f05c2481603403c717d51c5d04b1241fc1604040b924d061d787f12c100e0ae0c42c794a941284017da42a3b6a58590a02342587f1740b02020dd9260a1499d00560fe25820245d034741061b504bd2151c29a41a01487823425b6a1740b02e240a30f14209420155b82e04b0621e0780a99a9d0260a41856ea32048250fe0d2c866a68eb1730601760f1081e012853413116c2101286d0b868130615b825a300d035e6a0a8d1dd02c2805659c0bb353a004a10101400a0780a8456ed1f0782c1080c43f82508097940b42102c1080943685c40256d42a02005a28b31a16bc12e090822a02d20098d003c096e508a0ba6dc3a240e0980a9640088250d2304ab09651caa8f824933af17c1fc4b04048c13761341385e1302a020221a8398580ac2a0c093c078693a0c78f2980b19a8afc78f286987f0888174108160c411a1fc229c2a87f19e2782163c7219a85d26a3bca19c108160850b81bd00b19ab4cc78150508cb088809a1081605e1a61ac229c21c2c05d1b56704a1839a8298a5a8ee4180b19a825c78c601a0d30fe11120b0258421081ac5d05c3d2654c7583b6908bcf2b1e02e480b16d8f05d17711a1fe160454c14c1f25040d9014231012b47794a15ef284207f04a120c2f85405c04a0b8a3089886d1340943f982a05a56f4624a0cbcd41fc30025740d1d8150128781bca68e0d0538250b8636ed1c1a0840fe094201de504206829c1285c30afd215a81282e03c62ee2db0c50f1501701282e40cfc795a8298c21260b8f4983985ec7833c4982e381c016164db8bac126643f896080a0e78f0e88561260b8c02cdf935c300d04207f04a10138245f06b0a60b02308e385a17d824281d1b9424da3825495616e1545f094c78f28240c7b419a9604c058bba8ef28bb8a18841bd204cbb92617229c1285c39990aa6ec4d))
def rootSH11 (i : Nat) : Nat := (if i < 1 then 0xb2454e0049e98c89400d0c69400010924e7cca0000a00a5a001841758020969018a52981460cd82d4103a250106ada229583d6e1425be94a002414101bc17dce74ea623a0179d0b009401c812c062819a82941360060974502882322c4420125ec3e8cf2519d5ca0ef82be2ed06821395c8377c817941495c457c01b654ca21e0788103723060c00b445a07c153e119828286d0434cf68470123391604d5d6267381cc08f1c880d631940b000d4131853e06386408801488927809693602b64da22648f8c8073a104ed615043b53722d2100857417805b4171015d5a5cdbe160107a0cad054041a614e33855c89a803200ec3c54af245b381025e197065010c13c005f40a8075815a99c558a01f06712e782320fb3a1a15f2cd336c4e26f7283a603fb3fe0843e740f0828e0b210ba4d483e80ae80f88a3a082105187002c05004e485626e8044c052be8055a04440b9ce1c0f4851a13305ba8fc948218c84d60aab1468c38086023a4200d43be6f3bb5aa1662d80048862c0b1b6940c205e80f280e4152836449e80f4251a3ba9638071310a3920ea22c20e120a97a5226d71ba4cc0dfa3748e1841206c0000fa4051454e80f209fd00082b0000991268958382f8087852d6a0024403401a69124cf498b001af3da4996ac832571e063753f85548d73dbe51e0396080120cb37433200785240b6258a80e91660380012d3c058ec1f01a212992128c0000e0aba2ca07e22840d201aa04323ef347108404789c605402e171a549a89e03708615aaf79a855935b00000c60002c8e0002830539617edcd410784c08b35338000817400081245a7145000085bcba3a57842da35815e02436c4058ae6683b64144d440e7568201485da80b50980e6b3c6042803532added52902fc558a22698803fb55fb92f3a301b882181c1486028961fc28e02eb2a101fd11480ca2db56780db39eb15216cbdc682211250000050405120002010240e700005b0003030119000a020602044d07000c000001e20b173702000c031000136f00293b060102090a00070d0400000100001600033701000106003400030864001809010318370a031f003d3002000204000000011f041600150132050900000003280f340502000009fb0066050001010006270b0414760518072b1a000005216c1a0a03000003030000110d000031070a0b0e080003000d00005700080b0000000137745e001a024f00000b23071e0628010d010211390b08000a16021900032a020603133108240e04002f00000a001900130209c2030201070003000008070e04781f0c00960603130256010c0d00001c0a04134f022400071311030c000905120200243a0f12010a032e0200010004b706020612681b00141b31005700090033280000020015000205100f0701072b0000050000032504020389 else 0x97355c4e4f838f4ac005a8b50000122ddfed2282f60d1a3bc13a065842c0000000cc5c000008a0a733ae8a004bc15086560e439b807bd66c94d59c68e90406ea922200b420b28e28248482835411a20ca15a5dda0ba10080e2a1a9650009c12d433a0e0824c09d8180d3b046c06b95ba11283af3a483f4170011003ace4a09c005e14e02f0473833e169042e16a0534144032e120816051c04baaeca20601023154a5b27e61fbcf871aa03f51f04f211791bd0a2a39d60a853257784853155c860a68564132c0ae87425980db4db7122850eced21aef9f816d3655e48108857207d83bb4a183c50e3d66207602ec19ba22e015519a19d5e61352b29c0b30522e4c5d74e4a031f4cc80de083811a182d3b292952988fa143e572429e082431241b24ac0f9c662898014e0a186880d72078872a34c88282165a603dee263ce373d4292e9da5865113c5c15b90684dbb310164107e142068e07abb7b46780b5316a22a102054e0e8817338fa59682f81e608d1c8617b8322114946c177016687f20a441d539a01b53b410f15fe96e022cc4e05c80f3816b77d82388c40638517882d0b75d70c0da330913a0c413426120da55c2019ba1682882628515d2c0d802b2cb789f006425909a5bd01111cc440960044191ce94f3fa4968c185a2fa184276aab2fee0ebce614a8256f3aa462193364b799147556b842811e02780de22372f5201552401df192a29282723c24f524d2081029001384984a58156154d87098680ed667859c180d69a89c32428e35c888f9004816b)
def rootSD10 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x6a581482bfb0db50c92213fd86da864910bfe436cc2408847fe1b6a239482bfb0db4ac9a217fc86da5481108ffc36d2c72905ff21b68d204433fb0db46c92215fd86da264d10afec36d1b24884ff61b68d924437f4a9434982411ff86da3a2520ffc2a50d2408873f598606194839fac0b510ca419fd6a21a64910cfeb310d3248847fe2b6a193442ff515b50982417fa8ad9848110afdc56d4b048857ee2b66192442ff515b30982417fa8ada848110dfd455053309047fe2b6a2194c23ff15b511ca217fa8ada54c1208ffc56d2c329877ea2b64d20442ff515b42982417fa8ad9348110cfdaa5153268857ee2b64d924427f715b46c8a415fda6d8186520aff536a8a609047fe3b6a192443bed1db30982417f68ed984c120afbc76cc326885fda3b6a1304823ff1db510ca411ff8eda88a510bfb476caa60907fca3954930483beccc47298241dfa54a39481108ffd56cc2629067be4b6a1934433df25b46c92215ef92da364910bf7496d1a408867be4a661934833df2532ac9a415ef92d9364520af7c96c9c329077ba4b64d20442fdd25b26902219ef6164a64d10cf7b51253268867be4a609934433df25330c9a219ef6964a64d10cf7c94a93268867be4a68993442bdf25b26c9221dee92a0a64d10df7495053268867be4a8a993443fd5252a498241dee929984c120ff3494a9a60907f9a4a4c5304837dd25342982419ef6a24964530cf7b7524b029867beba925814c3bdd24c14c8a619ef9262a64530af7c56d0c92987f9a4a8e5304833df4d492c0a619ef92da386520af7c96d1c329047fe5b6a2194c23ff2db5114a211ff96da88e5208ffcb6d44728847fe5b68d924433df2d494c9a219ef96a49645308ffcb6d1c329047fe5b68e294423ff2db4744a419ef92a5964d208ffcb6d14329857be5b686494c23ff2dc54c9a215bf9ada864d109dfcd6d43229866fe6b6a192442b7f35b42cc2415bf9ada8649109dfcd6d4322905efa6b66120442b7f35b30c92217be9ad814c120cdfcd4d4b029066fdb99a98148337f5ccd4c0a41dbd9ad8186520cdfcd51cb02906ebe6a925814c337f35b5114a2137f9eda564910bbf4f6caa60905dfa7b69520443ef53daa49022197f9e9a954910abfcf6a93268865fdb99e9524432ff5ccf4a922157f9ed5286530abfcf6a94728865fe7aaa5524432ff3db4b1ca4157f9eda58e5208ffd16d2c329847fe8b696394831ff45330c9a418ffa29a864d10cf7d15253268867be8a925914c23ff45b470ca411ffa2da38a510efd512a92609077d953a2530483bed44a6298241dbe6da894c120e7f512cc2609073fa89829984833df25512c9a41dee92a894c1208ffd16d14329857be8b686494c337f35552c0a411ffa2e2a64d108ffd172d326887f615254520443fa4a9aa4982419af9aa4960530 else (if i < 2 then 0x217fe96d814c120cffcb51cb02904ffe5b6a2394833ff2d304c9a219ff96a2a64d109ffcb6d1d129057fe5b8a9934427ff2dc54c8a613ff96e2a64d109ffd74a9b309067fe9aaa553483f7d35b0298241bbf9a95360520ddfcd4c9b02906efdb39a98148377edccd4c0a41faf9aa4960530bbfcf6d2b048875fe7b54993442eff3daa4c8a61f7b9e98254910dbfcf4c1aa4886dfe7a68d524436ff3d352a922177f9ed5264d10dbfb673d2a48875fe7b54a194c3aff3daa51ca213ffa2da564d20bff516a9a408857fe8b54d92442bff45aa70ca415ffa2d538a510bff516caa60905ffa8b69520442bff45aa4c9a215ffa2d5286530affd16a9472884ffe8b69639482bff45b4b1ca415ffa2da3649109ffd16d1b22904ffe8b68d92442ffd45b46902219ffa299564d20affd16c9b229057fe8b64e194833ff454b2c9a417fea2d9348110cffd14a93268857fe8b64d924437fd45414c9a219ffa2a5a64d10cffd152ca62904ffe8b68e19482bff45b470ca41ffaa25524c120eff512caa609077fa8954530483feca9d12982419ff6968964d20cffcb544b269067fe5aa25314827ff55aa6c12213ffa2e2a64d10affd172d326884ffe8b96993443fe8c0a6298241ff86c95148110bfe36b0d2408877e95264d20443beccc26298241cfe661814c1209ff37105322985fd9b58e530482f7cdb512982415fe2e5514c120fed2a6a9240884ff9b1829984827fcd8534c12213fe6c29a549109ff3614d3029067f58168e194827fadac34c92213fd6c69a60910afeb6354a629057f5b1aa5814c2bfad8d52c0a415fb6caa94c910afdb6554aa48857edb2aa582442beed9d5298a415f76cea94c910afbb6754aa69057ddb396531482beed9d1298a415f76cea960d10a7fb7154b029053fdb8aa5824429fedc472c0a411ff6e1a58a5108ffb70d2c728847fda9aa5834423fedc34714a211ff6a6a9609108ffb70d14728847fdba8e5814823fedc454c9a211ff6e23a649108ffb711d4329047fdb8969934423fedc4b51ca411ff6d5a3649108ffb6ad1c329047fdb568e294423fedab4744a419bf54da6a25208ffb6a54a629047fdb568a194c23fedab451ca211ff6d69a609108ffb6b153268847fdb58e9924423fedac750ca411ff6d68a64d108ffb5354a648856fdb6a25934823fedd4b298a411ff6ea894c5208ffb670d3309047fdb3a299244337ed334744a411ff6ce8a865208ffb731d3029047fdb2969934423fed9514c9a211ff6e63a609108ffb731d2a48847fdb9969824433ded434324a619ef689a192530aff416d4326884ffa0b6a1914c27fd05b50c9a219fe82da8649109ff416d4322904ffa0b6a192442dfd05b30c0a413fe82da564d20aff416d2b26884ffa0b69592442bfb0db50c9a217fc86da848110cfec36d43248857f61b else 0xc6c9d5844ec13b06bf9ac95729aa0697da1267759a865fd9566485904630d63462095ca61058185f5d78a5d257145b1d6925975634579d5ca5685584553d53253f545453514b7526947d515142b4fd93cd4ec136f4ce927e4c452dc4a6d27e332924948811d3464914543e10c341d90414090fef3f18fa93dd0f3f3c28ee13ab0e6b3848ddd36a0d8b3588d453470ce73328cad3240c7331ccc562d50b5430e4bec2eacb8e2dc4b542c1cad22aa4a7428fca2227e49d026cc95a24948d8222c85620247a41dec75e1c746e81a9c67218045e4165c55614244e012dc49a11f446010dc40e07f81fe0fc43d40eac3820d6430c0bbc2c60a14268086c1fe07241ac05ac0fa01c4000ffe302a8a60907ff18354520443ff4a930298241ff654d814c120eff30ac9a40885ff9b5a2530483fec5caa698241ffa60d5248110ffb306a9a40887f798554d20442ffcdc2a690221bfd605a386520bfeb634d3048877ed82549934433fed2b3098a419ff6a15264d10cffaa4d44329867fd526a2394433fec1b4b14a215ff6d63960520cffb04d2c728867fd8568d92442bfedad12c9a415ff6d6a94c910affb70a93268857fcba61593442bfe5d2a4c9a215ff6e2594c520affb6b44a629067fd8568e29442bfedc2a6c92213ff6d5a3a2520bdfb6c54aa6906efd5369a894827fe5d2a6cc2413ffaad53a25209ffb6b1d302904ffdb5a29934833fe54b52a9a419ff615a28e510fedaa6c12a4885fbdb4a69824427fedc474a92213ff2e953609109ffb6b1d304884ffdb5a29934427fe5d304c9a213ff6ce9a609109ffb674d2a4884ffdb3969824427fed9514c9a215ff6c6a954d20cffaa6d0d12905ffa0b6a5814c2ffd05b52c1a217fe82da960910bff416d4aa6905ffa0b6a552443bfcc2c14c9a21bfe6160a64d10bfec36d4b04885ff61b6a532443ff8c0c3298241ffc6161a48110ffe3070d240887ff15386920443bfaa9b030ca41dfd64d8186520efeb02d1c329077f58386992443bfaa9c34c9221bfd6161a64910dfeb070d324886ff55386992442bff4db4ac12215ffa6da354910affc56c2b26885fee2b6a5824433ff15b510ca617fb8ada354910cffc56d2c329877ed528a9934437f6a9454c8a619ff6162a64d10dfdaa515326885ffa3b61520442bff1db0b14a213ff8eda864910bff476cc2408857fe3b6619244377f1db4d44a413ff8eda564910dfdc74c12a48867fd858e992443bfcc2c7290221dfb609528e510affc56c2c72885fbe4b64d81483bdec2c94c9a21def9295264d10df7b0b25326886fbe4a609934437df252a4c9a21fee929814c120ef7b5324b029877bdba925814c3bdf24aa4c0a61def9255264530ef7b6524b02985ffa5b60d20442bff2db06c92215ff96d838a510affcb6cc2629057fe5b66239483fb72db04a92)) else (if i < 4 then 0xfe605b05c0d306f20320637350182165c81810c11034c1fc904a0b8204283402c030240a01e8180c2440c055200568560a6482605c0ba040201585d0298229014c2e810060a743012408045610b00400a10702a3386002004d02e02283c1c2681701156dc8085068056060409203013c80228180c14c0cc40b8124b6e30b004603306c20358198814c22c409e16a204f0ba10028298814c2d441120ac16415207c05c602b06802303e097282e0198814c07840b806020890560b20a803e02e371e06983f822138f014f0b060c256e142090406609a07f02e24128398b86017007860ff08403c3825078158781560c6a3f4861600f1c06420422812480de0d014e1020f20e860a7081e3c6a607401e30b545780c83413a402ced1c1ec288078df07e99479f21a1fb5eb6d456806d0b801e1e0a02e0b498284070258100bc1e0380b904a4055c3c02e15508e28088458660241210f0b00b805f9a83502a38f017d202e12c20d409666d6d009c42530176b506a0416161749b1b435020310a094c1a80e7484309305702e184b02b880202d4416a0b420530be02e18020150050c0202e8416005c2a90c3c05a1f9a82d05d0fcd40782e860661263a004a08c0b4604605310540248298c13a24e096f280cca17406620b706708808104901e30600180818c28c124078817405c202e08a02407403e281282b05af9ad352c802a01700f27cd41540741640b02d50b3d86a401140b97f07b5fa1fc4dc13f41f20b6d4569fc5b35cfbb7ec4fa9fe96f9e7e68f92fe22bb83df9f773db3f62bd3df453cf7f36bca5f223c5ff10bc19eff3bdfeedbb99edf35fd572bb5fecabaf5ead3a7fcaff322e8fb69fcd734f1e70f9fde7839c3e70edc3b70f9c3e70f99ae5c7948e00b8e5c79b91fe40b7f1e3978e5e3235eccd738b7e20b84de0c3802e04f7f1e00b7f1df2379fdddb765dd2372bdc3b6e5daf369fda0aee0bb0edc3d9c7654d8aedc3d86b5fdd7b35dbd6fb589d58352bd43b4f1d32349fd17b41dcfa33b3cdfaee0cd86ec3315ae26cd72ee0ccff322cc172e8caff296c95722cc80f1e6c6f7188c51f11ec3a70b4c1ff056c056ff8bf6efb2be26f60bd0ef1abc6aef1bb82d3eb9b2ec3ba9ada6ba26e6cb90c47db89ae09b782dc3b69ad89b4facadb442d78b56ed3eb4b6d10b3ceccab2b6c84b16ec32b056bc8aeaeb76ad66b59acf2b13ab7aaa9aa02a3fa82a9d5a6e298fa4da901a3628a36a81aa0a1ea839a0727f39f5a79597be76c9d0e71a9bc66c89a7e66a98d660c97be5c6967655c946e12a933a12a06b248d91003d40f52423901a3ad8d823378c6a2c18a3224b87f8c56872617c84ecc9084aa0b981e20377fa947d7ea5f8c7d5df167b55e88791ddfa7685d6c5351d377439cf17321c0c727dc7670d5c0c53515846f8dba25729b795611b5 else (if i < 5 then 0x6c0788b6d46b456ad44d180028b901721c182f8170fcd70531280bb0b0a16a2aa2abba1410010cad0a0c15c23c160785805d884308601711c182a8170c2d407400078301019002160c015082c80ec402000220b2008003180181388094000417403a0003014000160c707882c0220417410b00a31058004082c0200a09a204d005105d00e8080c00404050ac0e603a30ba093856180f12902d0c0741fc4838817c136c2192b32607f0b51044032817810102e8008418a06020000140051be561e05d00f100949e4150078809a03a08030a105c05602e053281681705d020101d00b810016881740922025048053181983a61602d7486a38129c0a80b011814c987874005c30530b904001e201284b00f0c2dc2cb8255a82e8a04a080202508d01e18340128813c0780501241a0a00604a05c302702508b18440128170c0941a00b8600606805c30310d40531da60658128229021c1e80942e881660340923025068104701282d0c0780941d060260ce15209203c502701d0a9054049280980f04385582e837982dc19c28c1a0120a02601c15603c10208a60b205c10040658801c01001426404434c1e0e03801613a15217408060d407a01e182d06009c9a04da7805ba438f0168e0d213806816a40560890d4073040282b04485a85401f017182d41c0270078803811216a15207c05c60560690c109302e2d04840cc0ef0b30c424c72828b51c095214201619614c03c505000c0a703d0ba281e0058468298658209816811824c0941d0a054124208407405c02e202785a0540240299400022c1441b0300a00c0dc00212e0fe090602a0b908507f048280303700005382202d18c3c11417002c3101e8100e61e09606c044400904d0ba0402004a3680f0c094078404a0b803c301101e053180e02e0170fcd40501340680f4a00004a03c366a02501e1fb080980c82d034140941ac078605c1742b4c00302c01e206581280f0c2c00501e8078802004a03c3f8305584a05302e285b83382d05380f024996400b811814c816c0d603c05c40af0110681857be500f0df282d00941ac800403c201d0ba02e092040280004b059840817140ac2d02341700b8a04a0b805c30b920907f0960402806f0485a84084d817181400302a0094300a03a05c124080405a0c7e3c0a803e02e301284681700f100ac0b8248100802204a03c304f04c39004d01a08e30000128802417007860b803c202a0260480532013822882f80a812014c802818003c30c70401015022880a82e8404e1740803093048053185f013812820121096400b8605c03c2e6a0350490a106f281a82086983f93060172094603e1500b805c40b189807f04808d2c128240814c0b364011090280b904a37a00910307ca82c0c633e505f86005083794190170056e439a82e8d0dba4c134060088 else 0xf029890b2da80b876d40a6174374c818100e841fc1c05028134cc1811d799360c0c0420742e8617204a20b93af038181700f0298d01ae0d0101940e0154cf0600a0aa30880ba100282a0881c2d821433080a8164204d0c6039182e81c8b4600c40086108070200503010010268180c2c80a8400a0b4205a00c102ce9300ef0491c9816b824074836604fc1203a0fe5002e0900001d201000f839dcc83494058028740054100a10802e200001416930168018dc98004094617a0d601430580a100c1ba640a08094008503a0d6202e0db09d7b93058101ac0b51182c0806e0d62726003100184150200404a0323025011091180006301c0c0642030010200c156100c0028bcd40d0284603409014230020ba100c850880682054006210606603218ab0409c2c04e9813af08018010b43f8260941ac906a06009a3b184350300a1200022a08002094403302814230bae1806b18182dbbb085e6b5140497382c75a96dcb36f7072adad4403043f9560a1210203c0112db9013c014400270031027806081342c84004032200001d00c182a8180508c0c05580ac2840f8a02202e122301d04d00c1826806080a8da8078764c0b5c1203c4b47a2ce0901ea3128830148340c0341a)))
def rootSH10 (i : Nat) : Nat := 0x900018000000a4e43205624f00f03371b215070b38a5e938490a5343b42a75c29620466a21fa50662a9402a404825b4245a72208b05570d401b8106a91705998589966171606075407a993708524a4a41c00198d29400003d97d85e04200041393440678842196e03fa4c06c04000384b74ea2504463b42c92c75106f06604e05b04795db4400000106548386000006902e03763778600107e62800000148b978b4a07400000120b027137030a1178d42745e98f048072698b3a001976900080038000004448140280260183f700a62806103c0a1880408a805582018ae0
def rootSD9 (i : Nat) : Nat := 0x202812166da805c0b52615803a281601cc0d23061f5a8402000fee646c1c605b664602e00f014c60300f49bc1229d7840f004010210206b080b8342c0c81e5062f0487c30106181d4403a0c8102a040d01a8094771ae0c34350d0ac3d6a0d0fc3b610080905801d0398c174101680780a6300f00b84036080ac174053215828408a600b840c4102ac0941163002e816a05a18e60591f6224257f20b01602c7b4eb9c13566880b01602c64a0b1683133acb897a2e25a00b0162be5580b01628d4f69a52523844c850f402c0580b0161d63880b0d91a031c5bc1602c05850c9882c0584141602c0583986a02c1021bc2e82c0580b01602c0580c416000ffc152605314c120d7f0b9605514c120ff61835495148110ff4953549814c120bee9c6a25524c120ff48c954d524c120bed9c62e5534c120ded9536da894c120ff498354d524811097bebc6a64960530a6fdc62a5a954d20c6fda56da8964d2087fccb695984c52095fdc796e2a64d1087fcca6e15264d1087feca8ad8564d1087fdca8ad858e51087fecb2a5a954d20c7be4a6d68964d20b7b64c64d8186520e7ae4a6095264d10c7bdb89295264d10e7ae4a54a2a64d10b7b61c6ca4960530e7ae4954a2a64530d7b64b605a386520c6fe5a6da8964d2087fdcb96a894c520dfd25b605314c120deea6b549814c120deda6b54d814c120e6f66c605a386520c6fe6a6d63960520cebe6a92d9360520deba6b929814c120e6be6a6a64960530e6bdc99aa4960530e6be6a6ca4960530e6bdcb9aa4960530c5fe7b6a15264d10a5fe7c549a886530a5fe7c549a88e510c5fe7aa6da354910a5fe9c6ce7a54910e5be7b9295264d10d5be7b9295264d10cdbe7b9295264d10fdaa7b929524c120d5be7b9255260530d5be7b9255264530b3f68c54d8186520c7be8b9299564d20c7be8b9295264d10c5fe7ba295264d10ff4953a25524c120f7aa4aa25524c120d7da5ba25314c120d5fa7ba25954c120f3d198605314c12087bebc6a2496453086fecb9a9a96052085fecb9e9a95491087f5caa6d818652087bdcba6a4960530c6be4a6da8964d20ff0a4a54d524c12085fdcb9eaa95491086fdcb9aaa960520c6be6b92da864d10a6be6c6a24a64d10a6be6c6a24964530c6be6b9299864d10a6be6c6ea4960530c5be7b9299564d20fd627c5495148110c5be7b9295264d10f74953a25524c120
def rootSH9 (i : Nat) : Nat := 0x1934800019a01960194b04
def rootSD8 (i : Nat) : Nat := 0x6058160b032160642b083ead800502fc93ac64aa6a9260906f9254dc6a25524c120ef2535aa6a93029824145be7d6e24a54993443fa14f7252a6a926090712f9aa7b9255260530
def rootSLevel : Nat → Packing
  | 14 => (1,0,8,0,0,0,0,rootSD14)
  | 13 => (3,1,8,0,0,8,0,rootSD13)
  | 12 => (30,2,8,0,0,12,0,rootSD12)
  | 11 => (220,3,8,0,0,15,0,rootSD11)
  | 10 => (424,4,8,0,0,14,0,rootSD10)
  | 9 => (77,5,8,0,0,11,0,rootSD9)
  | 8 => (6,6,8,0,0,6,0,rootSD8)
  | _ => emptyPacking
def rootSIndex : Nat → Nat → Option (Nat × Nat)
  | 14 => rootLookup 11 19 3 7 2 4 rootSH14
  | 13 => rootLookup 37 67 6 10 5 4 rootSH13
  | 12 => rootLookup 181 431 7 13 8 4 rootSH12
  | 11 => rootLookup 331 719 8 14 9 4 rootSH11
  | 10 => rootLookup 53 127 5 12 7 4 rootSH10
  | 9 => rootLookup 5 11 1 8 3 4 rootSH9
  | _ => fun _ => none
def rootS : Forest := ⟨511,14,fun j => rootSSamples[j]?.getD (0,0),rootSCols,rootSAutos,rootSLevel,rootSIndex⟩


-- Successive groups record a common live-wire count and the number of states in the group.
end PEqualNP.Outside.L_meta_670.Projection

open PEqualNP.Outside.L_meta_670.Projection

namespace PEqualNP.Outside.L_meta_670.Projection
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem runtimeBenchmark : rowCut rootS 9 0 16 9 0 9 = true := by decide +kernel
end PEqualNP.Outside.L_meta_670.Projection

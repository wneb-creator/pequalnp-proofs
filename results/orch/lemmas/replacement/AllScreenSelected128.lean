import Lean

namespace ComputeBench
abbrev Sig := BitVec 128

def zero : Sig := 0

def one : Sig := BitVec.allOnes 128

def neg (a : Sig) : Sig := ~~~a

def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val

abbrev Wire (R : Type) := R → Bool

abbrev Row := Fin 128

def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

def plainWord (a : Sig) : Bool := !(bit 0 a)

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]

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

def backwards (d : Row) : Row := Fin.ofNat 128 (128-d.val)

def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)

def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 7).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none

def vars (m : Nat) := (selected m).map Prod.snd

def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)

def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
 (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6)

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
    BitVec.ofNat 128 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)

def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 128 d)

def properB (T : Sig) := T != zero && T != one

def paidSliceChoices (d : Sig) (pool : List Sig) : List Choice → List Choice
  | [] => []
  | c :: hist =>
    if availableB true d pool (choiceVal c) then paidSliceChoices d pool hist
    else c :: paidSliceChoices d (choiceVal c :: pool) hist

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

abbrev Bits := BitVec 128

abbrev Signals := Bits × Bits

abbrev Decor := Sig × Signals

def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b

def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

def defaultDecor : Decor := (zero,0,0)

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
  let n := (v.toNat * 232657547755585) % 2305843009213693921
  (n*(n+971)) % 2305843009213693921

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
    if (rs ||| column d z.2) != BitVec.allOnes 128 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true

def compactNext (path : Nat) (ws : List Decor) (hist : List Choice) :
    List Decor × List Choice :=
  let a := ws.getD (path &&& 31) defaultDecor
  let b := ws.getD ((path >>> 5) &&& 31) defaultDecor
  let d := (path >>> 10) &&& 3
  (ws ++ [dbin d a b], hist ++ [(d, a.1, b.1)])

def walkCompact : Nat → Nat → List Decor → List Choice → List Decor × List Choice
  | 0, _, ws, hist => (ws, hist)
  | depth + 1, path, ws, hist =>
    let next := compactNext path ws hist
    walkCompact depth (path >>> 12) next.1 next.2

def rowWires : List Decor → Nat → List Decor
  | [], _ => []
  | v :: bank, mask =>
    if mask.testBit 0 then v :: rowWires bank (mask >>> 1)
    else rowWires bank (mask >>> 1)

def compactPool (m : Nat) (domain : Sig × Nat) (hist : List Choice) : Option BoundPool :=
  materialize true (vars m) (paidSliceChoices domain.1 (vars m) hist) domain.1 domain.2

abbrev CompactGrid := Nat × Nat × (Nat → Bits) × (Nat → Bits)

def CompactGrid.mask (g : CompactGrid) := g.1

def CompactGrid.top (g : CompactGrid) := g.2.1

def CompactGrid.pos (g : CompactGrid) := g.2.2.1

def CompactGrid.neg (g : CompactGrid) := g.2.2.2

abbrev CompactTable := (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → List Nat) × (Nat → Nat → List Nat)

def CompactTable.count (t : CompactTable) := t.1

def CompactTable.path (t : CompactTable) := t.2.1

def CompactTable.live (t : CompactTable) := t.2.2.1

def CompactTable.picks (t : CompactTable) := t.2.2.2.1

def CompactTable.bucket (t : CompactTable) := t.2.2.2.2

def chartAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  let bank := walkCompact (g.top-k) (t.path k i) (rawDecor g.mask g.pos g.neg) []
  (rowWires bank.1 (t.live k i), bank.2)

def wordsAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  (chartAt g t k i).1.map Prod.fst

abbrev Domains := Array (Sig × Nat)

abbrev Perms := Array (List Nat)

def selectedHistory : List Choice → Nat → List Choice
  | [], _ => []
  | a :: rest, mask =>
    if mask.testBit 0 then a :: selectedHistory rest (mask >>> 1)
    else selectedHistory rest (mask >>> 1)

def poolList (m : Nat) (dom : Domains) (h : List Choice) (picks : List Nat) :=
  picks.filterMap (fun j => dom[j % dom.size]?.bind (fun d => compactPool m d (selectedHistory h (j / dom.size))))

def applySwaps : List Nat → List Sig → List Sig
  | [], xs => xs
  | p::ps,xs => xs.map (movedWord ((p::ps).map swapRows))

def linkedCandidates (g : CompactGrid) (t : CompactTable) (perms : Perms) (k tag : Nat) :=
  (t.bucket k tag).filterMap (fun code =>
    let name := code / perms.size
    if name < t.count k then
      perms[code % perms.size]?.map (fun swaps => applySwaps swaps (wordsAt g t k name))
    else none)

abbrev NodePool := BoundPool × List Sig × List Sig × Nat

def cacheOnePool (u : Bool) (front : List Sig) (p : BoundPool) : NodePool :=
  (p, front.filter (fun a => !(availableB u p.domain p.wires a)),
    p.wires.map (masked p.domain), front.countP (isMaskedConstant p.domain))

def maskedAvailable (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zero || m == d || pool.any (fun v => v==m) ||
    (u && (let c := masked d (neg a); pool.any (fun v => v==c)))

def cachedPoolCut (u : Bool) (a : NodePool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let (c,missing,bank,maxCon) := a
  if c.bound + maxCon + 1 ≤ k + c.paid then false else
  let z := choiceVal op
  let con := c.bound + (z::rest).countP (isMaskedConstant c.domain)
  if con ≤ k+c.paid then false else
  let extra := !(maskedAvailable u c.domain bank z)
  (decide (k+c.paid+extra.toNat < con) &&
   missing.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!missing.contains op.2.1 && !missing.contains op.2.2)))

def cachedClose (u : Bool) (pools : List NodePool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  pools.any (fun p => cachedPoolCut u p k rest op) ||
    (let ws := choiceVal op::rest; (links (keySet ws)).any (sameWords ws))

abbrev cached_NodeContext := Nat × Nat × List Decor × CovPair × List NodePool × (Nat → List (List Sig))

def cached_evalMove (c : cached_NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 128 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      cachedClose cov.2 pools links (cap-1) rest (movedChoice op a b)

def cached_testPair (ctx : cached_NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := cached_evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true

def cached_opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]

def cached_testRow (ctx : cached_NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (cached_opsOf ctx.2.2.2.1.2).all (cached_testPair ctx a b))

def cached_testAll (ctx : cached_NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => cached_testRow ctx a bs && cached_testAll ctx bs

def compactNode (g : CompactGrid) (t : CompactTable) (dom : Domains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := poolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))

abbrev SliceSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def specDomain (s : SliceSpec) : Sig × Nat :=
  (subcube s.1 s.2.1, s.2.2.2.2.2.1)

abbrev RichDomains := Array (Nat × Sig × Nat)

def richRaw (m code : Nat) : List Sig :=
  if code = 0 then vars m else typeWord (code-1) :: vars m

def richPoolList (m : Nat) (dom : RichDomains) (h : List Choice) (picks : List Nat) :=
  picks.filterMap (fun j => dom[j % dom.size]?.bind (fun d =>
    let raw := richRaw m d.1
    let selected := selectedHistory h (j / dom.size)
    materialize true raw (paidSliceChoices d.2.1 raw selected) d.2.1 d.2.2))

def richSpecDomain (s : Nat × SliceSpec) := (s.1, specDomain s.2)

def richNode (g : CompactGrid) (t : CompactTable) (dom : RichDomains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := richPoolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))

def primCheck (g : CompactGrid) (pools : List BoundPool) (links : Nat → List (List Sig)) (t : Nat) : Bool :=
  let allW := rawDecor 127 g.pos g.neg
  let ws := rawDecor g.mask g.pos g.neg
  let a := allW.getD (t/9%9) defaultDecor
  let b := allW.getD (t%9) defaultDecor
  let d := t/81
  (ws.contains a && ws.contains b && (a.1 != b.1) && properB a.1 && properB b.1 && allowedB true d &&
    properB (bin d a.1 b.1) && plainWord (bin d a.1 b.1) && !((vars g.mask).contains (bin d a.1 b.1)) &&
    (typeWord t == bin d a.1 b.1)) &&
    testPair (g.top,ws.length,ws,preCov true ws,pools,links) a b d

def readCompactBits (table : Nat → Nat) (start width : Nat) : Nat :=
  let i := start / 4096
  let j := start % 4096
  let low := table i >>> j
  let result := if j + width ≤ 4096 then low else low ||| (table (i+1) <<< (4096-j))
  result &&& ((1 <<< width)-1)

def compactIDsFromBits (bits width : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => (bits &&& ((1 <<< width)-1)) :: compactIDsFromBits (bits >>> width) width n

def samplesP21 : Nat → Bits
  | 0 => ~~~(0x6 : Bits)
  | 2 => 0x36
  | 4 => ~~~(0x30 : Bits)
  | _ => 0

def samplesQ21 : Nat → Bits
  | 0 => ~~~(0x1e : Bits)
  | 2 => 0x14
  | 4 => 0xa
  | _ => 0

def compactPerms21 : Array (List Nat) := ([[], [66], [32], [32, 66], [64, 66], [64]] : List (List Nat)).toArray

def compactDomains21 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords21 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount21 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath21 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive21 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords21 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs21 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords21 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords21 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket21 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP23 : Nat → Bits
  | 0 => 0xe2
  | 1 => ~~~(0x3a : Bits)
  | 2 => 0xd8
  | 4 => ~~~(0xc0 : Bits)
  | _ => 0

def samplesQ23 : Nat → Bits
  | 0 => 0x82
  | 1 => ~~~(0x3e : Bits)
  | 2 => 0x50
  | 4 => 0x2c
  | _ => 0

def compactPerms23 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains23 : Array (Sig × Nat) := ([(subcube 2 0, 4)] : List (Sig × Nat)).toArray

def compactWords23 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount23 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath23 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive23 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords23 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs23 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords23 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords23 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket23 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP27 : Nat → Bits
  | 0 => 0x3c
  | 1 => ~~~(0x2c : Bits)
  | 3 => 0x38
  | 4 => ~~~(0x10 : Bits)
  | _ => 0

def samplesQ27 : Nat → Bits
  | 0 => 0x30
  | 1 => ~~~(0x3e : Bits)
  | 3 => 0x38
  | 4 => 0xe
  | _ => 0

def compactPerms27 : Array (List Nat) := ([[], [48, 65]] : List (List Nat)).toArray

def compactDomains27 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords27 : Nat → Nat
  | 0 => 0xf
  | _ => 0

def compactCount27 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath27 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive27 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords27 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs27 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords27 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords27 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket27 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP31 : Nat → Bits
  | 0 => 0x8fc2
  | 1 => ~~~(0x984a : Bits)
  | 2 => 0x32a8
  | 3 => 0x3d70
  | 4 => ~~~(0x27b0 : Bits)
  | _ => 0

def samplesQ31 : Nat → Bits
  | 0 => 0x4f02
  | 1 => ~~~(0xb94e : Bits)
  | 2 => 0x20a8
  | 3 => 0x3940
  | 4 => 0x1044
  | _ => 0

def compactPerms31 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains31 : Array (Sig × Nat) := ([(subcube 8 0, 5), (subcube 0 8, 5), (subcube 1 0, 4), (subcube 4 0, 4), (subcube 2 8, 4)] : List (Sig × Nat)).toArray

def compactWords31 : Nat → Nat
  | 0 => 0xe47fbfc3fff05bca2404bd4153fc369bcbfe3fc5ebff1fe192503dffffc02202201401a9f
  | _ => 0

def compactCount31 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 3
  | 4 => 1
  | _ => 0

def compactPath31 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords31 (23 + 12*i) 12
  | 4 => let v := readCompactBits compactWords31 (224 + 12*i) 12
    (readCompactBits compactWords31 (212 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive31 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords31 (0 + 5*i) 5
  | 5 => readCompactBits compactWords31 (59 + 6*i) 6
  | 4 => readCompactBits compactWords31 (236 + 7*i) 7
  | _ => 0

def compactPoolIDs31 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords31 (17 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords31 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords31 (85 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords31 (77 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords31 (243 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords31 (243 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket31 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords31 (100 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords31 (102 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 4 => let d := readCompactBits compactWords31 (245 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits compactWords31 (247 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP55 : Nat → Bits
  | 0 => 0x23a
  | 1 => ~~~(0x4e : Bits)
  | 2 => 0x1f4
  | 4 => ~~~(0x1b2 : Bits)
  | 5 => 0x1ce
  | _ => 0

def samplesQ55 : Nat → Bits
  | 0 => 0x222
  | 1 => 0x330
  | 2 => 0x194
  | 4 => ~~~(0x3b6 : Bits)
  | 5 => 0xcc
  | _ => 0

def compactPerms55 : Array (List Nat) := ([[], [81, 64]] : List (List Nat)).toArray

def compactDomains55 : Array (Sig × Nat) := ([(subcube 2 0, 5)] : List (Sig × Nat)).toArray

def compactWords55 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount55 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath55 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive55 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords55 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs55 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords55 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords55 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket55 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP63 : Nat → Bits
  | 0 => 0x10bf8
  | 1 => ~~~(0x3652c : Bits)
  | 2 => 0xe346
  | 3 => 0x32da2
  | 4 => ~~~(0xabd2 : Bits)
  | 5 => 0x2f41c
  | _ => 0

def samplesQ63 : Nat → Bits
  | 0 => 0x10b90
  | 1 => ~~~(0x3f5ac : Bits)
  | 2 => 0xa046
  | 3 => 0x125a0
  | 4 => 0x25428
  | 5 => 0x2d00c
  | _ => 0

def compactPerms63 : Array (List Nat) := ([[], [64, 81], [50, 16, 84], [50, 80, 65]] : List (List Nat)).toArray

def compactDomains63 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 16 0, 7), (subcube 32 0, 7), (subcube 4 0, 6), (subcube 0 4, 6)] : List (Sig × Nat)).toArray

def compactWords63 : Nat → Nat
  | 0 => 0x3076223f
  | _ => 0

def compactCount63 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath63 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive63 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords63 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs63 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords63 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords63 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | _ => []

def compactBucket63 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP85 : Nat → Bits
  | 0 => 0xb6
  | 2 => ~~~(0x86 : Bits)
  | 4 => 0xca
  | 6 => ~~~(0x3a : Bits)
  | _ => 0

def samplesQ85 : Nat → Bits
  | 0 => 0x26
  | 2 => ~~~(0xe6 : Bits)
  | 4 => 0xc0
  | 6 => 0xc0
  | _ => 0

def compactPerms85 : Array (List Nat) := ([[], [32], [100], [100, 32]] : List (List Nat)).toArray

def compactDomains85 : Array (Sig × Nat) := ([(subcube 16 0, 4)] : List (Sig × Nat)).toArray

def compactWords85 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount85 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath85 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive85 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords85 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs85 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords85 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords85 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket85 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP87 : Nat → Bits
  | 0 => 0x1af2
  | 1 => 0x3b84
  | 2 => ~~~(0x2396 : Bits)
  | 4 => 0x251e
  | 6 => ~~~(0x187e : Bits)
  | _ => 0

def samplesQ87 : Nat → Bits
  | 0 => 0x1242
  | 1 => 0x3a80
  | 2 => ~~~(0x37d6 : Bits)
  | 4 => 0x514
  | 6 => 0x2580
  | _ => 0

def compactPerms87 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains87 : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 64 0, 5), (subcube 0 2, 5), (subcube 1 0, 4), (subcube 4 0, 4), (subcube 16 2, 4)] : List (Sig × Nat)).toArray

def compactWords87 : Nat → Nat
  | 0 => 0x39627e522017650397e8058231d1f
  | _ => 0

def compactCount87 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 1
  | _ => 0

def compactPath87 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords87 (29 + 12*i) 12
  | 4 => let v := readCompactBits compactWords87 (83 + 12*i) 12
    (readCompactBits compactWords87 (71 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive87 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords87 (0 + 5*i) 5
  | 5 => readCompactBits compactWords87 (41 + 6*i) 6
  | 4 => readCompactBits compactWords87 (95 + 7*i) 7
  | _ => 0

def compactPoolIDs87 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords87 (23 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords87 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords87 (55 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords87 (47 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords87 (102 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords87 (102 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket87 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords87 (61 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords87 (62 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | 4 => let d := readCompactBits compactWords87 (104 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords87 (105 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP91 : Nat → Bits
  | 0 => ~~~(0x5250 : Bits)
  | 1 => 0x5538
  | 3 => 0xfc0
  | 4 => ~~~(0x252e : Bits)
  | 6 => 0x327e
  | _ => 0

def samplesQ91 : Nat → Bits
  | 0 => ~~~(0x72da : Bits)
  | 1 => 0x3428
  | 3 => 0x4b80
  | 4 => 0x42d0
  | 6 => 0x305a
  | _ => 0

def compactPerms91 : Array (List Nat) := ([[], [49, 100], [16, 99], [16, 97, 99, 100], [48, 49, 67, 100], [48, 65], [64, 49, 99, 100], [64, 97], [96, 67], [96, 65, 67, 100]] : List (List Nat)).toArray

def compactDomains91 : Array (Sig × Nat) := ([(subcube 1 0, 4), (subcube 2 0, 4), (subcube 8 0, 4), (subcube 16 0, 4), (subcube 64 0, 4)] : List (Sig × Nat)).toArray

def compactWords91 : Nat → Nat
  | 0 => 0xff0ff0339b38c447f6452ff0ff082be51a00d04ffc1fe05749e23196566ff03544885fe0bd68f93a1ffe006fffd08900688d11f
  | _ => 0

def compactCount91 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 2
  | 4 => 1
  | _ => 0

def compactPath91 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords91 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords91 (279 + 12*i) 12
    (readCompactBits compactWords91 (267 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive91 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords91 (0 + 5*i) 5
  | 5 => readCompactBits compactWords91 (50 + 6*i) 6
  | 4 => readCompactBits compactWords91 (291 + 7*i) 7
  | _ => 0

def compactPoolIDs91 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords91 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords91 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords91 (64 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords91 (62 + 2*(v &&& 1)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords91 (298 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords91 (298 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket91 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords91 (68 + 1*(i % 4)) 1
    let off := ((i/4 + d) % 15)
    let v := readCompactBits compactWords91 (72 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords91 (300 + 2*(i % 2)) 2
    let off := ((i/2 + d) % 9)
    let v := readCompactBits compactWords91 (304 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP95 : Nat → Bits
  | 0 => 0x504454ee89b10
  | 1 => 0xa8b6f4d0f4a4
  | 2 => ~~~(0x1ede7c98ad5fc : Bits)
  | 3 => 0x419bc3ae24c8
  | 4 => 0x3ba2f091f4134
  | 6 => ~~~(0x1ba9f46fc2fb4 : Bits)
  | _ => 0

def samplesQ95 : Nat → Bits
  | 0 => 0x200546808810
  | 1 => 0x38e4f450b404
  | 2 => 0x5a1020742202
  | 3 => 0xc31b03ac00c0
  | 4 => 0x2810a090b4120
  | 6 => ~~~(0x3ff1f67fcaff6 : Bits)
  | _ => 0

def compactPerms95 : Array (List Nat) := ([[], [32], [49, 100], [49, 32, 100]] : List (List Nat)).toArray

def compactDomains95 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 4 0, 7), (subcube 8 0, 7), (subcube 16 0, 7), (subcube 64 0, 7), (subcube 0 2, 6), (subcube 0 8, 6), (subcube 10 0, 5), (subcube 18 0, 5), (subcube 72 0, 5), (subcube 2 8, 5), (subcube 16 2, 5), (subcube 64 8, 5), (subcube 3 0, 4), (subcube 5 0, 4), (subcube 6 0, 4), (subcube 9 0, 4), (subcube 17 0, 4), (subcube 20 0, 4), (subcube 65 0, 4), (subcube 68 0, 4), (subcube 24 2, 4)] : List (Sig × Nat)).toArray

def compactWords95 : Nat → Nat
  | 0 => 0x9058af2ce4c2749e8299a99d9a6c7e4b907674515674d5f72fdead3b2d5a8b4c5d2662910e5caa3054063d1e9c01434ff01ea14a5f83276916fce2f6bff803385fe03fc07f80be101a197027f80ff01fe0119ab1139240ad42267b995c253fe03fc017a330c5a07de90e50fff010085645806890c011bc048bc20604095573eb34d2951451050d2faaf14dcececc34aeaa489ca9268d07d864c59246640e3242f619800102802ec82c7661c1820c040172450c9700363b28ac434824d462f0814e005c1c515247018704180805c4891c286429c6448a0706180ae044898c046402e221cd18065a505061c30132017121e48c93041422e1eb8c071e59706123c0126810d8260141308c6c3830c047805c3cdae244c21b0a3c38324180935c1841b5c38318200430e480c3860a7060200b874804382840e0cc8c001977fdfffdef7ffffdfffdff7ffdfffffffffff5fffdfffffffdfdfccc099811301e60a48548ca9115662a4c5498a9111261acc249845214a32142428087310a6214c4284653042228cc5198490a8c8808804803fe0ff03acf417fe08819603c986b5ff030eca85fe0ff0511fc9ade1a77d54721c8d77011cfddc430e44e6f4770038c46080a4ceaf86b020cb6f63f01a5e6e9314e31183cd0332c30806e597418a438cc1e6f5803c5c290e316d9a5e4060ffffffffffffd21519109101108d0090070b1a23f
  | 1 => 0xf499fe0002839d05fe0104b718f7fe0050f52eafd2d80ab4e489fe0012949e777485208b2408ce4b8eea92ef968c485e16ece8c61ec4ce91fe012017fe00fc7fd446d02e3c67866bca9b242bbc0bfe01445b6ed54859d28e8a6f72adfe01b66866cf7833fe01fe0026a73ae6fccaba5dfe01e0cdfe01fe01121e3e9f9c43cc0f963f3802da0c1e5654010cf0ae362692d0146c87e8bf744edc1a7e659a543ec8a8db9480d0e8367266dc3e9dfe011e9754054607ee10c8d232d77ce5fe01fe01fe00fa6ca0fca026b6a5fe01c4d0b8de20f244bd1d079afedc3bfe0158e2f00106262001b231268811210000818010000238020b0b1a8a8a8a8a9a0a1989899909189808179707169615e282a19101011090000045000100002545450901011848022e0100230182c500cfef76ff773e7f7bbf4ff773bddefadf6fd7cfe7f7df77eafd7ef54ff5faf9fcfedf7e9fcfd69c47ce236711b380690b04e256712b38159c4ace256712838959c01ce50a72b5215a9ca5ce6267081214088a0ce5027281111c9cae4644a42a739529ca8ce416703d38989cb98a80998a80398880598480998480398090a98a80898880498280498090a90a80890a8048c880488a80888a80288880880880483546ddff8061a5cb182a47f806b035eebfc020977ebd0f0fcc6a0d4ff017d2a9f1ff80d3be789506982827bcd7d6d518dab64f3ba4dfcd
  | 2 => 0x28de93fe0b05c7a3fc064f253e24bfc1fe0ff07f828cbfe0ff029bbfc1fe0ff07f83fc1fe0f724d1abd5042ac9ff81805619d795755d51f61c4a429a0a282da019c098a8089ca98880488a8088048888088041013
  | _ => 0

def compactCount95 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 7
  | 7 => 26
  | 6 => 33
  | 5 => 5
  | _ => 0

def compactPath95 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords95 (30 + 12*i) 12
  | 7 => let v := readCompactBits compactWords95 (973 + 15*i) 15
    (readCompactBits compactWords95 (913 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords95 (4949 + 17*i) 17
    (readCompactBits compactWords95 (4541 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords95 (8353 + 14*i) 14
    (readCompactBits compactWords95 (8209 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive95 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords95 (0 + 6*i) 6
  | 8 => readCompactBits compactWords95 (114 + 7*i) 7
  | 7 => readCompactBits compactWords95 (1363 + 8*i) 8
  | 6 => readCompactBits compactWords95 (5510 + 9*i) 9
  | 5 => readCompactBits compactWords95 (8423 + 10*i) 10
  | _ => 0

def compactPoolIDs95 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords95 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords95 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 8 => let v := readCompactBits compactWords95 (548 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords95 (163 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords95 (2789 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords95 (1571 + 7*(v &&& 255)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords95 (5983 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits compactWords95 (5807 + 8*(v &&& 31)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords95 (8474 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords95 (8473 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket95 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords95 (625 + 3*(i % 5)) 3
    let off := ((i/5 + d) % 21)
    let v := readCompactBits compactWords95 (640 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits compactWords95 (3101 + 5*(i % 24)) 5
    let off := ((i/24 + d) % 88)
    let v := readCompactBits compactWords95 (3221 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 6 => let d := readCompactBits compactWords95 (6247 + 6*(i % 31)) 6
    let off := ((i/31 + d) % 111)
    let v := readCompactBits compactWords95 (6433 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 5 => let d := readCompactBits compactWords95 (8484 + 2*(i % 5)) 2
    let off := ((i/5 + d) % 29)
    let v := readCompactBits compactWords95 (8494 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []

def samplesP107 : Nat → Bits
  | 0 => 0x1f80
  | 1 => 0x1f10
  | 3 => ~~~(0x7d2 : Bits)
  | 5 => 0x4fa
  | 6 => ~~~(0x1cb8 : Bits)
  | _ => 0

def samplesQ107 : Nat → Bits
  | 0 => 0x1e00
  | 1 => 0x1700
  | 3 => 0x80c
  | 5 => 0xb2
  | 6 => ~~~(0x1ebe : Bits)
  | _ => 0

def compactPerms107 : Array (List Nat) := ([[], [16, 99]] : List (List Nat)).toArray

def compactDomains107 : Array (Sig × Nat) := ([(subcube 1 0, 5), (subcube 2 0, 5), (subcube 8 0, 5), (subcube 64 0, 5)] : List (Sig × Nat)).toArray

def compactWords107 : Nat → Nat
  | 0 => 0x41b1f
  | _ => 0

def compactCount107 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath107 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive107 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords107 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs107 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords107 (13 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords107 (5 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket107 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP111 : Nat → Bits
  | 0 => 0x11dd409ebdc20
  | 1 => 0x2adf666880
  | 2 => ~~~(0x4c7fc18475ffc : Bits)
  | 3 => 0x3c02b38c93154
  | 5 => 0x68751e01787c8
  | 6 => ~~~(0x39d7be9eba5c0 : Bits)
  | _ => 0

def samplesQ111 : Nat → Bits
  | 0 => 0x5513009c35000
  | 1 => 0x112c9f266800
  | 2 => 0x2aa43e438a002
  | 3 => 0x4c01220c91050
  | 5 => 0x2a4140108588
  | 6 => ~~~(0x7fff3edfbf5da : Bits)
  | _ => 0

def compactPerms111 : Array (List Nat) := ([[], [33, 48, 101]] : List (List Nat)).toArray

def compactDomains111 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 4 0, 7), (subcube 8 0, 7), (subcube 32 0, 7), (subcube 64 0, 7), (subcube 0 2, 6), (subcube 0 4, 6), (subcube 3 0, 5), (subcube 5 0, 5), (subcube 34 0, 5), (subcube 1 4, 5), (subcube 8 2, 5), (subcube 32 2, 5), (subcube 64 4, 5), (subcube 9 0, 4), (subcube 33 0, 4), (subcube 72 0, 4), (subcube 7 0, 4), (subcube 40 2, 4), (subcube 42 0, 4), (subcube 65 4, 4), (subcube 69 0, 4)] : List (Sig × Nat)).toArray

def compactWords111 : Nat → Nat
  | 0 => 0x3820c05995005c80e325c0156a1419c624ccaf265654765158863914c146068185640a286020073016c24028c3629538c1cb22ad64451c60ab92721ac51c35802767191d3114b8e1668307146430a20d4f0d081401c5c4ca9120c5ab002b8a182ac98b560b89951a40e850871915061c1060200aae2040e0b3214a900e0c3015c541160864110911869516b8a130a34d3b0e0830100b880f2068c03264c2151e507c73c6020036b89c666352345e0971b2c658998c9198d68bcdb12a2ca131f188196874584066d89426146a40e0830136007ae1e6c818084d70f200428704509980e27feffffbffef7e6ffafe7e7efffffbffff7f7fafffeffaeffffffdfefeffafffeffff6606cc0c9815216a02dcc1f84b330e242cc25884b330da22b405490a9195612a425480ab315262a4c54888b30d261948528c87110a22140439885310a620464c44485464444424404403402ff01d47fc1fe0d61004e88bfe0091ff8302abc86007f83ad9eae797ff8174e98da84de045e1d0adb5ff802244206e1fce94d4ec7ea9692e85e67e498318198003388c1068a4ce2ee6d0a238780cde76d131768b851982023b58689773d5cbe0b443e2ede024cba8dc28ce230600d670d5938521c460bc1bce18b19483db81a6b2eb30cc1de92e9600710ceb1690ccb4060ffffefffbffffffffffd21519311111111109101100d0890090070b1a23f
  | 1 => 0x48f89e23826ccc48f11c2348590920e218822000000c0226088e0d1c260890901a8c2718e827483865422a1a080b22261b14652298f20ab82a08000c022a002a2c0026e826261e8ee826262a2a2a32074420083320b91a162a260a0e04260a260a0a0c020e040c033ff3f3f7b3df5faf937bf773f9bce9fdfa7fbed7efa7feb9ff9fedeefb5fafdeadbefa7fafdbefa7f3fbec138d99c634858a02c539579c6b4e32a428b38959c0848522428521689c6fce07e71bf382490b24059272b511139cc74853a028121408ca0ce502728111268cb34059a72b9215c8cae4057672b9394d9c398a8099888079868099828c998090a98a80898880698680890a8c890a88890a80890a8068ca8088c88068c880484a88884a80880a8c880a84880a808808806db067d427a2ff00467b71c6e304979d49ffc07f80ff01fe03fc052846737fe003ce84192b197ab3b97bf3f801012df8e1bba3a7353e994daae06f929fe02f52c918d323e20f79cbb178d67627e949330ee92a9c353d0858999525100e8e4882ff01fe01fd5873eca2caa4d05e820a565a62c8282cf42601636d0698ff80ff01fe00887ff803c0f2802ec0b0a0ba76886b2c00681398410608410410e11402c231f8cf667823b19ccae1c6ac3365890bcc581ab4d552a144eca51d1ae8693eb1de4dd464d2bb14509b443c1bd8b343fa12606480cc0010a85005d9058e0c
  | 2 => 0x259058ff87f83107f87f8129ff8014acd3b69b3e459d2e54402aad6b9f338ef1bc6e1f8e5a05b401a428485890b5214a42a42a12a02232a62201a32a02201a02e61a02202e60a32202a62201a02a322018ba23f50e6ee09d269bd427fe03c53ea43ff00bc45621568d57592712d0a1f8819129ec48d19749c96fd849ac21c0bff016d21b20e09aff01d6f9b5a0dafd2145ccbfc0159dff013917fc07f805c725ea529717835481a816f933faa184bfe02f59fd3d5b6aecaffc06bbf7d484d29290ff808b70b65bfc0108eff00dc01107b697ff01fe018cff5b00a21fe03e83d39eff005c655835d0c9e02cc575e5e3470d5a61aa0201c02020e00078054c10000a306695129e13c6714c3929165e03c1760ed5b4ad2564a4149a614a0941292304648
  | _ => 0

def compactCount111 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 11
  | 7 => 34
  | 6 => 38
  | 5 => 7
  | _ => 0

def compactPath111 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords111 (30 + 12*i) 12
  | 7 => let v := readCompactBits compactWords111 (1496 + 15*i) 15
    (readCompactBits compactWords111 (1400 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords111 (6373 + 17*i) 17
    (readCompactBits compactWords111 (5869 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords111 (10123 + 15*i) 15
    (readCompactBits compactWords111 (9871 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive111 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords111 (0 + 6*i) 6
  | 8 => readCompactBits compactWords111 (162 + 7*i) 7
  | 7 => readCompactBits compactWords111 (2006 + 8*i) 8
  | 6 => readCompactBits compactWords111 (7019 + 9*i) 9
  | 5 => readCompactBits compactWords111 (10228 + 10*i) 10
  | _ => 0

def compactPoolIDs111 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords111 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords111 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 8 => let v := readCompactBits compactWords111 (889 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords111 (239 + 5*(v &&& 255)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords111 (4161 + 13*i) 13
    let n := v >>> 9
    let bits := readCompactBits compactWords111 (2278 + 7*(v &&& 511)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords111 (8025 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords111 (7361 + 8*(v &&& 127)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords111 (10301 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords111 (10298 + 3*(v &&& 1)) (3*n)
    compactIDsFromBits bits 3 n
  | _ => []

def compactBucket111 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords111 (1021 + 4*(i % 7)) 4
    let off := ((i/7 + d) % 27)
    let v := readCompactBits compactWords111 (1049 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits compactWords111 (4603 + 6*(i % 21)) 6
    let off := ((i/21 + d) % 76)
    let v := readCompactBits compactWords111 (4729 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 6 => let d := readCompactBits compactWords111 (8443 + 6*(i % 23)) 6
    let off := ((i/23 + d) % 86)
    let v := readCompactBits compactWords111 (8581 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 5 => let d := readCompactBits compactWords111 (10315 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 16)
    let v := readCompactBits compactWords111 (10323 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP119 : Nat → Bits
  | 0 => 0x3c8440172071b3ec90
  | 1 => 0x10318268bbb5160324
  | 2 => ~~~(0x3a8d937fe243373fbc : Bits)
  | 4 => 0x3460ea8e6466c2074
  | 5 => 0xac991545e0ba91b08
  | 6 => ~~~(0x47cefc3e35a9eb74 : Bits)
  | _ => 0

def samplesQ119 : Nat → Bits
  | 0 => 0x48002122021108c10
  | 1 => 0x1001a23bb1b5120204
  | 2 => 0x202101a4191c884002
  | 4 => 0x4e14404642642060
  | 5 => 0xa0a01c40e0aa90108
  | 6 => ~~~(0x3eeb4bf63f3fb9ef7e : Bits)
  | _ => 0

def compactPerms119 : Array (List Nat) := ([[], [98, 84]] : List (List Nat)).toArray

def compactDomains119 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 16 0, 7), (subcube 32 0, 7), (subcube 4 0, 6), (subcube 64 0, 6), (subcube 0 2, 6), (subcube 6 0, 5), (subcube 18 0, 5), (subcube 20 0, 5), (subcube 34 0, 5), (subcube 66 0, 5), (subcube 96 0, 5), (subcube 16 2, 5), (subcube 32 2, 5), (subcube 3 0, 4), (subcube 5 0, 4), (subcube 17 0, 4), (subcube 33 0, 4), (subcube 36 0, 4), (subcube 65 0, 4), (subcube 80 0, 4), (subcube 22 0, 4), (subcube 48 2, 4), (subcube 50 0, 4), (subcube 98 0, 4)] : List (Sig × Nat)).toArray

def compactWords119 : Nat → Nat
  | 0 => 0xfdff5fffdffffefeffdffefefefefefefefe7efeda61da615a603661b661b261b660b260b6603660326002618260826002603a22be60ea22ea62ea60ea602a32ae22aa22aa22ae62aa62aa322e61aa61ae602a606442e262e232626262602442a242a232a262a2621c429a429a329c229a229e629c629a629a321a221e621a621a621a219e611a615262d26252604c42ca42ca22ca62ca224a62144292429432923296229422922292229412921292029662946292629262923216221222122212121662126212621621922192019661926192619260c222c2220a228e610c228a2288228e220a220e218a218a018e610861622621c22c11401400a32222a22221a01a01200822bb1c2e677158a5ff81606e9285e83f038cea093581cf8bfe07cc3fe036b08cb163eaccbba44cd938c983ff81fe03c2bfe06040728b511fe07f81c0b8827527d20a0a0b955d397233118f9adf8c76b0ea388b476e69455a3b02ba110009104c0e136c5e8a71d8460833de6c9a28c460819b4e8e5293016013abb0a730403da74e21446081891f37a74ca3384c0e8b7a690a3b04c0eedba4ac0eb690628c860f629db402594600bb4d219607374731461374fb4808728ec2307bcd8090ce17db700159462393aee34060ddcd0f78607fffffffffffffffffffffffff7ffd845445045464c44444c434434234038224228024028014014018393f
  | 1 => 0xcd0008141820c040360e5dd833ae02cf0e043002e4c28300180906c682090a304956b44b040a24a830c040162618280025cb172214b9119448b52a1468068108850a441840c04034224429b1a504950a448b806740342e5c9910a103012200bb4227491b065c89202142182e446840025a05061808900d0890221048b0a0c1001c180896afda8909387106a04283043820012683040a302096810a05060830112002349ee8009684c9830b3c10602740096814810186c8052a40289201080568008340a1001008140340a703100c2c80028102830b4410602008342014a05204018228180b4365c8033ae84842075a10260c04f2011b3a260ce8068185053a0830100d08103a489833a401120c049856809d1c201083a04704806840011741048238141829e1809c0041a10384448220442836818089383c31b0e04e9c0004cb53ed0b1fa0700013259a353ad430f1e0428e06086800cd5a1e38d430f4cd0fb50074e063c7c7b43a71a803c3c32646d0f9f74003236838f1f3d40e002ed071f74003176834f1f740030d2ed11806a05d111a8cb9ca2d400f3e74e0e1a783343e007230cd0f5fdfdfffdfffffffffdfffdbdedfdf7fdefddfdedffffdfffddffff7dfffdfffffdffbdfdffffffbdfdffffffbffffdffffffbffdfffdffbdfffdfd7dffffffddffddffffffffffdfffffdffffff5fffffdffffdfffdffdfffdffd
  | 2 => 0x540a7deef7cdafc88f21f76b07a867fc01616ffc02cce0165ffc03fc03fc03fc03fc025487fc03fc009ddbd41e797ffc03fc028609b8973656769948f1093d64a3fc037b1b266cb05311ef140ffc0369709617e146be878406c03c86d93188914ffc03fc0025582c0500728d20104a4c4181cc0e4036e38c29b1401122031c02800040654c700301810100100403d0150400c81000480820458a56a8b8a0ce8059ed27739d166f49ae263497d25b595a24e6920a466901a3a98c5a2b789122078656148831e05380a5f977c9deb67959df2775dd657461c997009be26f1db566bdda83694da28668d972655d8e462958575f8d7b85cd96d75999608561154a529944c4e093624d1130949d921b4589142448d0f2435109441550053ed0f723d54f0939c8e53389cdb33618d263328c223020b852ce4aa5295c9e825a88c521e07f61e6470a198c63b162050911ec3c80d202c809201c904f007700278b021800c1254d030418080182428704003011850d050808e030c040161270a8236180871618d81081401a08141820c0401a2050d00193838918267070c1e786023048521444d0193c3b52f01b379cf43090e7100418301820c04037121e03713383860a0048602108373854989388098718109840adc19308710050665b82021a700324c98518e099b7258202385c296021801726249971c6c11c0a08086344c610244
  | 3 => 0x1608931600931511131510d31500d31500931200931110d31100d31100930d00930a11530500930311130310d30111130011519510d19500d19310d19111119100d19100911711111600911519111511111500d11500911500511200911100d11100911100510d00d10d00910d00501500900d00900d0043090041150044a0da6a8540bfc002ee7fc03fc03fc03fc015f2ffc02c1354060875360e6e6887da3fc0015e6ae97330e7551662251e9ca538182cf59801bc87819e3fc03fc026f3ddcf7a337e5ff3a661e3ffc033c8bfc00a2dfb6189d96caece5079a24c637fc00fc37fc03fc03d0a7e499dc715d12255cb36d8a621083674702389a2ddebdcf150ab6d675c68e15b5a4b7282e349c84b950fffc0329605447787e46cd364f251c66d7fc03a9bcc1d1085c919b0f4fd6e9b9c5fd8e8417fc029db0f001b811d25bc57909183233e280adf3894b84c4966bfc015ea7fc02c0aab9204b664da736b33757fc02774bfc03fc03fc03fc03fc00b9562e1dc9435ac625faa44b62b8bc295c32e12b04f841683603c763fc0351aba977fc03fc03fc0376a0f59d664865d458917ad1de915103884ee2ff00ed59bb7ee3c0da871f4cdd49925cd609ccd86c8d84d07718c3d5dda7739d0fb64720cb02115f243a28aead0207792d2b7508bd88cec8ad04b151674cd2a525842695158679c29e013a7ec14931935eec213dcb7
  | 4 => 0x88af9395f2323e4e3359cad539956722ace02d10a59314da32334e3669cc63381367226ce34d9c0891951672a24e5459c0c938d927317ce42f9c4bd1957a71af4e61c8ca3b39a4a72494e26e9c6dd381ba7325ce22910a53314a2728a4648e8cb1d3963a7121444439c41f3143a72874e4848cb0a1161272c2444849c8a7381a271344e6239c8a33905a428b4c5169ca8d2151a22a34e5629c4c53818a73304e2609c2c138182733c4e45c9c4361946a328dce41b9c6373816271ac4e2589c0b13982422844450888b220964212c84e4909c6d9389b270364e6499c09338d267013ce17680aed315da72894851280a273144a6289ce5129ca251904e71c64458c80b193963271a0ce5401ca812150622a0445419ca833950672a00e5408c88338dca02b94e5728c8e53903232864050c9ca193901a3283445079ca0d3941a3203444068870d3961a32434e43e8ca7f394fa729fce43e9c87738c6670414e55a9c6b538866718cce0199c00138c0270008e67488ae9395d47308c451088a23395c272854650a9ca09194142282445051ca093941221824e2829ca0539731511331500f31500b31100f31100b30d11730d11330d00b30900f30900730519330111730111311511311500b11100b11100710d00b10d00631500e31500a21710e21600a21510e21500e21500a19500a11500e11500a11500609500931711131710d3
  | 5 => 0x1f83f07e4f89ea3bc6a0d5199322620c41883165c0b89682d05a4b09592a252c9a90c1d03a4720c01822e05c8b1152290408790e418c2682202004800093dd1c40c041819ac4c7008180400e60c4c720c0c0c18040c1401a41418040018045c00105e700000148000105c080c5c01b05c145c0c5da410005c000c1804140014001400001000140414101401a014100004000000004e140e700000d93c000c1414141671b4080000001009a8442689a00810013c0c141414180404000000049a748e7498048c7c988e767000e88e167074007c0044005c347044d4e844508c5c4434008c408c2c027f3f9fcff79779fef67b7b9feeef7dbf5def3f3f9fdbfcfeb9fcff773fd7cfebf3f9fcffcfb7dbdde7f779fede7fb79fcfe7f779fddeefd7bbcffaf3f9fcfeef7e9fdefcfb7bbf9f6f3f9febe7fb7bbddf6fbb9feee7f3fbdcfef73ff5eeef7afddcfef77e9fdeefb7e9fdeef7dbeddeef7fabbdeefd3fef77bb59fcfcfe7f7bbf4fefd3fdf5f7f5bbbdfaff5bbdddeef7ebbdeef7d3f9fd7ebfafddeee7f9f8fe7f5f3ffd5efe77bf9feaf77bfb7eafd7efb7ebe53fdbcff6f3f9fcfe7f77bf4fefb7dbeff2f975be4f7f37d9efe7f37dbefd6fbf4fe7f3f9fcfa7f2fb7d3d9c1153922a703f4e3329c24338c867340445809c04b3815e701c4457a9c03d1947e720fce0948cb2938e527027ce42a8ca551162272c44e07c
  | 6 => 0x57f803fc01a16e057288d0ffc016e2fff003325bfc016b453319a91415623760929292bce300175f024235c4872d88a31107e71e59550626f50af17d7f8028801ccfeff00095f7fc01c02d55c4ff803fc01fe00f49d7f803fc000942ff001d2c1f402e47a735a9cc829a7cdd1c92bb41d4bddc4a756ddbcd845f21f1fe00ff00770e0066ec2d5fa4312de3fc01fe0013c47f8015589fe004c4ca4c27fc01fe004e7b544901018e0158e4c1a46bfc001c76ff0066333003a53810d393f3002931408080002c3140201294842030208987150628625020020504654090210082020ce00006080101101011e24182060000b020c2001c00402160058c000009e001810d00140850000011000cb000404200140878900001060e1c103000800b28140000e08002282898000387101566a8550aa74e699520a434628c518a3146e80500a033ea744e99c732e58ca89512a2544aa9312624c498931266484919112224448990120a384738b512a1cc3185308210c188310620c41883304dfcbf07e4f85ed3ca774ea1d4ba3710e21c4b826e0dc1b83716d4d61ac3586b0d61ac3586b0d65a83506a2d25a0341670ce598331652c8190320640c858c319622c2580afb5c8b0160ab8570ae558aa8552a8150a98530a614c298532a4544a824e29a92ca504a094128a4849092520a394608c514a204448410821042084504208412804fc
  | 7 => 0x18a14eb23ed1f2905e1c088e127fc01fe00324e9e1d036e7e02137c2a70aeb8b7ba836a0f02bf4d1c3fe004b208483e32d0f37ba197c0b91dd925aedd33d8a8c441c1811fff003926ffc01d405a4612e2a7fc0053471a5e5aa6a08889c47b28b390f088147ead2b0d83438a6c0a0daff00305513d8ffe00ff000b0d405f7fe00ff0019bc1487b1cd4a26ddb843fc012058f6307f801788dfe007a259accada51fe002d2eff801092aea518d490a067fc009665b240c256ab9944b4949b26b2ff118c72f13c3eff8012db9084d9c5ec29bd40c76b84e979083fdec6f5077b16fc7bb3c5453cc5725451d57c0254e3bff004425ede0b5923ff0049ae3a1417c53ff0054b2f82892eefff000ac1ffc00d67ea8422bb7bfc0070e710a69bb65d6eb704c818c8b102b1631cceb5690f33e215f30ea02a31f1b59a29fe00b36871dc6dad29c0660aeff80168860493ae891b837fc01cf15ed38491e62c111c5a69800baee7673fe0013b3f35d390c528eb920122addd1d3d0fc5398cc83bb512a4183d92ff80342a6d765c15d7295c78cd90acf648518978504e8f7d337678f87147131da846e40808a45996b5324724139c949cf48f39df17288e3bab60fa5e929f026a24e828a7c8a9945cc8366e887c4a2c8da3209fca5f061a89110006c602b1a4f7deb09f0dd5a713ddf6075a6d3088c321f3ad188242c2819f2cffc0028750b9
  | 8 => 0x95e57943f1dc3f3e4f97c4f97c4f93e5e9ea5e9ea4f97a5f17a128caf28329a00ce81388caea8036a043e81b080a0a22ac80a0232a480a3232a088a2232079ca1a7286a0a1a821da0a9e811ba0a668040a0656802fa0046802ba008e8017a04d232b4a062a328ba0efa819fa041282e70222a00c72a01a00c42a32621c32a22a01422e61201c22a02a01422a01a00a73442a01a72e22201272e22200a72e21a01272e21a00a72a62221a72a61a01272a21a01272a21a00a72a01a01272a01a00a72661a01272261a01271422a00a32a01a00a22e22200a22a32222222a22200a22a02a01222a01a01222a01a00a22201a01221a01a01221a01a00a02e62201202a21a013e4323e800003c714290c92168dad84895ee5ff2c09fe00afa4409fffc0110b9ff007c5b39ac7c8f300c3c9bbbfc01fe00ff007f803fc018627ff004e08d5a5dbc22ff004842d9d1c9e914f61f89e2ab07e8699d2a3fda9d6998f6f2d43d48d039285d08ff001cccd56a3fe007860d6603fc00dcaa8130f22846c27fe009433da5cbfc01fe00919e7f8031a3c795eff000705acc3eaf8bf89dec377ce7fc407b70d54c6d3d5caf2ddbc317aacfe0274c811adc8c854ab200d69b7ad5053907fc736ccb0e757de6b853278b960497d5daf424e7e94a4203014b4e6448935905f959bbf306db6e293c35380106b61cd19642c5c7f579f42da22874d07d4
  | 9 => 0x68e7295ff8028515a68805d930ff00a079751d68cff010a83fc07f804015fe01b0965c59b4e66f3fc04029c28e3e5eaa4ab22f955e2e8200ccb54e3a78c5d86ff80f029fe017411bb6ff01fe000876f007c4c4b0e842ff80323f8d10fa5d209ff00eb07fc0092c0b81b6dcac269a1880e3cca24b77914467a4d1f926f030727bef4c03171b3f1f48bb7616d2d1c31aa664129c38ff018ebc79dff80ff007cfc6443215eb20039d2301d40845c62b8b15844310011020408102040810204084c183240810222040810204081020408102040810204854da6130e000d4000078753c7d1df276d5b56d6b5cd6b5e96b5e96b5f16e5b
  | _ => 0

def compactCount119 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 17
  | 7 => 111
  | 6 => 198
  | 5 => 38
  | _ => 0

def compactPath119 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords119 (20 + 12*i) 12
  | 7 => let v := readCompactBits compactWords119 (2159 + 16*i) 16
    (readCompactBits compactWords119 (1991 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords119 (17182 + 19*i) 19
    (readCompactBits compactWords119 (15382 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords119 (35975 + 18*i) 18
    (readCompactBits compactWords119 (34787 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive119 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords119 (0 + 6*i) 6
  | 8 => readCompactBits compactWords119 (224 + 7*i) 7
  | 7 => readCompactBits compactWords119 (3935 + 8*i) 8
  | 6 => readCompactBits compactWords119 (20944 + 9*i) 9
  | 5 => readCompactBits compactWords119 (36659 + 10*i) 10
  | _ => 0

def compactPoolIDs119 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords119 (14 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords119 (6 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 8 => let v := readCompactBits compactWords119 (1253 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords119 (343 + 5*(v &&& 255)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords119 (9506 + 14*i) 14
    let n := v >>> 10
    let bits := readCompactBits compactWords119 (4823 + 7*(v &&& 1023)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords119 (24094 + 11*i) 11
    let n := v >>> 8
    let bits := readCompactBits compactWords119 (22726 + 8*(v &&& 255)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords119 (37111 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits compactWords119 (37039 + 9*(v &&& 15)) (9*n)
    compactIDsFromBits bits 9 n
  | _ => []

def compactBucket119 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords119 (1457 + 3*(i % 10)) 3
    let off := ((i/10 + d) % 36)
    let v := readCompactBits compactWords119 (1487 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 7 => let d := readCompactBits compactWords119 (11060 + 6*(i % 67)) 6
    let off := ((i/67 + d) % 245)
    let v := readCompactBits compactWords119 (11462 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 6 => let d := readCompactBits compactWords119 (26272 + 7*(i % 126)) 7
    let off := ((i/126 + d) % 449)
    let v := readCompactBits compactWords119 (27154 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 5 => let d := readCompactBits compactWords119 (37377 + 5*(i % 24)) 5
    let off := ((i/24 + d) % 88)
    let v := readCompactBits compactWords119 (37497 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | _ => []

def grid21 : CompactGrid := (21, 3, samplesP21, samplesQ21)

def tab21 : CompactTable := (compactCount21, compactPath21, compactLive21, compactPoolIDs21, compactBucket21)

def check21 (k : Nat) := compactNode grid21 tab21 compactDomains21 compactPerms21 k

def grid23 : CompactGrid := (23, 4, samplesP23, samplesQ23)

def tab23 : CompactTable := (compactCount23, compactPath23, compactLive23, compactPoolIDs23, compactBucket23)

def check23 (k : Nat) := compactNode grid23 tab23 compactDomains23 compactPerms23 k

def grid27 : CompactGrid := (27, 3, samplesP27, samplesQ27)

def tab27 : CompactTable := (compactCount27, compactPath27, compactLive27, compactPoolIDs27, compactBucket27)

def check27 (k : Nat) := compactNode grid27 tab27 compactDomains27 compactPerms27 k

def grid31 : CompactGrid := (31, 6, samplesP31, samplesQ31)

def tab31 : CompactTable := (compactCount31, compactPath31, compactLive31, compactPoolIDs31, compactBucket31)

def check31 (k : Nat) := compactNode grid31 tab31 compactDomains31 compactPerms31 k

def grid55 : CompactGrid := (55, 5, samplesP55, samplesQ55)

def tab55 : CompactTable := (compactCount55, compactPath55, compactLive55, compactPoolIDs55, compactBucket55)

def check55 (k : Nat) := compactNode grid55 tab55 compactDomains55 compactPerms55 k

def grid63 : CompactGrid := (63, 8, samplesP63, samplesQ63)

def tab63 : CompactTable := (compactCount63, compactPath63, compactLive63, compactPoolIDs63, compactBucket63)

def check63 (k : Nat) := compactNode grid63 tab63 compactDomains63 compactPerms63 k

def grid85 : CompactGrid := (85, 4, samplesP85, samplesQ85)

def tab85 : CompactTable := (compactCount85, compactPath85, compactLive85, compactPoolIDs85, compactBucket85)

def check85 (k : Nat) := compactNode grid85 tab85 compactDomains85 compactPerms85 k

def grid87 : CompactGrid := (87, 6, samplesP87, samplesQ87)

def tab87 : CompactTable := (compactCount87, compactPath87, compactLive87, compactPoolIDs87, compactBucket87)

def check87 (k : Nat) := compactNode grid87 tab87 compactDomains87 compactPerms87 k

def grid91 : CompactGrid := (91, 6, samplesP91, samplesQ91)

def tab91 : CompactTable := (compactCount91, compactPath91, compactLive91, compactPoolIDs91, compactBucket91)

def check91 (k : Nat) := compactNode grid91 tab91 compactDomains91 compactPerms91 k

def grid95 : CompactGrid := (95, 9, samplesP95, samplesQ95)

def tab95 : CompactTable := (compactCount95, compactPath95, compactLive95, compactPoolIDs95, compactBucket95)

def check95 (k : Nat) := compactNode grid95 tab95 compactDomains95 compactPerms95 k

def grid107 : CompactGrid := (107, 6, samplesP107, samplesQ107)

def tab107 : CompactTable := (compactCount107, compactPath107, compactLive107, compactPoolIDs107, compactBucket107)

def check107 (k : Nat) := compactNode grid107 tab107 compactDomains107 compactPerms107 k

def grid111 : CompactGrid := (111, 9, samplesP111, samplesQ111)

def tab111 : CompactTable := (compactCount111, compactPath111, compactLive111, compactPoolIDs111, compactBucket111)

def check111 (k : Nat) := compactNode grid111 tab111 compactDomains111 compactPerms111 k

def grid119 : CompactGrid := (119, 9, samplesP119, samplesQ119)

def tab119 : CompactTable := (compactCount119, compactPath119, compactLive119, compactPoolIDs119, compactBucket119)

def check119 (k : Nat) := compactNode grid119 tab119 compactDomains119 compactPerms119 k

def ax31P : Nat → Bits
  | 0 => 0x3c45fd12
  | 1 => ~~~(0x3641259a : Bits)
  | 2 => 0x32486ec8
  | 3 => 0x288bb5e0
  | 4 => ~~~(0x8c8fc60 : Bits)
  | _ => 0

def ax31Q : Nat → Bits
  | 0 => 0x25f002
  | 1 => ~~~(0x3f8b359e : Bits)
  | 2 => 0x20580ec0
  | 3 => 0x288b3580
  | 4 => 0x1082011c
  | _ => 0

def ax31Perms : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def ax31Words : Nat → Nat
  | 0 => 0x83f18da8f5a2ff807e55fe03fc07f80ff0115be844deb69fb3fe00d52c467ca9ffe02f6861ab4b25fe03fc02f087a4332e26c7f2cda03ffe00f9e97d7ff01fe009226cd3ad7624dd657b168b7c7739438864ceff017baffc06d2cff004903fc07a96e4bbb054f77781eff019385620ff80ef666f1e00777db1f688617fc04a9725aa89b62197f806c0ffe03fc06a80c0ccded45003001300cc41032092c3010188b400c044400d04100e10601dfd0d0d0d0d2c8c8c9c4c5c1bcbeb5b0b1ada9a4a5a0a29b8e8582787879747477686869665d5859564c4e44463c3e362c2e27181a130500d1404084040cc10505041311008049040880501041004911880440d2ffdbfdfbdfbfdfbeffddfbdfbf7fbeffddfbf7efdebf5efdfbf7f7fbf5fbfdfbdfbfdff5fefdff77fd7effebff7f5fbffa5281b285b282f192d192d28ad2863192119221123012228e128e128a12861281719161117280719330132013101300131290a090b010a011f191d191d111e011c011e291d291f08dc08dd285d281319130112291308c31902010308e9012a2929292a00a9288d090f010e290d290e00b08f01300609201200909101100900408c0100087a5703fc3d5578429ac0ba3ffc3fc15a3fc3fc3fc3fc1d6f5f414ffc2f1ffc3fc029bd59aa44218c982d02c02b5056a07130a08428e86a6fffffffbfffe32412212602402611c01600c09f
  | 1 => 0x2a1161f3828f41ff01f4a4136bb9b786bfe02941e233ff017123a97ff80d7bd6c07fc02863ec9d9a942a6392aa8b23e99f65cbabd5a0ca94c2840003c518024628024000b00000e0000570c42492492492496082082082082082082171e55044d2082082441041041041041041041041041041041413005051126ed6d6d74f4f6a5e5e7b4f4f565ececececed65ed756d65f1f1f5716d7aaeaf29f567a7a5faa7b1f1f3b1f1e5fcaebcb5756ea6fd357d0dcc230304b0c1483065c641319240a28d3149cc51b315dc6447190fc646d3148cc22030818c20530814c105315c4c071315f4c1653154c04520114cc153304a0c16911004c20130434c44008e08c55b30224c56211184c57b1913c644f30218a48529214c51719058c41708cec233b19070c2573082c040a2917023ca2404ca0404c64004c64002c23002c04402c040238a40028a2004824023804c238048028040238040028024014a44024a44014a40234a40024a38044a20044a18024a10044a10024a0824464c04464804464802464004404c23404c014040044020020a2404023802023401004c2300480298160445beb08243527fe03fc03a5eca51fe011130b60bda3af0c7aa74309c98f034aefbd06ff010e6e513c8039fa5d0b85e44a4be574f5ab2cc8564ee5b7c747d4a5c9708c8208ab4ebb1d784a0e695fc6daf495fe03fc02a017ac5a0125c541d
  | 2 => 0xd4ff7faebfe090740938330529008dca3fe0ff007050970e9ff047819aa893272ff83fc1fe0ff00bd315ca07342458be06e0d3587f83fc1e5220675bc45180aaaab498d168b45c570b15c2d2616c879c529c0c9c209c8b08858c8e9490948980899ca29c998294804784680400518880400518094804698b008004988046802981048046948804004047004802046943004cb7ced0af4f91d60af6948dd17ff01ceb7fc0523b3fb842fe6c5e94a6d1e9467a648d61cb5069a7c3240aebd65fe00e68ff80ff01fe037207f8036b5fe03913d5d4ff00516e7e21f3eff016a18a1a6e04dec49680af2db899cbb6b343b01ebc9b61ef63291cc2c0786099c7e3b857ff01fe024dcfae6c9d4c023fc0540d092b5a77fc01e9f7dd1d91760d67c6a5a7b957b1d6256602761b2ee949377d627803fc01b82
  | _ => 0

def ax31Count (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 8
  | 5 => 56
  | 4 => 55
  | 3 => 11
  | 2 => 1
  | _ => 0

def ax31Path (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits ax31Words (15 + 12*i) 12
  | 5 => let v := readCompactBits ax31Words (758 + 16*i) 16
    (readCompactBits ax31Words (602 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits ax31Words (5784 + 18*i) 18
    (readCompactBits ax31Words (4872 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 3 => let v := readCompactBits ax31Words (9857 + 16*i) 16
    (readCompactBits ax31Words (9497 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 2 => let v := readCompactBits ax31Words (10590 + 12*i) 12
    (readCompactBits ax31Words (10542 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | _ => 0

def ax31Live (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits ax31Words (0 + 5*i) 5
  | 6 => readCompactBits ax31Words (111 + 6*i) 6
  | 5 => readCompactBits ax31Words (1654 + 7*i) 7
  | 4 => readCompactBits ax31Words (6774 + 8*i) 8
  | 3 => readCompactBits ax31Words (10033 + 9*i) 9
  | 2 => readCompactBits ax31Words (10602 + 10*i) 10
  | _ => 0

def ax31PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits ax31Words (11 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits ax31Words (5 + 3*(v &&& 3)) (3*n)
    compactIDsFromBits bits 3 n
  | 6 => let v := readCompactBits ax31Words (258 + 9*i) 9
    let n := v >>> 6
    let bits := readCompactBits ax31Words (159 + 3*(v &&& 63)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits ax31Words (2270 + 8*i) 8
    let n := v >>> 6
    let bits := readCompactBits ax31Words (2046 + 4*(v &&& 63)) (4*n)
    compactIDsFromBits bits 4 n
  | 4 => let v := readCompactBits ax31Words (7250 + 6*i) 6
    let n := v >>> 4
    let bits := readCompactBits ax31Words (7214 + 4*(v &&& 15)) (4*n)
    compactIDsFromBits bits 4 n
  | 3 => let v := readCompactBits ax31Words (10135 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax31Words (10132 + 3*(v &&& 1)) (3*n)
    compactIDsFromBits bits 3 n
  | 2 => let v := readCompactBits ax31Words (10612 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax31Words (10612 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def ax31Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits ax31Words (330 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 22)
    let v := readCompactBits ax31Words (338 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 5 => let d := readCompactBits ax31Words (2718 + 6*(i % 34)) 6
    let off := ((i/34 + d) % 130)
    let v := readCompactBits ax31Words (2922 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits ax31Words (7580 + 6*(i % 32)) 6
    let off := ((i/32 + d) % 115)
    let v := readCompactBits ax31Words (7772 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 3 => let d := readCompactBits ax31Words (10157 + 3*(i % 7)) 3
    let off := ((i/7 + d) % 28)
    let v := readCompactBits ax31Words (10178 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 2 => let d := readCompactBits ax31Words (10614 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits ax31Words (10616 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def ax55P : Nat → Bits
  | 0 => 0x31d8
  | 1 => ~~~(0x2278 : Bits)
  | 2 => 0xfb0
  | 4 => ~~~(0x2d9c : Bits)
  | 5 => 0x2e6c
  | _ => 0

def ax55Q : Nat → Bits
  | 0 => 0x1108
  | 1 => ~~~(0x267a : Bits)
  | 2 => 0x2cb0
  | 4 => 0x242
  | 5 => 0x2660
  | _ => 0

def ax55Perms : Array (List Nat) := ([[], [81, 64]] : List (List Nat)).toArray

def ax55Words : Nat → Nat
  | 0 => 0x10bfeff7fbb41fa0141c9f
  | _ => 0

def ax55Count (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | _ => 0

def ax55Path (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits ax55Words (19 + 12*i) 12
  | _ => 0

def ax55Live (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits ax55Words (0 + 5*i) 5
  | 5 => readCompactBits ax55Words (31 + 6*i) 6
  | _ => 0

def ax55PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits ax55Words (13 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits ax55Words (5 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 5 => let v := readCompactBits ax55Words (37 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax55Words (37 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def ax55Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits ax55Words (39 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits ax55Words (41 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def ax87P : Nat → Bits
  | 0 => 0x1dc13af48
  | 1 => 0x141fdf814
  | 2 => ~~~(0x19f2395c : Bits)
  | 4 => 0x3bf251bc
  | 6 => ~~~(0x5fd1c7bc : Bits)
  | _ => 0

def ax87Q : Nat → Bits
  | 0 => 0x81112448
  | 1 => 0x141fde804
  | 2 => 0x10088c282
  | 4 => 0x2a021130
  | 6 => ~~~(0x1f599e7fe : Bits)
  | _ => 0

def ax87Perms : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def ax87Words : Nat → Nat
  | 0 => 0x7f80ff005c8ac507f80c40000188a7ff806a7ffe0324aff80bb3aea6bfc06219ff01b762b452fd9eb8e20def4bff80bdb61b562e15db6735fec3bfc06d88d605fe03fc02b40ff01fe02348ff80dc30486fb13e04b784bfe03fc010bbff013237d479b31ff00e4e3fc025a3bb1686254d6c4c48f91170d5a0d1460c728b01402801320044800a00278000008201e0027705c76557750d37405033c4f7304c725c670c437013e4f13a6dc370dcb62d4b44ca2e6ad2949c27495234859e8699745611a308b2288941e03600f028440008e328c2010802284022c0213148200ca20424584a42008011805090423206221c88508805848312880248c02c94023086900923008402efdf7efefdf7effdfb76fdfef9efdfef7f7eff77fdfdfb7efeffdfaffdfdfafeffbf7eddfbf7efdfb7651927112528e528911911111328d3289f011d011d28212921288d190d190f290d290d10cf289a191919191119291910da08d808d928d9280a190b01090109290a08cb00c900c928c2190208d60095009528871105110501060085008728b01300e08e00a00501100d00900400b9a3e2d2e5ff81241fe0ff07f8104c2ec681ff83fc0827ff01a935511819d4b50a10b1eeff061bf94028a5fe8f0c772f91c5e1680d02aa8e40266a840e212a42c806a0268ca2a60484ea6c12064b7ffffbfffffbec32602202411e01a01c01400a00c06a1f
  | 1 => 0x125ebd43779836962a44f4391991ec51ae35ff0056e7fc00b277d944a7640631a91669fe029cfff80ff002c17fc01042ff01fe0130068cdff01fe03fc0768fff005005b9b55975e37fe00e45c2b7ff00a6c69a07f80f77d1e0968c90d2c183dc549e82f13ff0032189844443ff01fe00268b6bc11130f1046727c6a123e153725ba5500a7dce00263449627e4a1f450860024802d848010018211000618400200a2305e3c78f5cb46ac562c5aa14a54270e1d3060c1832587040810204081020408140000000002081a6a0ca0000803cb20e0059c7c79d9d8fe6e69bc7e3b99de5b9bc9dc78feaea8fcdbc9de6f2c78f8fcd9dc7d5eaf8add9d99dbcadd9d9823271193098aacc266622730121811cc2da321d192898544c5023201308098004c57a325a316f88864440c62cf292698134c52a321510dc8c8ecc4aa62c9292498ad8646c118a19050464cc45c012d00b318a8cc01e626a00b48059468099448079448038888038090478088050c88050c80050470050468050460049488069478089470049468049460049458069450029410468c88068888028870048088048068048050028048028040041488040470054ac2200d805bc65cf44f62ee49112720e5ce9cd35794204a22cfd2dc2da896d031774d60da1b574f880f0459543a0f62ba4b3c5192536a15aecce094a8fbfc001ac220e8ea5f5e68bdff00093bfc0
  | 2 => 0x7ef411ff83acbfe0840ff808e7fe0ff07f83ae010eee3daa7fc1fe03997f82099fe0725ff8269aaf1c212b000008102c5a1d26161b4ae456385d009c4d1912324464e9cd9396a5254e530c8608f29208d00a19100800a08d00800931408e00930808e00930008e00928d00800830119100f3826b3a4d15fe00257f2ad8167de3acd5dd832e51b097c
  | _ => 0

def ax87Count (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 9
  | 5 => 47
  | 4 => 43
  | 3 => 10
  | _ => 0

def ax87Path (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits ax87Words (23 + 12*i) 12
  | 5 => let v := readCompactBits ax87Words (926 + 16*i) 16
    (readCompactBits ax87Words (806 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits ax87Words (5421 + 17*i) 17
    (readCompactBits ax87Words (4725 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 3 => let v := readCompactBits ax87Words (8666 + 15*i) 15
    (readCompactBits ax87Words (8378 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def ax87Live (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits ax87Words (0 + 5*i) 5
  | 6 => readCompactBits ax87Words (131 + 6*i) 6
  | 5 => readCompactBits ax87Words (1678 + 7*i) 7
  | 4 => readCompactBits ax87Words (6152 + 8*i) 8
  | 3 => readCompactBits ax87Words (8816 + 9*i) 9
  | _ => 0

def ax87PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits ax87Words (17 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits ax87Words (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 6 => let v := readCompactBits ax87Words (389 + 9*i) 9
    let n := v >>> 6
    let bits := readCompactBits ax87Words (185 + 4*(v &&& 63)) (4*n)
    compactIDsFromBits bits 4 n
  | 5 => let v := readCompactBits ax87Words (2482 + 10*i) 10
    let n := v >>> 7
    let bits := readCompactBits ax87Words (2007 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 4 => let v := readCompactBits ax87Words (6598 + 7*i) 7
    let n := v >>> 5
    let bits := readCompactBits ax87Words (6496 + 6*(v &&& 31)) (6*n)
    compactIDsFromBits bits 6 n
  | 3 => let v := readCompactBits ax87Words (8920 + 3*i) 3
    let n := v >>> 2
    let bits := readCompactBits ax87Words (8906 + 7*(v &&& 3)) (7*n)
    compactIDsFromBits bits 7 n
  | _ => []

def ax87Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits ax87Words (470 + 4*(i % 6)) 4
    let off := ((i/6 + d) % 24)
    let v := readCompactBits ax87Words (494 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits ax87Words (2952 + 6*(i % 28)) 6
    let off := ((i/28 + d) % 107)
    let v := readCompactBits ax87Words (3120 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits ax87Words (6899 + 6*(i % 24)) 6
    let off := ((i/24 + d) % 89)
    let v := readCompactBits ax87Words (7043 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 3 => let d := readCompactBits ax87Words (8950 + 2*(i % 5)) 2
    let off := ((i/5 + d) % 25)
    let v := readCompactBits ax87Words (8960 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []

def ax91P : Nat → Bits
  | 0 => 0x22ab5b2
  | 1 => 0x7dda744
  | 3 => ~~~(0x7807b6 : Bits)
  | 4 => 0x55e5a86
  | 6 => ~~~(0x7ceb0c6 : Bits)
  | _ => 0

def ax91Q : Nat → Bits
  | 0 => 0x8aa422
  | 1 => 0x198500
  | 3 => 0x3c67048
  | 4 => 0x4645a84
  | 6 => ~~~(0x7cef4ee : Bits)
  | _ => 0

def ax91Perms : Array (List Nat) := ([[], [49, 100], [16, 99], [16, 97, 99, 100], [48, 49, 67, 100], [48, 65], [64, 49, 99, 100], [64, 97], [96, 67], [96, 65, 67, 100]] : List (List Nat)).toArray

def ax91Words : Nat → Nat
  | 0 => 0xaf8391ff003bb79f3862e67812d81d452145e4f36cf8c566449e9634487423a9051fa05a8cae69a5bd22529ea2ff0062a7283b1e92ff0068d8ff0057599319ff004e87ff00cf742ddaff00db8aaa707315ff00aa7835b9ff00ff009ba8a5d79f04767a2582b336ff00438665d9ff00ff00ae850e3a9f2dfab8559f2c22abbba5469431439d4bd2b3b6ee17d37ee0e21f0ec93f9400dd6f185bc693eae0e8cd76010bed24b152245295a21bb84ac14ea468497fdcc0dab434c6bee5ff005171893eff00411072a5238e2465e55ccab3352bff00ff00572ccd7d4a83c840949a113c9989716dc94f254cff008213ff0054e33003d26a6bbaa0d1702f2c88ff00c87380643c585bb1731000232f84e20400a301b28504114124040510204005f0017041d42546080910008080802c00000082810001c000314904b2cb2da28a2a82082082175955044d280002181b60c77fedfbf7efdffb3efcffb7fedfbffbf5ffbfafdfbf5292c11d4a3a9435281e51bca03047229225244a48847128e41144a28940b00d201a4a35044b00925104a309450450028448020440022c263a3fe05b91fe07f80324e4a0da71ac4750bbbdfe040c7d0ca115acfff81fe01a26953931b8d203cd40ec3996707c857ab9525fe07f80747ff80b52ff80d4dff80145ff812c3632bfe0301859900057d552d046428c151a063447fffffc112114008009f
  | 1 => 0x8c1544fbfc02b05b554fc3d68a7484f698fb0eb5e62c40462b6424a7c408ea03fe0175c92000d185cd8e67250d3467d735c997f80334e6b155646312da27630301a602cff01392bfc07f80ff019e27fc012c9ae601c726c162836e16bc1d9dc091bae5de8f7e8aff801c31fe0011ad9a63e35471aa0cb5bbff01fe03fc06916ff01fe037c3768e9075fe02120c7c73a2e44fdfd26222ff008a802dba3c2ff00d12c9889b1d381a40e022680a311123091002a00100008fd3d5f497d5d6973988e111e60ec23118b028e851acc3c03401c024018224014a30224a24014a08220a3401f760ff00364335bc507bff0082a6ff00ff008a755762ff00ff009c8bff00b7804899be42e209ff0086e7c2db1fb5ff00a91f865e3eabff006d8426c22bc486761381ff00d60c0d97ff0060c720ec8dd500c131ad6a5fb6e8d72a4166ff00f4bfff0035411f5475d313207e4d985dd0a95aa1d9496028e14bff005c47df3d6acfcd94799b80a3327c865aeba40a30c6c9921e67ee7d024eeb2067b479b59c84becaeac5d43c27ff006c34ff0069c3c226d34550ef7072ff00ab072b56b08fee6e5c63f808352ebdcbff00387729d6e16b392987e920614c8d7d9e25988425709076064
  | _ => 0

def ax91Count (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 4
  | 5 => 24
  | 4 => 8
  | _ => 0

def ax91Path (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits ax91Words (7 + 12*i) 12
  | 5 => let v := readCompactBits ax91Words (885 + 15*i) 15
    (readCompactBits ax91Words (813 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits ax91Words (6076 + 15*i) 15
    (readCompactBits ax91Words (5908 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def ax91Live (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits ax91Words (0 + 5*i) 5
  | 6 => readCompactBits ax91Words (55 + 6*i) 6
  | 5 => readCompactBits ax91Words (1245 + 7*i) 7
  | 4 => readCompactBits ax91Words (6196 + 8*i) 8
  | _ => 0

def ax91PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits ax91Words (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax91Words (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 6 => let v := readCompactBits ax91Words (139 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits ax91Words (79 + 3*(v &&& 31)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits ax91Words (1446 + 6*i) 6
    let n := v >>> 4
    let bits := readCompactBits ax91Words (1413 + 3*(v &&& 15)) (3*n)
    compactIDsFromBits bits 3 n
  | 4 => let v := readCompactBits ax91Words (6260 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax91Words (6260 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def ax91Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits ax91Words (171 + 4*(i % 10)) 4
    let off := ((i/10 + d) % 43)
    let v := readCompactBits ax91Words (211 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 5 => let d := readCompactBits ax91Words (1590 + 6*(i % 69)) 6
    let off := ((i/69 + d) % 244)
    let v := readCompactBits ax91Words (2004 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 4 => let d := readCompactBits ax91Words (6276 + 5*(i % 24)) 5
    let off := ((i/24 + d) % 88)
    let v := readCompactBits ax91Words (6396 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | _ => []

def ax107P : Nat → Bits
  | 0 => 0xa37e08
  | 1 => 0x64fd4a0
  | 3 => ~~~(0x7a0d72a : Bits)
  | 5 => 0x7b0e372
  | 6 => ~~~(0x6fb62f0 : Bits)
  | _ => 0

def ax107Q : Nat → Bits
  | 0 => 0x4637800
  | 1 => 0x64ed400
  | 3 => 0x212894
  | 5 => 0x262
  | 6 => ~~~(0x5f37af6 : Bits)
  | _ => 0

def ax107Perms : Array (List Nat) := ([[], [16, 99]] : List (List Nat)).toArray

def ax107Words : Nat → Nat
  | 0 => 0x7f9c3fe7f9fe451004da350ce3a12262221a012222122013513fc1fe02ba59edd5ffe0c747f836168e6239fa57fc1bfdff06734471fe0ff02f85c21cd14c1605feb2d76194e39541dcdca63ca8dc587b26007f83fc06a202005006318c6334a598c71401304a4099ee39e9d8f9dbaeabae8eaf2bababa7cc034646cc04cc15cc45cc194c224642cc30444a4441c6414c484c25cc2ca4402c644028a34024a48434a44434a34024a2803444443444402443402424402915efc43d2e821db3a981d1cd4a787f83e5ffe09a1b6061c9fe0ff0025f6d9dea05cff83fc0825e8a8783fc18edd69709f627fe09a80036007113010102f4d4b2a29284625a00310100223126290bbf7eff7f77efdffdfaffef4f28ea5254a058c8911125244a23944200c20184a318c8111210e00d11110d00d00bfc14c949f78cc06bc3fc3fc25dbfc0317fc38527a7fc3fc3fc3cb490abc5a04106730642507432147597620fffffff911210e00d00f00a8dd51f
  | _ => 0

def ax107Count (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 5
  | 5 => 13
  | 4 => 15
  | 3 => 2
  | _ => 0

def ax107Path (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits ax107Words (26 + 12*i) 12
  | 5 => let v := readCompactBits ax107Words (538 + 15*i) 15
    (readCompactBits ax107Words (466 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits ax107Words (1716 + 16*i) 16
    (readCompactBits ax107Words (1452 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 3 => let v := readCompactBits ax107Words (2787 + 13*i) 13
    (readCompactBits ax107Words (2715 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def ax107Live (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits ax107Words (0 + 5*i) 5
  | 6 => readCompactBits ax107Words (86 + 6*i) 6
  | 5 => readCompactBits ax107Words (733 + 7*i) 7
  | 4 => readCompactBits ax107Words (1956 + 8*i) 8
  | 3 => readCompactBits ax107Words (2813 + 9*i) 9
  | _ => 0

def ax107PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits ax107Words (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits ax107Words (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 6 => let v := readCompactBits ax107Words (216 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits ax107Words (116 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 5 => let v := readCompactBits ax107Words (892 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits ax107Words (824 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 4 => let v := readCompactBits ax107Words (2106 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits ax107Words (2076 + 5*(v &&& 7)) (5*n)
    compactIDsFromBits bits 5 n
  | 3 => let v := readCompactBits ax107Words (2845 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits ax107Words (2831 + 7*(v &&& 3)) (7*n)
    compactIDsFromBits bits 7 n
  | _ => []

def ax107Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits ax107Words (256 + 2*(i % 3)) 2
    let off := ((i/3 + d) % 17)
    let v := readCompactBits ax107Words (262 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 5 => let d := readCompactBits ax107Words (996 + 5*(i % 8)) 5
    let off := ((i/8 + d) % 32)
    let v := readCompactBits ax107Words (1036 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits ax107Words (2181 + 4*(i % 10)) 4
    let off := ((i/10 + d) % 38)
    let v := readCompactBits ax107Words (2221 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 3 => let d := readCompactBits ax107Words (2853 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits ax107Words (2855 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | _ => []

def ax63P : Nat → Bits
  | 0 => 0xb70905f668
  | 1 => ~~~(0xb733329768 : Bits)
  | 2 => 0x1b070f1bba0
  | 3 => 0x80f716d490
  | 4 => ~~~(0xbfe0d5f2fc : Bits)
  | 5 => 0xf22fa034c
  | _ => 0

def ax63Q : Nat → Bits
  | 0 => 0x950905c028
  | 1 => ~~~(0x1eb777ad76a : Bits)
  | 2 => 0x2e0d03b80
  | 3 => 0x415512d400
  | 4 => 0x148162a0402
  | 5 => 0xa22680340
  | _ => 0

def ax63Perms : Array (List Nat) := ([[], [64, 81], [50, 16, 84], [50, 80, 65]] : List (List Nat)).toArray

def ax63Words : Nat → Nat
  | 0 => 0x589ff84b2ff85937f858bb1159530dff823254d0902c5d1d5ac5cb177fffffa32a12a11a017f833c7e41ff069be8c0655889e1264d9fe0e968abbfc054a1eba997989fe0e93c099bd055ad017f82ab66cbff07f80181080204edae83a13d9c11cc84001828407252c687950044f20aa9d819067408d00a96a47a518085894e899a9868042b5eb020096253a500101c62acd528d6066034e124a747553664c009a817b026b14253a2010d0a1048116885559af49ac003129d0e240861a2c5559a7de8059ffffffffffff42484344382242280240282574d03f
  | _ => 0

def ax63Count (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 7
  | 7 => 3
  | _ => 0

def ax63Path (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits ax63Words (36 + 12*i) 12
  | 7 => let v := readCompactBits ax63Words (1447 + 12*i) 12
    (readCompactBits ax63Words (1435 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def ax63Live (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits ax63Words (0 + 6*i) 6
  | 8 => readCompactBits ax63Words (120 + 7*i) 7
  | 7 => readCompactBits ax63Words (1483 + 8*i) 8
  | _ => 0

def ax63PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits ax63Words (30 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits ax63Words (6 + 6*(v &&& 7)) (6*n)
    compactIDsFromBits bits 6 n
  | 8 => let v := readCompactBits ax63Words (939 + 12*i) 12
    let n := v >>> 7
    let bits := readCompactBits ax63Words (169 + 7*(v &&& 127)) (7*n)
    compactIDsFromBits bits 7 n
  | 7 => let v := readCompactBits ax63Words (1563 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits ax63Words (1507 + 7*(v &&& 15)) (7*n)
    compactIDsFromBits bits 7 n
  | _ => []

def ax63Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits ax63Words (1023 + 5*(i % 7)) 5
    let off := ((i/7 + d) % 29)
    let v := readCompactBits ax63Words (1058 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits ax63Words (1584 + 1*(i % 3)) 1
    let off := ((i/3 + d) % 12)
    let v := readCompactBits ax63Words (1587 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def ax95P : Nat → Bits
  | 0 => 0x16aaaa8020d1152dd13b310
  | 1 => 0x11e45400d722dbc9a1d4424
  | 2 => 0xfffffffffe585f876288860dcea4a883
  | 3 => 0x1918ad0941266f175c64448
  | 4 => 0x95b42909e18bc223e818b4
  | 6 => 0xfffffffffeaf7116f004582f207b034b
  | _ => 0

def ax95Q : Nat → Bits
  | 0 => 0x80824801020150d0128210
  | 1 => 0xa4408e3e2393c8a154004
  | 2 => 0x10108052c884090e842802
  | 3 => 0x19008411409c6c175820440
  | 4 => 0x16420230c054282216810a0
  | 6 => 0xfffffffffe090122a824382600690109
  | _ => 0

def ax95Perms : Array (List Nat) := ([[], [32], [49, 100], [49, 32, 100]] : List (List Nat)).toArray

def word95_0 : Nat → Nat
  | 0 => 0x638135fc7c01cf60a6ad809218397f72870003e9a3611a8c4337e2cda8004c06e54586360060a8133405c15fc25500e2187c006c04c06080c6c032068b054099a0b0160182bfa2dca126c5410c1c1f007043e8b401188b72a3c25500e0011b346c0d50c963e1990e4b43070019e6c23f0412a84d06a7c4392c6a2c33362688c46a1a2ce545a33043e0023c0334b4a346a866c7fdfdfdfdfffffdfdff7f7dfdfffffffdffbdfdfdffffbfbffdfdfdffffffffffefffffffffffffffffefeffffffdfdffffffffefeff7fff5fdfffffff7fff5fdffefeffffffdfdfffc242c262c260c2603a61a242a232a662a262a43222322661a660123292123242b262b23232623260b2601a429e321a321a021e621a621e600e320a120c118a11aa120442824284328232862284228222802286128212840282028662866282628062862202220612021206020202020206620262062182218601820182018661826186110211040102010661066102610061632432411c00a12211a02201200ff83fc1a716f09600d27029aa6e81f817fe0ff01509d5f103ff05005df358e0cb463002eaaae2a2da9be2928a830a79f2b270e42801d33248ba5cb3e259f00400e3328a0824344af2eaaae2a2da9be2928ac2833309f2b27a70037a1848e25be331f003fb60e25c39f81c3444b46c63e33259f3527000e437ffffffffc644248234234013f
  | 1 => 0x66c0010e999201d148b46019b6da80395161c1e66b057fa82611e8e430f832d86c46a01829439516060e6691d7f1f540648f431f01f16c1070019a8023afe8b72d4130d88b4d0548f4aa180cdb71369161c0008b3c6a941391e8ec14d2a0868b0f9b02b150a04e261c095ca7ccd0d848350145b3d829b219c8180e138387c0060a2c8c9a2350d008c04c06e503b7db0180a8133582bf84ae406430a4f9500e0022c020ae093013018400e12026682300bfb96e40f033603116a81f0380e14a31ca8b3e3611b500e00268188b2191e664392c7c86cf0700182478eea1344c0603066438f8624b14c5a688d4621a30e545b60387c46d32a0184323e2c39d8458cd7f72a2c39ba4b2182c3e6c237617f9a0722cd84b22dca0013a4c0a8d198ac7832150886e25120d705340a8711b1a72b6ccc00464000934352181e060c22c02e2090792d82a90011a18d806c2a13bfb68240c8b25916e5b9015b100a8198388d1302cd400459992d820e36a015013234d47c4392c703e4b60838000ad42686a469f10e4b130f91982350110dba0e21828984b0f918d8d845b35002712c7c1c002612c8c4583c0c0170860241da8a5b748c00063601a8b05734178004814984b5c9b04b72d40388c1222c124e0012d301c4b39449504622c9c361f2392d9e0e000268ca84d10e4e3e1987c8e4693806861a0cc5632150a44228138944836728d47
  | 2 => 0x78a0a07a3c1b0e86d399a6fee53b9aee4d8371aa689a3925a2d503e070e2804d4d10c9746225328b25a1c7d8500202ea989c2247a34438f89600404e11a8c431e850983612cee6e10234606b356d0a2e5bad527066ba92d31ba0e4e1cb5045c8518280023aea7843ce119b43e12d0e3e0e25c0975a82191250b9361195046adb346d8b21d24964501cf27a8b1e0d8763b9ab608bbfb96e46b6c1d52cb69a010001c3709b1387c36110dbf6c269164b46dfd3082291409e4e2f1987c1c0022cba552de8eef509e8aca65d2a96ca6522c9409e4e0e262017725cf5165d2a96ca64d27938ca7c2d0f8b26600260a45845dde013d14140f8661f000506cd19fc383f2580cba552998cf852311989e98300f839a3275dc1224a822c968e33459b09a43267788846a5caa531419360663095840542793b666c805cea93725dcccc1c474dd2f00a80a10f166c218068846a5c01734ccdd108d2c8011d374ba187c1c4ca5c0773a8219111f77bb62d00763a96db0a85c920494692c2ee5d8459177f72dc96d0020a410c89023bddb16763aa00b601ec2139ab921920434592c12e5d845b350043dc96c3f72a192088018cc563c190a844231b8943e6e1ea1860e5178e44c001409ccf8a024d2021cc14a11d7f72a2ee4d80e6e86886089f11b16335fee5340e5422c8e45b95b0004b237748725dc9b01c19a1820963e459199ab94d0389
  | 3 => 0x3b8c560f3d363ff802a04c58ea4e1505baffc01fe00ff0042997fc01fe00e437d8a2e2d215ef09071d38eb147aaced0e85ac19de03a1672556ce43e5c957ca00ff004a1e9c8f2e46bd78b4d1d4d8a7fe00ff001f96f08c77917ff000f92e786e0a0a8b7473a50a22842935d404c34cba0f2850ac81a03d7663240cfd71586922f944d273ff004225c6177fe00ff00069a88007f06467473129d989dfe00ff006eb27fc01880dff0017a76cc652615f378ff80159d9201eba4ca927b40737c0c8f680522bd4d27802ff007f803fc01fe00eb6e844e007a2281852b4000018450a8042ca00c04029ca19280540900024003062e29cef28864008a0100814912008462ac5c8c4b9439bc22a40ecbf543ed53e35bd89bc563b93bb263a67b97c37f6b72a35e834ebb37632bab165b0b9af852ee3ae732e132db4ad28ac16ab49aa16a94da798269725b6a4e72409a2da2199a06a1f2b1dc51d2c1bad1a0719279836177696a795b714d793e59336926c10e610270f450ea48e168d460c8b8b158a668994091d876506cc054c83b882a801a580f7800c4e1f0d6ec223ae5509a1d0e6d85b1c5344b46c58f97f3693c9c7c1f070005d2a96cb8548b5f6dd4b3694caa53141f0383e00190c24f2b15372b6bed2cd84e2a950a4513093cc67c1f158981c29db8a0602f93b739abe85c968e39954e2533d9f01a70290f8001c2c5e10f413
  | 4 => 0xa80388880388680384a80384880384480318280510a8030ca8030c880508a80304680500a80300480298a84898a8029888049888029868089868029850029848029828049818c890b8c890b04690a84690a8028ca8088c90048c800488a80288880888880288680284a80284900284880884880484880284680484480280a80280884680880480880280480218a80218480208a8024c57ff007f80020840011ff0050937fc00d25cd10fde807fc0168a0ff007f8006c89fe007e8ad4ae61d840d1dbe1f7f8019d876e5fff00418d82076d2877f91aba23c8f6048f2f3c59306b8c25c23b6095793305676af2036940155d5344721c165bb0f014e236892642a70fd1a27aefd58218a11e01b67a076c70ff803fc01fe00363f7f803181fb6a3618f8e09ec44aa66d707dadbfd80faa049a70447983849ecab1e84e59a84d439f216774c1ac455016a676f586ff801ccd9fe00ff0067245816ffe00ff007f802c13fc8bdda68a3104641cd277cc72d9301005dc701b9081e2b484ddb84ad482e5206ecb45c95be491fb177449810fd06b9a0e2c9060214d3294f2344d52eaf7485b05a18195fc6df8d2f708bf58a2da310019ac067fc01211b254b4e0c2b02ea059ff007306f78e0d609ff0069a6fa48ccc0561776a1d2f9087c544177a890038b1c85d7d11463a4a97f3a66ff004420b0cad287f31738d04e41188c455c340e9f
  | 5 => 0xa70479c71e70689cba2712a90aae712b9cdd232a28ca62429898a62223e9cbb232b19c0c2702f9c032428d9ca32728c8883671669c4a272a89c39272e49c39473649cd9273509c65e72969ca5c32168c85e71979cc2a328a849c232f184bc632708490a32c384b0e32428493662cc98b3272cc8c936624c98932724c9cc4e32128c84a02139884a62139c84a72139cd5a1257046de12b6848da7237046da71a69ca9a709a9caea12549c554732d9c4b470ad9c0b4732c1ccb073529c54c73629c98c734e90b3a724f1cc9442a490a9672249c29670259c09473249cc9073009c80272009c60270009c004735c90b72725c9c476229c88a76714a90b2a720e90a3a12f29c5ca42f388bca22f29c9ca72731c5ca71729c51622c488b1671c59c412716198b8272e11cc8242a198a8672a09ca8473201cd6a429488a5672959c422428900a2202889ca22428908a2222899ca2472889ca2072888882671089c5ba42ef88bbc22ee88bb822ef9cbbe224188b0422c088b0022c19cb06715f1cc78733d9c56242d89cb62721100a4202919cb2212c898b22018684a1a028698a1a02068061a116a9cbac42ea90bac32ea8cbac22ea88baa12eb9cbac72ea9cbaa72ea889aa126a809ae726a9c9aa726a887aa71b984ae402b880ae672b99c8e201029cb98a84998a80998a8039888059888039848099848039808499808478c880588
  | 6 => 0x40861300f80281533405809008508568a82a61b06080a0082a0a986c26807c0700000e0f80f88b08f1b02344308f0f82343e29d0cc3604308f1186084308f0f82304315010e228478860f837c4308f0f8540462ef3041f446a7a10c1982588753a0013d01c11e23c3e19e10c360ae87c11e0a44786610e12c4329d4f40f86d2ee33c2183308c2a0864cf06810c4e0468da11efa89a2ee124678ad07c68021c2588f4f40700008d11e6797706633c0101307c11e21c2588653a9e81f0872a06084304b10e4f4a804b3041f1672ef4329e81615011a2196715010c1f1670d8122218a187c11e245f508d0cc21c258860f8d004639c11ab38091502c00709e0860621f08b08fbfeff7f3f9bcfe7f3ff7dfeffbff7fbf7fefbfefeff7fbffbeff7ff7dfe7f7fbfdfeff3fbfcfeff7fbffbfdf7fbfffbfdbfdfeff7fbfdfeff7fbfdfdffefbfdfdfefff7fbffb7fbfbfdfefffdfeff7fb7ffedfeff7fbeef6ff3fbfff6ffbfdfcfeff3fbfcffbf7f9ff7fbf7ffeffafdbfdfcfeff6fbbdfefd3ffedf6fbfdfedf7bf7fefff6ffbfdfeff7f3fdfefe7fbfdfcde7f7fdfdfe7fefdfdfeffbf9ffb7fb7dbefbffdfebffbbfdfeff7fbfdfef77fbfdafdfeff7fbf9febf7fbfdfefe7f3f9fcfe7ffdbedf7fbfdbeff77ffefeffb7ffeff7f6ffbfdfeff7fbfdfef67fbfdfcff7fbddf4ff7f3fdfeff7bbfdfcfe5fbfbfb29c0d242b49c5d
  | 7 => 0x5187c3042604783e10c4581f08f10c1984384b11ea8d4007c11cacca808607c2395993411e2188d83e11cdf846b9c52221c478660962194889811a0f84302c07c3604788d10c23c1f2ce1be2184788d0000704787c10cfa84384b4fc6e9690d807ca99420d811a2344988f10c23c4308f6802344308f12c6e83e34010e12c46ad207c0703300051e9b54d292518a75f527d11aa109a26811221872a84118218448025a4224460e510ca1000ad236045846a6850823cdd2ce2a04000880e2a0a10d81164fab386c28e10c070332847d44a13400051c23480150374a1080150374a1000100374541672ce2a06e8088da59c6e8a8100000540dd2ce0cc36934000126a38468002006e8a806659c0586d2ce37454177aa0508fa97720c10c1f046a7d41823c4683e11e2343e08f11a6081f08f11a12c4383e11a0700008f5dc2353e8864185404303e07c2183e08612a400c11502682181f0870960f8432d24d8a383e07c11821c258865a4a393603e0000703e066130e704b03e1b0230458980f82583328d11812c1f01c0002383e06611a21935ab607ca3148a8e540a10478860380cc158260480d13d0e50640a81d82107a0a013a7a048414000e5070678a62a6038218a60d82860a44a0021c83940e284030234461824f46c04c0862fe2604303e3044857717f508395409823609e84309800c060d8116024541530d85025fd3
  | _ => 0

def word95_1 : Nat → Nat
  | 0 => 0x84826b10c9e8430901129e84308b432450a627a18c070480b62709e95501c2002404490927a9e95501c12045880088360a405b00010e2581f08e10e4244303e12e4694c29059c0d0000e55082181902207a0c01403904e0dc12a1905e4e00f91b10c23c8c04b10e0000e03e7382343e11611e5c84308f2b4b384788d23452567086038234431ba0f823c9a08611a12c4383e0380004788d56c21d5991b10c23c0001c12c0f8461160f823c6d08611e1f06d8da000070333ea10e12d4088f1b00f94d19a5dca68cd08611e1988c04b10e0000e03e22c1f04791b5dca48cd0d85dc6684308f1c86088f26e2680704aa922a0001f51348044846f91b038a493715010c6684717f4dc23c3304b10ea483e03e0389b8000955144687119a1b421847bea1c42009408e7cee71453b81264686d0e21b42020103e7383608d08b268ee01f0d81c00708d0e21b4fa870bb80fd008473e71c00f88c28a0383608d0da1c20000e07e0ccfa84384b11ee71dc1181b00f97728e3342184781c234468142800480d4178270003944699a0706781303904a0900002a04ea00728351c8ad88f07c10c0a95b11e26846c150950024780e08c1ca2194201211a6697707c5229f44799a4fa0e00f0864fa6693b07c52223c002683041f00e0000100f83e0d811e4597719e10c1984788607c46c4308f07cbb84799e27e5403308f04c21c2583e500235
  | 1 => 0x618a604a5f0e5d4c5bca5a9458085706564455c854ce530a51c6510650444fcc4e504c524a14479644d2428e40d63e143b883a8a3950374a3608350c338c3210300c2e962bcc2a48294c27c826ce250a23ca228621c820d01ed01ccc1b441ad2188a174e15921352110810160d4a0c0a0ad20888078c061203c802cc014a0006c13410e12d5c2ef13421c4a2bb1062396405707c5f43e0870960f9740895d0e804688610eba00208d0cc21c2583e2702181a08910e12c1f2960f8011362960f821c2583e1120113611669a1f04517212422843887096a983d1160d41b8d80b65085c9470860381ac3b86a0dc9a1421721b0360468b61143604388a10c12c458d810c12c458861102344b9b022cbc0430881b0218440d810c2203e06607c2644b803110a5535ab316c0004383e21225c4303e11c4013f8901149fc430881de3b43e0ec1d419843a7f096f69ce0e510c0701f0001209fc258fa1e23bc768ec1d41803e2b110e1987d08603815c78a7f4ea4245b0871202593608612022472a8410c241362ee1125fcdda6c5082245b2ee4d823043a6c10ca99531ba11221c451ea10c2400e0870967a84301c10e2284301c10e12c4301c10cd342588b11612d3888611422c8499a4e2bb85b04b1164248008609622c4304b1169c48488b11a459388fa1e212d358885dc669358885dc2d8b910010c220430884d62204690912e21
  | 2 => 0x4340070040c78000004740020705484b4081400042040143860040400a800a000083c20c4042428285c0000180814845814041824311021182c0420c838d00c1804107004840c346c200008000c940404080050000800001010140028100034080000002854004800c840385c7c14481870301804007014201c00101400383800002c140c0000180434381c1c000004002800385024480400080c9c00400008002000042000100004001814182030080400081c3c04741010280034005c0040007c08001424000c18040c00080892e912c892b8d2a0b28d32693245122492147208320451fc31f8f1dc91cd11ac919c719071849174516cb15851507144314051393114b10090f0b0dc70d2308c907df040d028901890086ffcefe06fd44fcc2fc86fbc4fb48fa44f9c6f904f884f804f784f708f604f588f48ef2caf186f0c8efcaee86edcaec82ec46eb84eb06ea48e944e8c8e7c8e6cee50ce382e34ce1c6e10edf4cddd2db9ad846d796d4c6d40ad2c8d1c4d14ccfcece0ccc90ca86c9dac686c5c8c4d4c244c1c8c0c6c00ebe46bd90bb86bacab994b70eb558b252b00caea0aaa0a68ea4daa1969eca9d8c9c1299cc984a970e954a940c9288918690c88fcc8e528c0c8a848a10880a86ce850c8390818a80487f487e5c7ac879c6790478847806775e73907188708e6ece6d0c6b886a8c690c679065886488638a6246
  | 3 => 0x54e1d9b393fc00ca343fc00aead7fc0080293e759d1bd7fc00e110fd0c9b0667fc00757132a0300c30595691054a35e05438ca65b5381c88a3c7a7d045ff0021f1c75387fc009f309df42d10b6f0800117860555f55ffc004686242dd0099c741065430b065ff003fc00de5a62878913cffc0099109029583350fcebf3c55534b10a0c509ab24d6588de99be35adea5f8562cff003fc0081074b99fff0034546ff003fc00ff003fc005cc2e6d03ff000db31e84ce4dc05018bfc00ff00030fa6bba7922dff001a064ff0010c311a1affc006d5a9ba5b7892d0e9375d6f6115e66522327ff003fc00cc9c719723547d217a11873fc0038ce1c5523e42cc5f98c49bfc00e11587e05ff002b2915bb8db5f8b22d406be5fbec48143b977b1c54b2bf4c75a66a0ac5de437ae9dd0c94d967313ae64b2af51a7924d86833d190793a3c1c78d4a6ec40ff001d68b4a77aea226876beb1ac726f40f66f6fda734eac4ad82fff002def6dea073d5cb1534d93cff002a188ff00098f1ff003fc00cb4187a1b4a6b3fc00786dbfc005233d50b9b7533fc00ff003fc00ff0032d16ee5f3e179bb87bad271a8519c5c1f04a12097c529d60e7da257a26f046e85a5995419cd174bf87c13ff003fc0066b55c0ae8c8d441b9f1af02050a0005c3900b4741414a8782c9000044c1c1c2008353c181038801aac30441558f06d286c08000420040
  | 4 => 0xca32457542fa7ebc3fc00007effc00f0d83a047d6506703dff003fc00c90732225ad411b8f74012525ec2b8026545ff003fc00ff002f00fff002db49c42974092ff0035dd24a608a90f9e6f8b8ec195d6ee8592c060b225f00f5dd30032b1308ff0024affff000b62fde2427d42432ebc9f093bb6a074f2478f7454e7045cf4ec2ab44efe4c0fd8f0d5a9e435aa556939cf716e0ad5fe490ea09f575137009655d2c5f136cdf656c547e88b2f618131c96646ec8ae129605d5a2f9a34fad3769865de28c09c3299d6d36793871467b706763b40f1673d72a9f2ca4b7a45b22baf5c25e21486c8fb266c4d22be13e207d6e137ddd8655bbfc00a30ffe1057648e4ab3ff003fc00086376c335551f94daf94c1a1b0b45955d1cff003fc00ff0031559c825ccde6ff0025902ff000e4f84ad877120ff003c841a35cffc00c3afdb320ff003fc00f802ffc004a06fbaefd363ffc00ff002262103205d58eff003fc006c69ea84ce8bcad2020f403fc008f5827b14ff003fc00e881bfc0097b95a2138f8e47b21cb0aed0262950ca83c519b32cfc45616b1baae0dbc517cb2cfd4b4857408851b37927e87c9554e9cadb1cb4da3874b24d58d3b6ca49dd215240e50a75101e32e19a41db03a8fc507ed425ac232e7d6ad78a23113b1e00c363e6bc1680c829d1d112d9de7b3c2c3bca01f91ab863ed1f07ec1fd5f177b1d9c5df35a7
  | 5 => 0xc8d3b94b4602b2cc801a154cf0d3e528a044ac25b4d453295391908890e2360da61fb0180345dea83ecad77922e22a3ce563ff002c5fea40aaf7546bc96f92472315aec1cd450a928cd38e654b539dfa8950571a473c4b3ca5c3aff001f70f0021f14322a72d2dc3ff0014a79beccce4dbee377a1b55ab26d5f6313fffc00007d3fc00c332c84be9b4eb68c8d94bbfc007d19ffc00557aacd930853f946d6cc7f8a7dd72e1c8b7020dc9a272f30ea0bcf052540001865fda32ccb15d2d1161e551923c4bc69bd232190b2eff003fc00ff0031f284f8ffbaafff003fc0076c6d8d3da6d8ca5cc12ab66446b37ad9b13ff002d12a8f82015e036905ff35ff00239dc4765bfc00ef00bb230c3463fc00dc6abfc00145c22a51905effc004538aeed7252f7fc007f588108c29685815edb787fc007d15c682ea235421d9a57deda63ff001fc21cd221b137b14f86233db485a6b7ff001405fd169af587c58ec5d2b7dc2bfc00d5cb3fc00ff00299d1b718425fc52d5a4968960c01ec717c655e2a5fa7ea1841d83e7c63e3bf0aeb81e082c9b71e39a8a23781bc2571ab6c68477e9d4f3c4bbd1a98dbce336276288137c7e97252088729584d2a4890f9a7621150405d82c91a8421a92d85b5e4fb175d2510d9af7aa01d5cb61083c6aea719a6f5461e1784d5ddcc75691c32f7f2182e8cde0447ae319a475a6cd4486b858ca5c745
  | 6 => 0x45cc44010454c44019bc63fc003e143996bb6b9c34c01e87e685a5e089cc48ac5f4f161ff001bc4e354fffc0077723fc00cd3f7fc000f253fc00ea663fc009f3fa0c99ff003fc00ff00084a7ff003fc00ff00145b4872c55f43b58ac6d91ff001fa07aa56fc9d55f927e011f867258a034aaffc009f318e09c9dc3a373ae51effc00a0d05f87cff0039b2bcebc6073b6823bfc0093693fc00ff001618692d46058aff00110246eac464ea64034ad54485bda07361593fc00b39568340a597ffc005bd3b6b0975734e34a8567bcc05ff00326df1e70bfc00ed727b629d3828375f61893fc00058676ca6ff0030ad96e39ffc0057067fc00a3d60f1ffff003fc00b573bfc00ff001457604263fc00aacf9009eff0034948a0a6ffc00ff000611ad18401cabb83e640a1974c991aeef7f51d12459ef4c353ed3f69666705be913ac4db2859123d602c3d47a01525c36bc7723c22ef801e8f43471e557cda31396635bda37d2a97920bff003fc00ac7b7fc00399b7fc00e760fdc1fc08482c5888245f08b8c4c4c9eecbd30f8442f1e89e6e6f9d655f38235df0c17c370467f140d3e0d9a54eeca1506bf63abb4265605b29b95f2493e4aa51b3f0ed1d4d7f37338f9407c79e06f45e62de0bf8c2c0f1891e05d343951d8b81b3762db7245cbd57290abd88241efd60a1f3483cbcf333997cf68ce96375b70d2492cb3567401a234c
  | 7 => 0x1dac42b54856b08ad5115ae820dd051090b7d216fa82a9d0552a0aa51131c02e3405c6a017a016f20286ce4ce6465404ce6424402ce6423402ce5cc4401ce5cc2401ce54c4401ce54c2401ce5424402ce5424401ce5404401ce4cc2401ce44c2401ce4423402ce24c5401ce24c4401ce2465404ce2424401ce2404401ce04c5424ce0445401cc5c44401cc5444401cc4823402cc4423402c454c4401c45425401c44cc4401c25cc4402c254c44028e6c644028e6c454018e6c444018e68854018e68654018e68454018e64454018e60454018e5cc24018e54044018e2cc5401885cc2401865cc2401864cc4402845cc44018454c44018454044018238c14028054224018054044014e6c644024e68234024e64454014e5cc24014e5cc04244e5c224014e54c34044e54648024e54640024e54444014e54248014e54244024e54044234e54044014e4cc54014e4cc24014e4c224014e48234024e44c14024e40454014e34c14024e2cc54014e2cc04244e14020024e0cc54244e0485c644e04858234c58024014c54244044c5402401485cc2401485c244014854c0c64485404401465cc24044644c4002464402002445cc44014454244014454044014444044024444044014254c4002424cc24014248c14024244c2801424404402405404401404cc24014044234024024c24010e64854010e64454010e64444010e54044010
  | _ => 0

def word95_2 : Nat → Nat
  | 0 => 0xa7cbe5ffaba7cbe7edf37c9fa6f9fa7d9fa3fabeafabeafbeafabeafa9f6bd8fe3f8fe3f8ff7cd7a7edf33eabf3e8ff2fcbe3faf72f8febecef3b8ff3bceebb8fe3faee3f9fb2f8ffadbf27d9f7cef3a7bbbbaeabbcebbbce9fa7ef3aeebebced7aeebbbeae3eafe3eafabeb7afa3fabe3f8feafadebe8fe3fcef3b8fe3fd767d9f6b7aeeb7aee3faee3f8fe3fabe3fc7f1fc7f1f8febdebb2f8fe3f8ff2fc7f1f8ff2fcbf2f3fa046140106815750269a048b416d28369504d2a0073409968232d0265a005b408f6812cd0263a02c74018e834c50571a0b894196e81add06d0a004119452224e5077ea073641e6a83d34644f988df4143a2252464bb9899d40062703b4e04da0093411268030d0161a00c34187282155052aa023940ca2829450142a088540d76810b50592a041540a42814b5048ea0959386b242d6504aca031b381b68236ce008a08964192a8345504a120ca92155681425004788a8d1151e825cc45b888b5540aaa83ca505a8a055141d7e800348506a0a64418968061502b2a0ae52144a42abd022fa045c418b8833c48578a08452148e8391107c090b0d4115e8102485049ca3f4147a82d84447c90af94109a4293d0402a080540c0a80665029ea0b4641dec838050400a06014000483e4502b708b6c116de82db5056690aa1415d4839dd033ba046f40cde814150735a046b41e0283e550488a09114
  | 1 => 0xe4412704106818e08100000c3161e1822302080000204102180488a022008214047000000507080410006401060811312182c00010040080822d448893102204418730c6144298410860cc1082104208c088110220440881102600bfb7c0f89e83d1794ee5d8ba9742e65c8b88710e25c03816fad45a5b33636c0978aea5b2b41692c0582ae955298530a65492814f09e5382704e49852c2594a2925212304628a1152184308650821042084504a013f6784ec1d93a0740e99bb340684cd9842c4548a1131254468849011f23c0780f21c4340688c91822e4580b01602c0580b01622a450899120244448801021e4380700e01c0388690c01842d04809012024048092100208380700e8148200400840c81002202004008012008303e3dd10e0f81f03e07c21c4383ea1da2844aa63d412c0e55663c12fa097263c2181f03e07da03cf78310c22c438860380f90c80007c7a80003e2120f9009ea1208f5252344321980e066000071f508fec4fab3501c0000f81f7869d80f81f39c07c0f83301c0382343e0660009a34575411f37baa11611e237af26811e1e446f5ed15d53aa08fd15d500e000039a29672cef3da2847800d141983e20c10c0f81f03e07c0f84308610d3db9c03e10c1f01f06607c2344787c10c0f81f5a89eebe8fe3f8fe3f8fe6f9fabb9be7b9fabb9ee7b9f67e8fe3f8fe3f9de3f9fbeafaa3fabe3f8ff
  | 2 => 0xda767304f2602bfc0096580a5852a26f0e8c535c7e06d206cad674ff0021cadf20bf0d385f3c3fc00860e36d110e06ffc00962d2ad3fab5e6b07c4467668bcad4cabd7beb08749fbe6a26e90b5e436302da41c3a0fcb2106fa4c7f96c291bac5156d906b8f659748a537a4b1d43a2c91ecd2bb7d023729f1d4af87bc2d9c77804c9429e2beb4548b2942ce4694f2a11db6158b066ff002c89e982580831bf62af1deb89635931d46248c1da923c1e8a2f91c795867264ac572458dd104352a44a4dff003e99e1c76fc24b9c04a157f8a1ec513b200f3fc006e8750a538c17ae17090980848863492f999a74bb04ab4024dc5d15e32949034a5ae6d2c243b28a6578503dcba1944bfc006e7363da01e6570e85c3253fc00ff002b9096d3745dddff003288a335d4d2716f1b99209f7312bd8d1c9a6325acc0acf1bf24061b40f2c469f14e965dd3a87c00a265541055b0a8020577fc00e603bb550b9a0ab968f447f05b74a438f1a5b01115176c93c87a27a71f79617248d4f830ff002a58cff0005cc39c04edc3339608e0a6060c68412040150e0c9121a18092b8043010604cab4a15ca556048800d440040068482101c1030f24f0200040352025111000000100014240200b93023091c10340020a711140218f820610300022421200104331204303124858104080080a603018268f0906740140a1c095043810110145000
  | 3 => 0x3ea4c046ba185a5d5999a497d295e331e11e371410a73015ac856624044f99b05c0625db75ce0f5a33ce96791425c89fdec456a239c0948c953263d88e7a2816cdc82331722a23356ee828fb199cc42ad762ce1f2ab4305e73b165b65cbc0047fc00566a2027b2053184d5c55213c73d46d7058fff003fc00ff0026a68ff00195b3ff002c0efff001aceb3e6606cbbff002240841368dd938b188688cdd1bdac770b4b5b615ff003fc00ff003901607407fc00e2453fc00ff003fc00ff00135b06134c39917598ba129e104190d17c17eb9df060d7fc006f41ca14bff00380f70d027fc00ff00308f862913fc0059907fc00ff0035a7638887fc008b3508e64864674256994d06050ff003fc00ff0019465ff00361c9ff003fc003914c1d51ff003021b453f900cbff003fc00ff003fc00d09dffc0024363fc00ff003fc00075faa48bd59f3fc00ff00358145d5cbfc007095129626f57d38c78a0e9247a2c3835d18d3255b48d436208455ff003595bff0007e84ff003fc00ff0004994611a3fc00183a7640bb628d2a5cc42f7cc76d854bfc003e49f20800551bd1135a054f648634149219034cd8dacb82e37c27189c028a4c9183a01e205b96d00a88bbe4c6e034bfc008b5f1ee37d939a909ddb2b3fc002a123fc00033f7fc002e8fffc00f6073866bfa7ea9dd5ff0008d92ff001d1e3ff003fc00ff003fc0008611a851
  | 4 => 0x6243eb693fde7f1e0e721f68b70c2a0fed3062cb6756a9983695081b801146a6acee675a859ebf466b81b48b69abdff104e96483383654e8807335f1edbf423b4432332190ed9f47071105b9b6ba4ac74bde607a356425a7a168d1dcff833ac8e5c0282ec987b0dd2071ff001dd37cd07c8986054187c29625a74046977d7fc00f49e0581a876930823117bbfc00484c16dc7d901d4e2bb92abce59d93d15c86c02fc85b16598f802c680cbfc00ff001168dff003385293177fc00b54831a29ff002a84aed1ab8147ff003e0ffff003fc00704953879294a85e7dff001085a876dbfc00ff0039cb2837d0a68bc26f4887513557fc00a179828fb7491b8cb5ec58499abff003fc0070138d0b7c1597cc4262a040d83273855c22649a91ca19633ffc00829b85dd31b19348ea130f7a52172166425e882135df3ff003fc002b6b795a220226f980ff0017935be6bbfc00419b0d472f65937d169b1d12ddcf12cc10c9ff003e661ff002f97ac4207ad5c6e7c7fc00ff003fc00611ff88a87f8efc96da65be64a2e53899d9b92035155a0a45e3a83ce21dd891401034058d88b2844c1348e5936db0bbd10fde03149ecc41349e05f54f92867f967d786c8e095662d0a8c56249ff002dc6bd8309f157886060c3bb706569f0d730068782711491c5268cd9d67ff003927edf2fb85289a53e360d276866d8e4c23aa6453a37885c1e0
  | 5 => 0x804005fe0078d8edb544bfe027a87f803d83e935e098f150d9d4eff9489a04ff017c518e9ff800157d71d0c6ff805611fe03fc0174c620b3e2414938271742152ffc00e0298a48e38322ff80ff01048ffc07f80ff00013f594a10bff00c327b8352adff01fe01a40c4af1f66884268bb6b53818c0295ecc8d1aeabaeefa07e7036e6fac5811ce0d75c0edc77fc003bdff004001c61fb9f14633468200880d0241b100651a80539ce739dcd62c6318e210850000009028a447a8d37d446812529e56cae95d3e23d5aab556aad569ad552ea756aa9d52ea1f4aea574ce9d5aa8d23bd216d20cd20ad21ad27352445254521352394c594c49d26192874c47d247d26d52825220524052305205d22ce08e64454015054e34c40025054644c40025054644020025044e14020025044254c40025034e14020025014e54c4002485404cc24014644c44020024254c44020021064854044011044e1402002045ce24c4401f63c7fc005d80d8cb04526848c5ff003fc006b7df312bb11a4cc7e91330a2116d84fc9447379c8e8e1318f2d73589be815eff0032e1ff99ca24035724934df043421cdb164998a5f8338fdcd7540d3fc00cb0ff353dca11d4a57909d789226652764062159831392261c316cff000449fd190f6997e1507fc002b35b749c877a604e7ff0028c4b8f50e4c61d58bc65af6f82dcc249c1273c26ed9559e4e252e
  | 6 => 0xff0293ee939d5adff3f50f2adbea8ed2d66e7b3ff07f83fc0425ff050b438fe43ae0960000000001345351255255915915155154b50dea09d479a8f5317262fd441293a4ca069c2804005a48a069c28040052502089c2804004a4aa06988804004a4a8c8988804004a4884a988804004a42a0a988804004249a0c9c2
  | _ => 0

def ax95Words (i : Nat) : Nat :=
  if i < 23 then (if i < 8 then word95_0 (i % 8) else (if i < 16 then word95_1 (i % 8) else word95_2 (i % 8))) else 0

def ax95Count (k : Nat) : Nat := match k with
  | 10 => 1
  | 9 => 5
  | 8 => 73
  | 7 => 217
  | 6 => 164
  | 5 => 23
  | 4 => 8
  | _ => 0

def ax95Path (k : Nat) (i : Nat) : Nat := match k with
  | 10 => 0
  | 9 => readCompactBits ax95Words (8 + 12*i) 12
  | 8 => let v := readCompactBits ax95Words (1171 + 16*i) 16
    (readCompactBits ax95Words (1063 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 7 => let v := readCompactBits ax95Words (20729 + 18*i) 18
    (readCompactBits ax95Words (19289 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 6 => let v := readCompactBits ax95Words (65188 + 19*i) 19
    (readCompactBits ax95Words (61372 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 5 => let v := readCompactBits ax95Words (87964 + 16*i) 16
    (readCompactBits ax95Words (87292 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | 4 => let v := readCompactBits ax95Words (90569 + 15*i) 15
    (readCompactBits ax95Words (90089 + 60*(v >>> 12)) 60) ||| ((v &&& 4095) <<< 60)
  | _ => 0

def ax95Live (k : Nat) (i : Nat) : Nat := match k with
  | 10 => readCompactBits ax95Words (0 + 6*i) 6
  | 9 => readCompactBits ax95Words (68 + 7*i) 7
  | 8 => readCompactBits ax95Words (2339 + 8*i) 8
  | 7 => readCompactBits ax95Words (24635 + 9*i) 9
  | 6 => readCompactBits ax95Words (68304 + 10*i) 10
  | 5 => readCompactBits ax95Words (88332 + 11*i) 11
  | 4 => readCompactBits ax95Words (90689 + 12*i) 12
  | _ => 0

def ax95PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let v := readCompactBits ax95Words (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax95Words (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 9 => let v := readCompactBits ax95Words (783 + 12*i) 12
    let n := v >>> 7
    let bits := readCompactBits ax95Words (103 + 8*(v &&& 127)) (8*n)
    compactIDsFromBits bits 8 n
  | 8 => let v := readCompactBits ax95Words (13156 + 16*i) 16
    let n := v >>> 11
    let bits := readCompactBits ax95Words (2923 + 9*(v &&& 2047)) (9*n)
    compactIDsFromBits bits 9 n
  | 7 => let v := readCompactBits ax95Words (39942 + 16*i) 16
    let n := v >>> 11
    let bits := readCompactBits ax95Words (26588 + 11*(v &&& 2047)) (11*n)
    compactIDsFromBits bits 11 n
  | 6 => let v := readCompactBits ax95Words (71473 + 11*i) 11
    let n := v >>> 8
    let bits := readCompactBits ax95Words (69944 + 11*(v &&& 255)) (11*n)
    compactIDsFromBits bits 11 n
  | 5 => let v := readCompactBits ax95Words (88669 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits ax95Words (88585 + 12*(v &&& 7)) (12*n)
    compactIDsFromBits bits 12 n
  | 4 => let v := readCompactBits ax95Words (90785 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax95Words (90785 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def ax95Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let d := readCompactBits ax95Words (843 + 3*(i % 4)) 3
    let off := ((i/4 + d) % 16)
    let v := readCompactBits ax95Words (855 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 8 => let d := readCompactBits ax95Words (14324 + 5*(i % 75)) 5
    let off := ((i/75 + d) % 270)
    let v := readCompactBits ax95Words (14699 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 7 => let d := readCompactBits ax95Words (43414 + 8*(i % 249)) 8
    let off := ((i/249 + d) % 887)
    let v := readCompactBits ax95Words (45406 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 6 => let d := readCompactBits ax95Words (73277 + 7*(i % 197)) 7
    let off := ((i/197 + d) % 702)
    let v := readCompactBits ax95Words (74656 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 5 => let d := readCompactBits ax95Words (88784 + 5*(i % 21)) 5
    let off := ((i/21 + d) % 80)
    let v := readCompactBits ax95Words (88889 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits ax95Words (90801 + 5*(i % 6)) 5
    let off := ((i/6 + d) % 21)
    let v := readCompactBits ax95Words (90831 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []

def ax111P : Nat → Bits
  | 0 => 0x2827af610
  | 1 => 0x2177d99c40
  | 2 => ~~~(0x118611d7fe : Bits)
  | 3 => 0x514e3248aa
  | 5 => 0x503805e3e4
  | 6 => ~~~(0x537a7aeae0 : Bits)
  | _ => 0

def ax111Q : Nat → Bits
  | 0 => 0x10270d000
  | 1 => 0x5a7c99c00
  | 2 => 0x3a790e2800
  | 3 => 0x5048324028
  | 5 => 0xa100422c4
  | 6 => ~~~(0x7b7b7efaec : Bits)
  | _ => 0

def ax111Perms : Array (List Nat) := ([[], [33, 48, 101]] : List (List Nat)).toArray

def ax111Words : Nat → Nat
  | 0 => 0x44808807fe07f81fe07f814b4b7511e60eab6e77ac51eed608f31a4a016d3102ae54d016c4a3be60dc7333e37f800c7ff81705a6421ac7f81fe02739ca3ff81fe03c2f18120ad269f5c05a6b549473b8cc56f07874a8d00bad2b82428000718c6018002229f8b78a9cf16b3d8ef5c3d527513d2734030e8c3434b6a289c94a203466d134828b04a4006056d87342869d064a92865e543c0c7d42013256926a70269256014e7f32906c705e54682a523c360c0142887e304c06566a866c2654685a53a07f6f424c0670926a3c0c006654596ea08532305054063c260c62509b6f4e93422e824a4a7e9088928704546426066202500b682ebb2b3c924aae3d1aa08512ba7e2606873564468a4a920adf65354f29a4d0947c928090883833983b2810342d392c2691982606884a0c829ade9134527f04d0de7c90869280828c269200912c80867030203c0088852c827c0104de84d07c8e9291a880828c3c260c928e8166354f3482047c2422160e201e18d000122892e728bc04820cd00c92260086bb2884047c704a3c8886842c047ddf7f7f7f777f7ff7dffffff7f7ff7f7fff7ffbfb7f9217262e4c3c985930b260e4c0904aa110c2234857888d111a023cc46988d00de6054220844130a11200511108901100d004b6ff289ff3fc64c839c056d61b8547940601251bf26342a590e129e0125486267df827d03fff8444223f
  | 1 => 0x7f9fe0cbf5ff806140002fc650c92002085cbe31c503c21d9337d41120f10a84a88908898680957c17c7f8073bfe0ff07f83fc1fe03c6f757b0fc883fb8002647910f88fb07b5e63aa167f83fc0a923ccfc2b157fe03b9ff81c1c5c63e2ff8052dfe08ddff82c523202e508c0067d875d68c5c557552e44c38c2c329d1cd0f30c309900158a89030361242636c010f7e6c2720886854221c4f00246c2f049df91104872410d0a8409e591178df911048435efc8843a425c873217204eb85468fd1243281e04b2d00124de7d3d9c8f85d21d2cc2250f1bc9238142247e131f01a5a1e001c8927c3c094647c390e1123f09cb47c06171e09261be1f08a0194974064312d20de491f90c8843220fd4e132210452e1e10fc87afb5f2ed779f7ddefd3fbfcffddbfdfeada42e4e4890b1392270a844a9c75382c7354e6a9cc2110c7310e6e88998884510a88908880704a88898708898680890a8
  | _ => 0

def ax111Count (k : Nat) : Nat := match k with
  | 10 => 1
  | 9 => 2
  | 8 => 21
  | 7 => 15
  | 6 => 2
  | _ => 0

def ax111Path (k : Nat) (i : Nat) : Nat := match k with
  | 10 => 0
  | 9 => readCompactBits ax111Words (8 + 12*i) 12
  | 8 => let v := readCompactBits ax111Words (422 + 15*i) 15
    (readCompactBits ax111Words (338 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 7 => let v := readCompactBits ax111Words (4257 + 15*i) 15
    (readCompactBits ax111Words (4065 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 6 => let v := readCompactBits ax111Words (6613 + 13*i) 13
    (readCompactBits ax111Words (6541 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def ax111Live (k : Nat) (i : Nat) : Nat := match k with
  | 10 => readCompactBits ax111Words (0 + 6*i) 6
  | 9 => readCompactBits ax111Words (32 + 7*i) 7
  | 8 => readCompactBits ax111Words (737 + 8*i) 8
  | 7 => readCompactBits ax111Words (4482 + 9*i) 9
  | 6 => readCompactBits ax111Words (6639 + 10*i) 10
  | _ => 0

def ax111PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let v := readCompactBits ax111Words (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax111Words (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 9 => let v := readCompactBits ax111Words (256 + 10*i) 10
    let n := v >>> 5
    let bits := readCompactBits ax111Words (46 + 7*(v &&& 31)) (7*n)
    compactIDsFromBits bits 7 n
  | 8 => let v := readCompactBits ax111Words (3001 + 14*i) 14
    let n := v >>> 9
    let bits := readCompactBits ax111Words (905 + 8*(v &&& 511)) (8*n)
    compactIDsFromBits bits 8 n
  | 7 => let v := readCompactBits ax111Words (5796 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits ax111Words (4617 + 9*(v &&& 255)) (9*n)
    compactIDsFromBits bits 9 n
  | 6 => let v := readCompactBits ax111Words (6769 + 8*i) 8
    let n := v >>> 4
    let bits := readCompactBits ax111Words (6659 + 11*(v &&& 15)) (11*n)
    compactIDsFromBits bits 11 n
  | _ => []

def ax111Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let d := readCompactBits ax111Words (276 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits ax111Words (278 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | 8 => let d := readCompactBits ax111Words (3295 + 5*(i % 14)) 5
    let off := ((i/14 + d) % 50)
    let v := readCompactBits ax111Words (3365 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 7 => let d := readCompactBits ax111Words (5976 + 5*(i % 9)) 5
    let off := ((i/9 + d) % 40)
    let v := readCompactBits ax111Words (6021 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 6 => let d := readCompactBits ax111Words (6785 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits ax111Words (6787 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | _ => []

def ax127P : Nat → Bits
  | 0 => 0x260b9184111996d02408b689d8f65220
  | 1 => 0x98e46469c022690e333b26610b480c44
  | 2 => 0x72805010179c8402c3c373a465148103
  | 3 => 0x4ee3c022840012adc6c5c8e81882088
  | 4 => 0x5d1bc92040a328857c94883e36028164
  | 5 => 0xc374824fa00052118bd40151d4216c10
  | 6 => 0x99112a900e4400650023c9522ac1129b
  | _ => 0

def ax127Q : Nat → Bits
  | 0 => 0x202148a090291502408340188905020
  | 1 => 0x104000088512394c222b226109480804
  | 2 => 0x1265c2602834243a445048002
  | 3 => 0x8c2482684484b254445c8c80800080
  | 4 => 0x4d014b2440a140a15894881a32020140
  | 5 => 0x308225020942008990011054202410
  | 6 => 0x7000010080a0080d0021804222410209
  | _ => 0

def ax127Perms : Array (List Nat) := ([[], [65, 50, 80]] : List (List Nat)).toArray

def word127_0 : Nat → Nat
  | 0 => 0xc531a531a431c331a331c231a131c731a731a731a129e729e719e70d2235213567356735273527352125670d670d270ba433a233a133a033e733a733a733a223a023e723e713a713e703a7012431233121312031673127312731672167116709270b233321332033673327332733221b201b671b271b271b67032700a530a430a330a130a030e730a328a128e728a020a118e718a70824304330233042302130673047302730273020206720201827182718211067102710271423413403223221a13212211a11203202a02201a01200afc7fc1d4d0aedeae5afbba76e7b9e909fe066c3dd9acbb02ff07f83fc0199d70e0ccb19fe0ff0048cb53fe02daff83ca8be6aadefbc2d00526107f8081008038574279a548261dcf2e6b92ca146280739418b09503b00d680149413124b49c946c08811904b49c9468803949291cb4948c0860a1086904b4948c0c9a387030282018100924b49c948c68391030282018100904b49c948c6a3038e03820181008c8b830c2094c9c948c6828b1f134948868d8109838a05828084900201031ecb4948c6898192c9c688008d089e1249c8c0888c86838181021d91c9c8c6888c009d11494088060b8983020105040083829c90cb49c94688018703820180901c49c8c9010b07ffffffffffffffffffffffffffffffc23223413213403203202a12202221a11a01a11201200e159460c07f
  | 1 => 0x64f2b941c0d08f1881c2606a130e5729938c0e127935094a303829c248d932394a303829c260d052991b29101c65726478194a300700810065029e4c703dca4621c94848820794c9c6128380380c0401520132a4f2964c703b8c439246a84a84763cc9a4a303829c260c53490f0403bcae4e0a5888c6147941c0e868918c2520620834132a91ca460d638498ea143848c60a47a8341608521c0e8401248e521d0a8c1afff7fbfdfeff7fffffeffffffdffffffbffffff7fffeffffffbfdbeff7fbffff7fbfffeffff7fffffeffffbfffeffffdfffeff7fbfdff7fffdfeffffbfffeffff7fffdffff7fffdfeffffffffaffffbfdfeffffbfffeff7ffffffdffffffffffffffdffff7fbfdfff7ffffdffff7fffffeffffffffffbffbfffeffffffdfeffffbfffffff7ffffaffffbfdfeff7fffffffbffbfffefffbffdffff7fbffffffffffffffd7fffffefffeffdffffffffffffffdbffffff7fff5fffdffbfff6ffffbff232f272f2727271f270f2705a335e72de72da72de725e725a725e71de71da71de70de70da70ea336a32ea22ea72ea726a71ea716a704a434a434c334a334a334a234e72ca72ca724e71ca71ce714a714e704a7062436232e272e2726271e270ac532a532a532c432a432a432a332c232a132e72aa72ae722a722e71aa71ae712e70aa70a213220326732273227326712670c22346734273427346711
  | 2 => 0x3264e11e3e7a958d1620d05820471f95c98ec9e238d40d1b1323e4c779582c68d404018080207cae4cb0461de3c471a89c160903cae4f1e238d0ee0a46cae4c471a1d93e0b041d91b1f13cae4c470327c6a130392e4f1e948d0ee0d0492e55238f8d1ac7709834164b95c9a36343b828f32b934846876589e248ae3ac1c389e2289456325eca60c8e3a1a08a3315894488d941d43a331534e5306228ac64743a23c64451529134a43a23e0e25941143a33152684074828cc561c574924a1c3a91285783b8913d05158c94a7924c1c5525191d0f232578a8e89a3a100f30692874662a699265103198a8e8703a8ca262a572941a090c4d428926c82988731265657298f10ced3b072be62139482920726b3d412070a829886d12260e72b8f10ced249d8615e18393541c6847893233194caa3443052b9e80e060200c04012301731948963c42393ec220f06826632b94c78847304862788862338d46c3984a758b23cae3e25054926a769d50430cc9f2140e0a351a0e51b958930e479484a68f49d8498a4795ca63d34390382c0a03030224798ca144a8391ee3e2495860e60a351a0f11b95892f54b0949268f46c848820f98c7a48c595331a87293cc0e0750aca234ae7a873247093ca122307a829847057294eb2b938724a310451c260b0330a4870a1cac3b273a2794a09182f0d0719587651230435460f4a184c1a0a0f07
  | 3 => 0x71a95e5729934690628911f65280262a1461f1d4417e1f15ca64cf6268ec107c3e884584d1d82148a30f8a9447d948864c4c528ec122d28ca246091d1f26a0d044ba87283dc7a74fb0d4d1b216494bc1a0a371ee4d9594c7c5a089d3e8520f0881c18270b82e632993c78f46e4884c114308cc0f71e923ec3617051b8d87a4cc9c5b1f0449274fb068584209081ee63298f52992130d83c0e2b0b1e9a8c908cc6508e8d8b64d913f28414f88dcc65142501e9473046488f72848281f61308829182048c7c573194c9c34a07d4ec2606978410940663243644a14d42c7b94c9b0e7e5082a7ca69d1026b2993c79f52e3d36424410883c57318f4964ccc6a1e8821198ca64d1a7d338f4205412c4e38883544f2a478940e386a088404b1c81928d712cae3e271c81894f71c81894a84fcac4f1f12129509f1c81a3a44a14a0fa39033dc4d1b1c81928d48f278832b1329c4a071c470f0751c2a40d1a57878f0d693c9e0c911329cf8491b3d0d4963c89e54489187a22373e2c0372783ca91c78341246e2684231a4791363e57262487a227d1b2c65727833d892363cc98f08f838d94cbc3c23c384913cae4f06348d97a44a11f8f236843da221c3d46191083c9364d7d3e89a2a365029e4f072649c6cc43c358821f95c1a44c91b348f0743c4896236532ca210b26cae4d091b1e64e223b1e206365829c260a94358ed93038992
  | 4 => 0x32a97b2b8348e60d5943211c742bc1a44a655239490e86421ab3195ca64d04471c11b2681299548e528441e0d03122504f98ca64f1f09244164595c991212603541e0d05822693195ca64f1f0324c261107122504c2813e632993c7c0c910883c144428168906625cc63c6395c9c105c668441e0a26350904598ca64f2b0323c1a0b0481a684223cae531f934c11853068226842234ec272b9434e4f1e4624c1e0d058240d349d4c6572993c791893094cc1c5303118873193ca23d26468441e06244a0844c29118a04f09cc653278f2411a1107834160798ca64c9c462463d290982c104622108c45109170b4482c12e57278f492748d0814c1a082411e632b8fca2448d0883c144c21148904509cc1ab2993ca9188f0682c12069a4ce572993c7a608d06822688309249e72b94c99a71e99234260f03cc653278f4a1181708232449093cc6531e7d84413318f49654d3933311a1104161d92509cc63c7795c99a4fe468441a0998ca63f2a91234220f0682c0f319446e572667234220c388491f3195ca64cd28d2347a0d0581c6cd5192091e111aa1b20ab94c9e54530747c6008030100637198c0180e05cae53278f23104531a83c1a0b0481c6e3519cae53278f149060d058240e37192342235078c124f395ca64f1e2920c1c8d0682c1236418c9272b94c9e3c53038d47a11068246e579548e531e6b20c7a1308834160
  | 5 => 0x19d3197498e31883981a16d4165895481447935512ba117a10348fa80ea78db60cf48c640be68b180a15896688948803879407170636856404e783f50356828481f4816400e700091657064489180d4284e269329714e57298fc1c4892291208c4d831463f319430c489029130a05a2419e631e2318e570712161985226cc0932a6aca60cd11223a1d0a83120a44798cae531f12230984a30138c4502f170ac442dcae3c489d84c49249b106531f094d17d389aca8ca2594c7c25365f21c489394c795d35092a043319449e3e1254259531f98ca0c0a11284a4c7e48cc24f298f848d4be20cc63d25093f97f3195c7a485f1284998be25176631f1249424fe54cc6511b092fa3b3195ca1a057098919c744789663282246c24a821170b04b93c18f22d0e4e88d369d2264d33838b48cce9d2c0d486c4ca2461c868b26e449d4da644229ca64f0716871245225118a04398ca64f064813c385236108cc5c2c12e6327834945a1c23148d44632178a84b98ca60d2316870850c821488c4398ca64e2d0e230a52624139a8d798ca64f06472411c910f4a1f0f429138884395c1e4d247c2389c4c21188a0442e168b04a23c9e0f2a924e91c8e20c99489f83cac39249d2f15c4c321809c482bcc1ab299548a208e9d87a6d3499cae5327834b91c8e9224e4f06a0299fc7d93c1a54aa7a2394b2b98c9e0d247c238f08e2dc9e0d245
  | 6 => 0xa584b2d2db28fcbca0503adc552a41258e98626539e3206bfc00eabb706a6805e9e9568719464fc4ca746865074500ff8026c737a8242a5aea27988c133add2d30ba3043cf6da4608a39a430c4dcd7a777d3d4684801a6a6490f6ad6c5fd0e0eff003805ace234b2864211e990b57400c7d29f0608c34fc353634aa16c67664eec85287e5c120791ea28c7228a983445cbe6601600028002c8002a0028000664823e041824060a800a086900410111000440d1000303000c5021e2410000041a804089a82a5ca0000000801c040001e4420010683010e080010a182830400a230a2c080000008600701030e0028006082893f67675b674f7f405f35672997173f1057064efd46f54eec4ee33edc4ed34eca2ec54ebc4eb35ea84e9f66935e88667c766e76605e556649364356398e285e1d760f5e0445fc45f43ded4de445dc45d455ca45c26db545ad65a175938d826d756d687d5985495d3e952c751e9d0b64ff84ef64e374d54ccc54c254b874aa4ca164956489ac74946274549c41843164256c18640c4c0343fb63ef33e953df93cd83bd43b573a75b9cab873b804378736abb534b4a6b3d4b343b2d3b263b1f43172b124b09430132fb52f13aea6add62d152c772b93ab23aab5aa03a9982893a8252783a7142694261924f5a444a3b722d4a24421c6210420849ff49f641ee61e249d941d131cb39c459b941b171a33
  | 7 => 0x3d8676855cb3ca117906920825dc86d4c33fc01e6e6483bcbd57bea4de73920c124b3fc01231d4ea3961b50de352afd7098c13bfc00530163817f803fc01ecf8ff002009f8545fe00ff007f803fc01fe000f5c5f027fc01fe00128a730be0141fe0083a27f803d92bfe00ab688eaf4353648ceff007f802856f212e6ba6ff803c5da9aa7ff007f8017d01fe00a341af03cf4cf5a456499c998fb153a42c0b20aba45bcb2ac88e614b707fcdbc9a7ce39b9c8ec1c9e412b9e3ff2b4aa9e8f62e6897d4b2c7db80e2118757ac579672a4d355408f9d86a8ce62b4461d3a34ed9a1c84ca168fbed4420f342490a5e497889a38497879c690ffc01fe00a58b554fd9627312dea6b7f803111dfe00ff006347d75b3fe003309638a8e5ea949c012bdd1335915ce78ff003429aa1c586ddff007f8005588d69dff007f803ba4dc2530a1945ac2352f4e54068d2b1d7fc0121092339298f03d83fe0057a1a50d601631a1cf503cb2e7fc01763d519813c0c7aa0094ced4d7f80182a7fe00d101c8341708fa8dbff007f802f4fae89e9b51bb2d3fc00e46eeaa2ae2b3fc0034b34d7664ca7fc015ec61d2ede911a21f5d4ff38b8eaaea8d81d0091921538ffc01fe0096188415b9cf7fe00b15fac3a6340d77127f7c9219b6a31e83ead11394e39d65069349914621e819fa8194b704646ed5ef3cd52ba741832a9b0bf23ca62dd3fce95
  | _ => 0

def word127_1 : Nat → Nat
  | 0 => 0x484d9c48499c48479c480d9c480b9c48079c48039c288d9c28879c280d9c280b9c28099c28079c084d9c08479c08451cc8091cc80314c80d14c80910c80d0cc84d0cc8090cc80308c80d08c80908c8029cc8869cc8489cc8469cc8449cc80a9cc8089cc8069cc8029cb08c9cb04c9cb00c9ca88c9ca84c9ca80c9c908c9c904c9c900c9c884c9c880c9c708c9c704c9c700c9c688c9c68449c680c9c68029c504c9c484c9c48469c48029c300c9c288c9c280c9c28069c28049c108c9c104c9c084c9c08469c084494c80c94c80894c80490c84690c80c90c80890c80690c80490c8028cc84c8cc8448cc80c8cc8088cc8068cc8048cc8028cb08c8cb04c8cb00c8ca80488c88688c84c88c84888c84688b04c88884688684484c88684c84684c84484c80c84c80a84c80884c80684c80484c80284a80884a80484888684680484480280c84680c84480c80a80c80680c804808846808804808802806844806802b652cb52cb8a23cd187350445d64f5267664e4766141bf47cca7838ff00501bffc012e1d4d87474d33d3e0c05260db405436178e58ff001d172c804fb10592f8bcab5e41920a7e3802266f1d6224a7d8524aa1546ffe005005ff802896c8d3169a007b843a82c3058335a4c23fc016608ff007f801d143fe009c437118625dc98e70a7d3837c346d3600ff0010bdbfc01fe00ea836e013fc00422057571689
  | 1 => 0xa0c87a0287a00cc8cccc84ccca0ccca0667a0860a0861a0660a0460a04609c261a0260a026120e60a0e60a0e56a0456a0e49a0848a0849a0249a0248a0249a0e48a0e2094c208cc21a0a20a0a21a0620a060a94c0a90c0aa0a0ba080aa060aa030e84d0ea0b0ea090ea070ea023e84c3e80c3fa0c3ea0e3ea0e1a84c1a80c1b9cc1aa0c1aa0c1aa0e1aa0f0284d0280d02a0d02a0902a0702a020694c0690c068cc0684c06a0c068ca0684a1684c1680c179cc17a0c16a0c16a0c1680816a0eec80ceca0ceca0aeca08eca02708ca71a0855a06bca04bca02bca0e4690c47a0446a0447a0247a0247a0eb6a06b6a02b6a0e1e90c1e90c1f0cc1e8cc1e8cc1ea081fa050c8cd0ca090ca070ca04c8a08c8a04c8a02c8a00c8a0ea7a04a690ca690ca68cca7a08a6a08a7a06a7a04a7a040490c050cc048cc0508c0484c05a06f890cf90ccf88ccf908cf8a0cf8a06f8a040090c008cc0084c019cc009cc01a0883a0c83a048290c8284c83a0c82a0c83a0882a0883a0483a04148cc159cc149cc15a0c14a0c14806de8ccde84cdea0cde808dea08dea067ba087a8cc7a84c7ba0c7aa0c7a8087ba087ba087ba087aa087a2087ba067aa079cc8879cc8499cc8479cc8459cc80b9cc8079cc8059cc8039ca88d9ca84d9ca80d9ca8099ca8059c888d9c88479c880d9c88079c88039c688d9c684d9c68459c680d9c68099c68059c
  | 2 => 0xe4ca0eb890cb88cab8a0ab8a08b8a06b8a02b8a0e2514c2494c2494c2490c2490c250cc248cc248cc25a0a25a06ca8cacaa0acaa08caa06caa02caa00caa0eaba04aa94caa8ccab08caa84caba0aaaa0aaba06aba04aba04aba04aa204aba021d08c1c84c1ca0c1ca0f0490d0484d04a0d04a0704a0504a02ee90ceea0ceea0aeea04eea02d494cd48ccd484cd4a0cd4a0ad4a06d4a043da063da023da022e90c2e8cd1a88d1aa02b5a04b5a0cb5a04b5a021888c189cc18a0cda90cdba0cdaa0cdba08daa085fa045fa003690c37a0837a0836a0837a0e2c90c1290c13a0812a0813a041320e12a0f16a0916a0516a00b1a02b1a08b0a08b1a04b1a02b1a003284c32a0c32a0e0890c0884c099cc089cc08a0cfe90cfe88cfe80cfea0cfea04fea00e684ce6a0ce6a08e6a007da02ce90cce84ccea0ccea08cea0469a0459a0458a044ba084ba084aa084ba044ba044aa044ba002290c228cc22a0823a060c90c0ca080da020ca0310a0910a0510a02a9a08a9a04a9a00a9a08a9a08a8a08a9a04a9a04a9a02a9a00fa84cfaa0cfaa04faa02e08cce084ce080ce0a0ce0a08e0a02d290cd2a0cd2a08d2a0473a0873a0451a0051a0e2a8cc2ba0011a0514a0714a00afa02afa06afa02afa00308cc3084c319cc309cc31a02028cc0284c0280c039cc029cc03a0c02a0cf284cf280cf2a0cf2806f2a0087a028684c87a0c86
  | 3 => 0xa96a008c8ca8c88a8ca0a808ca8088a80a0a6c8cac088ac0a0ac0a0853a0852a0853a023a90c3a8cc3a88a3aa0b08a0908a0708a0508a009da0693a0493a00f4a0af4a08f4a04f4a00ea90ceaa0aeaa08eaa06eaa007fa00d090cd0a0ad0a08d0a06d0a046ba044094c4090ca08caa0a04948ca94a0a8a8ca8aa0a7890cc6a08c6a04c69c2648ca64a04c28cac2a0ac2a045c8ca5ca0a5da0a5ca0a5da045ca044e90cba8cabaa0abaa082894c2890c288cd06a0906a0706a0506a029a90c9ba089aa089ba069aa069ba029aa02fca0afca06fca04fca029094c909ca90a0a91a04f094cf0a0af0a08f0a04f0a028494c8490c849ca85a0a849c885a0884a0885a0285a00e490ce4a0ae4a08e4a06e4a02d894cd890cd8a0ad8a08d8a06d8a047494c7490c749ca75a0a75a0a74a0a749c875a0875a0874a0874a08749c675a0675a0674a062690c26a0827a0626a0627a0426a0427a0e0e94c0e90c0ea080fa060ea060ea060fa020ea020ea0312a0512a02ada04aca04aca04ada02aca02aca02ada04ada04aca04ada02ada02aca02e294ce284ce280ce2a0ce2a08e2a06e2a02d690cd6a0cd6a08d6a06d6a0439a0639a0f18a04b3a04e88cce8a0ce8a06c4a08c4a02c4a0e62a0863a0663a0262a026320e62a0e62a0e5a94c5ba0a5aa0a5ba045aa04be94cbea0abea08bea02bea0e4c90c4da024da024ca024da0e4da
  | 4 => 0x7df7fdbf773fdf79fef73fff7bfdffbfcff3fcff3fdff7ff7fffdffffcffdef7f7ffff7feffbfcff3fcff7ecff3fcffbecfffedff3ffdffeeffbfdffb7effbfcff3fcffbecff3fcff7eeffbecff3fcff7fdff7ffef7bdeffbdef7bfeddff6f7fdefdf7fd7f7fd3fcff3fdff7fdfdbfcff3feff3fcffbf6ff3fcff3feefbfefd3fcff3feff3fcff3fdff7fdff3ff7b7edf73fcff7ecffbecfff9ff3bdef7fcfeffeffdbfeff7fdffbeeff3feef3fdfbbecff3fefb3feffbecff3fddfffdfffddf7bfdffffeffbfcff7dcfffffffffdffffcff3ff7fdfdffffdfffff7ddf7fd7f7fdff67f3fcff3fcffffffd7ffff3fffbff6ffffdffffcffbfefd3fcff3fcffff7ddff7fd7f7fdff7fbff6ff7ffff7fffdffefd3fcff3fcffffddf7fdff7ecffffdff7fffb7ecff7fdfb3fffbdef7bfef7b7edfbbfcff3fcff77dff7edfd3fdffbfe7fbfcff3fcffbfcfff77fdff7fdfe5fdb7effbfeff3fcff3fffdfb7f9bf6fd7f5ff7feffbecff3fcff3feff3fffbbeefb7edfbfe6ffbecffbf4ff3fddfbfefb3fcffbf4ffb7cdf3fedf3fcfe4490ca48ca988ca8e8ca8ea0a6e8cb0aa070aa030aa090aa070aa070aa030aa029fa069fa0300a0b00a0700a02f69caf6a0af6a02f6a0af6a08f6a0289a0c899ca89a0a89a02dc9cadca0adc9c6dca06dca0adca08dca06779ca77a0a779c677a064294c3494ca28caa288a968ca9688a96a0
  | 5 => 0xbe25836383586eca7338e52a1c0b14a8a78e0a51e42c1b09983638290d70b2201052b830a58e0a61b86dccf31896158e0ae1b025cc60d8e0ae29b2a82aa49fe258e0d78960c1be3835b2b830a58e0ae298ae1b8a7cc52b896398306dcc60c1a32b8e0af83638ca8a42bd2b836382c0a41b8241a614ca6382bf7fafeffbbcffbfdff7fcffbfcffbfcff7fdff3fcff3feff7fdff3fcff3fd7fbfdff7feff7feff7fcff3fcffbfdffbfdffcff3fafebfb7edfb7edfbbeff3feffbdcffbff7f5fd7f5fd7fdef7fdfff77fcff3fcff3fdef7fdff3fcff3fcff9fcff3fcff3fdff9fcff3fcff3fdffcff7fafcffbfcffbbcff9fd7f5fe7fefd7fdfd7f5ffff7fd7f5fd7f5ff7fdfd7f5ff7fdff7f3fcff3fcffdfdffffdffffdffffcff3fcff3ff7fbfdff7de7f3fcff3fcffdff7fbfdffbfdff7fdffff67f3fcff3fcff9fe7f3fcff3fcffdff7fbffff7ffffbffff7ffff7feffffdfffff7f7fdff7fdff7fdffcf77dff5fdff5fd7f7fd7f4ff3fdffffdff7ffff7feff3feffbfcffbfebfbfefd3fcff3fcffbfcff3fcff3fdff3fcff3feff3fcff77dff3ffdf7fdffffeffffefff7ddf77ddf77f7f7fddf7fcfff7fff7ffffffcfffff5fffdff77dff7fcffdffffdffdfd7f7ffff7f7fdffffdff77dff7edfd3fdf7bfeff9feff3fcff3fcffbdcf7bdcffffffb7fcffb7eff3fcff3fcffb7cff3fcff3feffbfefb3fcff3fcfff9ff7
  | 6 => 0xe0fcbf318e14829c78521604914d8e47829e0e5272fcc6382387029a065272fcc0718e08c2986c1ae25cc72f839498e0a786b278e0a51e0a7868ae2386e5472e23638648ca2a08f8932aa919384e3832e1a520ae57c28533261b08eca638230cb52e25cb86f8e61a328b58906b52821cbb2b86e382906e1af33cbe2584e382c479868a58e3262986dcc6382be25830a83507ad1e25cc47829e3831b26acc0e280c989638d18cb038d702b46c9970326258e0ca6cc79208a7cc52f8e34631c16358c823f2f03a92284838e0cb4c0712bc798e07a350b04a730103478e0a31e06e2b8c829f2eca6394c3471e60e32347cbe391e0cb0a8b0ca0a78e478d18a386b461af2f8e0703286bcbe0d896394b8b01b7318e52e1c0ae5216f1fe258e0ca3d40e30871ccc0dcb8a51e1498e09e1de38350cb03c1102f33cbc7f4b1498e071cbe254b40b1f9498e0cb5441702f2f890778e0ca269234b63829c78c9e394b0a6348a6246382c0f4870afcb840d1e1b4b6382986e1af33cbe2584e382c06e1af33cb86984e382c0b1cb86f8e52d868a61af2f83068cae382c60cc9e38298b01bf338e52d896142b87466c791f068ca1474c52b8e60f838694ac7c51d318e07051e0d4ad318e0a509868a4731839474c6381d1474ae394c60c290768189e9ed2b4c6382906c263298e478358b01a2938e0703586dcc6258e60c35aa49fe381c0d61
  | 7 => 0x6c1a731c9f323153c2ee4fcc542280b61bb281a733c9e2d845342c64fcc069508f503c18ca31f208a38b33e35c17ce730318d703e2d06328c797120b3e35c1229c0ecc3294cab31ea4631d2f04c0fce62d05f30acc7a918c705b4107b3ed1c0e32b1e9bb285c47b20b398b416d134303e2cd1b289bc1f1eb3831e201e6314bc726417a3d62c1a6134b53c52a1282d2f1ce2ca452d4f14a3d0c48a0a14b8681e52c52d3d492761a8738314b4f0f65e9902f0698817a645238c0a24986a1cd2c528698b0bd84d3c84a1b52c729da0b4f0c63db2a368dc2c8f484f32a40c43562c360698b60dccf274b0c4366181b869ccf278b610360d8280b629e2d8309e2ad2f1e61d48b411f06a3d739cc5222a0af1e92226e2c7607183638648ca1a6241c6394b156320af8352d8e08e2986e1ae25ccf2e50e134b6381a6245914864c789d0ca1a0718915f8e52c320681c14d8e09e3221c32e386689e2695d4b60d8e0a78906b52f2f86d2d8e0a649e301a0718452b8e1642794888d2b83638238a61b731831494ae38298afcb95023e1b8e192328d63208eca8a064e138e0ca2be0d8e08e329482b95e53099cbe1b8e08e3288e27b282f60f8e0ca268d653e38cae0c290d5cc0691e638238c90b164549485195e2bc28ca94cc986c57638ca4798686c1ad4acb731cbe3983e241b86e1ab29ccf2f84e258e0b18506e1b327ccf318e0702b
  | _ => 0

def word127_2 : Nat → Nat
  | 0 => 0x435e141b86c1a733cc72712d3d8406bce60dcc0c23f739cc0a03f0a22ba76ca86c2618228b2a2ba76648981b1242ba76c786c26620c7e30289261a8734b0698b09f50e131297a640ae9db1e2606c1b869ccf274b61150c4a1a86e1a733c9c4b4b6115086b883382b8d584ac98bf322a990652778b52385b3f88612b20ae9c099cc8a4642778b60ecfd22ca33f8812628924356318b86a1ce2cce61264344ca0ae9d9941a1918812628e178c06a1cf38ca62d849905e8ae9d95c1a1910440f03338364123162dcc726231951eb3e3ef3903f303d0fb058d820b28c7b318b0fb05f3904f312dc7a230c7058ba1db30c7b298b0fb05b1e2eb30cab283d62c34e162809e50f386473133732c7c7b856101b86c1a733cc726ce6182bf39cc44a280b61bb29cce2d8309f128ac1b86c0931fccf318b615128ab1e8af50d3d240a462a926421282d441c8c54bd231d0ae9da914b62d4f247881262891b9fe3033e241a8738b2478498a918dc388e63a18a9d86e1a041ccf274d52d840af50e2151990216314be2f1c986350f58b06984d3c91a1282d463552f4b47348e2ca453c918f48a0a08989f51d2f4b068212c891d234f2775224664328650fe1a5426462148d3d8c0a249e2e6506a1c924918695262c3fe12ca8e0388e4618f58506e1b025ccf314d069860af508a10a8b0ca08f33069ccb1f4f2471ea122c727cc7323153c2e8
  | 1 => 0x4b8af94f2e1a61b8f62e2809827b3e1d8d623868c7e3d1f8d78f62e348d61b869ccf278be118f0af8f62f830a02a31e1060d8be3d4a8a62424b8f47e3d06e1af33cba4b84e3c27e53cb86f8be1b8f0a61bf338be158f5222b89bcbd238f47e2c09c49d238f47e2c0758ce3a2f0d38963b8cd2d1309a5089e2f62d8ce3a290698b47cc26338e88e27e3b1350b8ce241a86d8ee258c8d21b730c1e3b8c8742be2d8e869136322686d8cc4d8b63a2962c1a44d8ee322686dcc44d8ee258c89b1f4298cd0c9263a27a1ca4d2d8ed0d8c8af8ce3b8952d430af892498ee334352c1aa1d8ed2d436322ba798b50b8c9498e89e2c50d8b1498ce3a290a45e0b1896338ed2c3486c1dd2d8c9498ed0c9e06c1de2d436325263a2950c1a075891498ce3b8b1781d06a5250b8b6338e89f8b6338e8a42c0a58ce258e8b034e2d8ce3a2c0a58ce2d8963ac18b18e8a43d62d8e8af4b63226a494b0698ee3234e338ed2d890d29252c1a6338e89b8b0698c89b4b0af8ee338952c3486c2624942e32ca33f1f0b01a248a4d0b8ee321d06dcc2498963b8c89b8b6258ce3b428b1428a78e8af1f18c9d8c435e158812628e30338721af278b32984994218d9cc72659d4383194358d9c9f3112d3d830a88a0f424e0c338d750e20498a2490d58c62e1c86ac7e2d84994503298b191858ae9d9942c0aa2bf31c9d42650fc2c0aa2ef3150f278319
  | 2 => 0x18d74752b20d109362f8f8a61b87b42a4d8f8f74709a8952a1b87b8ba4d4463e299221a0798bd0a9363e319261063f8b8a38909c2586a9363ec5480288a62324d8fc80310a78f8c42f62f8909b8fd2e2be54c572f8be3e270a687a9234e3f8b8d61bf338962f8f8d38fe2f8909c2a30e1bf338962f8f8d21e52b8f8b0298909363f200f5448afcb86893732a4d118f8781b86bccf2f4463e2f655cb86f8fd182e06fcce2f8963f448aec9e3f428b029e821ae2f8f1923d06d8b87626c4f8f0c235b2634e0d8f09e2609b0a8d61b47f8f44e308d626b2b13e3d8309e2663c278fb8409d0af321b47fc9e3d1389a2732713e3d8309e82f33cbe3c2609f8b273848d748e3c328d430943cbd23cc8a4646138f09e2692348e0f8b0d61b076cac4f8563c296122709bccf2e1b60f8f1910440e35c162440a32f2e271922c47fc988d8f62ecb47e05b26caf278be3c3ef2f8bc0b1f88d8f0ca1c417ccf2e34e2f8f08c3506a1a32dcbf278be0f8f44e1b86e1a733c9e2f8463d1386a1b86bccf2f84e2f13e3c1a09a48c4f8f09f1fe1b8b89cc9f338f47e27a0bccf2f8f09e2672f13e0c3ee3cca89ecb06a1a72fc9e3d13e2f8386e1a868cb021cbf2713e2f83e3c1bb278f09e3e86e1a327c9f338f44f8be101a86e1af33cbc4f8be138f06882f33cbe3c278990a0af8f47e350ca9286e1a62f8372fc98ed4be3c3e869c9e2f8363d
  | 3 => 0x6334d8b01b069cc7278c60d4f0ae3272f4d0a42d61a2b86ea50d81e8d41a869cbf278ce1a3606acc869cbf278ce16360cc2b8b62c72f86e302a89e248a0338fa2606ccf8a43ef2e468ae10347868a58c0aa338a03e8c9cbe16280cf85f39cbe31860b0290ce2b8b7905182a0978be41460a825c289f51990452328a0278a829e2c68990649a82be0f9062f4932c31943cc8a46460f8b33e27e418b8a8c50ae1bf338b62f83e41148698be418386b1489f9060e278ae1ac5383e402786fccc538be4183e2c1a52493e418bb142a0681f52e93e2d83e4027d241a8958b52f83a4f900a54924e1b8918be4183e2c2986fcca4f8b60f9062e1a06fcca4f9060f8b09e1032b8b60f9062e1a06f9062f8b60e29e2f8f9923d31435e2d8be3e648c264c7225e2ecae3f460c62c27cca86a258c61a0798bd2b1463f460a0600a0ca8b09f1922586a1bf338bd2b464518f869088d6238918be3e3d0a66488d8bb2b8f8f41a0798be3e638c646326648b09f18e1a0783d7338bb278fe266389c2bf33cb8b14663e9f18e270afccf2f895182f63e638b01af2f8be258fc502706fcce2f8963f1409a1b86bccf2ec30798f8b1cbf0f1463e1e0a71463f8b8a22986bcbc501a62f8f89c1bf338fc518962e26f2fc38a78f8bc1b86bccf2ec363e2f4869f52aa48694462f8fd2e930681e62f4aa4d8fd102862e1a52f8fd102bc818ba4d8fd0a3
  | 4 => 0xd4b0a03e94587e2d4b612640d00852c280fb869458795e5415c5294d4ae254886e9f8994b54384890c7898278cb8792226e2c1b87b4b612575422997a640a6c78bc1b06e1b27f8686b8cd4bcbe0f50d2c280de3b3261b8f03ef3987f30320c787c2850c82a318a2c62f8512587c28cce10468a78906e650c9ce730508a03263787c298415d8914b8612c4686c2616832190298c831f39cc14a280c82833e5161fa18aa2c62e52e2d8cb3384990cce222827e2a990656162861e6462c24d23848f9ce730528a0640fa3509023e0c3e0c62814587e2d849903e6222815c9f8b03299183e1e6462c9c09984d22cf8cacfe1e3562f8b612640d187e2d849903e5221bc823e616cc9245109a488a6469941bc8386e1783945ce72fcc0901e8a05a1445792c48b28530a120e1783991cb86e510f920a1283a0651739cbf301e88c28021ce730280fbce730280fb0a8b0ca0ab0831f0a33e650fa5714a294210a31eca33e3ee31ce021cc60c508c6cc3290a14a640a03e86c1a731c9b383ee1b8386c1a82152f31cbb3f858a01a869cbf262c60d8c8adce731830ae31f38c9f30280fb52f39cc7261a8a383635ce730280fb86d4bcb8a5838aa2861e8953720a7e618a631e238661e359878b482646134d0cb889418789a489249162c1b87b4d612328414d60c290a34f0b1cc7274d8fa238fa3e06c1a731c9d3c3eb281a869cbf2783
  | 5 => 0xa38494ca0aac7c8a3f89dcc09bccc5b86125cbe163fc8a2ae3c36731c9b263c8fb8506e1b068c9f31c9f3316e118f86b228ba3649b8f731c9b263ee1634869ccf31cb8fec78f3856121b86c1af33cc72f16e0f8f06922e1725068ca45a348f38df33cc72ec78fe8d8b08f731c9a96208d79163f0a8b0ca08e1a31f228d62c727cc0d38f8d78506e1b069ccf31c9e118f8af97f319160c280a81b869ccf27846374a8b0c786d97f31836454a8a695c8a240ca3d0681b86a3ca578df31ccf2f48e123fe1b97f31cb86f9160e29f33cbe138d8b0296141b86dccf318de19488ae1a07d8c4554652b9089e1b731156314652b908681b7318963190e111506a1b7311563190e258406a2606c9452b84328cfc841b7318c62590e102be318961190d2a2c60e2c145cc72f4de1e240a1509245161e4886e2c62e52e2c51e861a6314de126406c1a86808633cc72fc9e0e5153c1b8d9cc72f4df275088b850fa6561e4889b8b07aca06fc9e31848f86561e4889b8b06e1ee12650ca501918c3294d994c78aa3f8b02b8aa1bacdcc72fc9d429f9943ae0c3cb26650fbcb8f3508b02af31c9a25830fa6561a2c32854326ccb1e1be2520b3e35e1424195cc3383609bc986fcb8d720e14cc8915288a36730cf8a1830a3ce7302461631f3983730280fd8594587b32340cb8b62433e314b61265616511222691b87e2d8907b4b06f848f8656
  | 6 => 0x328c234617856121be0ecd86c1af33cc72e230ab85f39cb86e230cb84f33cb8a4230ac338a82ee1b1e733cc72e308d23fb302332a23f39cc0c23e8691e2863cc96a5d2e30b2a3652c353294ab2695e1a34d22cdc7925496cc5231e09c2be1bccf2fcc0fecc4951e330ca069488f23fb2725d354b0c23e86925b2a308b148f39cc32b250c427327258b43eb2a2c0d2488b5ce73148c943147830b2ac986948d2f4ae1a34b283fc781a3283509c2bd23ccf2f86b29250d91e3302c3281a5223b0bc350cc358c98f62f85e2cca8c234614350ac4909a48d2385e3d8be2c35882cac5b860ab8f68e1b62d859903e62d858d0400d4490ad8e62e20e3c640c8c98ac4963d8b8d420d2251e383209c2b09bccf31cb8ab8663d85990a1c1103c0d0540a8da3c8cc168c23504f33cc083cbf26230930440f02e3e35c178e41434413cc72fc989c64c8a2332d8f48a05c14ca0d8c9b1f8f0fb03c0d8e8ab05413ccf2fc9c8aca6382348a1dc15ccf2e304178d8d2230ff03c0cca63a2ae3905413ccf2fc9c8a520ad028d42b413cc63dcbc8a230d122c141c417ccf31cb8d23fe362340a350acc7f318f413cbc8b168d18506e1b069ccf31c9e3f8445a1ae158486e1b06bccf31cbe0f16e3c1a09c2b0ab52f33cc63dc9e198e3272289a3889ac9c9b228ba270ac2af33cc7262ee3d8663916c8a2689c2b09b26f33cc619cbe3d85b1e2ac8
  | 7 => 0x6848130ca1086212d2a13859c9d2d50890230c4cab374ac94350538561027338cdf33c9f314a8922373814847cc0914a88c30852130c38bd2c10e2d4ae1a12732350d22488e236374d62f4b62d4a84214846120442308e240c213062140478b05c16859cc8421104acfb282388d8386c1a8201a32dcc72fc9d3c2306f84e101bb281a869ccf2fc9d382306d856101b86c1a733cc7274f06a236158486f8386c1ab1fccf31cbd3a23069850f22752c24f2620d3a3e8b0caf3030d3b250c52289cc9c9a630fa270afccf2f86b294d4943548a3b0b0ca4943009c2b869ccf31cbe1a3fb1e3cc8aca4943c8fe1b0683cf31c9f2e34b394b88c1ab281a72fc9d30230adce7301a88c31e17ce72e2808c2952c3652b48a96243363ea863c86f4b0d94ad22a5b28c7b363e8b0349226373030b37250c5ce731c9d2e34e1784b342af33c9f2f840d985e138406ecd06a1a733cbf26230ad4b0a03ee198452dcc86a330bb84f33cb89e230ab868591ff33cbb303488c3fe183b09c16535c98774b0faa1d2f4ab30cab27868d34b0fe1de18270afccf2e2661b250ff1fe18cc0ec1bb26c7d3548d2c3eb2bce0c34b494310d248982350d83109c2bf33cb86986c943f877ccf2e34a123508c360edce730cb08c3d615843381b86c1a0f3cc727ccb354a88ccb739cc0a0230a81bf322b52a2309e1b7302ad2a230a7cb8d2a58d0230ce2a090
  | _ => 0

def word127_3 : Nat → Nat
  | 0 => 0x85f4d52c158494a88f460c63584c1804e188501285c1685e15f32cfd18ca52a23e2f198b11445ecfd19258d62c1254ae2f14068cfd19258d6ca86c1af31cbd3e2389dcbf0e2f0d18986e1b327ccf314d08e26b0ec306f4e86c1af33cc72ec208e2af2fc3d34290a7258a54bc962a8d22b9234b8a5258abcbf0e238ac3286bcb88e270ce1bf322389a3386e1af33cbb0c238ce35730318c81bb32320fe357302a08e270ac320bc0af303508e3252a290a7258ab450a9ce72ecb7303508e3086e1af33cbd103fd141ab2dce0d5cc72f4306e2386e1af33cbd10238adce327cc0d54288e2a50a290ab258a7cc8afcb893848d42bd2b242534f61aa50d5849302b8a4ca733cbf27840922c6141bb261b069ccf31c9c494f6101ac282bb261bc56ce61b260d58386c1a8694c731cbf27123398586e2bf33cbe12cc44827e121b86a1a733cbf27123358406d85f382408e35731cb8a630f2f83843cc0902353a30e158453c1784215844150601384bccf31c9b274e88d8561230d3a2c31fccf2fcc60f120aa4ec4a2bf33cbe1aca093250d58509cc9d3d84733cc7274e8d3128aeca326a352f49b372561614e0ecd84226f31cbd274b892230521904610f39cc32749d2e2309aca18b2533ea34982c617168b1128af4b98d86f31cbc4ecfc9430e15c9b3834730cd8fb4bc49cc60d250c2cd8c5ce60dcc0d23d73983730308fc1185c1
  | 1 => 0x56501318040800c1c02250061400e70004918b294300d44e1344b8a4ca7324cf27c3e2c304098b498300d5ccb31c3e2c278c0cf333ccf27c386d8b0c10b0c4ca8898b337250d417535868d42ff303fe1b4d0be1b069cc7271b62d86d3c1bb29868be3f86e1a733c9e2d1b61b5006dcc5343fe1a2fb201b86dccf311b62d86d3e1a32986d342a0d5cc0a83fe1b4d0ae1b069cc726ce469868a81a7278b46986d2e2b52f1a62d868a42818b868a83fd2d868be3fd2d868be3fb3c1b869ccf278b467868ad4b61a280bf19e2d8689e2ae1a2a0b262e1a2a0fecc61a2a0ff4b61a2a0fe353298b0d94b186cc45f868a9cc5223fe1acc0be5ee1a2a0feca523868d82fd241bb3a1b733cc45f8b61a2a86f17e2d868cb8b45f868a42b0d94b62c3532861d2386c4c2a731135223fe1acc0a85ee1a2a0feca523868a8362464df2e4cf0f8d092338b1cc1366252b8d625450924e937cb933c3e35128ce4e8b0627304db278d624c4093cbc4bc38b03e0b0c9f3028c98cc624c40ae2c730cc0a3890902706e3e0fb12b3acdf2fc3e35138cf4b4742186a1b0a4c9e35893111233bcbf0e1b635128cec1c5d023361a8978d44a338b189634c43311986b4a86dcc331126358909b0a0af12b262206cca63589337253114b335258d610853cbf0e238923e053ce09035f2fc38a032d42238c6308cb891c75089e32f2fc3d42278cb8d8658b
  | 2 => 0x89399a4e54639220e38638b1ce1ea382acdf4437b28dd8937198dba636bacd9873629cd7c535c98d664357a0d4e53511cd36534b20d1c73439cd00633d18ce8533798cd273311ccb6732a14c9e732418c84631e18c6c73179cc50731098c36730a18c1c73039cc0082fc20be082f424bbe82eb94ba462e614b8e62e08cb7c62dc18b6452d698b4e62d094b3882ca20b1872c298afe52bd10aecd2b4a4ac072ac98aa6e2a2a0a7a829aa4a58b29094a38428c18a24828518a08e27b1c9de9273249bb0266bc97ce2581c952c24e9892ef24414906823da08e68235a48c4b22bac8985223a087ea21aa4858f20eb881e7204247ff11f7347c2e1e99c79931dc98766a1d4b473881ca2071851c3a46fc51bca46e051b5a46c4a1ac2c69af19f30664e19228634b187986124182c05ea9176145ce7170205b081680c59a516420580615d24562715518548a14d1c52671461850c5140984f68139a44d471319c4b8812a24496512328478711a9c45c7113c042eb1062440690fd1c3e670f6203c880ee243a660e6a838690dd3435a70d32833880ca1831c70c3a42fc90baa82d690b12c2ae70a820290a09f1c26e80979c250709098236708a2c2124082a81f68079a01d66072941c0506da41a4806520184705d9c16850579c150b04ea012a6047a410c6040200f06039180d86033140c2502e1c0aa50281c0928020a007270191c
  | 3 => 0x7321dcba572c29c9cc72111c7c971aa1c5ab71145c22770511c0c96feadbe4c6f34dba736e025b6ed6d52db3ee6c8a9b0eb6be2dae2b6b331ab4d6a699a8ed69d35a5a769331a347689b1a0e967f259eac674b99b68669a99926661a99726659a195686519593cc649219146642258f68639a18d68631a18b686299d89866232587b161631840a60b318149600a57f0b5f6997ceb5ee3d79ac5e0a177255da1575ed5d13972845c81d71245c2c96e645b7ad6c865af0d6b695a91969855a39d680d5999565ce59011638558bb96127581255f26579995da75731d5bea56aa159a556411588b55ca955e95532153ca54a1551e4545a9502953c1d4e27535194c8b52ca14a255261548e851f91476751a21458b510b542855079941235031940094fba13de54f51d3c674ee213a834e89939644e39538494dc8d36c54d89d35434d39134654cf19330f4c4a530054bda12e664b6912d254b2212b864ab2129c94a2a5278849a1d25a749319240448e1d22a84869920e847fa11ee8477a11ce6470991b6646aa51989461a917274591d15684519913a544c1d12274451510a743f290e88436190cc6430250ae6428ad08c841f1d06e741819054441319040740c99026640695010740094ff853fba8fda73f318fc073ec94fa863e71cf8e73e020f7073d890f5aa3d198f3a63cba0f1ea3c2b4ef093b7c4ebc83ab1ce9e93a328e7
  | 4 => 0xe14080e061a002a0822081a04100c000000005e080000104a000a000a001c00060a2a141e0024060c0a041a182c0002001212241604080002042a080a0a020c04100e080a1a2e0e360e040400040e00020206000008160006120602000004182616060c1600000200080400000800120404000a1a0c201c02040210041c000400081204040e59c0ae6ec59b89a6d689b1a26b659ab166a299a412688999d9666ca9961664e6990a263279891a6184984126084980265ee4979965dc3975925ce4971925bea96a9a59e49659658ca95e1656e59592a55079509253a594c225209943a24fea93a964e099339e4c0392ea24aac9249a486991d1e4668915ae440590d9e42889061640e5901163fad8f8423c098ebaa39a88e29238298dc3235868d31634268cd9632c58c89631878c29230248be962f038ba962e058b5a62c468ae2a2a478a59e288589f9a2728898ae24cc88d26222c8829e1fcb879a61d48871461a2c862aa176a858a6150c84e2e12278453a0f8783aa20da5834160c718291a098c8202207108143e0330804b1ffac7f8adfccd7eca5fa077e499f8697dd19f68a7d515f4aa7cda1f2657c719f1087c031ee897b595ecc97aeb1ea237a71de8e67a0a5e709797a9e4aa78dade20678519e08877e25de6577735dc2676d99daa676799d92576235d6e675899d56375429d3c674c51d0847402dcea773719cd04
  | 5 => 0x10c7a724421f9ddd881f25326a47c4d36bff000f268264097f800048647ea078c847f800ff001fe00380a511c93ec912803ea00cb7f800d11b72c5ca48ed26cbe308997461989c329039f077860853366fe4a96d35c9fe002954e2213a287fee2fb4c5748da417a089d488bfc0002910c620c3a292419e4f0c28960cfd2b1e1392784b5e36334b4a9522e7050c386dde107c02df305a4169b6cdbd6159449d7d34914254f44fb522c51e8438cc54f51b769a706700ec615f1d34e9a4830a3d4bedf0320a8e0a333a680d5b4e5d8c0eb61e03a99ffc0046cd8c29bdfe0029030123c5317162e1c280a6c1016001604882aec166206147804006a5e102a00080002742e1c1c1a143c06063606128e2e00103e22580e18220a0c16200242020200001034000200228200180a002802020604060864003214061c10080c4200060632140c040a0a5200009908001040007012140c1a000a0e502a00042a00380400100622080c1000361062044a0000260082061e00040618105c500000202a040c140602000e1c141a1400180a0c0012362a0018160a02183c060c341246121a4a0c1a583000000a1c0800001000000008020004040e000600320a140412000c0e00000e260412080000000e1a0056000a08000e060804040202020004001e000a12143a32241a1400260200100222120042040050000802080600040e067e00000
  | 6 => 0xa01bfc007caeee327f2e608b14072a139941c4c0cb3dfcb4a5fac00ef13aa7026a69372d0302d1243203e7babc23e5e6886099784a11de584e209c4457449d2a88b79118cd0c1bca2c16376cd388ec90462f81c5898c47fc97ed5260ba2b788d7b910287cd3c07a026939e8851bc2e305364892bfc007f8005e34d7ac1ca24ff888e0850ae905e084a97bb93d8fc4b157fc00763de011585094bfc0010013a33034531ef90b850e9a1999fe003fc0048acfff000271effc002d3bb438dedb35640aaa6ac7e13d576a94216fb3b196f477fe0027445ff800b20b1fe003fc0000021ff00082de9f4a0cd932ff001fe003fc00769b9f0713c2646bc0786b0160787fe003c641ff800326487e28e19468b9462a355fe0025a41560043093c30643fc002d1f903081fe003fc007f8005c784aadba30e81c1df7752ffe003fc00529e6c66825e87bd9552f20d2a6d9286af84fd63888506442444741783ba88ff0005a703fc0025308ff0010d197fc0077aae5e7e65637bfc007f8005d709fe00098fa63140ff0009e08ffc00703be4025b0e321d87089b44c848189339f8d280c2a0e5d6f29d78483ae8cd4d75244fbecc8d16b919e492c71a170693347c1f122fa590155880453546764a728fe20df9c6d4515be81808b4d194f0a6378eef714685135da33705834dac6b073d9813a210d54a408100be1579446c2b5889b0277679a
  | 7 => 0x2c15c861e0d82876c0fa91c28791ee1944327b5d9a400880ff0000e5c5b4cfd6acd0228842cdca5e6ae9a9a9653ce3c93421f389eff001fe003fc007706dff00144e775d31d73640235ee3030e8cf7f8005e828f6f7cfe6943cadff0012ec3694df662dbff001fe00018feff800eb4a6fcfc7fc0075c999373402cfffc00431ba0b86974931f63ba49685073de4001c9af94474423cf9ed1c419916c5e5939ff46c259196ec6c8e8136c00f5c0ba2a6aff001f4587fc0055a3e584bce2e4278f9fcb3d6c5e9229bffc007f800ff001fe00060153c25d306ff2d067354f8bc6e61475a2859b83bff80006867f3101f058c98a6147c1c86d2f627734b3ff0005936ee8737f800722463aeebfc0051b40a26ade40bcc5b8cf2e2b17c5ae58de80e4580e0f244ac4ed6004e94c29b81516075a21ca28839214a583ed993b182dd6b50dfe0035c3398be909760ca5eed61ec0885738113696114e2b93db5e57d0c132381a559c2a181b6661f81755914b2574e9445171cb9f41e5f8adfe0012da7de310b124e203b7fc003baf586768ead182cec312d0ff00116a43b18b754157372a0309bb0673c4512375ad06cd0e61cd08cff0019affbfc0022b65ce704cd396016ad088aff000ac27605017f8003d2b9fe002510434bc1cf63ac0f93fc005809cd22db7b21c892dba96bf31514ac793d009e1300d07f12e90b5080ea89d357f0
  | _ => 0

def word127_4 : Nat → Nat
  | 0 => 0xfc0069934091be2c667fc002eab844917fe003fc007f8007066c8277381427f800ff001fe003fc003b44d3b5e6df13ffc0044089ff000bf1ebfc007f800ff001fe003c5d2d83eeff0018e477fc00009491d0b3a075891dc494edff001fe003c0fc7f8009991d7a0bbfc00723cbf9317423c6ed3f7c430ff001fe003988c0c92b3a6f94e7b971169089bb38e0faccc08b053811d832b361d6ed49bd8cbeb65dfe001ec4d2a157ff0008a06df5c7b781f1e425fe0027e4a45c57da09ffe003fc007f80035960465dffc002a04890263fe00055b47f800bf61e343beddcb0f2ef7f7b54083ca4c7094d7ea979b2efd15f28c9db8231fc008bfc000d47d0075041260320e39b05922ebc021ffc0058a9ace187c0396a1d64932bc412c423a2fce77f8002d619fe003fc001e842823c2624f6ecbd58c80a3170a2d5e1d03dea9941048ccf9df83d5ec3eeb5188438824ffe946d239c0d806a4c60a248f64743bf3102e65019a1159646a35456486848df294d40adaf55b8c4278c4a2f864ab21b941b6bd75c1e4d7d65c03c88e559ca25c05913e8998617f52e3b3fc007f800ff001320f4fda51d2b0b935bfe000e8437f8000d5d9630c4c9057f80058389a11e40e57089cc344e20b228ddf645a5915638fece4ba6096aaf2324b18cc1a10d292700240618c999cb1040f7313c48a46ffc00310a700310f41561a53dd8816c805fe0
  | 1 => 0xfe76b6df62bdfe003fc00344c6ff001df295243c38a6164848172e56633a2ab4ff001fe003788e7f800ff001fe003fc00732a1872fffe001f87e042798527018cc4a156e6376309a9fe001953d052e6ff001fe00005ad5414ddf29c6acb00c56cd0cc844fabafda615e343e82b7c342ff7fc007f8005c897fe002aa34ff800677a86e499842fb59b29704b241dbfc007f80040441fe00290dab44d6b24a87c4b9a64dbc836ff0006939b1e1e6406ca788609198303ded0f4ff001fe000595059237f93effe001d0c6ff80002057fe002208167174ff001fe000fcc54f1fbff00116bfa1222df49176076683f7fc007f800ff00136df7fc004ea62ff0000a3662e00deb88ff000a41256238a419c965b3fe0007657ff800710531cd9d5e39814008265b6ac6a1e55ff80074699fe001fccbb6b69ff00106c0de02b7f8008a5a81f32324f1ff8002817ffe003a84c7f800d5462330e2ee2816444f038e4c3d7fc007f800ff0004a9359c055ec7faf04c5264f793426124b128b1a0df2875de4bae52fdfe003fc0018bf2ff0009ce80f267ee0740f318bc9cd889c883f4483d9db2557230ee909613e3fe0037d609e4727e1edb70a3d01d29247ff001fe000f0ad23a2f29258f537659f1cd13cc52cba7286e8384d294eb600790ae89bdca4b4126c13a5b28240a5b0b4a763b6b2e8cbeff800ff001f4d0dae4252b818422502317
  | 2 => 0x85a38567bbf0a5598be0b2f2e91ff90f9b990002a696b11eb2f46cdf5b203c2f43b1e055c8af832929323260a8bd4169bc2c2a08b9e752985b4724f2e99bb2e7c14ac5dc352076e2a4fb0d0ad804705559c4455725baa0c9a9167b0345d97fb544aa671a6d182c5db478634179ca4f5a1d2ade16a358c8f60159945c28d8bb46602ca0142a7f800d3630201a264f2de3dcff000009fd1e117f80000298af2a9e9aca80b0a9383d8b943473ff800083c86c8acbde4488b2107e0e292ffc002cb5bff001fe0027857ff8005b209747a3fc0002865c32069101b7a0c7f8001196b12177cc5485082a27affe003fc00551ef73479fe002003e9f1949c4af1d04fa605f0c201673782dd7794f12a56f06a09cf56f16d7f800ff000a2c806911fb947b55f3fe003fc004741a1b1c9d6f4ae5c9b142dec0619f38c199a4ab2aff000f6e7110637f8007a8a8bea3a9c49ff800d139324e3be5a956496254f60c24ab21d022f1da488e2c135e5b038eee92dc7308c256b86338353eb3ade2b00130152936e4661fbd450888016221faca1cb4d42cb9281947070742235ff800399d3fe0016d92ff800fa25532ed7366058c2f453e0547afddb31749a3d68ba2e1d4976ed0caff0013ef63545bff800d125264139d504ff800ff001732a5018a47094ff00134352f98fce852050e5fe001d984d32e0ff0016cad7900cff800bb6c22861214
  | 3 => 0x1fed283e2a2aea60d8c26c5b472b9011ae2cae979ea35dfe003d51803ab335449fe003fc001eae1541ae6b39d4121af02ccc5f5ea9b7985d38ade3984b58b9f5c3fff800b712e173723018aa0624e2505438d5e42ce2d6239398215e6890d129d528ba34aa79e70a63b27e21d1868af0b3d549dac18fbef109ccd6ab0228439af1d97252374059f59943281182e75486bd419b13a3300f6d3d3689248e8d794dfb0342d720a2633eeda4ae4422e5a3d05754805ebcd11d6c76691a91898028f4e852823cfc23acc2bdb421a2c2e4a25db2ba34f53018dc1ddfa9f412f67069686c9086743998f4cb66de4f993e3ac0c06a3d1316c10c689547678c18a9ec03371b584a674bea467951bf34bb7625641c5f4bc0e099ba7f0fcebffc004bb218b5570714be4752a942df69dfe00285d13cc6a7d6e6921ac04eadf0dd2b5ee7e5cd5d3a17a293634634dd3dd35d33530b7d4724054e08f12dc5f0414e8649cc03f3b35e5d1da8fe94deff8001801992767483ccf014df0f9d48ab2c30ff8009c61cf88a04897ff8009c962e66f1722d7f800df359fe003fc007f800f71b84e4ce98b7ff8003a3bc470efb4dba20bc9e7319242c157b6245fff001fe001b1e38fc468a1813d3926835492506d6c4d725fe80b3021f650708523029fde7225db729e845cb201e52caa42acd4522a56999090423a6013ad085110abb2b313342aba846
  | 4 => 0xe64044e54e44064e54e34064e54e14064e44e34064e44e14064e34e14064e14a64024a6ce24054a6ce14044a64e64044a64864044a64264044a64264024a64064024a6404402486ce04264864e3406486426404486406405486406403486406402486404402466ce44014664264044664264024664044024664044014664034014658464044654e38264654e38064654e08464654e08264654864064654044024454e3826445446426426ce6402426ce5404426ce5402426ce2405426ce2403426ce2401426ce0423426ce04224264e6404426465402426444423426443422426425404426425402426404423426404402426404401426403422426403401425404402406ce4423406ce24054064654024064254024064234024044234024034224011044e24016c95026b273954552ba06507fe0038439d433e782a392813fc0046bccf64f88f1621406fc45cc59b5fe001de08204620d7f9862f6918bf40a0263376612929ae7f800b75c746a09392d3fa2e2b755601b815e01eb77865b01036ade5eb3846c41690614e226cd52429017770cd40505903111701126458211a38869e8997bb1e2397e5e0332e54c950fd31e4fd23db9591b03e5fc37ce15978391fe0031e247f800702a0a84da20625c0b57c13f525992e76219763079ee8fde265fbeb6a5982cb2d523991e805e0688e08b0ea4e1ff800fa39ad0b1a8c1470
  | 5 => 0xb4860b4862a4868b52325d22094667bd250146601ce601d06164667ad24a24660092855d24d07466404d07426405d06465402d054e3406d054e1406d05426402d04ce1443d044e3406d044e2401d044e1406d044e1402d034e5406d034e1406d034a6402d03426402d03406405d024e6405d024e6404d024e4406d02426405d014e6405d014e5406d014e3406d014a6402d01406405d004e3406ce6425402ce64234029074a64049074a6402907406423846ce44018464e64048464044015078e64045078a64045078664045078464045074a64045074a6402507486402507465402507425404507425402507406423506ce4403506ce14055064e34015064e2401506425404506425402506423402506404423505ce6402505ce4406505ce24065058e64045058864065058664265058464065058464045054e64045054e44065054e1406505426402505406402504ce6401504ce5406504ce04265048e64045048464065048464045044e64035044e64015044e54065044e34065044e14065044a64045044264055044064235044064055044064035038e64045038464045034e54065034e24015034e1406503406405503406402502ce04265028864065024e6405502486403502466401502426405501ce6402501ce2405501ce24035014e64055014e54065014a64045014a64025014064055014064035014064025008
  | 6 => 0xfd214fd20965249650248d2648d2648d2548d2548d044850448d244852448d2348d234812348d024850239521184a618d2318523064a64ad267c5247c52287d225dd204650446d238e5268e5258e50184d2084d2684d2684d2284d22841228450184d203646586d22aa524aa520244866e465634655746557525854653552435927355272f4a62fd2529486724656546558465585254146588465374658a465134a6134666dd266dd22994a699466994260f4860f48679486794e679d2380d261a48638528a45265bd228c4868c5268c5047e4867ed267ed257e504114860d48676d2207528154864ed202dd222d52259d22434864350443d244352462d227d5211746649d26104660a466144669d5213ad243ad289352345d23455028d5268d50183d268350182d223450334d2334522349273452728d21a55236ad239c4a69c525335243352233522335212c52269d2369d21524a65250552d2552d21424a64250542d254250342d231b5251b523754264bd2412523054a60548605d24055230592805528a8486a8ce6a852181d2681d260ed230e5230452104928045289042678d2378d2378d2378d2378523781237fd2419d23195233252432d2332d212b52227d210c4a60c4660cd250cd231e4a61e4861e5061ed2608426085260846503928035288f42677d2177d210242602506a04654dd206846661d222648689523
  | 7 => 0xd9ffaff3fe7fcfe3fc7bcf79ef3dfedf5bbbf3fcf78ffcbf3fc7fbf7cfe9fe7fe7f4feafe7ff5beb67de7fe7b3fadf5bebf5efb7f5febfd1ef3ff378ffec7daf3d9ff5bebfcffbefbee9fe7fa7f9fe3debfb7feef9ff3ff7b3fefbebf9ffefbdd5baf7d6eaff5fef7dbfaff5fef7dbfaff6febfdcff9fe3f8df7dfcf7bebfdfdb7f6fed7f8fe7fdbf87f7f6feffcdfdbfb9edf79ffbde7bcffdef1bebfd7ffdd7faff5eabfdefbdf5febfdf7bf76febfdff2ff7dedfdbfb9edfddfbff37f6ef9fd9fe3dfeebfdfb3d676faff7dbda45ffe9df37e73d8df9be37c6f21486234a61d4a6204a6704451c4a631d2566d2551d25224a671465504651f4a61fd266f4656446567d2260d2660d209f48656d269548647d2647d2547d23745237452140d2340d216cd266cd20984a6984e5305253f4863fd24a74a6a74863d4a63dd053d5253dd22a34a6a34e5a35255fd265fd2094486944e491486914e47352473523735213e486a64a6a64e5a64a6a64866bd266bd233c4a63cd053cd22a14a6a14e5a15255ed205e4a65e4e55ed255ed203b4863bd043b5049e4869e4e454d2654d255cd275cd279752097527975274cd274cd27a95252ed222e5225a4a65ad229b4a6534a65348653d255350453d24534a6924a6444a64448644d2544d254450444d2444524444a64fd204fd2048d2548d2348d2548d239a5214fd264fd034f5034
  | _ => 0

def word127_5 : Nat → Nat
  | 0 => 0xd783c498b82244df0e60f1262e089137c39e93d00d10fd83f0e611c1e3462de0f32916f07e1cc1f870cfe0fc38653099a3c2783d0a60fc3983f0e1980c783cca61cc1e6730e194a228e78f5115348e78f7120a00f34fe9ed4c322a189212418e86d1a52d4368d03547ac205c4aee49a7b8d04d8280d82071ae1dc92ce857a2c858329b021d87bcfa4135456464e13e4852432e0d0d6193cfa970d5e8064a41579c902985306e68c29837c1c5485b9b807110f924ace34a5b9204f0cbe87cff110b01574ea3e88069b5072409f918d350bd400e39259ca1786c1d9a6291a839259c47c131cc149e4910035f1ae1c0df920576240ddd3e9de1d16f92398e35c381bf240afa778d037e496738773fe2fc7f8fe9ff374fe3fc7fe2fa7f5ff9fb7fa7f5fc7bb7f7fb5fdbfd7f6feefdf7cff9febfd7f97f3fb5de7bb7fcfebfe9fd7fcff3fd7faf7aff3fcff97f3fb5fe7ff7ddfb3fe7fcffcffcff5fd3fafedfdf7e7f9febdebfcff3feff6bfcff3fe7f73fcff9ff5fe7fb7f77e7fc7f9fd3fe3fcff8ff37edf5bef3d7eb4f79ef7d77b7f5fed3da7bcf7befbd77b7f5febfda7aff4febbf7de6fcf7aff4ff3fe7faff5fabfe7fe7f4ffafd5fcff9febfd7feef5dfbbe7fcffd7f8fd7faffc7a3fe7fcff1eff76efbef4feafe7fbfdcfe9ff7baf7def3ff7ef9f1eef7dfef5fb7f77ef79ff9ffd7f3fe7febed7fafdbfbbf7bcffdf
  | 1 => 0x9c17b48857091a40a4f27733112cde2fe4dc7c30937f3791f9344e72e327cdc4eb3a0ef9371f09b91e22f9bb3a3639371f89d8412604e0b146cca8464b8e5c5ad1b62e6578f98f09c16834993271c7f17f1fe4d6741af0e06814023f0ee4c13c35e9d06e0481a726e3fc3acb949d1dc85d184f0af4f89e71ed1bc84a4ea509e131cc68de42525d1c4206a0e7568370a7c7b870670aa15c1a839e3dc4e28d9c06a4ed8371e44a1889c136e1da89cc034727c7912fa02704db870ca7300d1c9fa4f418b41af0e0a147c4b7134ada649d8b3093a65830571948e34c85d471a642b9380980d41c83489ee7389835073c786523d0d71385986cf4169fcde0c1941af0804e0d983bd0fa0f37690348c87301242ba3dc23e93d00610fd84f8f138c27c781d998e3c1a709e11a346518b6130766638f13707384f8f038331c7834e13c23468c7b16c260e06413722513f09994a34c5b09f1e89ee71cc0ca084e605703cf430fe1f047727c52d2057c5bc781bf0e0a425a86a9ee3d90865057d3c52286a974ab1042bd11a220ef8f29aa228e78f511473c799f893295c461e83567f336950350720d6a1fa1f37a8b4f7100afa884b511070a6b8f511473c7a88a96473c7b8a050d5613c2169f191a9aa18348940e41ab1706c2481a07fe31c830c036e3c14b5152be220d41c8340ffcbfd071ee1c0df4cea906c1484b05e0680e46371e0
  | 2 => 0x706965c3c87fe1cc783ca45f4036126d97b380f81b995b38e5c1a59706ee64361940d264c1f0343281ff91e551b2e6326e52f43e7f89d9706965c3fd9c3260d41d59c06a0d0c7b97242e603fb1f0b011ecb94b48a1ac290470bc0d01ab1f0b0c8bd079b2961a435e9d06e0481b011069c8f8759706e14c38835522e5fd079be41c3a54835d4d1362859cd460dc9fb06e411449c136d441f4322a12704df870ca7300d1c9b0627fc803c87de264e09b2a50ea4483ef20f41e6f54857e1d3483eb98a340d1c987d33f83050ca9d3c0d787050d3c4ff4f13fe2e4fc9cccde2f8704944527e0df8be1c12dc5f0e03707a0d822048b423291c6990fac591c699091861ce8ca7411caa3848e24e774c86b0cb8609c8ae9340dc1bc4506e0dc1e83788b0601b04433f8711d0441430630e1980fa8eb0e43c42a6520a0360220d408034019c82d0713f41e6f9070eb4815dcc393e40e8c2bf0e59cac954b98727c83873a30aee71cc2a9e4015f872cc48248850a41e1da9032863935a8c1b83d60d2698b03707bc678bd2ae3d8601b7201a7a8b888360220d4086a2e41c381a6a60b015c23a68295a8ecba410aa1f79471ee3fc3ece83489c1609cb99e3e4e49ba28d1bc9dcb83773347c2f139733c689c937451c7f93e8df43e7f8d6940d933e8fb9706ee6521f1fd3b11393e901925278fa41d1bc9c29863c3c0d78d68d1a54bb93f1f
  | 3 => 0x4e0d82e21e39972e0fa4d29608c1d81b29672ee641ba950a81d81b3987300d1c9c9e878a5cca8d1879a65259980686634cf0e0ae6603fc0873211c5c048069a6525da0c880d329e99b36a683ed9b06e31b221590a394f5169ed3313acec9560c2e022c955221383859d4781381a699b3a1a64c8960b41a64c83e7381683bb9c61b678270771a30f14b99593410148c950d2a541b59cb38e642c39708125548858069a6525d9cc880d329e9909c1541b01106a040276350aa1a85bf261901902687f06e0482687f09a1541b81206c04426e350aba671a8b816cc78a1e1126f9379344e0c4106cec4ee4c136ce06cb3765d8f07dc9b116ce8d8e4d13b07e0ec24c7708b1c0abe87cff9b48a1b309c43f42183cfb1b0d21183fe1209c130ca846a3e0ef09a4509c362ce4430ff849cbd1f0fbc8cca04ec1f83b0959c63b8458e055f43e7fcda450d81a82b322f40c7922a4df3e1a434613881e87d079f0c21a58d87f08c11e8f9950c21185ad97880c6f09a45b2e1383f8d8c6b1018de1272f47c3ef2331e1382d6120d264c3bf23c1a1a82b322c2365d8f7a0f3e91526868494136cda45c6be87920b7b362d5862450aa936cba45ca59372af0e171e805b635b2ec7b56fa1f3e14b91f1416f65f89e4de260d1c9d9be4c937d059b0d21281b035326e601a83472766d228d9f4366c348377320e81a5970f21fd2507949bc4f9359
  | 4 => 0xa3334086710cc1995332446408c7118c2314861a4bec97462dc85a8cb3916542c2a5718ab115442a0a52d8a2a141327c84e8c9bc12f525424a6090a91c1236845cc8a191152186424c83110461fc23f447e20f831ea83c647410e641c4637e46b10d421a4e32c864a0c53184c2f185b20b2216082b0c5490a7214a828484f989c21348258c49a08f31188222040087f10fc81e883c107670de61b1433986430c321630261849208f20f901d2835705ce09e40f30185027002d403300089816112f9ff1f0fb910490cfe851484333bc6acdd90093a791284444e15f8d19b09292a2c7a13341274f38c72f13d1985845e8a024e944961aca539cd2367a27e8d06c0441a81006f67627e8d06e0481b01106b66e27f1133415d18fa1f3fe6c24f1087d0a4a30490afa7f4d99b89d0a4c9ba160ce7d138463369312570e0b0671cc049d3a66e27195170c19cffa0f376741aea689c13926d9d4949142759d4942e352849733c482c24db389285c43c7329352507948a9354d64dca5957512970ec0d9cc0340a0a5b4e8403300db4e83e33127ad1b260c41d586f9f16e2d985da0494d3f4f85773e929a3c5f0a2d3dcc39373e92b4fa9ad3d0d01dc9e52e6564d0403312782b84c331c383f84c1701238a59b5341f78a198b360dc6329a0d264c1b69ec8e56428ea2d33a7a2759d934e705c03608b2694b04e0e76743606261a2db4f0
  | 5 => 0x42450840340820c002010c0008100381016624000060870e18207800c10281140c000105c39b1a6019f02180010614581040489b020400a0010382001408002080000210016097c0537e62f8c5e98bc2b7722ea45ccab8516e96daa5b13b5cd6a12d2359e4b3496596c8a58d3b14761cec225804af855e96baa5714adaf5996b0cd584aa89540ea6ad484a88750569e2d378a5e74b12941d252a46b478e8da5172a2a9444e871d0b3a10b40d27f94fd59f0b3cd277a4eb39d0739666e1cd939ac734d66724ca498c730d25facba396e92cce5824ac594e928ca50bc9a592a524d247948d790cd201a3d2c7568ded1a722ecc54789af1192211c3fd86550a2a0f2c19482b30312041c0567ff8fcd1f7c3e747c66f81decd3cf4796af185e2a3c1477aaee09db0bb54762cead1d3c39f273ace5c9caab90371b4e0cdc0237c56ee6dd1db6936b36d10d825ab935546a2ed289a42b4326828cf599b9b3436624cbd595132876422c8118e0b1b3630ac4c988930f46166c20d829b0245fc4bf0d7c92f745e68bbe173aae215c24b7c56f12dc25b46b5d5690ad1359ccb2255fb2b975650aa9d519aa05536aa591495288850129dc93ab26f14dc69ad9329a6244bce95d928a24d848ac8fe11b9235845aa8a1d10ba1a8424e82d9029a0253fac7dc8faa9f083d0c78a0ed39d323a2c72c8e491c733888701cdc99b6735e66b18d319
  | 6 => 0xfc0071223fc00e78f78cd1d8822a01fac61a2079269d93d7d67448a9ae948c95e5cba09d3679801f64851de608a846b8a358c41ac027fc00c22e9358a060bf3a9f398e2b66eff003fc0018769f0b8e140fb052769a36821079d5f96170932b162f394bfc00723ca6481c1102d63b8a7eec4e1f42c05915a30a451ec680d960ded97382cbc235173056994025cfe5a7b7714bea3f715833a32b86709f42a8a9ae843ffc002495f25c2a56dffc005177cc26566956e15a1700bfc00f418ffc00f23de4d88cf53ab0744a8adf1846b81c425faf9904e89036a2592d2012fe00f057e7fc007ca83cc22e349ffc004185379d7de453b2258d127fc00f8863a4cfb6742d87181922e8e90957e783d3516a188734503fc00b572579011d5513c83344400d0433988a95ec684af8c7d456459e5ba2d828eae26effc001c2e7693dff003fc003438bfc004359e0e92e42bc55580724a724fea6d7fc00015c580f80a9a4e1f52014ea1a2bc76ffc00755987e4bd9a4ffc00ff003fc00ff0035220ff000c9efb096bfc0000dc015040cb8652047a102193010c44000221c4045808b89580c20412003860a1808014e400d025088c042519506240005620b880f00102042508700a0a05086801f2008b801c242050020600120454708180040c040060008f00060458012881860009d01005533836200120400b80028408510044813c000170
  | 7 => 0xc61118828ff0019c8b9f4ef726d928d3747bad4ccde0f7ea47bc391b270e979c90c14a13f93fd741b9e1fbd8c674177c25bad3ad4884c26975058f77053a6161730186c789d1e40bd93ba029b9a4b266581a7e2646f0a94338e08983af95506979a9232d54b264de1482f57a3858c22475a71d655c9a52435dd1a4de4591771a84cf676012121d7a263b813e753304c20a55de490f8326018ca5a7a4c329188ef82378669f54f47199e875e8041b414bc9cda01af570366199f77325f36c353ca366aa31147ad7590c59dad7eb41c8545da4d75d28c5796ed658244620f377fc00f1840bd9c2c62ffc00c478ed4f0c9315805b4126bfc00ff003fc007824535ee320fe08b7b738fe8120a6d07482705c1412b585ed98fbdc01de13293887fc00ff0004496c43d7356b807c90e7ef08bcb1d9ff0010d9fff001fd561d4a7fc00ff003a5b1ff000c8506329cb4a2b78b3d6845d03bfc00ff001ca7b7aa0e4113ab907888c1e3569dbac90ebfc00905fc84f4bf1fc2e45ff0030417495064cc3a67d145e0ac45898daaa2a3a49bd047ffc00ee42e1e0aaa467fc003c9fec58e41a15fdb9a927775953c123c0e7a395b70a4df031d9d660a74b25dff00271786b69d88add0522ad5b2882f220688393fc00be3634e03bfa5bfc000c893fc00ff00099def3066a1426e8442447ae37c5dbeff001fe28082a7a854ff003fc00ff003
  | _ => 0

def word127_6 : Nat → Nat
  | 0 => 0xff003fc005b8fd71a1b49649a7a0441f064aff0030a3cb4a60f14a868129c06c143a04256f2d3fc00ff003fc00ff0010059d2225fe05ff001e0119f0de51a3c16b028f9e02bbba67d05a5fca013a01da6af9305928b7ba1f9630b874f7dfe9e0b7fc002612aa1b0c1607128622888957cad28e79fd438eae85e5d1b6481d760d585f03c1dd609f039affc00072516a820810ffc00ff0005908ff00389e6ff00154f3ad86bad928b298ade102237fc00ff0019998f590bfc00c411410ceff003fc00be80538cdff0037e99ff0032c26a04ff2147996ff7e465800ebd85d26f17517da435c0b2d664fde8a57a41c015b4826b45f608b6a5ea9d0719d3a0372f1de9be2cce1e2208d4e80a401368d443b73cf48e17a22ce153550ee57217718d018b74bd3251f265239d44e85b20e54b901bc6ee50af7ce88c6b600fad33bcf0bf799f7856d849807138168abe420b14bb242afa13cac4e692175469f89f3e424eb36d44867a9dffc00f0747fc00e0430e278cf10880c8d94872aa152755dc3e228dffc00985bfd502ff001f60d900ed5a54ff002d11ded0cffc00ff002b60cff002c8e6a2447fc00ff0032d749e6bda1aa2a87a34f1538e79551eb7deb62e437ac40c09c5b234dcff0003c08c22f5bd9b953b59139442ede9e4b094c5c5546737fc005f5a9447278427fc009e5756e27e393bfc006e037fc00a8287fc00700c7fc
  | 1 => 0x5521505ce24065214a6ce24055214a6406402504907406423504507406423504503406405504501406405504501406403502d014e64055025014e64055025014a64025019074a64045019074a64025015074a64045015074a64024e5d024e44064e4d034e14064e4d014e34064e4d004e34064a6d024e64044a65014064054a6406ce2405486d054e3406486465404402486406465402426d024e64041235064254021235014e64051225074a6404db311dd3eff003426fff003fc00ff003fc00de86d9c16ff003fc00ff003fc00ba535b5a64e7fffc00ff0011587d94dbfc000fa3bfc00341730281e43b3fc002e5cffc003879ffc003f34a70cc2f85ffc00ff00361e8067dbfc002276045c35c5f930d34ea73149ecb3f0ad1c692fb05fc002ad15c543713921f3d13014cb036589cd9e3a5cc000161943d25cf2b07e43264f20c936923cc41e0d35bd5350c2c5ad99aa2aaca6c6b4a87dca466a4d468a79c7dc9991a3cc5b3e9017fc00f61c3fc00ef871c9d294192d4a5f898f318d816f69565cf46d95b6b125f8d30ea8a6bcb50d926e5802f257fc00e14c5ca3eff003fc0012643fc00a26c8d6950319d48d04a0d3fc00ff0030934586ad6001ab35f9946ec1ae156891899c98f6e0f20633110ba519e0f5dfb860105410d977154db5f14318608805591289895b1cfd666e3416d672df15ffc007946a282c78493fc00
  | 2 => 0xdf1df1de73e3bd3de8fe2fd3dd7d679d3be1fd3bddb6dd6cf6cf59bddd7cb55f55f61fd5f55f57b47bcafdf56d74fb55f55f56f23d461ba863750432a2b44a669a0a2f50856a11cd4539a86cd2999e82c24a66294c33509aa53414862e94c5f509e2533e4862c94c5b509da53244a649a8a21508eea294d4629a80ff4992ea325d4073a4ce7495ce823950403a4c07495869193d4627a464f500dea1b74a64294c1d504fea03850423a86db49806930fd431fa44cb49990912c54551a84251941a53034667490ce9398cea14348631a4a63508aea112d2321a863b49876a19ad4334a4501299ea5326d4308a84812997aa32bd463d9ccb951956a32ad43052928b5142aa1444864fa86b55194ea329d45d26465404402d25507406423d255044e1406d25503406405d25503406402d255014e6405d25501406405d25501406402d24503406405d24501406405d23506425404d235014e6405d235014a6404d23426ce2405d225074a6404d22504406405d224e44e3406d224e44e1406d205074a6404d205044e1406d025014e64059284064654029284064254029284064234029274a64264045284064654025284064254025284064234025274a6426404526425404402525426ce64025245014e6405524501406405523505ce4406523426ce5402523426ce2405523406465402522506ce1405521d06465402521d024e640
  | 3 => 0xcc1294d0baa2b60c5181ae18df23d8f589d868497622dcf3cff803eb67f805d1014bb812ff58564b3ff8045967f807f802447b181a534ab22a2197f807f807f807f804aa059b297be7f80548aff80524879b84045f2c44fa8e357064f2ab7911e7f807f8056217f807108c9540004808c4860014480050a0c3110c404026a75582300400c00002820e5809d24540040a0400e06005030648006223438400000040800406002f8be2f9bc6e8ba2e9b86d8b66d0b46c9b02c5a66959a663926448861a835e1771b96c1b06c1b16a5a16659064589605785e9685a560581605895054548525414e5314a1284a12948911425013e4f03c4e9384d9344c8328b82e4b32649122480208711a85816451128380e4300c03208419048042e351655008b5103b83bed6ca38dc3932270dd463dd3a8f98dcd2697b91cd20dd0dd5d3c62a8fccfe97ccf8dd034cd183b82d08b82d3cf927a5ea200080088089cc1cc3cf808ed3ed60060063d003fb873d03d06955d47549d19cc1c99cc38738f3d0dd3e97e95d8b5d4006710dd409bb064a3ca3e1279714d11c91cf9711c91ce90f9701a70ff1611c91ce90f9751fd3dd3dd4fe9de3dd3ddbd52fd3be9de3de4fe5f53decd6cf74f57d6cf6cf74f57d6cf6cf4ef74f4afd1fd3f68fc9fcbf69beabe3be3be9beabe3bd1fe3bd3f5abe8fe8ff8f53f673d3be9de9dd3be3de9f6bd58fd9df2
  | 4 => 0x35c85b82fcc8c037fc3dc7fc3fc2ee5433fc1faeb8341ce6275bfc3bd4495556b166a6b535473b8b61ce8e785bcd964a6a94c7589eb1cd431ac5f4956a1ea1282283a03211ea1282281a03202ea1282280a03202e91280a83a532022a0a53203671202a91290a53203201282691a80a73202a73691a83212a025723cfd5b724da9c55317f8078b580d3749cff807f8072cddeda89d2f742e7cfff802109c6041c920ed622464b40719a7f807f807f80062bff807f8072a71f8017c37f807f807f804a3c0f307f801a33730d76b43f47412e382c5b5bd1d1b103ff8012185b94831d3453aec9245a7598aa96e344b1d237d4e22acad523416d51448c504393325831bc919b880d028382770ff50a26d023dc35a67c2d26c8b846b156854a2c9d904d6e1fbb80deaf1da52f0e26b8bdca9f3e8619f8409015db17ff8001a7b457a6115429af3fef3ad54e7f80051b7f804f394c142dbb15139e92e53f2ca30ba87a0ee9dc90b094d81541e6a1ccba74aee2861d220736f325c0837c42468f7a07d7d97b9329cba45b4c26c84c7f801f0b488764897f803d1bff8008cca0374a2c9e9ef2d9d6a0c00121cb78b99205a1d0ab2a7f805b498090a9957f804bb5181f7f805c24364eff807f8044
  | _ => 0

def ax127Words (i : Nat) : Nat :=
  if i < 53 then (if i < 24 then (if i < 8 then word127_0 (i % 8) else (if i < 16 then word127_1 (i % 8) else word127_2 (i % 8))) else (if i < 40 then (if i < 32 then word127_3 (i % 8) else word127_4 (i % 8)) else (if i < 48 then word127_5 (i % 8) else word127_6 (i % 8)))) else 0

def ax127Count (k : Nat) : Nat := match k with
  | 12 => 1
  | 11 => 15
  | 10 => 171
  | 9 => 631
  | 8 => 337
  | 7 => 93
  | 6 => 8
  | _ => 0

def ax127Path (k : Nat) (i : Nat) : Nat := match k with
  | 12 => 0
  | 11 => readCompactBits ax127Words (43 + 12*i) 12
  | 10 => let v := readCompactBits ax127Words (2611 + 16*i) 16
    (readCompactBits ax127Words (2431 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 9 => let v := readCompactBits ax127Words (37449 + 20*i) 20
    (readCompactBits ax127Words (34041 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 8 => let v := readCompactBits ax127Words (155348 + 20*i) 20
    (readCompactBits ax127Words (149192 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 7 => let v := readCompactBits ax127Words (206716 + 19*i) 19
    (readCompactBits ax127Words (203404 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | 6 => let v := readCompactBits ax127Words (216167 + 15*i) 15
    (readCompactBits ax127Words (215687 + 60*(v >>> 12)) 60) ||| ((v &&& 4095) <<< 60)
  | _ => 0

def ax127Live (k : Nat) (i : Nat) : Nat := match k with
  | 12 => readCompactBits ax127Words (0 + 7*i) 7
  | 11 => readCompactBits ax127Words (223 + 8*i) 8
  | 10 => readCompactBits ax127Words (5347 + 9*i) 9
  | 9 => readCompactBits ax127Words (50069 + 10*i) 10
  | 8 => readCompactBits ax127Words (162088 + 11*i) 11
  | 7 => readCompactBits ax127Words (208483 + 12*i) 12
  | 6 => readCompactBits ax127Words (216287 + 13*i) 13
  | _ => 0

def ax127PoolIDs (k : Nat) (i : Nat) : List Nat := match k with
  | 12 => let v := readCompactBits ax127Words (37 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits ax127Words (7 + 5*(v &&& 7)) (5*n)
    compactIDsFromBits bits 5 n
  | 11 => let v := readCompactBits ax127Words (1719 + 13*i) 13
    let n := v >>> 8
    let bits := readCompactBits ax127Words (343 + 8*(v &&& 255)) (8*n)
    compactIDsFromBits bits 8 n
  | 10 => let v := readCompactBits ax127Words (24004 + 16*i) 16
    let n := v >>> 11
    let bits := readCompactBits ax127Words (6886 + 9*(v &&& 2047)) (9*n)
    compactIDsFromBits bits 9 n
  | 9 => let v := readCompactBits ax127Words (106359 + 18*i) 18
    let n := v >>> 13
    let bits := readCompactBits ax127Words (56379 + 10*(v &&& 8191)) (10*n)
    compactIDsFromBits bits 10 n
  | 8 => let v := readCompactBits ax127Words (182812 + 15*i) 15
    let n := v >>> 11
    let bits := readCompactBits ax127Words (165795 + 11*(v &&& 2047)) (11*n)
    compactIDsFromBits bits 11 n
  | 7 => let v := readCompactBits ax127Words (210739 + 10*i) 10
    let n := v >>> 7
    let bits := readCompactBits ax127Words (209599 + 12*(v &&& 127)) (12*n)
    compactIDsFromBits bits 12 n
  | 6 => let v := readCompactBits ax127Words (216404 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits ax127Words (216391 + 13*(v &&& 1)) (13*n)
    compactIDsFromBits bits 13 n
  | _ => []

def ax127Bucket (k : Nat) (i : Nat) : List Nat := match k with
  | 11 => let d := readCompactBits ax127Words (1914 + 4*(i % 9)) 4
    let off := ((i/9 + d) % 37)
    let v := readCompactBits ax127Words (1950 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 10 => let d := readCompactBits ax127Words (26740 + 7*(i % 108)) 7
    let off := ((i/108 + d) % 385)
    let v := readCompactBits ax127Words (27496 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 9 => let d := readCompactBits ax127Words (117717 + 8*(i % 417)) 8
    let off := ((i/417 + d) % 1481)
    let v := readCompactBits ax127Words (121053 + 19*off) 19
    if v >>> 11 == (i/104729)%251 then [v &&& 2047] else []
  | 8 => let d := readCompactBits ax127Words (187867 + 7*(i % 219)) 7
    let off := ((i/219 + d) % 778)
    let v := readCompactBits ax127Words (189400 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 7 => let d := readCompactBits ax127Words (211669 + 7*(i % 62)) 7
    let off := ((i/62 + d) % 224)
    let v := readCompactBits ax127Words (212103 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 6 => let d := readCompactBits ax127Words (216420 + 2*(i % 5)) 2
    let off := ((i/5 + d) % 19)
    let v := readCompactBits ax127Words (216430 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def ax31G : CompactGrid := (31,7,ax31P,ax31Q)

def ax31T : CompactTable := ((fun k => if k=7 then 0 else ax31Count k),ax31Path,ax31Live,ax31PoolIDs,ax31Bucket)

def ax31S : List (Nat × SliceSpec) := [(0, 8, 0, 23, 0, 0, 5, 5), (0, 0, 8, 21, 2, 240, 5, 4), (0, 1, 0, 30, 0, 0, 4, 4), (0, 4, 0, 27, 0, 0, 4, 4), (0, 2, 8, 21, 0, 0, 4, 4), (0, 10, 0, 21, 0, 0, 4, 4)]

def ax31D : RichDomains := (ax31S.map richSpecDomain).toArray

def ax31check (k : Nat) := richNode ax31G ax31T ax31D ax31Perms k

def ax31pools := richPoolList 31 ax31D [] (ax31PoolIDs 7 0)

def ax31links := linkedCandidates ax31G ax31T ax31Perms 6

def ax55G : CompactGrid := (55,6,ax55P,ax55Q)

def ax55T : CompactTable := ((fun k => if k=6 then 0 else ax55Count k),ax55Path,ax55Live,ax55PoolIDs,ax55Bucket)

def ax55S : List (Nat × SliceSpec) := [(0, 2, 0, 53, 0, 0, 5, 5), (0, 32, 0, 23, 0, 0, 5, 5), (0, 1, 0, 54, 0, 0, 4, 4), (0, 16, 0, 39, 0, 0, 4, 4)]

def ax55D : RichDomains := (ax55S.map richSpecDomain).toArray

def ax55check (k : Nat) := richNode ax55G ax55T ax55D ax55Perms k

def ax55pools := richPoolList 55 ax55D [] (ax55PoolIDs 6 0)

def ax55links := linkedCandidates ax55G ax55T ax55Perms 5

def ax87G : CompactGrid := (87,7,ax87P,ax87Q)

def ax87T : CompactTable := ((fun k => if k=7 then 0 else ax87Count k),ax87Path,ax87Live,ax87PoolIDs,ax87Bucket)

def ax87S : List (Nat × SliceSpec) := [(0, 2, 0, 85, 0, 0, 5, 5), (0, 64, 0, 23, 0, 0, 5, 5), (0, 0, 2, 69, 16, 983040, 5, 4), (0, 1, 0, 86, 0, 0, 4, 4), (0, 4, 0, 83, 0, 0, 4, 4), (0, 16, 2, 69, 0, 0, 4, 4), (0, 18, 0, 69, 0, 0, 4, 4), (0, 66, 0, 21, 0, 0, 4, 4)]

def ax87D : RichDomains := (ax87S.map richSpecDomain).toArray

def ax87check (k : Nat) := richNode ax87G ax87T ax87D ax87Perms k

def ax87pools := richPoolList 87 ax87D [] (ax87PoolIDs 7 0)

def ax87links := linkedCandidates ax87G ax87T ax87Perms 6

def ax91G : CompactGrid := (91,7,ax91P,ax91Q)

def ax91T : CompactTable := ((fun k => if k=7 then 0 else ax91Count k),ax91Path,ax91Live,ax91PoolIDs,ax91Bucket)

def ax91S : List (Nat × SliceSpec) := [(0, 1, 0, 90, 0, 0, 4, 4), (0, 2, 0, 89, 0, 0, 4, 4), (0, 8, 0, 83, 0, 0, 4, 4), (0, 16, 0, 75, 0, 0, 4, 4), (0, 64, 0, 27, 0, 0, 4, 4)]

def ax91D : RichDomains := (ax91S.map richSpecDomain).toArray

def ax91check (k : Nat) := richNode ax91G ax91T ax91D ax91Perms k

def ax91pools := richPoolList 91 ax91D [] (ax91PoolIDs 7 0)

def ax91links := linkedCandidates ax91G ax91T ax91Perms 6

def ax107G : CompactGrid := (107,7,ax107P,ax107Q)

def ax107T : CompactTable := ((fun k => if k=7 then 0 else ax107Count k),ax107Path,ax107Live,ax107PoolIDs,ax107Bucket)

def ax107S : List (Nat × SliceSpec) := [(0, 1, 0, 106, 0, 0, 5, 5), (0, 2, 0, 105, 0, 0, 5, 5), (0, 8, 0, 99, 0, 0, 5, 5), (0, 64, 0, 43, 0, 0, 5, 5), (0, 32, 0, 75, 0, 0, 4, 4), (0, 3, 0, 104, 0, 0, 4, 4), (0, 10, 0, 97, 0, 0, 4, 4), (0, 65, 0, 42, 0, 0, 4, 4)]

def ax107D : RichDomains := (ax107S.map richSpecDomain).toArray

def ax107check (k : Nat) := richNode ax107G ax107T ax107D ax107Perms k

def ax107pools := richPoolList 107 ax107D [] (ax107PoolIDs 7 0)

def ax107links := linkedCandidates ax107G ax107T ax107Perms 6

def ax63G : CompactGrid := (63,9,ax63P,ax63Q)

def ax63T : CompactTable := ((fun k => if k=9 then 0 else ax63Count k),ax63Path,ax63Live,ax63PoolIDs,ax63Bucket)

def ax63S : List (Nat × SliceSpec) := [(0, 1, 0, 62, 0, 0, 7, 7), (30, 1, 0, 62, 0, 0, 7, 7), (111, 1, 0, 62, 0, 0, 7, 7), (119, 1, 0, 62, 0, 0, 7, 7), (120, 1, 0, 62, 0, 0, 7, 7), (129, 1, 0, 62, 0, 0, 7, 7), (182, 1, 0, 62, 0, 0, 7, 7), (191, 1, 0, 62, 0, 0, 7, 7), (192, 1, 0, 62, 0, 0, 7, 7), (273, 1, 0, 62, 0, 0, 7, 7), (282, 1, 0, 62, 0, 0, 7, 7), (291, 1, 0, 62, 0, 0, 7, 7), (292, 1, 0, 62, 0, 0, 7, 7), (0, 2, 0, 61, 0, 0, 7, 7), (30, 2, 0, 61, 0, 0, 7, 7), (40, 2, 0, 61, 0, 0, 7, 7), (111, 2, 0, 61, 0, 0, 7, 7), (121, 2, 0, 61, 0, 0, 7, 7), (130, 2, 0, 61, 0, 0, 7, 7), (181, 2, 0, 61, 0, 0, 7, 7), (192, 2, 0, 61, 0, 0, 7, 7), (201, 2, 0, 61, 0, 0, 7, 7), (202, 2, 0, 61, 0, 0, 7, 7), (211, 2, 0, 61, 0, 0, 7, 7), (273, 2, 0, 61, 0, 0, 7, 7), (282, 2, 0, 61, 0, 0, 7, 7), (283, 2, 0, 61, 0, 0, 7, 7), (291, 2, 0, 61, 0, 0, 7, 7), (292, 2, 0, 61, 0, 0, 7, 7), (0, 16, 0, 47, 0, 0, 7, 7), (20, 16, 0, 47, 0, 0, 7, 7), (100, 16, 0, 47, 0, 0, 7, 7), (101, 16, 0, 47, 0, 0, 7, 7), (111, 16, 0, 47, 0, 0, 7, 7), (181, 16, 0, 47, 0, 0, 7, 7), (182, 16, 0, 47, 0, 0, 7, 7), (192, 16, 0, 47, 0, 0, 7, 7), (0, 32, 0, 31, 0, 0, 7, 7), (111, 32, 0, 31, 0, 0, 7, 7), (119, 32, 0, 31, 0, 0, 7, 7), (181, 32, 0, 31, 0, 0, 7, 7), (182, 32, 0, 31, 0, 0, 7, 7), (192, 32, 0, 31, 0, 0, 7, 7), (100, 8, 0, 55, 0, 0, 6, 6), (0, 0, 4, 42, 17, 983055, 6, 4), (0, 0, 8, 21, 34, 15728880, 6, 4), (0, 5, 0, 58, 0, 0, 5, 5), (0, 1, 4, 42, 16, 983040, 5, 4)]

def ax63D : RichDomains := (ax63S.map richSpecDomain).toArray

def ax63check (k : Nat) := richNode ax63G ax63T ax63D ax63Perms k

def ax63pools := richPoolList 63 ax63D [] (ax63PoolIDs 9 0)

def ax63links := linkedCandidates ax63G ax63T ax63Perms 8

def ax95G : CompactGrid := (95,10,ax95P,ax95Q)

def ax95T : CompactTable := ((fun k => if k=10 then 0 else ax95Count k),ax95Path,ax95Live,ax95PoolIDs,ax95Bucket)

def ax95S : List (Nat × SliceSpec) := [(0, 1, 0, 94, 0, 0, 7, 7), (20, 1, 0, 94, 0, 0, 7, 7), (56, 1, 0, 94, 0, 0, 7, 7), (110, 1, 0, 94, 0, 0, 7, 7), (119, 1, 0, 94, 0, 0, 7, 7), (120, 1, 0, 94, 0, 0, 7, 7), (138, 1, 0, 94, 0, 0, 7, 7), (139, 1, 0, 94, 0, 0, 7, 7), (182, 1, 0, 94, 0, 0, 7, 7), (191, 1, 0, 94, 0, 0, 7, 7), (192, 1, 0, 94, 0, 0, 7, 7), (200, 1, 0, 94, 0, 0, 7, 7), (201, 1, 0, 94, 0, 0, 7, 7), (202, 1, 0, 94, 0, 0, 7, 7), (218, 1, 0, 94, 0, 0, 7, 7), (219, 1, 0, 94, 0, 0, 7, 7), (220, 1, 0, 94, 0, 0, 7, 7), (221, 1, 0, 94, 0, 0, 7, 7), (263, 1, 0, 94, 0, 0, 7, 7), (272, 1, 0, 94, 0, 0, 7, 7), (273, 1, 0, 94, 0, 0, 7, 7), (281, 1, 0, 94, 0, 0, 7, 7), (282, 1, 0, 94, 0, 0, 7, 7), (283, 1, 0, 94, 0, 0, 7, 7), (299, 1, 0, 94, 0, 0, 7, 7), (300, 1, 0, 94, 0, 0, 7, 7), (301, 1, 0, 94, 0, 0, 7, 7), (302, 1, 0, 94, 0, 0, 7, 7), (0, 2, 0, 93, 0, 0, 7, 7), (28, 2, 0, 93, 0, 0, 7, 7), (37, 2, 0, 93, 0, 0, 7, 7), (39, 2, 0, 93, 0, 0, 7, 7), (40, 2, 0, 93, 0, 0, 7, 7), (55, 2, 0, 93, 0, 0, 7, 7), (57, 2, 0, 93, 0, 0, 7, 7), (59, 2, 0, 93, 0, 0, 7, 7), (109, 2, 0, 93, 0, 0, 7, 7), (111, 2, 0, 93, 0, 0, 7, 7), (118, 2, 0, 93, 0, 0, 7, 7), (120, 2, 0, 93, 0, 0, 7, 7), (121, 2, 0, 93, 0, 0, 7, 7), (136, 2, 0, 93, 0, 0, 7, 7), (138, 2, 0, 93, 0, 0, 7, 7), (139, 2, 0, 93, 0, 0, 7, 7), (181, 2, 0, 93, 0, 0, 7, 7), (190, 2, 0, 93, 0, 0, 7, 7), (199, 2, 0, 93, 0, 0, 7, 7), (201, 2, 0, 93, 0, 0, 7, 7), (202, 2, 0, 93, 0, 0, 7, 7), (217, 2, 0, 93, 0, 0, 7, 7), (219, 2, 0, 93, 0, 0, 7, 7), (220, 2, 0, 93, 0, 0, 7, 7), (221, 2, 0, 93, 0, 0, 7, 7), (262, 2, 0, 93, 0, 0, 7, 7), (271, 2, 0, 93, 0, 0, 7, 7), (273, 2, 0, 93, 0, 0, 7, 7), (280, 2, 0, 93, 0, 0, 7, 7), (282, 2, 0, 93, 0, 0, 7, 7), (283, 2, 0, 93, 0, 0, 7, 7), (298, 2, 0, 93, 0, 0, 7, 7), (300, 2, 0, 93, 0, 0, 7, 7), (302, 2, 0, 93, 0, 0, 7, 7), (0, 4, 0, 91, 0, 0, 7, 7), (110, 4, 0, 91, 0, 0, 7, 7), (118, 4, 0, 91, 0, 0, 7, 7), (119, 4, 0, 91, 0, 0, 7, 7), (172, 4, 0, 91, 0, 0, 7, 7), (191, 4, 0, 91, 0, 0, 7, 7), (202, 4, 0, 91, 0, 0, 7, 7), (217, 4, 0, 91, 0, 0, 7, 7), (253, 4, 0, 91, 0, 0, 7, 7), (271, 4, 0, 91, 0, 0, 7, 7), (280, 4, 0, 91, 0, 0, 7, 7), (283, 4, 0, 91, 0, 0, 7, 7), (299, 4, 0, 91, 0, 0, 7, 7), (0, 8, 0, 87, 0, 0, 7, 7), (10, 8, 0, 87, 0, 0, 7, 7), (59, 8, 0, 87, 0, 0, 7, 7), (91, 8, 0, 87, 0, 0, 7, 7), (101, 8, 0, 87, 0, 0, 7, 7), (118, 8, 0, 87, 0, 0, 7, 7), (119, 8, 0, 87, 0, 0, 7, 7), (120, 8, 0, 87, 0, 0, 7, 7), (136, 8, 0, 87, 0, 0, 7, 7), (137, 8, 0, 87, 0, 0, 7, 7), (138, 8, 0, 87, 0, 0, 7, 7), (172, 8, 0, 87, 0, 0, 7, 7), (181, 8, 0, 87, 0, 0, 7, 7), (199, 8, 0, 87, 0, 0, 7, 7), (200, 8, 0, 87, 0, 0, 7, 7), (201, 8, 0, 87, 0, 0, 7, 7), (217, 8, 0, 87, 0, 0, 7, 7), (218, 8, 0, 87, 0, 0, 7, 7), (219, 8, 0, 87, 0, 0, 7, 7), (221, 8, 0, 87, 0, 0, 7, 7), (253, 8, 0, 87, 0, 0, 7, 7), (262, 8, 0, 87, 0, 0, 7, 7), (263, 8, 0, 87, 0, 0, 7, 7), (280, 8, 0, 87, 0, 0, 7, 7), (298, 8, 0, 87, 0, 0, 7, 7), (299, 8, 0, 87, 0, 0, 7, 7), (302, 8, 0, 87, 0, 0, 7, 7), (0, 16, 0, 79, 0, 0, 7, 7), (10, 16, 0, 79, 0, 0, 7, 7), (20, 16, 0, 79, 0, 0, 7, 7), (56, 16, 0, 79, 0, 0, 7, 7), (91, 16, 0, 79, 0, 0, 7, 7), (101, 16, 0, 79, 0, 0, 7, 7), (110, 16, 0, 79, 0, 0, 7, 7), (139, 16, 0, 79, 0, 0, 7, 7), (172, 16, 0, 79, 0, 0, 7, 7), (191, 16, 0, 79, 0, 0, 7, 7), (192, 16, 0, 79, 0, 0, 7, 7), (217, 16, 0, 79, 0, 0, 7, 7), (218, 16, 0, 79, 0, 0, 7, 7), (219, 16, 0, 79, 0, 0, 7, 7), (220, 16, 0, 79, 0, 0, 7, 7), (253, 16, 0, 79, 0, 0, 7, 7), (262, 16, 0, 79, 0, 0, 7, 7), (263, 16, 0, 79, 0, 0, 7, 7), (272, 16, 0, 79, 0, 0, 7, 7), (298, 16, 0, 79, 0, 0, 7, 7), (299, 16, 0, 79, 0, 0, 7, 7), (301, 16, 0, 79, 0, 0, 7, 7), (0, 64, 0, 31, 0, 0, 7, 7), (20, 64, 0, 31, 0, 0, 7, 7), (109, 64, 0, 31, 0, 0, 7, 7), (110, 64, 0, 31, 0, 0, 7, 7), (119, 64, 0, 31, 0, 0, 7, 7), (181, 64, 0, 31, 0, 0, 7, 7), (191, 64, 0, 31, 0, 0, 7, 7), (199, 64, 0, 31, 0, 0, 7, 7), (263, 64, 0, 31, 0, 0, 7, 7), (283, 64, 0, 31, 0, 0, 7, 7), (0, 0, 2, 69, 24, 1044480, 6, 4), (0, 0, 8, 21, 66, 251658480, 6, 4), (0, 10, 0, 85, 0, 0, 5, 5), (0, 18, 0, 77, 0, 0, 5, 5), (0, 72, 0, 23, 0, 0, 5, 5), (0, 2, 8, 21, 64, 251658240, 5, 4), (0, 8, 2, 69, 16, 983040, 5, 4), (0, 16, 2, 69, 8, 61440, 5, 4), (0, 64, 8, 21, 2, 240, 5, 4), (0, 3, 0, 92, 0, 0, 4, 4), (0, 5, 0, 90, 0, 0, 4, 4), (0, 6, 0, 89, 0, 0, 4, 4), (0, 17, 0, 78, 0, 0, 4, 4), (0, 20, 0, 75, 0, 0, 4, 4), (0, 65, 0, 30, 0, 0, 4, 4), (0, 68, 0, 27, 0, 0, 4, 4), (0, 24, 2, 69, 0, 0, 4, 4), (0, 26, 0, 69, 0, 0, 4, 4), (0, 66, 8, 21, 0, 0, 4, 4), (0, 74, 0, 21, 0, 0, 4, 4)]

def ax95D : RichDomains := (ax95S.map richSpecDomain).toArray

def ax95check (k : Nat) := richNode ax95G ax95T ax95D ax95Perms k

def ax95pools := richPoolList 95 ax95D [] (ax95PoolIDs 10 0)

def ax95links := linkedCandidates ax95G ax95T ax95Perms 9

def ax111G : CompactGrid := (111,10,ax111P,ax111Q)

def ax111T : CompactTable := ((fun k => if k=10 then 0 else ax111Count k),ax111Path,ax111Live,ax111PoolIDs,ax111Bucket)

def ax111S : List (Nat × SliceSpec) := [(0, 1, 0, 110, 0, 0, 7, 7), (48, 1, 0, 110, 0, 0, 7, 7), (101, 1, 0, 110, 0, 0, 7, 7), (129, 1, 0, 110, 0, 0, 7, 7), (141, 1, 0, 110, 0, 0, 7, 7), (210, 1, 0, 110, 0, 0, 7, 7), (0, 2, 0, 109, 0, 0, 7, 7), (30, 2, 0, 109, 0, 0, 7, 7), (48, 2, 0, 109, 0, 0, 7, 7), (111, 2, 0, 109, 0, 0, 7, 7), (127, 2, 0, 109, 0, 0, 7, 7), (130, 2, 0, 109, 0, 0, 7, 7), (192, 2, 0, 109, 0, 0, 7, 7), (210, 2, 0, 109, 0, 0, 7, 7), (222, 2, 0, 109, 0, 0, 7, 7), (273, 2, 0, 109, 0, 0, 7, 7), (291, 2, 0, 109, 0, 0, 7, 7), (292, 2, 0, 109, 0, 0, 7, 7), (300, 2, 0, 109, 0, 0, 7, 7), (0, 4, 0, 107, 0, 0, 7, 7), (10, 4, 0, 107, 0, 0, 7, 7), (49, 4, 0, 107, 0, 0, 7, 7), (91, 4, 0, 107, 0, 0, 7, 7), (127, 4, 0, 107, 0, 0, 7, 7), (128, 4, 0, 107, 0, 0, 7, 7), (136, 4, 0, 107, 0, 0, 7, 7), (172, 4, 0, 107, 0, 0, 7, 7), (209, 4, 0, 107, 0, 0, 7, 7), (217, 4, 0, 107, 0, 0, 7, 7), (299, 4, 0, 107, 0, 0, 7, 7), (0, 8, 0, 103, 0, 0, 7, 7), (101, 8, 0, 103, 0, 0, 7, 7), (127, 8, 0, 103, 0, 0, 7, 7), (137, 8, 0, 103, 0, 0, 7, 7), (141, 8, 0, 103, 0, 0, 7, 7), (210, 8, 0, 103, 0, 0, 7, 7), (218, 8, 0, 103, 0, 0, 7, 7), (0, 32, 0, 79, 0, 0, 7, 7), (20, 32, 0, 79, 0, 0, 7, 7), (56, 32, 0, 79, 0, 0, 7, 7), (91, 32, 0, 79, 0, 0, 7, 7), (101, 32, 0, 79, 0, 0, 7, 7), (110, 32, 0, 79, 0, 0, 7, 7), (139, 32, 0, 79, 0, 0, 7, 7), (172, 32, 0, 79, 0, 0, 7, 7), (182, 32, 0, 79, 0, 0, 7, 7), (190, 32, 0, 79, 0, 0, 7, 7), (191, 32, 0, 79, 0, 0, 7, 7), (220, 32, 0, 79, 0, 0, 7, 7), (253, 32, 0, 79, 0, 0, 7, 7), (271, 32, 0, 79, 0, 0, 7, 7), (272, 32, 0, 79, 0, 0, 7, 7), (273, 32, 0, 79, 0, 0, 7, 7), (299, 32, 0, 79, 0, 0, 7, 7), (300, 32, 0, 79, 0, 0, 7, 7), (301, 32, 0, 79, 0, 0, 7, 7), (0, 64, 0, 47, 0, 0, 7, 7), (48, 64, 0, 47, 0, 0, 7, 7), (127, 64, 0, 47, 0, 0, 7, 7), (208, 64, 0, 47, 0, 0, 7, 7), (210, 64, 0, 47, 0, 0, 7, 7), (291, 64, 0, 47, 0, 0, 7, 7), (0, 0, 2, 69, 40, 15790080, 6, 4), (0, 0, 4, 42, 65, 251658255, 6, 4), (0, 6, 0, 105, 0, 0, 5, 5), (0, 1, 4, 42, 64, 251658240, 5, 4), (0, 8, 2, 69, 32, 15728640, 5, 4), (0, 32, 2, 69, 8, 61440, 5, 4), (0, 64, 4, 42, 1, 15, 5, 4), (0, 9, 0, 102, 0, 0, 4, 4), (0, 7, 0, 104, 0, 0, 4, 4), (0, 14, 0, 97, 0, 0, 4, 4), (0, 40, 2, 69, 0, 0, 4, 4), (0, 65, 4, 42, 0, 0, 4, 4)]

def ax111D : RichDomains := (ax111S.map richSpecDomain).toArray

def ax111check (k : Nat) := richNode ax111G ax111T ax111D ax111Perms k

def ax111pools := richPoolList 111 ax111D [] (ax111PoolIDs 10 0)

def ax111links := linkedCandidates ax111G ax111T ax111Perms 9

def ax127G : CompactGrid := (127,12,ax127P,ax127Q)

def ax127T : CompactTable := (ax127Count,ax127Path,ax127Live,ax127PoolIDs,ax127Bucket)

def ax127S : List (Nat × SliceSpec) := [(0, 1, 0, 126, 0, 0, 10, 10), (111, 1, 0, 126, 0, 0, 10, 10), (119, 1, 0, 126, 0, 0, 10, 10), (120, 1, 0, 126, 0, 0, 10, 10), (121, 1, 0, 126, 0, 0, 10, 10), (129, 1, 0, 126, 0, 0, 10, 10), (131, 1, 0, 126, 0, 0, 10, 10), (138, 1, 0, 126, 0, 0, 10, 10), (182, 1, 0, 126, 0, 0, 10, 10), (201, 1, 0, 126, 0, 0, 10, 10), (282, 1, 0, 126, 0, 0, 10, 10), (302, 1, 0, 126, 0, 0, 10, 10), (0, 2, 0, 125, 0, 0, 10, 10), (121, 2, 0, 125, 0, 0, 10, 10), (221, 2, 0, 125, 0, 0, 10, 10), (271, 2, 0, 125, 0, 0, 10, 10), (0, 4, 0, 123, 0, 0, 10, 10), (0, 8, 0, 119, 0, 0, 10, 10), (0, 16, 0, 111, 0, 0, 10, 10), (101, 16, 0, 111, 0, 0, 10, 10), (218, 16, 0, 111, 0, 0, 10, 10), (0, 32, 0, 95, 0, 0, 10, 10), (91, 32, 0, 95, 0, 0, 10, 10), (101, 32, 0, 95, 0, 0, 10, 10), (109, 32, 0, 95, 0, 0, 10, 10), (110, 32, 0, 95, 0, 0, 10, 10), (111, 32, 0, 95, 0, 0, 10, 10), (119, 32, 0, 95, 0, 0, 10, 10), (139, 32, 0, 95, 0, 0, 10, 10), (191, 32, 0, 95, 0, 0, 10, 10), (272, 32, 0, 95, 0, 0, 10, 10), (299, 32, 0, 95, 0, 0, 10, 10), (0, 64, 0, 63, 0, 0, 9, 9), (100, 64, 0, 63, 0, 0, 9, 9), (101, 64, 0, 63, 0, 0, 9, 9), (109, 64, 0, 63, 0, 0, 9, 9), (110, 64, 0, 63, 0, 0, 9, 9), (111, 64, 0, 63, 0, 0, 9, 9), (119, 64, 0, 63, 0, 0, 9, 9), (120, 64, 0, 63, 0, 0, 9, 9), (121, 64, 0, 63, 0, 0, 9, 9), (127, 64, 0, 63, 0, 0, 9, 9), (181, 64, 0, 63, 0, 0, 9, 9), (182, 64, 0, 63, 0, 0, 9, 9), (190, 64, 0, 63, 0, 0, 9, 9), (191, 64, 0, 63, 0, 0, 9, 9), (192, 64, 0, 63, 0, 0, 9, 9), (273, 64, 0, 63, 0, 0, 9, 9), (282, 64, 0, 63, 0, 0, 9, 9), (283, 64, 0, 63, 0, 0, 9, 9), (291, 64, 0, 63, 0, 0, 9, 9), (292, 64, 0, 63, 0, 0, 9, 9), (0, 0, 2, 69, 56, 16773120, 7, 4), (0, 0, 4, 42, 81, 252641295, 7, 4), (0, 0, 8, 21, 98, 267387120, 7, 4), (0, 0, 16, 104, 7, 4095, 7, 4), (0, 3, 0, 124, 0, 0, 7, 7), (0, 5, 0, 122, 0, 0, 7, 7), (0, 6, 0, 121, 0, 0, 7, 7), (0, 9, 0, 118, 0, 0, 7, 7), (0, 10, 0, 117, 0, 0, 7, 7), (0, 17, 0, 110, 0, 0, 7, 7), (0, 18, 0, 109, 0, 0, 7, 7), (0, 20, 0, 107, 0, 0, 7, 7), (0, 24, 0, 103, 0, 0, 7, 7), (0, 33, 0, 94, 0, 0, 7, 7), (0, 34, 0, 93, 0, 0, 7, 7), (0, 36, 0, 91, 0, 0, 7, 7), (0, 40, 0, 87, 0, 0, 7, 7), (0, 48, 0, 79, 0, 0, 7, 7), (0, 65, 0, 62, 0, 0, 7, 7), (0, 66, 0, 61, 0, 0, 7, 7), (0, 80, 0, 47, 0, 0, 7, 7), (0, 96, 0, 31, 0, 0, 7, 7), (0, 12, 0, 115, 0, 0, 6, 6), (0, 68, 0, 59, 0, 0, 6, 6), (0, 72, 0, 55, 0, 0, 6, 6), (0, 1, 4, 42, 80, 252641280, 6, 4), (0, 1, 16, 104, 6, 4080, 6, 4), (0, 2, 8, 21, 96, 267386880, 6, 4), (0, 2, 16, 104, 5, 3855, 6, 4), (0, 4, 16, 104, 3, 255, 6, 4), (0, 8, 2, 69, 48, 16711680, 6, 4), (0, 16, 2, 69, 40, 15790080, 6, 4), (0, 16, 4, 42, 65, 251658255, 6, 4), (0, 32, 2, 69, 24, 1044480, 6, 4), (0, 32, 8, 21, 66, 251658480, 6, 4), (0, 64, 4, 42, 17, 983055, 6, 4), (0, 64, 8, 21, 34, 15728880, 6, 4), (0, 14, 0, 113, 0, 0, 5, 5), (0, 19, 0, 108, 0, 0, 5, 5), (0, 21, 0, 106, 0, 0, 5, 5), (0, 26, 0, 101, 0, 0, 5, 5), (0, 69, 0, 58, 0, 0, 5, 5), (0, 74, 0, 53, 0, 0, 5, 5), (0, 84, 0, 43, 0, 0, 5, 5), (0, 104, 0, 23, 0, 0, 5, 5), (0, 3, 16, 104, 4, 3840, 5, 4), (0, 5, 16, 104, 2, 240, 5, 4), (0, 6, 16, 104, 1, 15, 5, 4), (0, 17, 4, 42, 64, 251658240, 5, 4), (0, 24, 2, 69, 32, 15728640, 5, 4), (0, 34, 8, 21, 64, 251658240, 5, 4), (0, 40, 2, 69, 16, 983040, 5, 4), (0, 48, 2, 69, 8, 61440, 5, 4), (0, 65, 4, 42, 16, 983040, 5, 4), (0, 66, 8, 21, 32, 15728640, 5, 4), (0, 80, 4, 42, 1, 15, 5, 4), (0, 96, 8, 21, 2, 240, 5, 4), (0, 11, 0, 116, 0, 0, 4, 4), (0, 13, 0, 114, 0, 0, 4, 4), (0, 25, 0, 102, 0, 0, 4, 4), (0, 35, 0, 92, 0, 0, 4, 4), (0, 37, 0, 90, 0, 0, 4, 4), (0, 38, 0, 89, 0, 0, 4, 4), (0, 41, 0, 86, 0, 0, 4, 4), (0, 44, 0, 83, 0, 0, 4, 4), (0, 49, 0, 78, 0, 0, 4, 4), (0, 73, 0, 54, 0, 0, 4, 4), (0, 82, 0, 45, 0, 0, 4, 4), (0, 88, 0, 39, 0, 0, 4, 4), (0, 97, 0, 30, 0, 0, 4, 4), (0, 7, 16, 104, 0, 0, 4, 4), (0, 30, 0, 97, 0, 0, 4, 4), (0, 56, 2, 69, 0, 0, 4, 4), (0, 81, 4, 42, 0, 0, 4, 4), (0, 85, 0, 42, 0, 0, 4, 4), (0, 98, 8, 21, 0, 0, 4, 4), (0, 106, 0, 21, 0, 0, 4, 4)]

def ax127D : RichDomains := (ax127S.map richSpecDomain).toArray

def ax127check (k : Nat) := richNode ax127G ax127T ax127D ax127Perms k

end ComputeBench

open ComputeBench

def main : IO Unit := do
  let badTotal ← IO.mkRef 0
  do
    for k in List.range 13 do
      let count := tab21.count k
      let bad := (List.range count).filter (fun i => !(check21 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact21\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := tab23.count k
      let bad := (List.range count).filter (fun i => !(check23 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact23\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := tab27.count k
      let bad := (List.range count).filter (fun i => !(check27 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact27\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := tab31.count k
      let bad := (List.range count).filter (fun i => !(check31 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact31\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := tab55.count k
      let bad := (List.range count).filter (fun i => !(check55 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact55\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := tab63.count k
      let bad := (List.range count).filter (fun i => !(check63 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact63\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := tab85.count k
      let bad := (List.range count).filter (fun i => !(check85 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact85\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := tab87.count k
      let bad := (List.range count).filter (fun i => !(check87 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact87\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := tab91.count k
      let bad := (List.range count).filter (fun i => !(check91 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact91\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := tab95.count k
      let bad := (List.range count).filter (fun i => !(check95 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact95\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := tab107.count k
      let bad := (List.range count).filter (fun i => !(check107 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact107\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := tab111.count k
      let bad := (List.range count).filter (fun i => !(check111 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact111\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := tab119.count k
      let bad := (List.range count).filter (fun i => !(check119 k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tcompact119\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := ax31T.count k
      let bad := (List.range count).filter (fun i => !(ax31check k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tax31\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := ax55T.count k
      let bad := (List.range count).filter (fun i => !(ax55check k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tax55\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := ax87T.count k
      let bad := (List.range count).filter (fun i => !(ax87check k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tax87\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := ax91T.count k
      let bad := (List.range count).filter (fun i => !(ax91check k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tax91\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := ax107T.count k
      let bad := (List.range count).filter (fun i => !(ax107check k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tax107\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := ax63T.count k
      let bad := (List.range count).filter (fun i => !(ax63check k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tax63\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := ax95T.count k
      let bad := (List.range count).filter (fun i => !(ax95check k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tax95\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := ax111T.count k
      let bad := (List.range count).filter (fun i => !(ax111check k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tax111\t{k}\t{count}\t{bad}"
  do
    for k in List.range 13 do
      let count := ax127T.count k
      let bad := (List.range count).filter (fun i => !(ax127check k i))
      badTotal.modify (· + bad.length)
      IO.println s!"CHECK\tax127\t{k}\t{count}\t{bad}"
  do
    let names : List Nat := [9, 27, 39, 108, 109, 118, 171, 180, 181, 189, 190, 198, 199, 201, 270, 271, 279, 280, 282]
    let bad := names.filter (fun t => !(primCheck ax31G ax31pools ax31links t))
    badTotal.modify (· + bad.length)
    IO.println s!"PRIM\tax31\t{names.length}\t{bad}"
  do
    let names : List Nat := [99]
    let bad := names.filter (fun t => !(primCheck ax55G ax55pools ax55links t))
    badTotal.modify (· + bad.length)
    IO.println s!"PRIM\tax55\t{names.length}\t{bad}"
  do
    let names : List Nat := [9, 36, 54, 55, 58, 90, 117, 118, 135, 136, 171, 180, 181, 198, 199, 216, 217, 220, 279, 297, 298, 301]
    let bad := names.filter (fun t => !(primCheck ax87G ax87pools ax87links t))
    badTotal.modify (· + bad.length)
    IO.println s!"PRIM\tax87\t{names.length}\t{bad}"
  do
    let names : List Nat := [9, 109, 171, 190]
    let bad := names.filter (fun t => !(primCheck ax91G ax91pools ax91links t))
    badTotal.modify (· + bad.length)
    IO.println s!"PRIM\tax91\t{names.length}\t{bad}"
  do
    let names : List Nat := [9, 27, 48, 90, 109, 126, 138, 171, 189, 190, 207, 210, 270, 271, 288]
    let bad := names.filter (fun t => !(primCheck ax107G ax107pools ax107links t))
    badTotal.modify (· + bad.length)
    IO.println s!"PRIM\tax107\t{names.length}\t{bad}"
  do
    let names : List Nat := [100, 108, 110, 118, 120, 126, 129, 272, 281, 282, 290]
    let bad := names.filter (fun t => !(primCheck ax63G ax63pools ax63links t))
    badTotal.modify (· + bad.length)
    IO.println s!"PRIM\tax63\t{names.length}\t{bad}"
  do
    let names : List Nat := [100, 108, 109, 138, 190, 282, 298]
    let bad := names.filter (fun t => !(primCheck ax95G ax95pools ax95links t))
    badTotal.modify (· + bad.length)
    IO.println s!"PRIM\tax95\t{names.length}\t{bad}"
  do
    let names : List Nat := [100, 209, 217]
    let bad := names.filter (fun t => !(primCheck ax111G ax111pools ax111links t))
    badTotal.modify (· + bad.length)
    IO.println s!"PRIM\tax111\t{names.length}\t{bad}"
  let n ← badTotal.get
  IO.println s!"TOTAL_BAD\t{n}"
  if n > 0 then throw (IO.userError s!"certificate failures: {n}")

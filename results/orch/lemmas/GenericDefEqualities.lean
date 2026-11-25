import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Image
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Intervals
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace C2444
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def Live (target : Sig) (k t : Nat) (U : Finset Sig) : Prop :=
  ∀ P : Nat → Nat → Finset Sig → Prop,
    ((hp : proper target) → P 0 0 {target}) →
    (∀ {k t : Nat} {U : Finset Sig} {a : Sig}, (ha : proper a) → (hf : neg a ∉ insert a U) → P k t (insert (neg a) U) → P (k+1) (t+1) (insert a U)) →
    (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}, (ha : proper a) → (hb : proper b) → (ne : a ≠ b) → (hf : bin d a b ∉ insert a (insert b U)) → P k t (insert (bin d a b) U) → P (k+1) t (insert a (insert b U))) →
    P k t U
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

def Reach {R : Type} (roots : List (Wire R)) (k : Nat) (ws : List (Wire R)) : Prop :=
  ∀ P : Nat → List (Wire R) → Prop,
    (P 0 roots) →
    (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R}, P p bank → (ha : Available bank a) → P (p+1) (inv a :: bank)) →
    (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R}, (op : Bool) → P p bank → (ha : Available bank a) → (hb : Available bank b) → P (p+1) (combine op a b :: bank)) →
    P k ws
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R : Type} (goal : Wire R) (k : Nat) (ws : List (Wire R)) : Prop :=
  ∀ P : Nat → List (Wire R) → Prop,
    (P 0 [goal]) →
    (∀ {s : Nat} {xs zs : List (Wire R)}, (p : xs.Perm zs) → P s xs → P s zs) →
    (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)}, (save : Bool) → P s (inv a :: kept save a rest) → P (s+1) (a::rest)) →
    (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)}, (op : Bool) → (ka : Bool) → (kb : Bool) → P s (combine op a b :: kept ka a (kept kb b rest)) → P (s+1) (a::b::rest)) →
    P k ws
def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
def pairSeed (a b : Fin 9) : Sig := inputs.getD a.val zero &&& inputs.getD b.val zero
def FirstPair (p : Fin 9 × Fin 9) : Prop := p ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(4,6)] : List (Fin 9 × Fin 9))
def neighbor (i : Fin 9) : Nat := [5,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))

def chartEnd (m : Nat) : Fin 9 := if m=1023 then 1 else if m=1535 then 2 else 3
def chartGoal (m : Nat) : Sig :=
  if 511 < m then graphGoal m &&& ~~~(pairSeed 0 (chartEnd m)) else graphGoal m

def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
abbrev BoundPool := (Sig) × (Nat) × (Nat) × (List Sig)
abbrev BoundPool.domain (v : BoundPool) : Sig := v.1
abbrev BoundPool.bound (v : BoundPool) : Nat := v.2.1
abbrev BoundPool.paid (v : BoundPool) : Nat := v.2.2.1
abbrev BoundPool.wires (v : BoundPool) : List Sig := v.2.2.2


def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev IndexTree (α : Type) := List α
def IndexTree.leaf {α : Type} (xs : List α) : IndexTree α := xs
def IndexTree.fork {α : Type} (_p : Nat) (a b : IndexTree α) : IndexTree α := a ++ b
def IndexTree.read {α} (a : IndexTree α) (i : Nat) := a[i]?
def IndexTree.values {α} (a : IndexTree α) := a
abbrev Forest := (Nat) × (Nat) × (Nat → Bits × Bits) × (IndexTree ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
abbrev Forest.mask (v : Forest) : Nat := v.1
abbrev Forest.cap (v : Forest) : Nat := v.2.1
abbrev Forest.samples (v : Forest) : Nat → Bits × Bits := v.2.2.1
abbrev Forest.cols (v : Forest) : IndexTree ColumnInfo := v.2.2.2.1
abbrev Forest.autos (v : Forest) : Array (List Nat) := v.2.2.2.2.1
abbrev Forest.levels (v : Forest) : Nat → Packing := v.2.2.2.2.2.1
abbrev Forest.index (v : Forest) : Nat → Nat → Option (Nat × Nat) := v.2.2.2.2.2.2


def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD (chartEnd g.mask).val defaultDecor))
  if 511 < g.mask then ws.map (fun w => dbin false w nonedge) else ws
def targetOf (g : Forest) := chartGoal g.mask

def chartSamples (m : Nat) (v : Nat → Bits) :=
  if 511 < m then liftGoal m v &&& ~~~(v 0 &&& v (chartEnd m).val) else liftGoal m v
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
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
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

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
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
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
end C2444
namespace C4338
abbrev Sig:=BitVec 512
def zero : Sig:=0
def one : Sig:=BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig:=if d then a ||| b else a &&& b
def proper (a : Sig) : Prop:=a≠zero∧a≠one
def Live (target : Sig) : Nat → Nat → Finset Sig → Prop:=fun k t S =>
  ∀ (M : (Nat → Nat → Finset Sig → Prop)),(proper target → M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig},proper a → neg a ∉ insert a U → M k t (insert (neg a) U) → M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool},proper a → proper b → a≠b → bin d a b ∉ insert a (insert b U) → M k t (insert (bin d a b) U) → M (k+1) t (insert a (insert b U))) →
  M k t S
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs:=g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def represented (w : List Sig) (v : Sig) : Prop:=v ∈ w∨¬proper v
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w,proper a∧z=neg a) ∨
  (∃ d a b,a ∈ w∧b ∈ w∧proper a∧proper b∧a≠b∧z=bin d a b)
def bit (i : Fin 512) (a : Sig) : Bool:=a.getLsbD i.val
abbrev Wire (R : Type):=R → Bool
def inv {R} (a : Wire R) : Wire R:=fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r||b r else fun r => a r&&b r
def Constant {R} (a : Wire R) : Prop:=∃ b : Bool,a=fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat:=by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat:=(xs.map cost).sum
def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop:=v ∈ pool∨Constant v
def supply {R} (pool xs : List (Wire R)):=∀ a ∈ xs,Available pool a
def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop:=fun p bank =>
  ∀ (M : (Nat → List (Wire R) → Prop)),(M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R},M p bank → Available bank a → M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool),M p bank → Available bank a → Available bank b → M (p+1) (combine op a b :: bank)) →
  M p bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α):=if save then x::xs else xs
def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop:=fun s ws =>
  ∀ (M : (Nat → List (Wire R) → Prop)),(M 0 [goal]) →
  (∀ {s : Nat} {xs zs : List (Wire R)},xs.Perm zs → M s xs → M s zs) →
  (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),M s (inv a :: kept save a rest) → M (s+1) (a::rest)) →
  (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),M s (combine op a b :: kept ka a (kept kb b rest)) → M (s+1) (a::b::rest)) →
  M s ws
def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)
abbrev Row:=Fin 512
def observe (a : Sig) : Wire Row:=fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
def inputs : List Sig:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig:=0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def oldSeed : Sig:=0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888
def sample (r : Row) (j : Fin 9):=bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0&&x 1)||(x 1&&x 2)||(x 2&&x 3)||(x 3&&x 4)||(x 4&&x 0) ||
  (x 0&&x 5)||(x 1&&x 6)||(x 2&&x 7)||(x 3&&x 8)||(x 5&&x 7) ||
  (x 6&&x 8)||(x 8&&x 5)
def neighbor (i : Fin 9) : Nat:=[4,2,1,2,0,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row:=Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row:=Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))
def rename (f : Row → Row) (a : Sig):=table fun r => bit (f r) a
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank,Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p
def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t,k ≤ cap → ¬Live T k t S
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row,bit r T≠bit s T∧∀ v ∈ roots,v≠a → bit r v=bit s v
def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i,bit (pos i) T=true∧bit (negRow i) T=false) ∧
  ∀ w i,(asig w).1.getLsbD i.val=bit (pos i) w ∧
    (asig w).2.getLsbD i.val=bit (negRow i) w
def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws
def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig),(∀ r,bit (f r) d=true) ∧
    (∀ a ∈ raw,Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank,Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p
def masked (d a : Sig):=a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m:=masked d a
  m==zero||m==d||(pool.map (masked d)).any (fun v => v==m)
def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool,Available bank (restrictRows f (observe a))
abbrev Choice:=Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1&&(c.1==2||availableB d pool c.2.2)
def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none
def isMaskedConstant (d a : Sig):=masked d a==zero||masked d a==d
def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d))&&ws.all (availableB d pool)
abbrev Move:=Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row:=Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig):=(m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
def movedRow (ms : List Move) (r : Row):=ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig):=ms.foldr wordMove a
def freeWord (roots : List Sig) (w : Sig):=w==zero||w==one||roots.contains w
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T==G&&raw.all (fun a => freeWord base (movedWord ms a))
def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w==a||bit rs.1 w==bit rs.2 w)
def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G&&checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1==zero||movedWord ms a.1==one)
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat):=(selected m).map Prod.snd
def vertex (m j : Nat):=if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x:=vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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
  let fixed:=z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x:=inputs.getD j zero
    let step:=Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i:=v &&& 15
  let j:=v >>> 4
  let a:=inputs.getD i zero
  let b:=inputs.getD j zero
  let d:=(1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r:=1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def properB (T : Sig):=T != zero&&T != one
def assertSize (m hints L : Nat) :=
  let xs:=graphPairs m hints
  properB (graphGoal m)&&checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
abbrev ColumnInfo:=Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat):=m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~oldSeed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L):=c
  let ms:=fixRows z o
  let free:=colFree m z o
  let G:=movedWord ms (chartGoal m)
  let xs:=supportPairs s
  let count:=(xs.map Prod.fst).toFinset.card
  properB G&&checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs&&decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))
def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old)&&properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1==q)).map Prod.snd).getD 0
abbrev BoundPool:=(Sig) × (Nat) × (Nat) × (List Sig)
abbrev BoundPool.domain (c : BoundPool) : Sig:=c.1
abbrev BoundPool.bound (c : BoundPool) : Nat:=c.2.1
abbrev BoundPool.paid (c : BoundPool) : Nat:=c.2.2.1
abbrev BoundPool.wires (c : BoundPool) : List Sig:=c.2.2.2
def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r,bit (f r) c.domain=true)∧¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws,Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank∧poolSupply f bank c.wires∧True
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z:=choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires))&&(!extra||choiceOK c.domain c.wires op)
def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
abbrev Bits:=BitVec 768
abbrev Signals:=Bits × Bits
abbrev Decor:=Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals:=(ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i,bit (r i) T=true∧bit (s i) T=false
def faithful (r s : Fin 768 → Row) (x : Decor):=x.2=pairSig r s x.1
def dneg (x : Decor) : Decor:=(neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
def codeDecor (op : Nat) (x y : Decor):=if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor:=(zero,0,0)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a:=ws.getD (bits &&& 15) defaultDecor
    let b:=ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x:=fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
abbrev Cov:=Bits × Bits × Bits
def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)
def takeOne (c : Cov) (a : Bits) : Bits:=c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb
def sameWords (a b : List Sig):=(a.all (fun x => b.contains x))&&(b.all (fun x => a.contains x))
def keyWord (v : Sig) :=
  let n:=v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig):=xs.foldl (fun v x => v+keyWord x) 0
def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws:=choiceVal op::rest
  (links (keySet ws)).any (sameWords ws)||pools.any (fun p => scalarPoolCut p k rest op)
abbrev CovPair:=Cov × Cov
def preCov (ws : List Decor) : CovPair:=(coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool):=if d then c.2 else c.1
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb
def movedDecor (op : Nat) (a b : Decor):=codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice:=(op,a.1,b.1)
abbrev NodeContext:=Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links):=c
  let un:=op==2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len>cap then true else
    let d:=len==cap
    let rs:=restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1||ws.any (fun v => v.1==z.1) then true else
      let rest:=(opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)
def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op:=if d then 1 else 0
  let z:=movedDecor op a b
  let attempt:=evalMove ctx op a b z
  attempt false false&&attempt true false&&attempt false true&&attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z:=movedDecor 2 a a
  evalMove ctx 2 a a z false false&&evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false&&testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs&&testAll ctx bs
def composedOK (p q : List Move):=inputs.all (fun a => movedWord p (movedWord q a)==a)
def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T==T)&&composedOK p p.reverse&&composedOK p.reverse p
abbrev Packing:=Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing:=(0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i:=pos/8192
  let shift:=pos % 8192
  let lo:=word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a:=h % nb
  let sh:=packedAt data (a*sw) sw
  let row:=(h/nb+sh)%slots
  let word:=packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw))==h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none
def IndexTree (α : Type):=List α
def IndexTree.leaf {α} (xs : List α) : IndexTree α:=xs
def IndexTree.fork {α} (_ : Nat) (a b : IndexTree α) : IndexTree α:=List.append a b
def IndexTree.read {α} (tree : IndexTree α) (i : Nat):=(show List α from tree)[i]?
def IndexTree.values {α} (tree : IndexTree α) : List α:=tree
def Forest:=(Nat) × (Nat) × (Nat → Bits × Bits) × (IndexTree ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (c : Forest) : Nat:=c.1
def Forest.cap (c : Forest) : Nat:=c.2.1
def Forest.samples (c : Forest) : Nat → Bits × Bits:=c.2.2.1
def Forest.cols (c : Forest) : IndexTree ColumnInfo:=c.2.2.2.1
def Forest.autos (c : Forest) : Array (List Nat):=c.2.2.2.2.1
def Forest.levels (c : Forest) : Nat → Packing:=c.2.2.2.2.2.1
def Forest.index (c : Forest) : Nat → Nat → Option (Nat × Nat):=c.2.2.2.2.2.2
def wiresOf (g : Forest) :=
  let ws:=rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge:=dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
def targetOf (g : Forest):=chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1==1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
def storedDepth (_g : Forest) (depth : Nat):=depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw:=wiresOf g
  let (_,depth,_,_,_,_,_,data):=g.levels k
  let len:=10*storedDepth g depth
  let width:=len+raw.length+depth
  let recp:=packedAt data (i*width) width
  let stored:=recp &&& ((1 <<< len)-1)
  let ops:=stored
  let bank:=decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)
def getFieldV (x pos width : Nat):=(x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more:=chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1==0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more
def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x:=packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)
def stateSet (g : Forest) (k i : Nat):=(readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)
def nodeVerified (g : Forest) (k i : Nat) :=
  let raw:=wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
  let (ops,bank,ws):=readNode g k i
  let values:=ws.map Prod.fst
  let start:=num*(10*storedDepth g depth+raw.length+depth)
  let pos:=start+num*offw+packedAt data (start+i*offw) offw
  let nr:=packedAt data pos 5
  let nl:=packedAt data (pos+5) lw
  let st:=pos+5+lw
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls:=fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup&&!(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)
def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n)&&block g k start n
def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top,block g k 0 (g.levels k).1=true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1)==BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2)==0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1)&&sameWords (stateSet g k i) ws
def Known (entries : List (Nat × Nat)):=∀ e ∈ entries,Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
def lanePlace (v : Nat) (upper : Nat):=2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
def fullMarks (r packed : Nat):=((packed+r) >>> 768) &&& r
abbrev PackedSig:=Nat × Nat
abbrev PackedCov:=Nat × Nat × Nat
def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1:=fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2:=c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2
def contextWire (c : NodeContext) (i : Nat):=c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a:=contextWire c i
  let b:=contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a:=contextWire c i
  let b:=contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2
def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1==0)||f x)&&onMarks f (mask >>> 769) xs
abbrev Batch:=Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat):=b.2.2.2.1.getD i (0,0)
def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero||m==p.domain||(p.wires.map (masked p.domain)).any (fun v => v==m)
def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
abbrev QuickPool:=BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p:=s.1
  let un:=op==2
  let const:=fun w : Decor => isMaskedConstant p.domain w.1
  let z:=choiceVal (movedChoice op a b)
  let zm:=masked p.domain z
  let zc:=isMaskedConstant p.domain z
  let cm:=s.2.1 - constantLoss const a ka - constantLoss const b (un||kb)+zc.toNat
  let free:=zc||zm==masked p.domain a.1||zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)
def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a:=contextWire c i
  let b:=contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)
def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length∧j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v):=b
  let un:=op==2
  let len:=1+(n-(if ka then 0 else 1)-(if un||kb then 0 else 1))
  if len>k then true else
    let d:=len==k
    let a:=laneWire b i
    let b':=laneWire b j
    let z:=packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov:=if d then v else u
    let mask:=fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs
def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f:=batchMove b xs i j op
  f false false&&f true false&&f false true&&f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false&&batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0&&batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js&&batchRows b xs js
def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw:=wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
  let (ops,bank,ws):=readNode g k i
  let start:=num*(10*storedDepth g depth+raw.length+depth)
  let pos:=start+num*offw+packedAt data (start+i*offw) offw
  let nr:=packedAt data pos 5
  let nl:=packedAt data (pos+5) lw
  let st:=pos+5+lw
  let rules:=(getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls:=fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)
def prelim (T : Sig) (c : NodeContext) :=
  let ws:=c.2.2.1.map Prod.fst
  decide ws.Nodup&&!(ws.contains T)
def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar&&prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs:=contexts g k start n
  let b:=makeBatch k ar xs
  (List.range len).all (fun d =>
    let i:=lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d∧boxes g k start n ar (lo+num/2) (num-num/2) d
def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true∧boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d∧cells g k (start+n/2) (n-n/2) ar rows d
def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d∧listPieces f (xs.drop (xs.length/2)) d
end C4338
theorem eq_Sig : @C4338.Sig = @C2444.Sig := rfl
theorem eq_zero : @C4338.zero = @C2444.zero := rfl
theorem eq_one : @C4338.one = @C2444.one := rfl
theorem eq_neg : @C4338.neg = @C2444.neg := rfl
theorem eq_bin : @C4338.bin = @C2444.bin := rfl
theorem eq_proper : @C4338.proper = @C2444.proper := rfl
theorem eq_Live : @C4338.Live = @C2444.Live := rfl
theorem eq_gv : @C4338.gv = @C2444.gv := rfl
theorem eq_execute : @C4338.execute = @C2444.execute := rfl
theorem eq_represented : @C4338.represented = @C2444.represented := rfl
theorem eq_witness : @C4338.witness = @C2444.witness := rfl
theorem eq_bit : @C4338.bit = @C2444.bit := rfl
theorem eq_Wire : @C4338.Wire = @C2444.Wire := rfl
theorem eq_inv : @C4338.inv = @C2444.inv := rfl
theorem eq_combine : @C4338.combine = @C2444.combine := rfl
theorem eq_Constant : @C4338.Constant = @C2444.Constant := rfl
theorem eq_cost : @C4338.cost = @C2444.cost := rfl
theorem eq_mass : @C4338.mass = @C2444.mass := rfl
theorem eq_Available : @C4338.Available = @C2444.Available := rfl
theorem eq_supply : @C4338.supply = @C2444.supply := rfl
theorem eq_Reach : @C4338.Reach = @C2444.Reach := rfl
theorem eq_kept : @C4338.kept = @C2444.kept := rfl
theorem eq_Run : @C4338.Run = @C2444.Run := rfl
theorem eq_restrictRows : @C4338.restrictRows = @C2444.restrictRows := rfl
theorem eq_Row : @C4338.Row = @C2444.Row := rfl
theorem eq_observe : @C4338.observe = @C2444.observe := rfl
theorem eq_table : @C4338.table = @C2444.table := rfl
theorem eq_inputs : @C4338.inputs = @C2444.inputs := rfl
theorem eq_graph : @C4338.graph = @C2444.graph := rfl
theorem eq_sample : @C4338.sample = @C2444.sample := rfl
theorem eq_edge : @C4338.edge = @C2444.edge := rfl
theorem eq_rename : @C4338.rename = @C2444.rename := rfl
theorem eq_Lower : @C4338.Lower = @C2444.Lower := rfl
theorem eq_Impossible : @C4338.Impossible = @C2444.Impossible := rfl
theorem eq_Essential : @C4338.Essential = @C2444.Essential := rfl
theorem eq_childOne : @C4338.childOne = @C2444.childOne := rfl
theorem eq_childTwo : @C4338.childTwo = @C2444.childTwo := rfl
theorem eq_Sep : @C4338.Sep = @C2444.Sep := rfl
theorem eq_column : @C4338.column = @C2444.column := rfl
theorem eq_Slice : @C4338.Slice = @C2444.Slice := rfl
theorem eq_masked : @C4338.masked = @C2444.masked := rfl
theorem eq_availableB : @C4338.availableB = @C2444.availableB := rfl
theorem eq_poolSupply : @C4338.poolSupply = @C2444.poolSupply := rfl
theorem eq_Choice : @C4338.Choice = @C2444.Choice := rfl
theorem eq_choiceVal : @C4338.choiceVal = @C2444.choiceVal := rfl
theorem eq_choiceOK : @C4338.choiceOK = @C2444.choiceOK := rfl
theorem eq_isMaskedConstant : @C4338.isMaskedConstant = @C2444.isMaskedConstant := rfl
theorem eq_poolCut : @C4338.poolCut = @C2444.poolCut := rfl
theorem eq_Move : @C4338.Move = @C2444.Move := rfl
theorem eq_shifted : @C4338.shifted = @C2444.shifted := rfl
theorem eq_backwards : @C4338.backwards = @C2444.backwards := rfl
theorem eq_rowMove : @C4338.rowMove = @C2444.rowMove := rfl
theorem eq_mux : @C4338.mux = @C2444.mux := rfl
theorem eq_wordMove : @C4338.wordMove = @C2444.wordMove := rfl
theorem eq_movedRow : @C4338.movedRow = @C2444.movedRow := rfl
theorem eq_movedWord : @C4338.movedWord = @C2444.movedWord := rfl
theorem eq_freeWord : @C4338.freeWord = @C2444.freeWord := rfl
theorem eq_checkMap : @C4338.checkMap = @C2444.checkMap := rfl
theorem eq_witnessB : @C4338.witnessB = @C2444.witnessB := rfl
theorem eq_checkEssential : @C4338.checkEssential = @C2444.checkEssential := rfl
theorem eq_checkLift : @C4338.checkLift = @C2444.checkLift := rfl
theorem eq_selected : @C4338.selected = @C2444.selected := rfl
theorem eq_vars : @C4338.vars = @C2444.vars := rfl
theorem eq_vertex : @C4338.vertex = @C2444.vertex := rfl
theorem eq_graphGoal : @C4338.graphGoal = @C2444.graphGoal := rfl
theorem eq_cube0 : @C4338.cube0 = @C2444.cube0 := rfl
theorem eq_cube3 : @C4338.cube3 = @C2444.cube3 := rfl
theorem eq_cube6 : @C4338.cube6 = @C2444.cube6 := rfl
theorem eq_subcube : @C4338.subcube = @C2444.subcube := rfl
theorem eq_fixRows : @C4338.fixRows = @C2444.fixRows := rfl
theorem eq_swapRows : @C4338.swapRows = @C2444.swapRows := rfl
theorem eq_supportPairs : @C4338.supportPairs = @C2444.supportPairs := rfl
theorem eq_graphPairs : @C4338.graphPairs = @C2444.graphPairs := rfl
theorem eq_properB : @C4338.properB = @C2444.properB := rfl
theorem eq_assertSize : @C4338.assertSize = @C2444.assertSize := rfl
theorem eq_ColumnInfo : @C4338.ColumnInfo = @C2444.ColumnInfo := rfl
theorem eq_colFree : @C4338.colFree = @C2444.colFree := rfl
theorem eq_relabelOK : @C4338.relabelOK = @C2444.relabelOK := rfl
theorem eq_boundsBefore : @C4338.boundsBefore = @C2444.boundsBefore := rfl
theorem eq_BoundPool : @C4338.BoundPool = @C2444.BoundPool := rfl
theorem eq_ValidPool : @C4338.ValidPool = @C2444.ValidPool := rfl
theorem eq_scalarPoolCut : @C4338.scalarPoolCut = @C2444.scalarPoolCut := rfl
theorem eq_Bits : @C4338.Bits = @C2444.Bits := rfl
theorem eq_Signals : @C4338.Signals = @C2444.Signals := rfl
theorem eq_Decor : @C4338.Decor = @C2444.Decor := rfl
theorem eq_ofRows : @C4338.ofRows = @C2444.ofRows := rfl
theorem eq_pairSig : @C4338.pairSig = @C2444.pairSig := rfl
theorem eq_properPairs : @C4338.properPairs = @C2444.properPairs := rfl
theorem eq_faithful : @C4338.faithful = @C2444.faithful := rfl
theorem eq_dneg : @C4338.dneg = @C2444.dneg := rfl
theorem eq_dbin : @C4338.dbin = @C2444.dbin := rfl
theorem eq_codeDecor : @C4338.codeDecor = @C2444.codeDecor := rfl
theorem eq_defaultDecor : @C4338.defaultDecor = @C2444.defaultDecor := rfl
theorem eq_asRow : @C4338.asRow = @C2444.asRow := rfl
theorem eq_rawDecor : @C4338.rawDecor = @C2444.rawDecor := rfl
theorem eq_liftGoal : @C4338.liftGoal = @C2444.liftGoal := rfl
theorem eq_Cov : @C4338.Cov = @C2444.Cov := rfl
theorem eq_addCov : @C4338.addCov = @C2444.addCov := rfl
theorem eq_coverage : @C4338.coverage = @C2444.coverage := rfl
theorem eq_takeOne : @C4338.takeOne = @C2444.takeOne := rfl
theorem eq_takeTwo : @C4338.takeTwo = @C2444.takeTwo := rfl
theorem eq_delOne : @C4338.delOne = @C2444.delOne := rfl
theorem eq_delTwo : @C4338.delTwo = @C2444.delTwo := rfl
theorem eq_sameWords : @C4338.sameWords = @C2444.sameWords := rfl
theorem eq_keyWord : @C4338.keyWord = @C2444.keyWord := rfl
theorem eq_keySet : @C4338.keySet = @C2444.keySet := rfl
theorem eq_closeChild : @C4338.closeChild = @C2444.closeChild := rfl
theorem eq_CovPair : @C4338.CovPair = @C2444.CovPair := rfl
theorem eq_preCov : @C4338.preCov = @C2444.preCov := rfl
theorem eq_getCov : @C4338.getCov = @C2444.getCov := rfl
theorem eq_restCov : @C4338.restCov = @C2444.restCov := rfl
theorem eq_opKeep : @C4338.opKeep = @C2444.opKeep := rfl
theorem eq_movedDecor : @C4338.movedDecor = @C2444.movedDecor := rfl
theorem eq_movedChoice : @C4338.movedChoice = @C2444.movedChoice := rfl
theorem eq_NodeContext : @C4338.NodeContext = @C2444.NodeContext := rfl
theorem eq_evalMove : @C4338.evalMove = @C2444.evalMove := rfl
theorem eq_moveFront : @C4338.moveFront = @C2444.moveFront := rfl
theorem eq_testPair : @C4338.testPair = @C2444.testPair := rfl
theorem eq_testRow : @C4338.testRow = @C2444.testRow := rfl
theorem eq_composedOK : @C4338.composedOK = @C2444.composedOK := rfl
theorem eq_autoOK : @C4338.autoOK = @C2444.autoOK := rfl
theorem eq_Packing : @C4338.Packing = @C2444.Packing := rfl
theorem eq_emptyPacking : @C4338.emptyPacking = @C2444.emptyPacking := rfl
theorem eq_packedAt : @C4338.packedAt = @C2444.packedAt := rfl
theorem eq_lookupWord : @C4338.lookupWord = @C2444.lookupWord := rfl
theorem eq_IndexTree : @C4338.IndexTree = @C2444.IndexTree := rfl
theorem eq_Forest : @C4338.Forest = @C2444.Forest := rfl
theorem eq_storedDepth : @C4338.storedDepth = @C2444.storedDepth := rfl
theorem eq_getFieldV : @C4338.getFieldV = @C2444.getFieldV := rfl
theorem eq_Known : @C4338.Known = @C2444.Known := rfl
theorem eq_extendKnown : @C4338.extendKnown = @C2444.extendKnown := rfl
theorem eq_lanePlace : @C4338.lanePlace = @C2444.lanePlace := rfl
theorem eq_fullMarks : @C4338.fullMarks = @C2444.fullMarks := rfl
theorem eq_PackedSig : @C4338.PackedSig = @C2444.PackedSig := rfl
theorem eq_PackedCov : @C4338.PackedCov = @C2444.PackedCov := rfl
theorem eq_packedColumn : @C4338.packedColumn = @C2444.packedColumn := rfl
theorem eq_packedOp : @C4338.packedOp = @C2444.packedOp := rfl
theorem eq_takePacked : @C4338.takePacked = @C2444.takePacked := rfl
theorem eq_contextWire : @C4338.contextWire = @C2444.contextWire := rfl
theorem eq_checkAt : @C4338.checkAt = @C2444.checkAt := rfl
theorem eq_combField : @C4338.combField = @C2444.combField := rfl
theorem eq_Batch : @C4338.Batch = @C2444.Batch := rfl
theorem eq_laneWire : @C4338.laneWire = @C2444.laneWire := rfl
theorem eq_availableMasked : @C4338.availableMasked = @C2444.availableMasked := rfl
theorem eq_constantLoss : @C4338.constantLoss = @C2444.constantLoss := rfl
theorem eq_QuickPool : @C4338.QuickPool = @C2444.QuickPool := rfl
theorem eq_summarizePool : @C4338.summarizePool = @C2444.summarizePool := rfl
theorem eq_fastCost : @C4338.fastCost = @C2444.fastCost := rfl
theorem eq_quickAt : @C4338.quickAt = @C2444.quickAt := rfl
theorem eq_fallbackAt : @C4338.fallbackAt = @C2444.fallbackAt := rfl
theorem eq_prelim : @C4338.prelim = @C2444.prelim := rfl
end PEqualNP.Outside.L_meta_670

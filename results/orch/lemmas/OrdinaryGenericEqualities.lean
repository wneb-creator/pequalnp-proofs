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
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,0,fun _ => 0)
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
def cmpException (iw ow : Nat) : Nat → Nat → Nat → Option Nat
  | 0,_,_ => none
  | n+1,packed,i =>
    if packed &&& ((1 <<< iw)-1) = i then
      some ((packed >>> iw) &&& ((1 <<< ow)-1))
    else cmpException iw ow n (packed >>> (iw+ow)) i
def cmpWidth (g : Forest) (k : Nat) : Nat :=
  let (_,depth,_,pw,_,_,_,_,_) := g.levels k
  (if depth=0 then 0 else pw+10)+(wiresOf g).length+depth
def cmpNode (g : Forest) (k i : Nat) : Nat :=
  let (_,_,_,_,_,_,_,_,data) := g.levels k
  packedAt data (i*cmpWidth g k) (cmpWidth g k)
def cmpParent (g : Forest) (k i : Nat) : Nat :=
  let (_,_,_,pw,_,_,_,_,_) := g.levels k
  cmpNode g k i &&& ((1 <<< pw)-1)
def cmpOps (g : Forest) : Nat → Nat → Nat → Nat
  | 0,_,_ => 0
  | fuel+1,k,i =>
    let (_,depth,_,pw,iw,_,ec,ex,_) := g.levels k
    match cmpException iw (10*depth) ec ex i with
    | some ops => ops
    | none =>
      cmpOps g fuel (k+1) (cmpParent g k i) |||
        (((cmpNode g k i >>> pw) &&& 1023) <<< (10*(depth-1)))
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,pw,_,_,_,_,_) := g.levels k
  let len := if depth=0 then 0 else pw+10
  let recp := cmpNode g k i
  let ops := cmpOps g depth k i
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

def cmpNewRules (g : Forest) (k i : Nat) : List (Nat × Nat) :=
  let (num,depth,cw,_,_,ow,_,_,data) := g.levels k
  let start := num*cmpWidth g k
  let pos := start+num*ow+packedAt data (start+i*ow) ow
  let nr := packedAt data pos 5
  getPairs data cw depth nr (pos+5)
def cmpRules (g : Forest) : Nat → Nat → Nat → List (Nat × Nat)
  | 0,k,i => cmpNewRules g k i
  | fuel+1,k,i =>
    let parent := cmpParent g k i
    let fresh := cmpNewRules g k i
    if parent < (g.levels (k+1)).1 then
      fresh ++ cmpRules g fuel (k+1) parent
    else fresh
def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst

def sortedIndexKey (g : Forest) (k iw code : Nat) : Nat :=
  let perm := (g.autos[code >>> iw]?).getD []
  keySet ((stateSet g k (code &&& ((1 <<< iw)-1))).map
    (movedWord (perm.map swapRows).reverse))
def sortedSeek (get key : Nat → Nat) (target : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel+1, lo, hi =>
    if lo < hi then
      let mid := (lo+hi)/2
      let code := get mid
      let value := key code
      if target == value then some code
      else if target < value then sortedSeek get key target fuel lo mid
      else sortedSeek get key target fuel (mid+1) hi
    else none
def sortedLookup (g : Forest) (k count iw pw : Nat) (data : Nat → Nat)
    (h : Nat) : Option (Nat × Nat) :=
  let get := fun i => packedAt data (i*(iw+pw)) (iw+pw)
  (sortedSeek get (sortedIndexKey g k iw) h (Nat.log2 (count+1)+1) 0 count).map
    (fun code => (code &&& ((1 <<< iw)-1), code >>> iw))
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let depth := (g.levels k).2.1
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (cmpRules g depth k i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
  let depth := (g.levels k).2.1
  let (ops,bank,ws) := readNode g k i
  let rules := (cmpRules g depth k i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
namespace C1676
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
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
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
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
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
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,0,fun _ => 0)
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
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
def storedDepth (_g : Forest) (depth : Nat) := depth
def cmpException (iw ow : Nat) : Nat → Nat → Nat → Option Nat
  | 0,_,_ => none
  | n+1,packed,i =>
    if packed &&& ((1 <<< iw)-1) = i then
      some ((packed >>> iw) &&& ((1 <<< ow)-1))
    else cmpException iw ow n (packed >>> (iw+ow)) i
def cmpWidth (g : Forest) (k : Nat) : Nat :=
  let (_,depth,_,pw,_,_,_,_,_) := g.levels k
  (if depth=0 then 0 else pw+10)+(wiresOf g).length+depth
def cmpNode (g : Forest) (k i : Nat) : Nat :=
  let (_,_,_,_,_,_,_,_,data) := g.levels k
  packedAt data (i*cmpWidth g k) (cmpWidth g k)
def cmpParent (g : Forest) (k i : Nat) : Nat :=
  let (_,_,_,pw,_,_,_,_,_) := g.levels k
  cmpNode g k i &&& ((1 <<< pw)-1)
def cmpOps (g : Forest) : Nat → Nat → Nat → Nat
  | 0,_,_ => 0
  | fuel+1,k,i =>
    let (_,depth,_,pw,iw,_,ec,ex,_) := g.levels k
    match cmpException iw (10*depth) ec ex i with
    | some ops => ops
    | none =>
      cmpOps g fuel (k+1) (cmpParent g k i) |||
        (((cmpNode g k i >>> pw) &&& 1023) <<< (10*(depth-1)))
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,pw,_,_,_,_,_) := g.levels k
  let len := if depth=0 then 0 else pw+10
  let recp := cmpNode g k i
  let ops := cmpOps g depth k i
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

-- Each induced subgraph in this search retains the edge between vertices zero and four.
-- Its initial bank offers their disjunction at no cost.
def edgeBank (m : Nat) := vars m ++ [bin true (inputs.getD 0 zero) (inputs.getD 4 zero)]
def poolRoots (m : Nat) (c : ColumnInfo) := if c.2.2.1 < 1024 then vars m else edgeBank m
def ordinaryCol (m : Nat) (c : ColumnInfo) (p : Nat → Nat) := decide (c.2.2.1 < 1024) && colCheck m c p
def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (poolRoots g.mask ci) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def cmpNewRules (g : Forest) (k i : Nat) : List (Nat × Nat) :=
  let (num,depth,cw,_,_,ow,_,_,data) := g.levels k
  let start := num*cmpWidth g k
  let pos := start+num*ow+packedAt data (start+i*ow) ow
  let nr := packedAt data pos 5
  getPairs data cw depth nr (pos+5)
def cmpRules (g : Forest) : Nat → Nat → Nat → List (Nat × Nat)
  | 0,k,i => cmpNewRules g k i
  | fuel+1,k,i =>
    let parent := cmpParent g k i
    let fresh := cmpNewRules g k i
    if parent < (g.levels (k+1)).1 then
      fresh ++ cmpRules g fuel (k+1) parent
    else fresh
def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst

def sortedIndexKey (g : Forest) (k iw code : Nat) : Nat :=
  let perm := (g.autos[code >>> iw]?).getD []
  keySet ((stateSet g k (code &&& ((1 <<< iw)-1))).map
    (movedWord (perm.map swapRows).reverse))
def sortedSeek (get key : Nat → Nat) (target : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel+1, lo, hi =>
    if lo < hi then
      let mid := (lo+hi)/2
      let code := get mid
      let value := key code
      if target == value then some code
      else if target < value then sortedSeek get key target fuel lo mid
      else sortedSeek get key target fuel (mid+1) hi
    else none
def sortedLookup (g : Forest) (k count iw pw : Nat) (data : Nat → Nat)
    (h : Nat) : Option (Nat × Nat) :=
  let get := fun i => packedAt data (i*(iw+pw)) (iw+pw)
  (sortedSeek get (sortedIndexKey g k iw) h (Nat.log2 (count+1)+1) 0 count).map
    (fun code => (code &&& ((1 <<< iw)-1), code >>> iw))
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let depth := (g.levels k).2.1
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (cmpRules g depth k i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
  g.cols.values.all (fun c => ordinaryCol g.mask c prior) &&
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
  let depth := (g.levels k).2.1
  let (ops,bank,ws) := readNode g k i
  let rules := (cmpRules g depth k i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
end C1676
namespace C1678
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
def seed : Sig := inputs.getD 4 zero ||| inputs.getD 6 zero

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
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
def varsX (m : Nat) : List Sig := if m.testBit 9 then vars m ++ [seed] else vars m
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
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m ^^^ (m &&& (c.1 &&& 512))
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
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
abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,0,fun _ => 0)
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


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
def storedDepth (_g : Forest) (depth : Nat) := depth
def cmpException (iw ow : Nat) : Nat → Nat → Nat → Option Nat
  | 0,_,_ => none
  | n+1,packed,i =>
    if packed &&& ((1 <<< iw)-1) = i then
      some ((packed >>> iw) &&& ((1 <<< ow)-1))
    else cmpException iw ow n (packed >>> (iw+ow)) i
def cmpWidth (g : Forest) (k : Nat) : Nat :=
  let (_,depth,_,pw,_,_,_,_,_) := g.levels k
  (if depth=0 then 0 else pw+10)+(wiresOf g).length+depth
def cmpNode (g : Forest) (k i : Nat) : Nat :=
  let (_,_,_,_,_,_,_,_,data) := g.levels k
  packedAt data (i*cmpWidth g k) (cmpWidth g k)
def cmpParent (g : Forest) (k i : Nat) : Nat :=
  let (_,_,_,pw,_,_,_,_,_) := g.levels k
  cmpNode g k i &&& ((1 <<< pw)-1)
def cmpOps (g : Forest) : Nat → Nat → Nat → Nat
  | 0,_,_ => 0
  | fuel+1,k,i =>
    let (_,depth,_,pw,iw,_,ec,ex,_) := g.levels k
    match cmpException iw (10*depth) ec ex i with
    | some ops => ops
    | none =>
      cmpOps g fuel (k+1) (cmpParent g k i) |||
        (((cmpNode g k i >>> pw) &&& 1023) <<< (10*(depth-1)))
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,pw,_,_,_,_,_) := g.levels k
  let len := if depth=0 then 0 else pw+10
  let recp := cmpNode g k i
  let ops := cmpOps g depth k i
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
    materialize (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def cmpNewRules (g : Forest) (k i : Nat) : List (Nat × Nat) :=
  let (num,depth,cw,_,_,ow,_,_,data) := g.levels k
  let start := num*cmpWidth g k
  let pos := start+num*ow+packedAt data (start+i*ow) ow
  let nr := packedAt data pos 5
  getPairs data cw depth nr (pos+5)
def cmpRules (g : Forest) : Nat → Nat → Nat → List (Nat × Nat)
  | 0,k,i => cmpNewRules g k i
  | fuel+1,k,i =>
    let parent := cmpParent g k i
    let fresh := cmpNewRules g k i
    if parent < (g.levels (k+1)).1 then
      fresh ++ cmpRules g fuel (k+1) parent
    else fresh
def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst

def sortedIndexKey (g : Forest) (k iw code : Nat) : Nat :=
  let perm := (g.autos[code >>> iw]?).getD []
  keySet ((stateSet g k (code &&& ((1 <<< iw)-1))).map
    (movedWord (perm.map swapRows).reverse))
def sortedSeek (get key : Nat → Nat) (target : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | fuel+1, lo, hi =>
    if lo < hi then
      let mid := (lo+hi)/2
      let code := get mid
      let value := key code
      if target == value then some code
      else if target < value then sortedSeek get key target fuel lo mid
      else sortedSeek get key target fuel (mid+1) hi
    else none
def sortedLookup (g : Forest) (k count iw pw : Nat) (data : Nat → Nat)
    (h : Nat) : Option (Nat × Nat) :=
  let get := fun i => packedAt data (i*(iw+pw)) (iw+pw)
  (sortedSeek get (sortedIndexKey g k iw) h (Nat.log2 (count+1)+1) 0 count).map
    (fun code => (code &&& ((1 <<< iw)-1), code >>> iw))
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let depth := (g.levels k).2.1
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (cmpRules g depth k i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (varsX e.1) (graphGoal e.1) e.2
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
  let depth := (g.levels k).2.1
  let (ops,bank,ws) := readNode g k i
  let rules := (cmpRules g depth k i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
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
end C1678
theorem eq_C1676_Sig : @C1676.Sig = @C2444.Sig := rfl
theorem eq_C1676_zero : @C1676.zero = @C2444.zero := rfl
theorem eq_C1676_one : @C1676.one = @C2444.one := rfl
theorem eq_C1676_neg : @C1676.neg = @C2444.neg := rfl
theorem eq_C1676_bin : @C1676.bin = @C2444.bin := rfl
theorem eq_C1676_proper : @C1676.proper = @C2444.proper := rfl
theorem eq_C1676_Live : @C1676.Live = @C2444.Live := rfl
theorem eq_C1676_gv : @C1676.gv = @C2444.gv := rfl
theorem eq_C1676_execute : @C1676.execute = @C2444.execute := rfl
theorem eq_C1676_represented : @C1676.represented = @C2444.represented := rfl
theorem eq_C1676_witness : @C1676.witness = @C2444.witness := rfl
theorem eq_C1676_bit : @C1676.bit = @C2444.bit := rfl
theorem eq_C1676_Wire : @C1676.Wire = @C2444.Wire := rfl
theorem eq_C1676_inv : @C1676.inv = @C2444.inv := rfl
theorem eq_C1676_combine : @C1676.combine = @C2444.combine := rfl
theorem eq_C1676_Constant : @C1676.Constant = @C2444.Constant := rfl
theorem eq_C1676_cost : @C1676.cost = @C2444.cost := rfl
theorem eq_C1676_mass : @C1676.mass = @C2444.mass := rfl
theorem eq_C1676_Available : @C1676.Available = @C2444.Available := rfl
theorem eq_C1676_supply : @C1676.supply = @C2444.supply := rfl
theorem eq_C1676_Reach : @C1676.Reach = @C2444.Reach := rfl
theorem eq_C1676_kept : @C1676.kept = @C2444.kept := rfl
theorem eq_C1676_Run : @C1676.Run = @C2444.Run := rfl
theorem eq_C1676_restrictRows : @C1676.restrictRows = @C2444.restrictRows := rfl
theorem eq_C1676_Row : @C1676.Row = @C2444.Row := rfl
theorem eq_C1676_observe : @C1676.observe = @C2444.observe := rfl
theorem eq_C1676_table : @C1676.table = @C2444.table := rfl
theorem eq_C1676_inputs : @C1676.inputs = @C2444.inputs := rfl
theorem eq_C1676_graph : @C1676.graph = @C2444.graph := rfl
theorem eq_C1676_sample : @C1676.sample = @C2444.sample := rfl
theorem eq_C1676_edge : @C1676.edge = @C2444.edge := rfl
theorem eq_C1676_rename : @C1676.rename = @C2444.rename := rfl
theorem eq_C1676_Lower : @C1676.Lower = @C2444.Lower := rfl
theorem eq_C1676_Impossible : @C1676.Impossible = @C2444.Impossible := rfl
theorem eq_C1676_Essential : @C1676.Essential = @C2444.Essential := rfl
theorem eq_C1676_childOne : @C1676.childOne = @C2444.childOne := rfl
theorem eq_C1676_childTwo : @C1676.childTwo = @C2444.childTwo := rfl
theorem eq_C1676_Sep : @C1676.Sep = @C2444.Sep := rfl
theorem eq_C1676_column : @C1676.column = @C2444.column := rfl
theorem eq_C1676_Slice : @C1676.Slice = @C2444.Slice := rfl
theorem eq_C1676_masked : @C1676.masked = @C2444.masked := rfl
theorem eq_C1676_availableB : @C1676.availableB = @C2444.availableB := rfl
theorem eq_C1676_poolSupply : @C1676.poolSupply = @C2444.poolSupply := rfl
theorem eq_C1676_Choice : @C1676.Choice = @C2444.Choice := rfl
theorem eq_C1676_choiceVal : @C1676.choiceVal = @C2444.choiceVal := rfl
theorem eq_C1676_choiceOK : @C1676.choiceOK = @C2444.choiceOK := rfl
theorem eq_C1676_isMaskedConstant : @C1676.isMaskedConstant = @C2444.isMaskedConstant := rfl
theorem eq_C1676_poolCut : @C1676.poolCut = @C2444.poolCut := rfl
theorem eq_C1676_Move : @C1676.Move = @C2444.Move := rfl
theorem eq_C1676_shifted : @C1676.shifted = @C2444.shifted := rfl
theorem eq_C1676_backwards : @C1676.backwards = @C2444.backwards := rfl
theorem eq_C1676_rowMove : @C1676.rowMove = @C2444.rowMove := rfl
theorem eq_C1676_mux : @C1676.mux = @C2444.mux := rfl
theorem eq_C1676_wordMove : @C1676.wordMove = @C2444.wordMove := rfl
theorem eq_C1676_movedRow : @C1676.movedRow = @C2444.movedRow := rfl
theorem eq_C1676_movedWord : @C1676.movedWord = @C2444.movedWord := rfl
theorem eq_C1676_freeWord : @C1676.freeWord = @C2444.freeWord := rfl
theorem eq_C1676_checkMap : @C1676.checkMap = @C2444.checkMap := rfl
theorem eq_C1676_witnessB : @C1676.witnessB = @C2444.witnessB := rfl
theorem eq_C1676_checkEssential : @C1676.checkEssential = @C2444.checkEssential := rfl
theorem eq_C1676_checkLift : @C1676.checkLift = @C2444.checkLift := rfl
theorem eq_C1676_selected : @C1676.selected = @C2444.selected := rfl
theorem eq_C1676_vars : @C1676.vars = @C2444.vars := rfl
theorem eq_C1676_vertex : @C1676.vertex = @C2444.vertex := rfl
theorem eq_C1676_graphGoal : @C1676.graphGoal = @C2444.graphGoal := rfl
theorem eq_C1676_cube0 : @C1676.cube0 = @C2444.cube0 := rfl
theorem eq_C1676_cube3 : @C1676.cube3 = @C2444.cube3 := rfl
theorem eq_C1676_cube6 : @C1676.cube6 = @C2444.cube6 := rfl
theorem eq_C1676_subcube : @C1676.subcube = @C2444.subcube := rfl
theorem eq_C1676_fixRows : @C1676.fixRows = @C2444.fixRows := rfl
theorem eq_C1676_swapRows : @C1676.swapRows = @C2444.swapRows := rfl
theorem eq_C1676_supportPairs : @C1676.supportPairs = @C2444.supportPairs := rfl
theorem eq_C1676_graphPairs : @C1676.graphPairs = @C2444.graphPairs := rfl
theorem eq_C1676_properB : @C1676.properB = @C2444.properB := rfl
theorem eq_C1676_assertSize : @C1676.assertSize = @C2444.assertSize := rfl
theorem eq_C1676_ColumnInfo : @C1676.ColumnInfo = @C2444.ColumnInfo := rfl
theorem eq_C1676_colFree : @C1676.colFree = @C2444.colFree := rfl
theorem eq_C1676_relabelOK : @C1676.relabelOK = @C2444.relabelOK := rfl
theorem eq_C1676_boundsBefore : @C1676.boundsBefore = @C2444.boundsBefore := rfl
theorem eq_C1676_BoundPool : @C1676.BoundPool = @C2444.BoundPool := rfl
theorem eq_C1676_ValidPool : @C1676.ValidPool = @C2444.ValidPool := rfl
theorem eq_C1676_scalarPoolCut : @C1676.scalarPoolCut = @C2444.scalarPoolCut := rfl
theorem eq_C1676_Bits : @C1676.Bits = @C2444.Bits := rfl
theorem eq_C1676_Signals : @C1676.Signals = @C2444.Signals := rfl
theorem eq_C1676_Decor : @C1676.Decor = @C2444.Decor := rfl
theorem eq_C1676_ofRows : @C1676.ofRows = @C2444.ofRows := rfl
theorem eq_C1676_pairSig : @C1676.pairSig = @C2444.pairSig := rfl
theorem eq_C1676_properPairs : @C1676.properPairs = @C2444.properPairs := rfl
theorem eq_C1676_faithful : @C1676.faithful = @C2444.faithful := rfl
theorem eq_C1676_dneg : @C1676.dneg = @C2444.dneg := rfl
theorem eq_C1676_dbin : @C1676.dbin = @C2444.dbin := rfl
theorem eq_C1676_codeDecor : @C1676.codeDecor = @C2444.codeDecor := rfl
theorem eq_C1676_defaultDecor : @C1676.defaultDecor = @C2444.defaultDecor := rfl
theorem eq_C1676_asRow : @C1676.asRow = @C2444.asRow := rfl
theorem eq_C1676_rawDecor : @C1676.rawDecor = @C2444.rawDecor := rfl
theorem eq_C1676_liftGoal : @C1676.liftGoal = @C2444.liftGoal := rfl
theorem eq_C1676_Cov : @C1676.Cov = @C2444.Cov := rfl
theorem eq_C1676_addCov : @C1676.addCov = @C2444.addCov := rfl
theorem eq_C1676_coverage : @C1676.coverage = @C2444.coverage := rfl
theorem eq_C1676_takeOne : @C1676.takeOne = @C2444.takeOne := rfl
theorem eq_C1676_takeTwo : @C1676.takeTwo = @C2444.takeTwo := rfl
theorem eq_C1676_delOne : @C1676.delOne = @C2444.delOne := rfl
theorem eq_C1676_delTwo : @C1676.delTwo = @C2444.delTwo := rfl
theorem eq_C1676_sameWords : @C1676.sameWords = @C2444.sameWords := rfl
theorem eq_C1676_keyWord : @C1676.keyWord = @C2444.keyWord := rfl
theorem eq_C1676_keySet : @C1676.keySet = @C2444.keySet := rfl
theorem eq_C1676_closeChild : @C1676.closeChild = @C2444.closeChild := rfl
theorem eq_C1676_CovPair : @C1676.CovPair = @C2444.CovPair := rfl
theorem eq_C1676_preCov : @C1676.preCov = @C2444.preCov := rfl
theorem eq_C1676_getCov : @C1676.getCov = @C2444.getCov := rfl
theorem eq_C1676_restCov : @C1676.restCov = @C2444.restCov := rfl
theorem eq_C1676_opKeep : @C1676.opKeep = @C2444.opKeep := rfl
theorem eq_C1676_movedDecor : @C1676.movedDecor = @C2444.movedDecor := rfl
theorem eq_C1676_movedChoice : @C1676.movedChoice = @C2444.movedChoice := rfl
theorem eq_C1676_NodeContext : @C1676.NodeContext = @C2444.NodeContext := rfl
theorem eq_C1676_evalMove : @C1676.evalMove = @C2444.evalMove := rfl
theorem eq_C1676_moveFront : @C1676.moveFront = @C2444.moveFront := rfl
theorem eq_C1676_testPair : @C1676.testPair = @C2444.testPair := rfl
theorem eq_C1676_testRow : @C1676.testRow = @C2444.testRow := rfl
theorem eq_C1676_composedOK : @C1676.composedOK = @C2444.composedOK := rfl
theorem eq_C1676_autoOK : @C1676.autoOK = @C2444.autoOK := rfl
theorem eq_C1676_Packing : @C1676.Packing = @C2444.Packing := rfl
theorem eq_C1676_emptyPacking : @C1676.emptyPacking = @C2444.emptyPacking := rfl
theorem eq_C1676_packedAt : @C1676.packedAt = @C2444.packedAt := rfl
theorem eq_C1676_lookupWord : @C1676.lookupWord = @C2444.lookupWord := rfl
theorem eq_C1676_IndexTree : @C1676.IndexTree = @C2444.IndexTree := rfl
theorem eq_C1676_Forest : @C1676.Forest = @C2444.Forest := rfl
theorem eq_C1676_storedDepth : @C1676.storedDepth = @C2444.storedDepth := rfl
theorem eq_C1676_getFieldV : @C1676.getFieldV = @C2444.getFieldV := rfl
theorem eq_C1676_Known : @C1676.Known = @C2444.Known := rfl
theorem eq_C1676_extendKnown : @C1676.extendKnown = @C2444.extendKnown := rfl
theorem eq_C1676_lanePlace : @C1676.lanePlace = @C2444.lanePlace := rfl
theorem eq_C1676_fullMarks : @C1676.fullMarks = @C2444.fullMarks := rfl
theorem eq_C1676_PackedSig : @C1676.PackedSig = @C2444.PackedSig := rfl
theorem eq_C1676_PackedCov : @C1676.PackedCov = @C2444.PackedCov := rfl
theorem eq_C1676_packedColumn : @C1676.packedColumn = @C2444.packedColumn := rfl
theorem eq_C1676_packedOp : @C1676.packedOp = @C2444.packedOp := rfl
theorem eq_C1676_takePacked : @C1676.takePacked = @C2444.takePacked := rfl
theorem eq_C1676_contextWire : @C1676.contextWire = @C2444.contextWire := rfl
theorem eq_C1676_checkAt : @C1676.checkAt = @C2444.checkAt := rfl
theorem eq_C1676_combField : @C1676.combField = @C2444.combField := rfl
theorem eq_C1676_Batch : @C1676.Batch = @C2444.Batch := rfl
theorem eq_C1676_laneWire : @C1676.laneWire = @C2444.laneWire := rfl
theorem eq_C1676_availableMasked : @C1676.availableMasked = @C2444.availableMasked := rfl
theorem eq_C1676_constantLoss : @C1676.constantLoss = @C2444.constantLoss := rfl
theorem eq_C1676_QuickPool : @C1676.QuickPool = @C2444.QuickPool := rfl
theorem eq_C1676_summarizePool : @C1676.summarizePool = @C2444.summarizePool := rfl
theorem eq_C1676_fastCost : @C1676.fastCost = @C2444.fastCost := rfl
theorem eq_C1676_quickAt : @C1676.quickAt = @C2444.quickAt := rfl
theorem eq_C1676_fallbackAt : @C1676.fallbackAt = @C2444.fallbackAt := rfl
theorem eq_C1676_prelim : @C1676.prelim = @C2444.prelim := rfl
theorem eq_C1678_Sig : @C1678.Sig = @C2444.Sig := rfl
theorem eq_C1678_zero : @C1678.zero = @C2444.zero := rfl
theorem eq_C1678_one : @C1678.one = @C2444.one := rfl
theorem eq_C1678_neg : @C1678.neg = @C2444.neg := rfl
theorem eq_C1678_bin : @C1678.bin = @C2444.bin := rfl
theorem eq_C1678_proper : @C1678.proper = @C2444.proper := rfl
theorem eq_C1678_Live : @C1678.Live = @C2444.Live := rfl
theorem eq_C1678_gv : @C1678.gv = @C2444.gv := rfl
theorem eq_C1678_execute : @C1678.execute = @C2444.execute := rfl
theorem eq_C1678_represented : @C1678.represented = @C2444.represented := rfl
theorem eq_C1678_witness : @C1678.witness = @C2444.witness := rfl
theorem eq_C1678_bit : @C1678.bit = @C2444.bit := rfl
theorem eq_C1678_Wire : @C1678.Wire = @C2444.Wire := rfl
theorem eq_C1678_inv : @C1678.inv = @C2444.inv := rfl
theorem eq_C1678_combine : @C1678.combine = @C2444.combine := rfl
theorem eq_C1678_Constant : @C1678.Constant = @C2444.Constant := rfl
theorem eq_C1678_cost : @C1678.cost = @C2444.cost := rfl
theorem eq_C1678_mass : @C1678.mass = @C2444.mass := rfl
theorem eq_C1678_Available : @C1678.Available = @C2444.Available := rfl
theorem eq_C1678_supply : @C1678.supply = @C2444.supply := rfl
theorem eq_C1678_Reach : @C1678.Reach = @C2444.Reach := rfl
theorem eq_C1678_kept : @C1678.kept = @C2444.kept := rfl
theorem eq_C1678_Run : @C1678.Run = @C2444.Run := rfl
theorem eq_C1678_restrictRows : @C1678.restrictRows = @C2444.restrictRows := rfl
theorem eq_C1678_Row : @C1678.Row = @C2444.Row := rfl
theorem eq_C1678_observe : @C1678.observe = @C2444.observe := rfl
theorem eq_C1678_table : @C1678.table = @C2444.table := rfl
theorem eq_C1678_inputs : @C1678.inputs = @C2444.inputs := rfl
theorem eq_C1678_graph : @C1678.graph = @C2444.graph := rfl
theorem eq_C1678_sample : @C1678.sample = @C2444.sample := rfl
theorem eq_C1678_edge : @C1678.edge = @C2444.edge := rfl
theorem eq_C1678_rename : @C1678.rename = @C2444.rename := rfl
theorem eq_C1678_Lower : @C1678.Lower = @C2444.Lower := rfl
theorem eq_C1678_Impossible : @C1678.Impossible = @C2444.Impossible := rfl
theorem eq_C1678_Essential : @C1678.Essential = @C2444.Essential := rfl
theorem eq_C1678_childOne : @C1678.childOne = @C2444.childOne := rfl
theorem eq_C1678_childTwo : @C1678.childTwo = @C2444.childTwo := rfl
theorem eq_C1678_Sep : @C1678.Sep = @C2444.Sep := rfl
theorem eq_C1678_column : @C1678.column = @C2444.column := rfl
theorem eq_C1678_Slice : @C1678.Slice = @C2444.Slice := rfl
theorem eq_C1678_masked : @C1678.masked = @C2444.masked := rfl
theorem eq_C1678_availableB : @C1678.availableB = @C2444.availableB := rfl
theorem eq_C1678_poolSupply : @C1678.poolSupply = @C2444.poolSupply := rfl
theorem eq_C1678_Choice : @C1678.Choice = @C2444.Choice := rfl
theorem eq_C1678_choiceVal : @C1678.choiceVal = @C2444.choiceVal := rfl
theorem eq_C1678_choiceOK : @C1678.choiceOK = @C2444.choiceOK := rfl
theorem eq_C1678_isMaskedConstant : @C1678.isMaskedConstant = @C2444.isMaskedConstant := rfl
theorem eq_C1678_poolCut : @C1678.poolCut = @C2444.poolCut := rfl
theorem eq_C1678_Move : @C1678.Move = @C2444.Move := rfl
theorem eq_C1678_shifted : @C1678.shifted = @C2444.shifted := rfl
theorem eq_C1678_backwards : @C1678.backwards = @C2444.backwards := rfl
theorem eq_C1678_rowMove : @C1678.rowMove = @C2444.rowMove := rfl
theorem eq_C1678_mux : @C1678.mux = @C2444.mux := rfl
theorem eq_C1678_wordMove : @C1678.wordMove = @C2444.wordMove := rfl
theorem eq_C1678_movedRow : @C1678.movedRow = @C2444.movedRow := rfl
theorem eq_C1678_movedWord : @C1678.movedWord = @C2444.movedWord := rfl
theorem eq_C1678_freeWord : @C1678.freeWord = @C2444.freeWord := rfl
theorem eq_C1678_checkMap : @C1678.checkMap = @C2444.checkMap := rfl
theorem eq_C1678_witnessB : @C1678.witnessB = @C2444.witnessB := rfl
theorem eq_C1678_checkEssential : @C1678.checkEssential = @C2444.checkEssential := rfl
theorem eq_C1678_checkLift : @C1678.checkLift = @C2444.checkLift := rfl
theorem eq_C1678_selected : @C1678.selected = @C2444.selected := rfl
theorem eq_C1678_vars : @C1678.vars = @C2444.vars := rfl
theorem eq_C1678_vertex : @C1678.vertex = @C2444.vertex := rfl
theorem eq_C1678_graphGoal : @C1678.graphGoal = @C2444.graphGoal := rfl
theorem eq_C1678_cube0 : @C1678.cube0 = @C2444.cube0 := rfl
theorem eq_C1678_cube3 : @C1678.cube3 = @C2444.cube3 := rfl
theorem eq_C1678_cube6 : @C1678.cube6 = @C2444.cube6 := rfl
theorem eq_C1678_subcube : @C1678.subcube = @C2444.subcube := rfl
theorem eq_C1678_fixRows : @C1678.fixRows = @C2444.fixRows := rfl
theorem eq_C1678_swapRows : @C1678.swapRows = @C2444.swapRows := rfl
theorem eq_C1678_supportPairs : @C1678.supportPairs = @C2444.supportPairs := rfl
theorem eq_C1678_graphPairs : @C1678.graphPairs = @C2444.graphPairs := rfl
theorem eq_C1678_properB : @C1678.properB = @C2444.properB := rfl
theorem eq_C1678_assertSize : @C1678.assertSize = @C2444.assertSize := rfl
theorem eq_C1678_ColumnInfo : @C1678.ColumnInfo = @C2444.ColumnInfo := rfl
theorem eq_C1678_colFree : @C1678.colFree = @C2444.colFree := rfl
theorem eq_C1678_boundsBefore : @C1678.boundsBefore = @C2444.boundsBefore := rfl
theorem eq_C1678_BoundPool : @C1678.BoundPool = @C2444.BoundPool := rfl
theorem eq_C1678_ValidPool : @C1678.ValidPool = @C2444.ValidPool := rfl
theorem eq_C1678_scalarPoolCut : @C1678.scalarPoolCut = @C2444.scalarPoolCut := rfl
theorem eq_C1678_Bits : @C1678.Bits = @C2444.Bits := rfl
theorem eq_C1678_Signals : @C1678.Signals = @C2444.Signals := rfl
theorem eq_C1678_Decor : @C1678.Decor = @C2444.Decor := rfl
theorem eq_C1678_ofRows : @C1678.ofRows = @C2444.ofRows := rfl
theorem eq_C1678_pairSig : @C1678.pairSig = @C2444.pairSig := rfl
theorem eq_C1678_properPairs : @C1678.properPairs = @C2444.properPairs := rfl
theorem eq_C1678_faithful : @C1678.faithful = @C2444.faithful := rfl
theorem eq_C1678_dneg : @C1678.dneg = @C2444.dneg := rfl
theorem eq_C1678_dbin : @C1678.dbin = @C2444.dbin := rfl
theorem eq_C1678_codeDecor : @C1678.codeDecor = @C2444.codeDecor := rfl
theorem eq_C1678_defaultDecor : @C1678.defaultDecor = @C2444.defaultDecor := rfl
theorem eq_C1678_asRow : @C1678.asRow = @C2444.asRow := rfl
theorem eq_C1678_rawDecor : @C1678.rawDecor = @C2444.rawDecor := rfl
theorem eq_C1678_liftGoal : @C1678.liftGoal = @C2444.liftGoal := rfl
theorem eq_C1678_Cov : @C1678.Cov = @C2444.Cov := rfl
theorem eq_C1678_addCov : @C1678.addCov = @C2444.addCov := rfl
theorem eq_C1678_coverage : @C1678.coverage = @C2444.coverage := rfl
theorem eq_C1678_takeOne : @C1678.takeOne = @C2444.takeOne := rfl
theorem eq_C1678_takeTwo : @C1678.takeTwo = @C2444.takeTwo := rfl
theorem eq_C1678_delOne : @C1678.delOne = @C2444.delOne := rfl
theorem eq_C1678_delTwo : @C1678.delTwo = @C2444.delTwo := rfl
theorem eq_C1678_sameWords : @C1678.sameWords = @C2444.sameWords := rfl
theorem eq_C1678_keyWord : @C1678.keyWord = @C2444.keyWord := rfl
theorem eq_C1678_keySet : @C1678.keySet = @C2444.keySet := rfl
theorem eq_C1678_closeChild : @C1678.closeChild = @C2444.closeChild := rfl
theorem eq_C1678_CovPair : @C1678.CovPair = @C2444.CovPair := rfl
theorem eq_C1678_preCov : @C1678.preCov = @C2444.preCov := rfl
theorem eq_C1678_getCov : @C1678.getCov = @C2444.getCov := rfl
theorem eq_C1678_restCov : @C1678.restCov = @C2444.restCov := rfl
theorem eq_C1678_opKeep : @C1678.opKeep = @C2444.opKeep := rfl
theorem eq_C1678_movedDecor : @C1678.movedDecor = @C2444.movedDecor := rfl
theorem eq_C1678_movedChoice : @C1678.movedChoice = @C2444.movedChoice := rfl
theorem eq_C1678_NodeContext : @C1678.NodeContext = @C2444.NodeContext := rfl
theorem eq_C1678_evalMove : @C1678.evalMove = @C2444.evalMove := rfl
theorem eq_C1678_moveFront : @C1678.moveFront = @C2444.moveFront := rfl
theorem eq_C1678_testPair : @C1678.testPair = @C2444.testPair := rfl
theorem eq_C1678_testRow : @C1678.testRow = @C2444.testRow := rfl
theorem eq_C1678_composedOK : @C1678.composedOK = @C2444.composedOK := rfl
theorem eq_C1678_autoOK : @C1678.autoOK = @C2444.autoOK := rfl
theorem eq_C1678_Packing : @C1678.Packing = @C2444.Packing := rfl
theorem eq_C1678_emptyPacking : @C1678.emptyPacking = @C2444.emptyPacking := rfl
theorem eq_C1678_packedAt : @C1678.packedAt = @C2444.packedAt := rfl
theorem eq_C1678_lookupWord : @C1678.lookupWord = @C2444.lookupWord := rfl
theorem eq_C1678_getFieldV : @C1678.getFieldV = @C2444.getFieldV := rfl
theorem eq_C1678_extendKnown : @C1678.extendKnown = @C2444.extendKnown := rfl
theorem eq_C1678_lanePlace : @C1678.lanePlace = @C2444.lanePlace := rfl
theorem eq_C1678_fullMarks : @C1678.fullMarks = @C2444.fullMarks := rfl
theorem eq_C1678_PackedSig : @C1678.PackedSig = @C2444.PackedSig := rfl
theorem eq_C1678_PackedCov : @C1678.PackedCov = @C2444.PackedCov := rfl
theorem eq_C1678_packedColumn : @C1678.packedColumn = @C2444.packedColumn := rfl
theorem eq_C1678_packedOp : @C1678.packedOp = @C2444.packedOp := rfl
theorem eq_C1678_takePacked : @C1678.takePacked = @C2444.takePacked := rfl
theorem eq_C1678_contextWire : @C1678.contextWire = @C2444.contextWire := rfl
theorem eq_C1678_checkAt : @C1678.checkAt = @C2444.checkAt := rfl
theorem eq_C1678_combField : @C1678.combField = @C2444.combField := rfl
theorem eq_C1678_Batch : @C1678.Batch = @C2444.Batch := rfl
theorem eq_C1678_laneWire : @C1678.laneWire = @C2444.laneWire := rfl
theorem eq_C1678_availableMasked : @C1678.availableMasked = @C2444.availableMasked := rfl
theorem eq_C1678_constantLoss : @C1678.constantLoss = @C2444.constantLoss := rfl
theorem eq_C1678_QuickPool : @C1678.QuickPool = @C2444.QuickPool := rfl
theorem eq_C1678_summarizePool : @C1678.summarizePool = @C2444.summarizePool := rfl
theorem eq_C1678_fastCost : @C1678.fastCost = @C2444.fastCost := rfl
theorem eq_C1678_quickAt : @C1678.quickAt = @C2444.quickAt := rfl
theorem eq_C1678_fallbackAt : @C1678.fallbackAt = @C2444.fallbackAt := rfl
theorem eq_C1678_prelim : @C1678.prelim = @C2444.prelim := rfl
end PEqualNP.Outside.L_meta_670

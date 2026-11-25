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
    op (second % 4) v (input a b c (second/4))

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
    natOp (second % 4) v (natInput a b c (second/4))

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


namespace PEqualNP.Outside.L_meta_10760.KernelPN

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def lowMasks : List Nat := [
  0x5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555,
  0x3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]

def flipPatternBits (i x : Nat) : Nat :=
  ((x &&& lowMasks[i]!) <<< (1 <<< i)) |||
    ((x >>> (1 <<< i)) &&& lowMasks[i]!)

def fastVertices (n positive negative : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range n).map fun i =>
    let low := lowMasks[i]!
    let high := low <<< (1 <<< i)
    let forkP := positive &&& flipPatternBits i negative
    let forkN := negative &&& flipPatternBits i positive
    (i,low,high,forkP,forkN)

def edgeBoolFast (vi vj : Nat × Nat × Nat × Nat × Nat) : Bool :=
  let (_,li,hi,pi,ni) := vi
  let (_,lj,hj,pj,nj) := vj
  let cp := pi &&& pj
  let cn := ni &&& nj
  (!(cp &&& li &&& lj == 0) && !(cn &&& hi &&& hj == 0)) ||
  (!(cp &&& hi &&& lj == 0) && !(cn &&& li &&& hj == 0)) ||
  (!(cp &&& li &&& hj == 0) && !(cn &&& hi &&& lj == 0)) ||
  (!(cp &&& hi &&& hj == 0) && !(cn &&& li &&& lj == 0))

def tryColors (v adjacent : Nat) (next : List Nat → Bool) : List Nat → Bool
  | [] => false
  | c :: cs =>
    ((adjacent &&& c == 0) && next ((c ||| (1 <<< v)) :: cs)) ||
      tryColors v adjacent (fun tail => next (c :: tail)) cs

def colorGraph : List (Nat × Nat) → List Nat → Bool
  | [], _ => true
  | (v, adjacent) :: rest, classes =>
    if adjacent == 0 then colorGraph rest classes
    else tryColors v adjacent (colorGraph rest) classes

def graphPN (n positive negative : Nat) : List (Nat × Nat) :=
  let es := (pairs (fastVertices n positive negative)).filterMap fun (vi,vj,_) =>
    if edgeBoolFast vi vj then some (vi.1,vj.1) else none
  (List.range n).map fun i =>
    (i, es.foldl (fun mask (a,b) =>
      if a == i then mask ||| (1 <<< b)
      else if b == i then mask ||| (1 <<< a) else mask) 0)

def hasEdgePN (n positive negative : Nat) : Bool :=
  (pairs (fastVertices n positive negative)).any fun (vi,vj,_) => edgeBoolFast vi vj

def colorablePN (n positive negative colors : Nat) : Bool :=
  if n <= colors || 10 < n then true
  else if colors == 1 then !(hasEdgePN n positive negative)
  else colorGraph (graphPN n positive negative) (List.replicate colors 0)

def projectPatternBits (i s : Nat) : Nat :=
  let d := 1 <<< i
  let t := (s &&& lowMasks[i]!) ||| ((s >>> d) &&& lowMasks[i]!)
  (List.range (9-i)).foldl (fun t offset =>
    let j := i + 1 + offset
    (t ||| (t >>> (1 <<< (j-1)))) &&& lowMasks[j]!) t

def projectDropped (i j keep s : Nat) : Nat :=
  let s := if keep &&& 2 == 0 then projectPatternBits j s else s
  if keep &&& 1 == 0 then projectPatternBits i s else s

def keepSize (keep : Nat) : Nat :=
  if keep == 0 then 0 else if keep == 3 then 2 else 1

def allPatterns : Nat := (1 <<< 1024) - 1

def transitionSet (n i j keep gate s : Nat) : Nat :=
  let zero := projectDropped i j keep (s &&& (allPatterns ^^^ gate))
  let one := projectDropped i j keep (s &&& gate)
  zero ||| (one <<< (1 <<< (n - 2 + keepSize keep)))

def gates (i j : Nat) : List Nat :=
  let li := lowMasks[i]!
  let lj := lowMasks[j]!
  let hi := li <<< (1 <<< i)
  let hj := lj <<< (1 <<< j)
  [hi &&& hj, hi ||| hj, hi &&& lj, hj &&& li]

def solved (n positive negative : Nat) : Bool :=
  (List.range n).any fun i =>
    let low := lowMasks[i]!
    let high := low <<< (1 <<< i)
    ((positive &&& low == 0) && (negative &&& high == 0)) ||
      ((positive &&& high == 0) && (negative &&& low == 0))

def redundant (n active gate : Nat) : Bool :=
  (List.range n).any fun i =>
    active &&& (gate ^^^ (lowMasks[i]! <<< (1 <<< i))) == 0

abbrev Key := Nat × Nat × Nat

def keyCompare (a b : Key) : Ordering :=
  match compare a.1 b.1 with
  | .eq => match compare a.2.1 b.2.1 with
    | .eq => compare a.2.2 b.2.2
    | other => other
  | other => other

def forceNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | p + 1 => k (Nat.succ p)

theorem forceNat_eq {α : Type} (n : Nat) (k : Nat → α) : forceNat n k = k n := by
  cases n <;> rfl

def gateSpecs (i j : Nat) : List (Nat × Nat × Nat × Nat) :=
  let li := lowMasks[i]!
  let lj := lowMasks[j]!
  let hi := li <<< (1 <<< i)
  let hj := lj <<< (1 <<< j)
  let different := hi ^^^ hj
  let same := allPatterns ^^^ different
  [(hi &&& hj, lj, li, different), (hi ||| hj, hj, hi, different),
   (hi &&& lj, hj, li, same), (hj &&& li, lj, hi, same)]

def validKeep (keep ci cj cij samei samej sameij : Nat) : Bool :=
  if keep == 3 then true
  else if keep == 1 then cj &&& samej == 0
  else if keep == 2 then ci &&& samei == 0
  else ci &&& samei == 0 && cj &&& samej == 0 && cij &&& sameij == 0


def bankMember (budget : Nat) (s : Key) : Bool :=
  (match keyCompare s (7,43259896884819308636185731858431,181481808856423728312281469044960264192) with
| .eq => budget <= 6
| .lt => (match keyCompare s (6,6857574488292687743,11565243847324237952) with
 | .eq => budget <= 7
 | .lt => (match keyCompare s (6,252025654974840591,18194718418718982144) with
  | .eq => budget <= 7
  | .lt => (match keyCompare s (6,35005136518479871,18194718418727370752) with
   | .eq => budget <= 7
   | .lt => (match keyCompare s (6,1970561178089471,17296075228044642304) with
    | .eq => budget <= 5
    | .lt => (match keyCompare s (6,21025010750463,14699785332472160256) with
     | .eq => budget <= 6
     | .lt => (match keyCompare s (6,3708561620991,277766415089664) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (6,3707272591231,277766272485504) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,3569243064191,17293836588019091584) with
        | .eq => budget <= 5
        | .lt => (match keyCompare s (5,56590335,4238376960) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,3707845244799,277766272485504) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,7934154115071,17293832226881931264) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (6,7932925642751,17293832224336513024) with
        | .eq => budget <= 5
        | .lt => (match keyCompare s (6,3809694125951,17293836347568029824) with
         | .eq => budget <= 5
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,8207736964991,17293831949525190784) with
        | .eq => budget <= 5
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (6,131387401142271,150087575568384) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (6,84439113627519,140741726734464) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,75093529007103,14699899267626049536) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (6,46909689395071,140741726734464) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,88442087606271,17293999040866289664) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,847787897354111,17297213462971713664) with
       | .eq => budget <= 5
       | .lt => (match keyCompare s (6,844936082585471,17297200853140146304) with
        | .eq => budget <= 5
        | .lt => (match keyCompare s (6,844695631001471,17297201093591730304) with
         | .eq => budget <= 5
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,852151580456831,17297209099288610944) with
        | .eq => budget <= 5
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (6,18110383251324927,17330036637060562944) with
     | .eq => budget <= 6
     | .lt => (match keyCompare s (6,2058315835601151,17296250325149712384) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (6,1973653444444031,17296087597424623744) with
       | .eq => budget <= 5
       | .lt => (match keyCompare s (6,1970835988889471,17296074953233842304) with
        | .eq => budget <= 5
        | .lt => (match keyCompare s (6,1970562402840831,17296075230594760704) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,1978051486758911,17296083199382308864) with
        | .eq => budget <= 5
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,9631718101221375,12288291489364049920) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,5422872954621183,14708906054027083776) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (6,5348158843604223,14708757347348545536) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,18067657568616447,17330063024936976384) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (6,22518479291103231,17338859115267016704) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (6,21395479515135999,14735830897043472384) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,19161270746619903,14738065102389436416) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (6,19140625153859583,14738030330864787456) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,21467191489822719,14735928064900890624) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,32752787083231231,18196970768162619392) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,32214566486114303,18052828643117268992) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,22525724790372351,17338867395837609984) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,32787970918449151,18196935584327401472) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))))
   | .gt => (match keyCompare s (6,237670212126605311,18194718418727370752) with
    | .eq => budget <= 7
    | .lt => (match keyCompare s (6,216278332939927551,18158689621708406784) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (6,146967501649313791,12150861879392108544) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (6,105084679073267711,17618257666423947264) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,96085622673899519,15891092575113707520) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,86469697175781375,13441142624689881088) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,146931403000020991,12150804155912454144) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,216277237723267071,18158689621708406784) with
       | .eq => budget <= 8
       | .lt => (match keyCompare s (6,216277237723265023,18158689619426672640) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (6,176294570055696383,17908748639547686912) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,216278113896575795,18158689621708374016) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (6,228099916889554943,18194718418727370752) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (6,225847567454306303,18196970768162619392) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,220499426798436351,18158689621708406784) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,219092030405834229,18158689621574189056) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,225882751289524223,18196935584327401472) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,235417862691356671,18196970768162619392) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,230632680578842623,18158689621708406784) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,230549700745363455,13297062621120299008) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,235453046526574591,18196935584327401472) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (6,249764474959921151,8358716095061852160) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (6,247803465907011583,18194718418727370752) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (6,238822103171694591,18203699777168769024) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (6,238690846679007231,18203549696121667584) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (6,238690782254497791,18203549696121667584) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,240202975815892991,18158689621708406784) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,249752195245801471,18196935584327401472) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,249714665821569023,18196935584327401472) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,249679481986351103,18196970768162619392) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,249756748448006143,18196970768162619392) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (6,251941215925141503,18194577681239015424) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (6,249808489382150143,18196935584327401472) with
       | .eq => budget <= 9
       | .lt => (match keyCompare s (6,249808489346358749,18196935583790530560) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,249791932283224063,18196935584327401472) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,251931831421599743,18194718418727370752) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,252025654947968501,18194718418593153024) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,252024559765520383,18194718418727370752) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,252009097883254783,18194718418727370752) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,252025654973857791,18194718418718982144) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))))))
  | .gt => (match keyCompare s (6,1175439983830835199,16185937610727284736) with
   | .eq => budget <= 6
   | .lt => (match keyCompare s (6,393915430520699835,18052828642043527168) with
    | .eq => budget <= 7
    | .lt => (match keyCompare s (6,307374054712293375,14449852318423762944) with
     | .eq => budget <= 6
     | .lt => (match keyCompare s (6,288233912055632895,14411572445427277824) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (6,252025654981654391,18194718416437248000) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,252025654979428181,18194718418718982144) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,252025654977199923,18194718418718982144) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,252025654982161203,18194718418727337984) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,289149649480535295,14425179277501169664) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (6,289075038447160575,14425030467744989184) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (6,288305469413856255,14411668891741200384) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,307371001037142015,14449799954981505024) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (6,380281279712591871,14594134498577743872) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (6,369989692499656703,18052828643117268992) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,320974915698163711,17908748639547686912) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,316983627957141503,16899977507791437824) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,379559987736707071,18052828643117268992) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,393859136455933951,18052828643117268992) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,393821607031701503,18052828643117268992) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,393791254497820671,18052687905628913664) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,393914335375622143,18052828643117268992) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (6,537901610601283583,17908748639547686912) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (6,504403531935463423,17870284042969597952) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (6,504403394496518143,17870284180408543232) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (6,504403394494429183,17870284180410632192) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (6,393915430592253711,18052828643117236224) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,504403531931285503,17870284042973775872) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,514069696069238783,17908748639547686912) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,504403669372319743,17870283905532741632) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (6,504403669370230783,17870283905534830592) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,523639991306289151,17908748639547686912) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (6,1152940129049706495,16195190553455886336) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (6,1076060067317889023,16140901068430690304) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,537995434090281915,17908748638473945088) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,537994338945204223,17908748639547686912) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,1152924937635235839,16140915223400810496) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,1153766064023630079,16144279728973971456) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (6,1153017488820207615,16195129531491680256) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (6,1153009946625771519,16141077536328124416) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,1153853920534032639,16144454720451280896) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false)))))
   | .gt => (match keyCompare s (6,1546766565646520271,16899977507254566912) with
    | .eq => budget <= 7
    | .lt => (match keyCompare s (6,1513209711027494911,16861477863877566464) with
     | .eq => budget <= 6
     | .lt => (match keyCompare s (6,1513209607946713087,16861477966958348288) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (6,1513209607944101887,16861477966960959488) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (6,1185065701811945471,16899977507791437824) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,1175442831350702079,16185950289277280256) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,1513209607944108031,16861477966960953344) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,1513209711021750271,16861477863883311104) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (6,1513209711021744127,16861477863883317248) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (6,1513209607948285951,16861477966956775424) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,1513209711025922047,16861477863879139328) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (6,1522840827825487871,16899977507791437824) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (6,1513209985899640831,16861477589005420544) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (6,1513209882821992447,16861477692083068928) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (6,1513209882820425727,16861477692084635648) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,1513209985901207551,16861477589003853824) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,1546765470701453311,16899977507791437824) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,1546710271781765119,16899977507791437824) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,1532411123062538239,16899977507791437824) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,1546766565560221695,16899977506717696000) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (6,4035131438393677823,14411518811755292672) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (6,2305841910062200831,16140901068430690304) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (6,2291487562423285759,16140901068430690304) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,2281917267186235391,16140901068430690304) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,1944142141172692991,16140901068430690304) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,2305786711142512639,16140901068430690304) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,4011299523861633023,14411518811755292672) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,3818204743490557951,14411518811755292672) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,3673524397848090623,14411518811755292672) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,4020869819098683391,14411518811755292672) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (6,4611451453175199743,13835198796973770752) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (6,4587619538643154943,13835198796973770752) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,4249844412629612543,13835198796973770752) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,4035224166737598463,14411518811755292672) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,4597189833880205311,13835198796973770752) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,4611544181519120383,13835198796973770752) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,4611488982599432191,13835198796973770752) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)
       | .gt => (match keyCompare s (6,6664479707921612671,11565243847324237952) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))))))
 | .gt => (match keyCompare s (7,3146430921135653972107154773,49672344094522819111962017792) with
  | .eq => budget <= 8
  | .lt => (match keyCompare s (7,135930669759474878997069823,74431751697691781621009088512) with
   | .eq => budget <= 7
   | .lt => (match keyCompare s (7,228740394940728167759871,3257862043495616639024976199942144) with
    | .eq => budget <= 6
    | .lt => (match keyCompare s (6,8610647922247163903,9836002327901806592) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (6,8393721227344044031,9836002327901806592) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (6,6881443932248964991,11565243847324237952) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,6881406402824732543,11565243847324237952) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,6867144783529738111,11565243847324237952) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,6881483669286387583,11565243847324237952) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (6,8596386302952169471,9836002327901806592) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,8586816007715119103,9836002327901806592) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,8574993328548831231,9799973530882842624) with
         | .eq => budget <= 8
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,8606519556732575743,9836002327901806592) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (6,9172987792743423871,9259400838110552192) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (6,8970322717135298431,9259400838110552192) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (6,8610740650591084543,9836002327901806592) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,8610725188708818943,9836002327901806592) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (6,9163417497506373503,9259400838110552192) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,146395858778048718831615,3448009633678603864067207593984000) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (6,9187326678500073343,9259400838110552192) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (6,9187249412038418303,9259400838110552192) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,146395858801357150683135,52613509489520727641651937280) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (7,41267178813575552900731391,180777765845141559601323937721743310848) with
     | .eq => budget <= 6
     | .lt => (match keyCompare s (7,12288372712035152074997759,225968759283629733354643408294288326656) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (7,12139619320746262853419007,225968759283629882108034697183509905408) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,606824342857238792077183,170808403787764582678768919260002516992) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,228740394964139677253631,49711938769630789485602013184) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,12288372374249718218588159,213507246826047569013245327123454918656) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,41267175787051050159439871,225968759283600754551568392396203884544) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,41267174581192235399872511,181481159810032427852777207432220803072) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,41267174581191685644091391,181481159810032427852777207981976584192) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,41267176507873281158616575,225968759283600754563097361151663554560) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,96945166381786876967485439,213507246847711819565967042755017342976) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (7,82567264420261234541330431,63299962750680276180918075392) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,82567263335440113106632511,63299962750680276180918075392) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,82567257692738991649062911,181481159820554882766648440602694254592) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,82567265641283122320318271,63299962748374433171704389632) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,135779556337866059563925503,74431902811113390440442232832) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,135779552648798717171154751,74431902811113390440442232832) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,97245037010945229133414399,319014718988573844452865870931257491456) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,135930668376250545281122111,74431751695385938612332265472) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))))
   | .gt => (match keyCompare s (7,1320169648389511908009932663,62062360360562392289471627264) with
    | .eq => budget <= 7
    | .lt => (match keyCompare s (7,928903662382007728329396223,77990978062875758033383718912) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,660121495956891509378383871,181481159809413573531401508158242291712) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (7,660086082152493846955513343,52158688933434202022846922752) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,660086078496421748109606911,181481159809413608948861977919511068672) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,621551567996205443165847551,181481159809452143459362194224454828032) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,660086082223989590540550143,52158688933434202022846922752) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,928903659201216316137766911,271162511154978874132274324325391171584) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,928903656594793903970803551,212679724539595744844700249099237064704) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,660121505124729086524391423,52158653510533462526863081472) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,928903662381883552227622911,319014718992094385202666495269222252544) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,1072317207496170499944447871,78154636395705947720815509632) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,1072317202730761615918333823,78154636398011790729492332672) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,928903662890508835033677823,77990978063452078048064602112) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,928903662854901150968119551,77990978063416189988533960704) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,1072317205036604625132019583,78154636395705947720278646912) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,1320169647765613825695547391,181481159819317280376575565768647770112) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,1072317210100416721439383423,78154636395705947720278646912) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,1072317207794573712225697663,78154636398011790729492332672) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,1320169647774585840578199551,181481159819317280376566593753765117952) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (7,1547987015329591374862843903,77371894711012995508235436032) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,1485528032889559887551869951,61897001982139481784324718592) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,1320205065379127359213535231,181481159819317244958962052235129782272) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,1320169649926459108634132479,62062360365174078306825273344) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,1320169649854963365051315199,62062360365174078306825273344) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,1320207426562368794036109311,181481159819317242597778810800307208192) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,1547987011640383295028933631,77371894711013136245723758592) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,1547722558217787755748884479,319014718991475566289537033409929445376) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,1547722558198007240922071039,225968759308195405873764694001039998976) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,1547987013792503437031069183,77371894706401450228370112512) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,2166805917131421731018724863,76753075803062531934382456832) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,1691287226180634277796870143,77535666380639055541725857792) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,1691287224715182821038454783,77535666376027369524372211712) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,1691287222563062679034099711,77535666380639055541725857792) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,2166805914979301589016589311,76753075807674217951736102912) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,2310257245247004400431355903,76916696361572685419091372032) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,2310257243781552943672940543,76916696356960999401737725952) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,2166805918668368931362177023,76753075807674217951736102912) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,3146430921135513788669591423,49672344094522677824717881472) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))))))
  | .gt => (match keyCompare s (7,29402280136730721776171942143,49517601589612146577608015872) with
   | .eq => budget <= 8
   | .lt => (match keyCompare s (7,10728813662013298482789963263,42089961353573397387012472832) with
    | .eq => budget <= 7
    | .lt => (match keyCompare s (7,6499444937327141474283238399,72420436785326378066469453824) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,3960803648406433119058998271,59421726366622608552817590272) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,3301173426103893966405990263,49517601585865230304352927744) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,3300468225217377432404426751,49517903814444577351756939264) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,3300367672015431641995804671,3257911560235344642097876717010944) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,3301173427309787965554120191,49517601588276907904248315904) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,6499331599618823664971415551,225968759303243796832343877576990654464) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,3961408112469091568972149759,59421121902559950102904438784) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,3960803648439797799399421951,59421726366660739616059983872) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,6499444937173418607608550911,72420436783020535057792630784) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,9902311388770803519094783999,69324642214431314701665173504) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,9595239507924437152762369535,225968759352760340593666925772423577600) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,6499482715339493705898098687,225968759303243645716623207536063971328) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,6499444938710365807952003071,72420436787632221075146276864) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,9595239508222204839087518719,69324642214431314701665173504) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,10728008350449551887685779455,3448051722584628432440695466229760) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,9942360007933491192142978911,212679724550892552163458908502406201344) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,9902311389976697517962166271,69324642216842992301560561664) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,10728108460929639909066735615,42090263579407870280925184000) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (7,19498155359681847267038296063,59421726366660739616059983872) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,17022879743780798805944784383,61897001976413154859456397312) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,13204089277530171714297091583,39614685738056524155505344512) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,13049951235418555987862577023,39768823780239635625524895872) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,10728813662046698347504687103,42089961353611493265882785792) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,13204089277563536394639734783,39614685738094655218747738112) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,17329951624680208035198009343,61897001982139481784324718592) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,17329951624329397485954269183,61897001976413154859456397312) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,17022879744165009219903248383,61897001982177577663195031552) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,19498155359297672037384786431,180777765893876381693191716328437710848) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,23613706234860901789397647231,39768823780239635626061758592) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,23613706234642847124950564671,39768823779372869169074143232) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,21136859030358453727140216831,271162511182367541916449182613803925504) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,19805831703106888581292457983,59421121903712801238230269952) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,23613706234642882308785782591,39768823779372833985238925312) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,24895338272928578675288276863,49672344094522677824717881472) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,24895338272698134558666604351,49672344091064054598946783232) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,23613706234861041972835201843,39768823780239776913305894912) with
         | .eq => budget <= 8
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,24895338272928718858725822223,49672344094522819111962017792) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false)))))
   | .gt => (match keyCompare s (7,2693757689181701760126355832831,181481849401436461675645695791036628992) with
    | .eq => budget <= 6
    | .lt => (match keyCompare s (7,36982249748047398319155085311,42244703858772291500350930944) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,34798254124268422491135741711,39769428243111338265274220544) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,29554609512368647921821876223,49672344094522819111962017792) with
       | .eq => budget <= 8
       | .lt => (match keyCompare s (7,29554609512150488257822982143,49672344093655876183895048192) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,29554609512138063621813174271,49672344091064054598946783232) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,34797720792003763400579448831,319014719028148633259821402848866893824) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,34798858587211620874481262463,39768823780239635625524895872) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,34798858586981176757859589951,39768823776781012399753797632) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,34798254124268422491143081983,39769428243111338265282609152) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,36829315909499664858917830911,42090565816771426280584249344) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,792281824256821431074330542079,213507449647048755431735904805708660736) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (7,39458129826555578146046214143,39768823774186974199364452352) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,39458129826433495272643887103,39768823779372869169074143232) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,36982249748047398319163408383,42244703858772291500359319552) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,792281675503767906728563212287,225968771959942456259190160654451376128) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,793829051759723393905309286399,225968771984700501461648962003138543616) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,792378362912278727346887884799,213507449671806949387585995318491119616) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,792281824257159195892658503679,225968771959942307505798871490356084736) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,798780810736273259652878204927,225968771979748742485099096255569625088) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (7,6338265114103409342300094627839,213508869418815254317021586633269477376) with
     | .eq => budget <= 6
     | .lt => (match keyCompare s (7,2700256711078617388285675241471,225968770078272842142754967622772588544) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (7,2695077677515967823475727204351,181481849421242935615622281754964918272) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,2693757689182907597844566310911,225968770058466442580050469538448277504) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,2693757689181701760126364188671,181481849401436461675645695791028273152) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,2695077677515967823475735560191,181481849421242935615622281754956562432) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,6338253232241959583186286182399,213508869415721310913893211752049442816) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,5388175129503445759902557601791,181482539013265939458133645515441569792) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,5387515411271933890565931466751,181482539003362950412385645465490685952) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,6338253532112588713174920888319,319014731664886418604021334127325249536) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,40724595684362849868376697536511,181481811391724928768740236853994586112) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (7,10776350269078823223950756020223,181483918227022734762046510781803003904) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,10775071366605773901553188470783,181483918217737882238113053252647911424) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,6339800426466955017560178851839,319014731667980661877421301412027990016) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,40723275696028583805027326164991,181481811371918454828763650890066296832) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,43258576780786775547339472699391,181481808836617370070571908577919762432) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,43258576745369315156192085737471,181481808836617405488032299725306724352) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false)
       | .gt => (match keyCompare s (7,43258658944780023264158369513471,181481808857661668351566841072322609152) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))))))))
| .gt => (match keyCompare s (7,2659307855868838016586605553698952703,223312899489812735639160181417010266112) with
 | .eq => budget <= 8
 | .lt => (match keyCompare s (7,333610163648585705443407611819933503,255878995517999198540000885099517181952) with
  | .eq => budget <= 8
  | .lt => (match keyCompare s (7,1298094099351361374525967078211391,255214371378902543240621360294494470144) with
   | .eq => budget <= 7
   | .lt => (match keyCompare s (7,243390167747859140830555784049651,15950735951894870570710443766281437184) with
    | .eq => budget <= 7
    | .lt => (match keyCompare s (7,101412048315767463058588352675839,319014921812476752708027680910106198016) with
     | .eq => budget <= 6
     | .lt => (match keyCompare s (7,86517194574090484695185780047871,181482457884246494871094710232219123712) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (7,86517153523647016567509978120191,181482457873724838037302968521444032512) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,86517153488229412061175178002431,181482457873724873454907474856244150272) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,86517153488229403053976460132351,181482457873724873454916482054962020352) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,86517153526008199808944800694271,181482457873724835676119727086621458432) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,86517813544110127377076355530751,181482457883627524851452028341643640832) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,86517774858483899708943301804031,181482457883666210477679696474697367552) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,86517194574090484695735535828991,181482457884246494871094709682463342592) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,101412048315767443355639451647999,225970381876204897221690862998072098816) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,202824096237992259278770842588501,3245185537188748336152574641045504) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,162893102129327727891985291280383,181483766089143364520406065831783432192) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,101412144732600622520446995169279,319014921812669274144756485716136984576) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,101412060109084521581563255357439,225970381876397418658419667804102885376) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,162895588325563454433864600483703,181483766128912188282448907160761925632) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,216292883764679311016946608177151,3245185536886510296997258187505664) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,216292883664126109094567709048831,3245235247661193486282292549648384) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,202825024892947319365510168008021,3245263526806742246929618629033984) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,243389844090806218822077230838771,15950736023696148411182221115005108224) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (7,689608425808532748371792203087871,225971517710949137880884125730103885824) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,689601967630770968185558859218943,225971517691306208938057054167849009152) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,425930613766330656744001336147967,225970057357843761412284505366022094848) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,425930601974194170138520065835007,225970057357651238794964080117457911808) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,425930601823078449442091262738431,225970057357651389910684776546261008384) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,425930642780550327459917559693311,225970057357814747192613789449798549504) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,689601967630775147572191574294783,2758460482962222109106871260413952) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,689601967630772841869919832179967,45193751898942157183882530301180657664) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,689601967630772121036694185050111,225971517691306208936904203032523177984) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,689603474350607061754350437105663,225971517715900595806570743171869868032) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,703070714252319410761786621689855,2758407706398870920632070507069440) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,703070714152208921127070476599295,2758460318550805563582906388971520) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,689621424679516092048860600271103,2758467127822988073788920542789632) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,689611521763664718813975977854207,45193751926011781888548998364528656384) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,703070714252319401191783425703935,2758407706398870882352057789972480) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,855191932609890395592325630088533,2606339306413334172155046508101632) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,855188786984907758327213215143253,2606289634069257846271518873485312) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,703070755255059598725956308566015,2758460482962208273978449649991680) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,1298075143235134361908400499932991,255214371357702366725612918345620783104) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))))
   | .gt => (match keyCompare s (7,21013550701039536591163302108934963,15992274364056092875246762679034970112) with
    | .eq => budget <= 7
    | .lt => (match keyCompare s (7,1622593696818006665767708631437311,319017964177630213891261179626671570944) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,1541486651701636386675547028009983,271165107328166186746820120003081142272) with
      | .eq => budget <= 8
      | .lt => (match keyCompare s (7,1541464058422286279429678857925631,271165107303407537083142894199446175744) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,1541464058422281379514161593004851,2596226419641004520815135234719744) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,1541463130240190156902795722044211,2596148429871894882621446971981824) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,1541484175217094872576431117775871,271165107330642671288262441904713498624) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,1622592768825466114764147452219151,3245185537188748336152574641045504) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,1547508083934845902835183971939123,2606329402893019889112847851978752) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,1547484471195737189898144890958643,2606289634069257846271518873485312) with
         | .eq => budget <= 8
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,1622593696817998595318209054707471,3245263526806742246929618629033984) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,2280503430948380117443837253586703,2606289634069257846271518873485312) with
      | .eq => budget <= 8
      | .lt => (match keyCompare s (7,1926829840801938154449835028054271,3245263526806742246929618629033984) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,1926828912946649449772217932906751,3245185537188748336152574641045504) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,1622627431142138886834152456261631,319017964213531079485088193267445530624) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,2271654635543141000661647715405823,319017315186326678483046142986464264192) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,2585927996303073964383986939592703,2606289634069257846271518873485312) with
       | .eq => budget <= 8
       | .lt => (match keyCompare s (7,2575866020867965846641911848173823,2596148429267432011060095003656192) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,2280528325148857621887801453645583,2606339306413334172155046508101632) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,21013530815717419430169513504797683,15992274324287269113203921350056476672) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (7,176541420823787759082760919783440213,706162514120280906384686446492516352) with
     | .eq => budget <= 8
     | .lt => (match keyCompare s (7,166805096776970066945021525642645263,213343699662785410923667944378415972352) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,166805071921075950610090226649882463,213343699662785410923667944378415972352) with
       | .eq => budget <= 8
       | .lt => (match keyCompare s (7,166153499511800110581445306250952703,213341093373151341684018608443869888512) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,22316675633662275394410604892730163,15994880613921338352853257284602560512) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,166805075028062715151956639023977813,213343699662785410923667944378415972352) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,176538093190347836161160318038278143,226674911656197077198733625546437066752) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,168434002942748490449080654122389263,213343699662785410923667944378415972352) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,167008688298785018089964030083945813,213343699662785410923667944378415972352) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,176538094840367883144043813280907263,226674911680955235736835102783217631232) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,251510757650408702756420161884851983,63805550097213551468053288097165606912) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,250207612832463846792179070496919503,63802943807579482228403952162619523072) with
       | .eq => budget <= 8
       | .lt => (match keyCompare s (7,177230389204351123731581649146576895,45193751861638899845709224071921696768) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,177230388874236289985984721158373375,45193751898942157168894550743439147008) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,250207632717785963953172859101056783,63802943847348305990446793491598016512) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,333610143821368470700773176458084351,255878995493085806361651294383617605632) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,333610143768156181101435996122120191,255878995481953866301504158700364890112) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,333610143768156181101400812286902271,255878995481953866301504193884200108032) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,333610143821519586428225004568051711,255878995493085655245923842555507638272) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))))))
  | .gt => (match keyCompare s (7,581546121845506411234925034601447183,664624139252002285358694275672440832) with
   | .eq => budget <= 8
   | .lt => (match keyCompare s (7,415383748683017311096422761817407487,835635275671355515831348719989587968) with
    | .eq => budget <= 6
    | .lt => (match keyCompare s (7,354460801361529046546820843785403323,271868663552652398395358534930700173312) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,353076209994074513581975424805843763,271868663552652398395358534930700173312) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,353076187370478525004538935374774271,271868663527738855101281492386690629632) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,353076186380728580775849452877381631,271868663512884181457408601063887470592) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,353076186380368278970741941352792063,271868663512883574633315693601721679872) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,353076209993107387683678980433772543,271868663552652398395358534930700173312) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,353320549646358268659527544554648563,271868663552652398395358534930700173312) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,353082207812601488486901578296721203,706162514120280906384686446492516352) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,353076215934977791089581373792518143,271868663562555918709641577129356296192) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,354460798875977561419143260724247483,90387503713374279370755899288811732992) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,354623691978751639496091052881425203,90390110003008348610405235223357816832) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,354623674578981007462774847338443763,271871269802517643872965029536267763712) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,354623670851564015910831596861600563,271871269802517643872965029536267763712) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,354623670850596890012535152489529343,271871269802517643872965029536267763712) with
         | .eq => budget <= 8
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,354623691978106888897226756633377723,271871269802517643872965029536267763712) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,355662114376671352685317438910234623,271871269802517643872965029536267763712) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,354623694463696300530719886532654003,101062866054521884974435887189571141632) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,354623694463335998725472191570509823,271871269842286467635007870865246257152) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,415383748683017311096417809795678207,830767571642881472052407428427317248) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (7,415485556871717777625633983011258367,106338239662793572075333730519335600128) with
     | .eq => budget <= 6
     | .lt => (match keyCompare s (7,415383750236256072954802559627132927,106341497524835903605531381334435463168) with
      | .eq => budget <= 6
      | .lt => (match keyCompare s (7,415383748700922440313210312505458687,830767497365574799042154523000864768) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,415383748683317181725576161961607167,106338239712504906358951235604667465728) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,415383748683317181725552750452113407,106341497524836463205959471095265394688) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,415383748700943709409127299542908927,835635275670496045131666555676950528) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,415384937105247536079918504004845567,830767571642022001352525156051877888) with
       | .eq => budget <= 6
       | .lt => (match keyCompare s (7,415384937105226266984006468989124607,830767497365574799041954414938062848) with
        | .eq => budget <= 6
        | .lt => (match keyCompare s (7,415383750236356626156748350035755007,106338239662793572075333860809475391488) with
         | .eq => budget <= 6
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,415485556871617224423711604112130047,106338239712504346758523015553697742848) with
        | .eq => budget <= 6
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,581537249092818204596841643375591423,319679332989995758957778832329290022912) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,581537248156280549967524525049380863,319679332986273025374053041505904361472) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,417664276969249441654141376065900303,106340845952427339084386228818266816512) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,417012704559973601625496455666970543,106338239662793269844736892883720732672) with
         | .eq => budget <= 8
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,581537248156431665694976353159348223,319679332986272874258325589677794394112) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,581537273051238967292609250206879503,319679333035944611510558565743263219712) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,581537273050101172118142845063266303,319679333035944611510558565743263219712) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,581537249092818204596876827210809343,319679332989995758957778797145454804992) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,581537277710510206732538313302933503,319679333035944611510558565743263219712) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))))
   | .gt => (match keyCompare s (7,617893388142283799582315864951619583,706162513965538401474013912138514432) with
    | .eq => budget <= 8
    | .lt => (match keyCompare s (7,583817756595727434824784404330565583,319681939285809856988165060348830810112) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,583817751585711279306867823591030783,319681939275906336673882018150174687232) with
      | .eq => budget <= 8
      | .lt => (match keyCompare s (7,582514631663104696021537101546770383,319679333035944611510558565743263219712) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,582195158953578843325715305504661263,213343699662785410923667944378415972352) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,581546146604307196942530531241754383,319679343177149413336393777167133048832) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,583166204071773711957133272535773103,319679333035944611510558565743263219712) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,583817751721115398322283981443170063,319681939276061079178792690684528689152) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,583817751625155435650846893941940063,319681939325578680750207901677809303552) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,583817751586849074481334228734643983,319681939275906336673882018150174687232) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,583817751722248766278172696294395663,667220287681269699172818786348695552) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,604831278673044581036989152864763903,335674213600193605768889003915903762432) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,584123176152203768328274378420649983,319681939275906336673882018150174687232) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,583817776479911756811311787791089663,319681939325578680750207901677809303552) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,583817776441605395641799122583793583,319681939275906336673882018150174687232) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,602306464212567710322655305065037823,335671607360231880605565551508992294912) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,617883349840038813524725157318426623,271868663552652398395358534930700173312) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,617883326319178067102499935510134783,706152372915479080549475022622687232) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,604831307296766971166139217057350403,335674213649865949845214887443538378752) with
         | .eq => budget <= 8
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,617883351077978852810105432150441983,319720871410812890131584557914083295232) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (7,1939109039852132119953664581539201023,324998851259046000165209016015144353792) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,1770573255169360750964299090612649983,111655151645932933336063890748690399232) with
      | .eq => budget <= 8
      | .lt => (match keyCompare s (7,620469254161947561726017527888216063,708758662394805815288138422814769152) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,620165018017892786669674811793342463,319723477650774615294908010320994762752) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,619434851272161326534452293165645823,271871269802517643872965029536267763712) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,1330952026907853501032874773518985983,111655151645932933336063890748690399232) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,1773159156756679295197300268145311743,111657757935567002575713226683236483072) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,1772303967970500325937361914622377983,111655151645932933336063890748690399232) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,1770573257654912236091976673673805823,293136311485211052360666526390578839552) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,1936726754681160861295935907481452543,324996245019084275001885563608232886272) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,2658658815975754673631183559521039861,10633824041794424958852373148782854144) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,2658496556430145663322233367244570623,223313710736843694045703006359463657472) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,2658456002143096964229322931615137791,223310303334110570494506201829076926464) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,2658455991879765382906611953323835391,223310303317863363061305692629390884864) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,2658496557936865499415802158822457343,223313710761438080914216695363484516352) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,2658658816296974948555110510314747381,10633823968755207079383445901311770624) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,2658658815975754675934246959853819391,223313548503399191749900376986840203264) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)
       | .gt => (match keyCompare s (7,2658658826188556935902017508775777791,223313548519493016719772992247655563264) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))))))
 | .gt => (match keyCompare s (7,4607298052730516210961327573092532223,335671607310559536529239667981357678592) with
  | .eq => budget <= 7
  | .lt => (match keyCompare s (7,3989610851083482815449221968394391311,334968700163104812463979859396708532224) with
   | .eq => budget <= 7
   | .lt => (match keyCompare s (7,2835849274207074290291880401039086933,42537902164654897502745296637286940672) with
    | .eq => budget <= 7
    | .lt => (match keyCompare s (7,2834994087905640867911039260267249663,224016455714298947287698596344629297152) with
     | .eq => budget <= 8
     | .lt => (match keyCompare s (7,2834994084760063883701713757204905983,224016455664627361151193072107270438912) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,2669695777180825665087921167231440213,10677968630781674861526259419632893952) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,2669044204810993981403255317183419733,10675362390819949698202807012721426432) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,2669044204771549825059276246832510453,10675362341147605621876923485086810112) with
         | .eq => budget <= 8
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,2834994084760028466241322609817944063,224016455664627396568653463254657400832) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,2834994085172259589666285905808195583,224016455690623344030312860690690342912) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,2834994085172259589666250721972977663,224016455690623344030312895874525560832) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,2834994084760214999429165585314873343,224016455664627210035465620279160471552) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,2834994086410199628951622749335322623,224016455689385403991027523847163215872) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,2835686381104300212214932608881909213,42535295875020828263095960702740856832) with
      | .eq => budget <= 8
      | .lt => (match keyCompare s (7,2835197704283349935390913063701313013,224016455714298947287698596344629297152) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,2834994114314625397392613580292030463,224016455714298947287698596344629297152) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,2834994087906446806159619630577309013,224016455714298947287698596344629297152) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,2835645660314916707939684180666179423,224019062003933016527347932279175380992) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,2835686383590496447941474488191112533,42535295914789652025138802031719350272) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,2835686383589851697342610191943065053,224016455714298947287698596344629297152) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,2835686381104907036307981358291836253,213343699662785410923667944378415972352) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,2835849273546194854533712501375238143,224019061954260672451022048751540764672) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (7,3987684024183463787451588812702973951,334965454979888761307462484459085922304) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,3987683987355196244035919081938911231,15950736023696148411182221115005108224) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,3252861981252599376795245950385063173,330357301666726286353887889578568712192) with
       | .eq => budget <= 8
       | .lt => (match keyCompare s (7,3190310075568603336588892755442340113,314406565717307295879906895983659712512) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,3188070295413196770217232168257716223,314403959427673226640257560049113628672) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,3276339320983859910979449555075006463,224016455714298947287698596344629297152) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,3987684016755823551772838415369764863,334965454987316401543213012070697009152) with
       | .eq => budget <= 8
       | .lt => (match keyCompare s (7,3987683989539276574755160555026153471,15950735951894870570710443766281437184) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,3987683987355196252102147487658115071,334965454937799555560196471123047645184) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,3987684016909357130863896320549126143,334965454987471144048123684605051011072) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,3989306580123110596453305194272263951,334968700123335384248863213074518114304) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,3987988228141148376618818679502532863,15950735949418990492177929179236401152) with
       | .eq => budget <= 8
       | .lt => (match keyCompare s (7,3987988225665268298014526878179619071,15950735951894870570710443766281437184) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,3987988223499180183590829614054732031,15950736023696148411182221115005108224) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,3988718396124989881232804780189928703,63802943807579482228403952162619523072) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,3989610816267094536012298277485576191,334968700123335384248863072337029791744) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,3989610816267094535508018264640786191,334968700123335384248286752322348908544) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,3989306617105822832441133627611287311,334968700165580692542550619946372562944) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,3989610851065348651453841425130524431,334968700163104812463979859396708532224) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))))
   | .gt => (match keyCompare s (7,4357945633694247489196811926240231423,271871269802517643872965029536267763712) with
    | .eq => budget <= 7
    | .lt => (match keyCompare s (7,4166801303600479276202624268237078613,335674213649865949845214887443538378752) with
     | .eq => budget <= 8
     | .lt => (match keyCompare s (7,4024030094783701232464801002456940543,335006993362184680164239004241517084672) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,3990259853374411380888758551045996543,334968051086228067385611925588092649472) with
       | .eq => budget <= 8
       | .lt => (match keyCompare s (7,3989610853249348979152556049085530111,334968700165580088079640812631785242624) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,3989610853249344275232817253149868031,334968700165580088079640812631785242624) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,4024030070024900446757195505816633343,15992274324287269113203921350056476672) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,4026615993360794485857375535134408703,15994880613921338352853257284602560512) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,4024335489930983901164206592406585343,15992274324287269113203921350056476672) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,4024030094919100924261639470016692223,15992274373959613189529804877691092992) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,4164222109996782575557119566689992703,335671607360231880605565551508992294912) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,4253529570666098290458539263508086783,63802943797675961914120909963963400192) with
      | .eq => budget <= 8
      | .lt => (match keyCompare s (7,4252491135567445716319336953507282943,245284103646857601253006587804507963392) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,4252491133081894231191659370446127103,63802943807579482228403952162619523072) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,4190183569536700557088832322685435903,229333367697438610779025594209598963712) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,4252491156694633339904596409527107583,63802943847348305990446793491598016512) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,4343342090589293005606764926750359603,335674213649865949845214887443538378752) with
       | .eq => budget <= 8
       | .lt => (match keyCompare s (7,4340760203228070192784483684613095423,335671607360231880605565551508992294912) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,4255077055136326901500332474644824063,63805550087310031153770245898509484032) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,4356337088855541295986553536866484223,271868663552652398395358534930700173312) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (7,4605567318180801141121085897297690623,335671607310559536529239667981357678592) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,4584798151912535080421017401495977983,319679333035944611510558565743263219712) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,4569221265047123937933567274410573823,335630068985363601984539559338172219392) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,4441348169635063386204963259698642943,122330513987080538939743878649449807872) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,4439413843563201508293893044628946943,122330513987080538939743878649449807872) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,4571806004622197928354788383055085583,335632675274997671224188895272718303232) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,4605567313673925685597748334237384703,335671607310714279034150340515711680512) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,4605567313520392106506690429058023423,335671607310559536529239667981357678592) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,4587139714429361878491144597341732863,319681939275906336673882018150174687232) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,4605567316666017089143955541472968703,335671607360231880605565551508992294912) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,4605577375497031418077564263678869503,335671617451764338355074879405227507712) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,4605567339929376635988264749082804223,335671607310559536529239667981357678592) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,4605567338414592584011134393258082303,335671607360231880605565551508992294912) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,4605567319462262509912592822416769023,335671607320463056843522710180013801472) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,4605567342921468039534471956318388223,335671607360077138100654878974638292992) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,4606605757046466569179472715478728703,335671607310559536529239667981357678592) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,4606422531861986526134048585330742613,335674213649865949845214887443538378752) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,4605872738086884595528096983887642623,335671607310559536529239667981357678592) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,4607114827546197355565619517006558003,335674213649865949845214887443538378752) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false))))))
  | .gt => (match keyCompare s (8,3004893228578014451226347774184595039258009134397303,58123087917355293493615765628302222126930334746503969437198259080514190180352) with
   | .eq => budget <= 7
   | .lt => (match keyCompare s (7,6646139979068441537053307016149172223,332306998946393382137419504174648819712) with
    | .eq => budget <= 7
    | .lt => (match keyCompare s (7,5316993118039564105969557725480222719,265849655649426395248810214443559419904) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,4608153265130401414832499410068517683,335674213639962429530931845244882255872) with
      | .eq => budget <= 8
      | .lt => (match keyCompare s (7,4608143209095869584222363283963773183,335674203508661148019379676019668549632) with
       | .eq => budget <= 8
       | .lt => (match keyCompare s (7,4607847846505949998493165209369186063,335674213649865949845214887443538378752) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,4607847816950202691199859371785846783,335674213600193605768889003915903762432) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,4608153244663126101107111409340470613,335674213649865949845214887443538378752) with
        | .eq => budget <= 8
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,4608153271071304692340105359055192063,335674213649865949845214887443538378752) with
       | .eq => budget <= 8
       | .lt => (match keyCompare s (7,4608153270918975316702179213405257983,335674213649711207340304214909184376832) with
        | .eq => budget <= 8
        | .lt => (match keyCompare s (7,4608153266412033452900176295959138063,335674213649865949845214887443538378752) with
         | .eq => budget <= 8
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,5316993112860288818391545025029734399,265849655639068318828763749275133804544) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,5669988169520054424196358829831618559,266551751529744855613988091686933233664) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,5318291187302437655735169250502868991,265848357580163521699044602918536773632) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,5318291187074922524289836148611612671,265848357564853685122865458151551926272) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,5318291187074922524145756145042030591,265848357564853685123009538155121508352) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,5318291187921256559650407559171407871,265848357579544702795129364609868234752) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,5669988174842932154118519522496348159,266551751540266401472167511799569055744) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,5669988169891171996977068792180867071,266551751545218161629308962529884536832) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,5669988169520356654498340983055286271,266551751529744553383686109533709565952) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,6646139978925141326163992312484429823,332306998946229610467831715941889114112) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (7,90387503729158614598912195147253112831,180775007426749163192563345494275825664) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (7,42535944902263313370351227303091986271,170143779658571598801041172391457193984) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,27913787911483493061170001619139428351,311039351013671258732825706635234115584) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,9304595970638273282860885952203587583,329648542954823550391611925238594404352) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,9304595970494821956244154604264095743,329648542954659929837751553650109448192) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,27913787911627095503514149611353669631,311039351013834728170958661579444322304) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,45194603744197120284996746778752538111,180777603575177826140837877167941484544) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,45194603718509510298319753619724785151,180777603627172063357355256136706555904) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,42535944929150269265657293722869522271,170143779611374379235637749280338345984) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,90387503713466157723424668850305851391,180775007490038243223382967490638290944) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (7,148875807157786564542136922066158292991,170143779683175657081838105353743499264) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (7,148873535528045977457527772015259246591,170141183534900376594297394234187096064) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,90389045192288133225990408509973271551,180777603575177826143431915368330829824) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,90389045176504515787938791554283410431,180777603638313372595196226781547864064) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (7,148873535530077572574550655874857132031,170141183462945716290497722946592743424) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (7,158178131499333443905017215017520422911,180775007504738781189896858254268473344) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (7,158178131498405588616312537400425275391,180775007426749163195986081210280484864) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (7,148875807159952652656560619330283180031,170143779611374379241366328005019828224) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (8,3004893228578014448945869238574487850533030606632823,58122201056482360385578726829680642409842879181541266868359938635985250680832) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))))
   | .gt => (match keyCompare s (8,52312185780721807057911293039237226155193314595043229503,58123087917355293494400403344491951908295142101783061612777826034913747402752) with
    | .eq => budget <= 7
    | .lt => (match keyCompare s (8,6541652098660374843988134309462504420910426982642048863,58123087917355293495283120776030703890667014693566425914923292755185035640832) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (8,3077010471924803319951393759362230917376963142068690783,58123087917355293494203477668406978208729313026718184920402936792257052803072) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (8,41904631685720267607087762890733332965193661676457983,108555083659983933209597846337044004194815905534582109981633475813074987384832) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (8,28435409756979540724021137660566097082070811885384703,92271821110986343228158176570014579448331303284049202030919754738675841236992) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (8,3004893228578018472975909708865422239080614601389943,61754838608134089087595462324257954916789668218387900088666476668230368755712) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (8,3077010471924803319949846298504741415048106970012933983,58122201056482360386166438869785398491641857461745578831250333305529457180672) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (8,6513106484258182865889911137785539282338388131043303263,58122201056482360387246033900584867850248027885291387024699121802891893932032) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (8,6154021309213822046012887809796579917247247946358931263,58123087917355293494988115385147625599494571631995425646901947021564661727232) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (8,6154021309213822046012032624156025930624574705250942783,58122201056482360386951076586526045882407116067032723078063626577035722227712) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (8,6513106484258182868558955339410658186262010405768658943,61754838608134089089262769395162180357189500010154880581514332837272042340352) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (8,10769536649190154718106166949865395339191735258472478583,58123087917355293496165071959799022928620383474157555627452066261198492925952) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (8,10727469245278167139310328776424512972261314341391783423,72370055790172588808674869758734946182642608897894991183586017989736836104192) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (8,10727469245278167136651183816144000519129142652293314423,58122201056482360388127985084535874592867759530657977341317430686361805914112) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (8,6541652098660374846656323325447069338211376016259416063,61754838608134089089262817471986436680521031253467216902900183345036244549632) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (8,10727469245278167140641280773930086336563467338738827263,108555083659983933209610058410888133742040656975992499110735673000274849431552) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (8,52296410390074996298388883879428825541710231457441857343,58122201056482360386363316469228803572542518158283483326643190460077060390912) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (8,49055571430417742133071962645442725363696209981781005823,72370055790172588806897222821813312670684704558529246281687992122485183086592) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (8,10769536649190154722093688071032893327510139809241759743,108555083659983933209610106487529702360705825364670424887352912669472112771072) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (8,52296410390074996298409897386630836726279358998111453183,61754838608134089088380051963806116079489307195140020067264011534520834588672) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))))
    | .gt => (match keyCompare s (8,845789342515396316011878824004375485626239203937664334280954868723,3632637565184358185558708211387336075528085213320825817314900270234239762432) with
     | .eq => budget <= 7
     | .lt => (match keyCompare s (8,84957721546752713585242404804296967003000857328739103743,92271821110986343229348111466280539269089778093202582898693659619276579930112) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (8,73607302302795567517458832777546213779136361968622895103,108555083659983933209892085479976816332272901565643051399421051043885415923712) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (8,73559786503916788430049229856949220483598324730140033023,108555083659983933209892037590404602796577894797415717697870063438714520993792) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (8,52312185780721807057930759085581747837433585963657068543,61754838608134089088380100040447684698154475573666992264246043622629925978112) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (8,84957721546752713585241026213233590930068615646311577463,61754838608134089090439725969813577686315311852317010562064452076905873539072) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (8,845789342463487536846846376051411545331078038062751411170423469043,3632637565184358181721339376142857355689582195087043707332773319192977866752) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (8,845789342463099905679845233649839731805381007851680750493810906453,13532629479409598490865154262289882081266363937693411867234981117952) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (8,84957721546752713585243134972280808507614843429426499583,108555083659983933209905063801588524328541461799179612647292271678210265055232) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (8,845789342469613012106062010572022304448654140934831292798328722773,13532629484424690148166087846329341199337310082680626521525056438272) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))
     | .gt => (match keyCompare s (8,964698497368997843952493206019119687338995920116488847380937485521071758813,14474011154664524427946373126268676186618247259425973337618051220497982554112) with
      | .eq => budget <= 7
      | .lt => (match keyCompare s (8,113078218912131336798538950499541643601755381406279284504810949494889495483,28948022309329048855990825966787393850487039117453470793260421989307202404352) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (8,8424983333509126666791477115273873184618394468107122443690357795583,36185027886661311069964012529830388091295145511123447391760060076837287493632) with
        | .eq => budget <= 7
        | .lt => (match keyCompare s (8,8424983333495302404622001120165709396495660849491090434766970792703,36185027886661311073801381365074866811133648529357229501742187027878549389312) with
         | .eq => budget <= 7
         | .lt => false
         | .gt => false)
        | .gt => false)
       | .gt => (match keyCompare s (8,113078218912131336802727772103792018366592343049069773589932482450474908603,28948022309329048860220513660493540118044011326705173400282485242662980943872) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false))
      | .gt => (match keyCompare s (8,1356938545749799165119991562044413679796861054168825659613329663151675788543,21711016731996786641919559689311670427426353653095949936117689308028067643392) with
       | .eq => budget <= 7
       | .lt => (match keyCompare s (8,964698497368997843985141746620337765935569171006573199937212662093377822173,14474011154664524433353783642031277318376175568514839979645202177102574518272) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)
       | .gt => (match keyCompare s (8,1356938545749799165131370416155751468539548873223676026653045822891092856063,21711016731996786646934651346612604011465812771166896081104903962318142963712) with
        | .eq => budget <= 7
        | .lt => false
        | .gt => false)))))))))

def allowed (budget : Nat) (s : Key) : Bool :=
  let (n,p,q) := s
  solved n p q ||
    (!(budget+1 < n) && (p &&& q == 0) &&
      (!(budget+1-n <= 3) || colorablePN n p q (budget+2-n)))

def children (budget : Nat) (s : Key) : List Key :=
  let (n, positive, negative) := s
  let extra := budget+1-n
  (pairs (List.range n)).flatMap fun (i,j,_) =>
    let fi := flipPatternBits i negative
    let fj := flipPatternBits j negative
    forceNat (positive &&& fi) fun ci =>
      forceNat (positive &&& fj) fun cj =>
        forceNat (positive &&& flipPatternBits i fj) fun cij =>
          (gateSpecs i j).flatMap fun spec =>
            let (gate,samei,samej,sameij) := spec
            if redundant n (positive ||| negative) gate then []
            else ([0,1,2,3] : List Nat).filterMap fun keep =>
              if !(keepSize keep <= extra) || !(validKeep keep ci cj cij samei samej sameij) then none
              else
                forceNat (transitionSet n i j keep gate positive) fun p =>
                  forceNat (transitionSet n i j keep gate negative) fun q =>
                    if p &&& q == 0 then some (n-1+keepSize keep,p,q) else none

def nodeCheck (budget : Nat) (s : Key) : Bool :=
  if !(allowed budget s) then true
  else if solved s.1 s.2.1 s.2.2 then false
  else match budget with
  | 0 => true
  | k+1 => (children (k+1) s).all fun t => bankMember k t || !(allowed k t)

def root : Key := (6,249808489382150143,18196935584327401472)


def checkEntry (e : Nat × Key) : Bool :=
  (List.range (e.1+1)).all fun k => nodeCheck k e.2

def chunk0 : List (Nat × Key) := [(6,(5,56590335,4238376960)),(5,(6,3569243064191,17293836588019091584)),(7,(6,3707272591231,277766272485504)),(7,(6,3707845244799,277766272485504)),(7,(6,3708561620991,277766415089664)),(5,(6,3809694125951,17293836347568029824)),(5,(6,7932925642751,17293832224336513024)),(6,(6,7934154115071,17293832226881931264)),(5,(6,8207736964991,17293831949525190784)),(6,(6,21025010750463,14699785332472160256)),(7,(6,46909689395071,140741726734464)),(6,(6,75093529007103,14699899267626049536)),(7,(6,84439113627519,140741726734464)),(6,(6,88442087606271,17293999040866289664)),(7,(6,131387401142271,150087575568384)),(5,(6,844695631001471,17297201093591730304))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk0 : chunk0.all checkEntry = true := by
  decide +kernel

def chunk1 : List (Nat × Key) := [(5,(6,844936082585471,17297200853140146304)),(5,(6,847787897354111,17297213462971713664)),(5,(6,852151580456831,17297209099288610944)),(5,(6,1970561178089471,17296075228044642304)),(6,(6,1970562402840831,17296075230594760704)),(5,(6,1970835988889471,17296074953233842304)),(5,(6,1973653444444031,17296087597424623744)),(5,(6,1978051486758911,17296083199382308864)),(6,(6,2058315835601151,17296250325149712384)),(6,(6,5348158843604223,14708757347348545536)),(6,(6,5422872954621183,14708906054027083776)),(7,(6,9631718101221375,12288291489364049920)),(6,(6,18067657568616447,17330063024936976384)),(6,(6,18110383251324927,17330036637060562944)),(6,(6,19140625153859583,14738030330864787456)),(6,(6,19161270746619903,14738065102389436416))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk1 : chunk1.all checkEntry = true := by
  decide +kernel

def chunk2 : List (Nat × Key) := [(7,(6,21395479515135999,14735830897043472384)),(7,(6,21467191489822719,14735928064900890624)),(6,(6,22518479291103231,17338859115267016704)),(6,(6,22525724790372351,17338867395837609984)),(7,(6,32214566486114303,18052828643117268992)),(7,(6,32752787083231231,18196970768162619392)),(7,(6,32787970918449151,18196935584327401472)),(7,(6,35005136518479871,18194718418727370752)),(7,(6,86469697175781375,13441142624689881088)),(7,(6,96085622673899519,15891092575113707520)),(7,(6,105084679073267711,17618257666423947264)),(7,(6,146931403000020991,12150804155912454144)),(7,(6,146967501649313791,12150861879392108544)),(7,(6,176294570055696383,17908748639547686912)),(6,(6,216277237723265023,18158689619426672640)),(8,(6,216277237723267071,18158689621708406784))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk2 : chunk2.all checkEntry = true := by
  decide +kernel

def chunk3 : List (Nat × Key) := [(6,(6,216278113896575795,18158689621708374016)),(7,(6,216278332939927551,18158689621708406784)),(6,(6,219092030405834229,18158689621574189056)),(7,(6,220499426798436351,18158689621708406784)),(7,(6,225847567454306303,18196970768162619392)),(7,(6,225882751289524223,18196935584327401472)),(7,(6,228099916889554943,18194718418727370752)),(7,(6,230549700745363455,13297062621120299008)),(7,(6,230632680578842623,18158689621708406784)),(7,(6,235417862691356671,18196970768162619392)),(7,(6,235453046526574591,18196935584327401472)),(7,(6,237670212126605311,18194718418727370752)),(6,(6,238690782254497791,18203549696121667584)),(6,(6,238690846679007231,18203549696121667584)),(6,(6,238822103171694591,18203699777168769024)),(7,(6,240202975815892991,18158689621708406784))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk3 : chunk3.all checkEntry = true := by
  decide +kernel

def chunk4 : List (Nat × Key) := [(7,(6,247803465907011583,18194718418727370752)),(7,(6,249679481986351103,18196970768162619392)),(7,(6,249714665821569023,18196935584327401472)),(7,(6,249752195245801471,18196935584327401472)),(7,(6,249756748448006143,18196970768162619392)),(7,(6,249764474959921151,8358716095061852160)),(7,(6,249791932283224063,18196935584327401472)),(7,(6,249808489346358749,18196935583790530560)),(9,(6,249808489382150143,18196935584327401472)),(7,(6,251931831421599743,18194718418727370752)),(7,(6,251941215925141503,18194577681239015424)),(7,(6,252009097883254783,18194718418727370752)),(7,(6,252024559765520383,18194718418727370752)),(7,(6,252025654947968501,18194718418593153024)),(7,(6,252025654973857791,18194718418718982144)),(7,(6,252025654974840591,18194718418718982144))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk4 : chunk4.all checkEntry = true := by
  decide +kernel

def chunk5 : List (Nat × Key) := [(7,(6,252025654977199923,18194718418718982144)),(7,(6,252025654979428181,18194718418718982144)),(7,(6,252025654981654391,18194718416437248000)),(7,(6,252025654982161203,18194718418727337984)),(6,(6,288233912055632895,14411572445427277824)),(6,(6,288305469413856255,14411668891741200384)),(6,(6,289075038447160575,14425030467744989184)),(6,(6,289149649480535295,14425179277501169664)),(6,(6,307371001037142015,14449799954981505024)),(6,(6,307374054712293375,14449852318423762944)),(7,(6,316983627957141503,16899977507791437824)),(7,(6,320974915698163711,17908748639547686912)),(7,(6,369989692499656703,18052828643117268992)),(7,(6,379559987736707071,18052828643117268992)),(7,(6,380281279712591871,14594134498577743872)),(7,(6,393791254497820671,18052687905628913664))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk5 : chunk5.all checkEntry = true := by
  decide +kernel

def chunk6 : List (Nat × Key) := [(7,(6,393821607031701503,18052828643117268992)),(7,(6,393859136455933951,18052828643117268992)),(7,(6,393914335375622143,18052828643117268992)),(7,(6,393915430520699835,18052828642043527168)),(7,(6,393915430592253711,18052828643117236224)),(6,(6,504403394494429183,17870284180410632192)),(6,(6,504403394496518143,17870284180408543232)),(6,(6,504403531931285503,17870284042973775872)),(6,(6,504403531935463423,17870284042969597952)),(6,(6,504403669370230783,17870283905534830592)),(6,(6,504403669372319743,17870283905532741632)),(7,(6,514069696069238783,17908748639547686912)),(7,(6,523639991306289151,17908748639547686912)),(7,(6,537901610601283583,17908748639547686912)),(7,(6,537994338945204223,17908748639547686912)),(7,(6,537995434090281915,17908748638473945088))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk6 : chunk6.all checkEntry = true := by
  decide +kernel

def chunk7 : List (Nat × Key) := [(7,(6,1076060067317889023,16140901068430690304)),(6,(6,1152924937635235839,16140915223400810496)),(6,(6,1152940129049706495,16195190553455886336)),(6,(6,1153009946625771519,16141077536328124416)),(6,(6,1153017488820207615,16195129531491680256)),(6,(6,1153766064023630079,16144279728973971456)),(6,(6,1153853920534032639,16144454720451280896)),(6,(6,1175439983830835199,16185937610727284736)),(6,(6,1175442831350702079,16185950289277280256)),(7,(6,1185065701811945471,16899977507791437824)),(6,(6,1513209607944101887,16861477966960959488)),(6,(6,1513209607944108031,16861477966960953344)),(6,(6,1513209607946713087,16861477966958348288)),(6,(6,1513209607948285951,16861477966956775424)),(6,(6,1513209711021744127,16861477863883317248)),(6,(6,1513209711021750271,16861477863883311104))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk7 : chunk7.all checkEntry = true := by
  decide +kernel

def chunk8 : List (Nat × Key) := [(6,(6,1513209711025922047,16861477863879139328)),(6,(6,1513209711027494911,16861477863877566464)),(6,(6,1513209882820425727,16861477692084635648)),(6,(6,1513209882821992447,16861477692083068928)),(6,(6,1513209985899640831,16861477589005420544)),(6,(6,1513209985901207551,16861477589003853824)),(7,(6,1522840827825487871,16899977507791437824)),(7,(6,1532411123062538239,16899977507791437824)),(7,(6,1546710271781765119,16899977507791437824)),(7,(6,1546765470701453311,16899977507791437824)),(7,(6,1546766565560221695,16899977506717696000)),(7,(6,1546766565646520271,16899977507254566912)),(7,(6,1944142141172692991,16140901068430690304)),(7,(6,2281917267186235391,16140901068430690304)),(7,(6,2291487562423285759,16140901068430690304)),(7,(6,2305786711142512639,16140901068430690304))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk8 : chunk8.all checkEntry = true := by
  decide +kernel

def chunk9 : List (Nat × Key) := [(7,(6,2305841910062200831,16140901068430690304)),(7,(6,3673524397848090623,14411518811755292672)),(7,(6,3818204743490557951,14411518811755292672)),(7,(6,4011299523861633023,14411518811755292672)),(7,(6,4020869819098683391,14411518811755292672)),(7,(6,4035131438393677823,14411518811755292672)),(7,(6,4035224166737598463,14411518811755292672)),(7,(6,4249844412629612543,13835198796973770752)),(7,(6,4587619538643154943,13835198796973770752)),(7,(6,4597189833880205311,13835198796973770752)),(7,(6,4611451453175199743,13835198796973770752)),(7,(6,4611488982599432191,13835198796973770752)),(7,(6,4611544181519120383,13835198796973770752)),(7,(6,6664479707921612671,11565243847324237952)),(7,(6,6857574488292687743,11565243847324237952)),(7,(6,6867144783529738111,11565243847324237952))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk9 : chunk9.all checkEntry = true := by
  decide +kernel

def chunk10 : List (Nat × Key) := [(7,(6,6881406402824732543,11565243847324237952)),(7,(6,6881443932248964991,11565243847324237952)),(7,(6,6881483669286387583,11565243847324237952)),(7,(6,8393721227344044031,9836002327901806592)),(8,(6,8574993328548831231,9799973530882842624)),(7,(6,8586816007715119103,9836002327901806592)),(7,(6,8596386302952169471,9836002327901806592)),(7,(6,8606519556732575743,9836002327901806592)),(7,(6,8610647922247163903,9836002327901806592)),(7,(6,8610725188708818943,9836002327901806592)),(7,(6,8610740650591084543,9836002327901806592)),(7,(6,8970322717135298431,9259400838110552192)),(7,(6,9163417497506373503,9259400838110552192)),(7,(6,9172987792743423871,9259400838110552192)),(7,(6,9187249412038418303,9259400838110552192)),(7,(6,9187326678500073343,9259400838110552192))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk10 : chunk10.all checkEntry = true := by
  decide +kernel

def chunk11 : List (Nat × Key) := [(6,(7,146395858778048718831615,3448009633678603864067207593984000)),(6,(7,146395858801357150683135,52613509489520727641651937280)),(6,(7,228740394940728167759871,3257862043495616639024976199942144)),(6,(7,228740394964139677253631,49711938769630789485602013184)),(7,(7,606824342857238792077183,170808403787764582678768919260002516992)),(6,(7,12139619320746262853419007,225968759283629882108034697183509905408)),(6,(7,12288372374249718218588159,213507246826047569013245327123454918656)),(6,(7,12288372712035152074997759,225968759283629733354643408294288326656)),(6,(7,41267174581191685644091391,181481159810032427852777207981976584192)),(6,(7,41267174581192235399872511,181481159810032427852777207432220803072)),(6,(7,41267175787051050159439871,225968759283600754551568392396203884544)),(6,(7,41267176507873281158616575,225968759283600754563097361151663554560)),(6,(7,41267178813575552900731391,180777765845141559601323937721743310848)),(6,(7,82567257692738991649062911,181481159820554882766648440602694254592)),(7,(7,82567263335440113106632511,63299962750680276180918075392)),(7,(7,82567264420261234541330431,63299962750680276180918075392))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk11 : chunk11.all checkEntry = true := by
  decide +kernel

def chunk12 : List (Nat × Key) := [(7,(7,82567265641283122320318271,63299962748374433171704389632)),(6,(7,96945166381786876967485439,213507246847711819565967042755017342976)),(6,(7,97245037010945229133414399,319014718988573844452865870931257491456)),(7,(7,135779552648798717171154751,74431902811113390440442232832)),(7,(7,135779556337866059563925503,74431902811113390440442232832)),(7,(7,135930668376250545281122111,74431751695385938612332265472)),(7,(7,135930669759474878997069823,74431751697691781621009088512)),(6,(7,621551567996205443165847551,181481159809452143459362194224454828032)),(6,(7,660086078496421748109606911,181481159809413608948861977919511068672)),(7,(7,660086082152493846955513343,52158688933434202022846922752)),(7,(7,660086082223989590540550143,52158688933434202022846922752)),(6,(7,660121495956891509378383871,181481159809413573531401508158242291712)),(7,(7,660121505124729086524391423,52158653510533462526863081472)),(7,(7,928903656594793903970803551,212679724539595744844700249099237064704)),(7,(7,928903659201216316137766911,271162511154978874132274324325391171584)),(7,(7,928903662381883552227622911,319014718992094385202666495269222252544))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk12 : chunk12.all checkEntry = true := by
  decide +kernel

def chunk13 : List (Nat × Key) := [(7,(7,928903662382007728329396223,77990978062875758033383718912)),(7,(7,928903662854901150968119551,77990978063416189988533960704)),(7,(7,928903662890508835033677823,77990978063452078048064602112)),(7,(7,1072317202730761615918333823,78154636398011790729492332672)),(7,(7,1072317205036604625132019583,78154636395705947720278646912)),(7,(7,1072317207496170499944447871,78154636395705947720815509632)),(7,(7,1072317207794573712225697663,78154636398011790729492332672)),(7,(7,1072317210100416721439383423,78154636395705947720278646912)),(6,(7,1320169647765613825695547391,181481159819317280376575565768647770112)),(6,(7,1320169647774585840578199551,181481159819317280376566593753765117952)),(7,(7,1320169648389511908009932663,62062360360562392289471627264)),(7,(7,1320169649854963365051315199,62062360365174078306825273344)),(7,(7,1320169649926459108634132479,62062360365174078306825273344)),(6,(7,1320205065379127359213535231,181481159819317244958962052235129782272)),(6,(7,1320207426562368794036109311,181481159819317242597778810800307208192)),(7,(7,1485528032889559887551869951,61897001982139481784324718592))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk13 : chunk13.all checkEntry = true := by
  decide +kernel

def chunk14 : List (Nat × Key) := [(6,(7,1547722558198007240922071039,225968759308195405873764694001039998976)),(6,(7,1547722558217787755748884479,319014718991475566289537033409929445376)),(7,(7,1547987011640383295028933631,77371894711013136245723758592)),(7,(7,1547987013792503437031069183,77371894706401450228370112512)),(7,(7,1547987015329591374862843903,77371894711012995508235436032)),(7,(7,1691287222563062679034099711,77535666380639055541725857792)),(7,(7,1691287224715182821038454783,77535666376027369524372211712)),(7,(7,1691287226180634277796870143,77535666380639055541725857792)),(7,(7,2166805914979301589016589311,76753075807674217951736102912)),(7,(7,2166805917131421731018724863,76753075803062531934382456832)),(7,(7,2166805918668368931362177023,76753075807674217951736102912)),(7,(7,2310257243781552943672940543,76916696356960999401737725952)),(7,(7,2310257245247004400431355903,76916696361572685419091372032)),(7,(7,3146430921135513788669591423,49672344094522677824717881472)),(8,(7,3146430921135653972107154773,49672344094522819111962017792)),(6,(7,3300367672015431641995804671,3257911560235344642097876717010944))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk14 : chunk14.all checkEntry = true := by
  decide +kernel

def chunk15 : List (Nat × Key) := [(6,(7,3300468225217377432404426751,49517903814444577351756939264)),(7,(7,3301173426103893966405990263,49517601585865230304352927744)),(7,(7,3301173427309787965554120191,49517601588276907904248315904)),(7,(7,3960803648406433119058998271,59421726366622608552817590272)),(7,(7,3960803648439797799399421951,59421726366660739616059983872)),(7,(7,3961408112469091568972149759,59421121902559950102904438784)),(6,(7,6499331599618823664971415551,225968759303243796832343877576990654464)),(7,(7,6499444937173418607608550911,72420436783020535057792630784)),(7,(7,6499444937327141474283238399,72420436785326378066469453824)),(7,(7,6499444938710365807952003071,72420436787632221075146276864)),(6,(7,6499482715339493705898098687,225968759303243645716623207536063971328)),(6,(7,9595239507924437152762369535,225968759352760340593666925772423577600)),(7,(7,9595239508222204839087518719,69324642214431314701665173504)),(7,(7,9902311388770803519094783999,69324642214431314701665173504)),(7,(7,9902311389976697517962166271,69324642216842992301560561664)),(7,(7,9942360007933491192142978911,212679724550892552163458908502406201344))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk15 : chunk15.all checkEntry = true := by
  decide +kernel

def chunk16 : List (Nat × Key) := [(6,(7,10728008350449551887685779455,3448051722584628432440695466229760)),(6,(7,10728108460929639909066735615,42090263579407870280925184000)),(7,(7,10728813662013298482789963263,42089961353573397387012472832)),(7,(7,10728813662046698347504687103,42089961353611493265882785792)),(7,(7,13049951235418555987862577023,39768823780239635625524895872)),(7,(7,13204089277530171714297091583,39614685738056524155505344512)),(7,(7,13204089277563536394639734783,39614685738094655218747738112)),(7,(7,17022879743780798805944784383,61897001976413154859456397312)),(7,(7,17022879744165009219903248383,61897001982177577663195031552)),(7,(7,17329951624329397485954269183,61897001976413154859456397312)),(7,(7,17329951624680208035198009343,61897001982139481784324718592)),(6,(7,19498155359297672037384786431,180777765893876381693191716328437710848)),(7,(7,19498155359681847267038296063,59421726366660739616059983872)),(7,(7,19805831703106888581292457983,59421121903712801238230269952)),(7,(7,21136859030358453727140216831,271162511182367541916449182613803925504)),(7,(7,23613706234642847124950564671,39768823779372869169074143232))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk16 : chunk16.all checkEntry = true := by
  decide +kernel

def chunk17 : List (Nat × Key) := [(7,(7,23613706234642882308785782591,39768823779372833985238925312)),(7,(7,23613706234860901789397647231,39768823780239635626061758592)),(8,(7,23613706234861041972835201843,39768823780239776913305894912)),(7,(7,24895338272698134558666604351,49672344091064054598946783232)),(7,(7,24895338272928578675288276863,49672344094522677824717881472)),(8,(7,24895338272928718858725822223,49672344094522819111962017792)),(8,(7,29402280136730721776171942143,49517601589612146577608015872)),(7,(7,29554609512138063621813174271,49672344091064054598946783232)),(7,(7,29554609512150488257822982143,49672344093655876183895048192)),(8,(7,29554609512368647921821876223,49672344094522819111962017792)),(7,(7,34797720792003763400579448831,319014719028148633259821402848866893824)),(7,(7,34798254124268422491135741711,39769428243111338265274220544)),(7,(7,34798254124268422491143081983,39769428243111338265282609152)),(7,(7,34798858586981176757859589951,39768823776781012399753797632)),(7,(7,34798858587211620874481262463,39768823780239635625524895872)),(7,(7,36829315909499664858917830911,42090565816771426280584249344))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk17 : chunk17.all checkEntry = true := by
  decide +kernel

def chunk18 : List (Nat × Key) := [(7,(7,36982249748047398319155085311,42244703858772291500350930944)),(7,(7,36982249748047398319163408383,42244703858772291500359319552)),(7,(7,39458129826433495272643887103,39768823779372869169074143232)),(7,(7,39458129826555578146046214143,39768823774186974199364452352)),(6,(7,792281675503767906728563212287,225968771959942456259190160654451376128)),(6,(7,792281824256821431074330542079,213507449647048755431735904805708660736)),(6,(7,792281824257159195892658503679,225968771959942307505798871490356084736)),(6,(7,792378362912278727346887884799,213507449671806949387585995318491119616)),(6,(7,793829051759723393905309286399,225968771984700501461648962003138543616)),(6,(7,798780810736273259652878204927,225968771979748742485099096255569625088)),(6,(7,2693757689181701760126355832831,181481849401436461675645695791036628992)),(6,(7,2693757689181701760126364188671,181481849401436461675645695791028273152)),(6,(7,2693757689182907597844566310911,225968770058466442580050469538448277504)),(6,(7,2695077677515967823475727204351,181481849421242935615622281754964918272)),(6,(7,2695077677515967823475735560191,181481849421242935615622281754956562432)),(6,(7,2700256711078617388285675241471,225968770078272842142754967622772588544))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk18 : chunk18.all checkEntry = true := by
  decide +kernel

def chunk19 : List (Nat × Key) := [(6,(7,5387515411271933890565931466751,181482539003362950412385645465490685952)),(6,(7,5388175129503445759902557601791,181482539013265939458133645515441569792)),(6,(7,6338253232241959583186286182399,213508869415721310913893211752049442816)),(6,(7,6338253532112588713174920888319,319014731664886418604021334127325249536)),(6,(7,6338265114103409342300094627839,213508869418815254317021586633269477376)),(6,(7,6339800426466955017560178851839,319014731667980661877421301412027990016)),(7,(7,10775071366605773901553188470783,181483918217737882238113053252647911424)),(7,(7,10776350269078823223950756020223,181483918227022734762046510781803003904)),(6,(7,40723275696028583805027326164991,181481811371918454828763650890066296832)),(6,(7,40724595684362849868376697536511,181481811391724928768740236853994586112)),(6,(7,43258576745369315156192085737471,181481808836617405488032299725306724352)),(6,(7,43258576780786775547339472699391,181481808836617370070571908577919762432)),(6,(7,43258658944780023264158369513471,181481808857661668351566841072322609152)),(6,(7,43259896884819308636185731858431,181481808856423728312281469044960264192)),(6,(7,86517153488229403053976460132351,181482457873724873454916482054962020352)),(6,(7,86517153488229412061175178002431,181482457873724873454907474856244150272))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk19 : chunk19.all checkEntry = true := by
  decide +kernel

def chunk20 : List (Nat × Key) := [(6,(7,86517153523647016567509978120191,181482457873724838037302968521444032512)),(6,(7,86517153526008199808944800694271,181482457873724835676119727086621458432)),(6,(7,86517194574090484695185780047871,181482457884246494871094710232219123712)),(6,(7,86517194574090484695735535828991,181482457884246494871094709682463342592)),(6,(7,86517774858483899708943301804031,181482457883666210477679696474697367552)),(6,(7,86517813544110127377076355530751,181482457883627524851452028341643640832)),(6,(7,101412048315767443355639451647999,225970381876204897221690862998072098816)),(6,(7,101412048315767463058588352675839,319014921812476752708027680910106198016)),(6,(7,101412060109084521581563255357439,225970381876397418658419667804102885376)),(6,(7,101412144732600622520446995169279,319014921812669274144756485716136984576)),(7,(7,162893102129327727891985291280383,181483766089143364520406065831783432192)),(8,(7,162895588325563454433864600483703,181483766128912188282448907160761925632)),(7,(7,202824096237992259278770842588501,3245185537188748336152574641045504)),(7,(7,202825024892947319365510168008021,3245263526806742246929618629033984)),(6,(7,216292883664126109094567709048831,3245235247661193486282292549648384)),(6,(7,216292883764679311016946608177151,3245185536886510296997258187505664))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk20 : chunk20.all checkEntry = true := by
  decide +kernel

def chunk21 : List (Nat × Key) := [(7,(7,243389844090806218822077230838771,15950736023696148411182221115005108224)),(7,(7,243390167747859140830555784049651,15950735951894870570710443766281437184)),(6,(7,425930601823078449442091262738431,225970057357651389910684776546261008384)),(6,(7,425930601974194170138520065835007,225970057357651238794964080117457911808)),(6,(7,425930613766330656744001336147967,225970057357843761412284505366022094848)),(6,(7,425930642780550327459917559693311,225970057357814747192613789449798549504)),(7,(7,689601967630770968185558859218943,225971517691306208938057054167849009152)),(7,(7,689601967630772121036694185050111,225971517691306208936904203032523177984)),(6,(7,689601967630772841869919832179967,45193751898942157183882530301180657664)),(6,(7,689601967630775147572191574294783,2758460482962222109106871260413952)),(7,(7,689603474350607061754350437105663,225971517715900595806570743171869868032)),(7,(7,689608425808532748371792203087871,225971517710949137880884125730103885824)),(6,(7,689611521763664718813975977854207,45193751926011781888548998364528656384)),(6,(7,689621424679516092048860600271103,2758467127822988073788920542789632)),(6,(7,703070714152208921127070476599295,2758460318550805563582906388971520)),(6,(7,703070714252319401191783425703935,2758407706398870882352057789972480))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk21 : chunk21.all checkEntry = true := by
  decide +kernel

def chunk22 : List (Nat × Key) := [(7,(7,703070714252319410761786621689855,2758407706398870920632070507069440)),(7,(7,703070755255059598725956308566015,2758460482962208273978449649991680)),(8,(7,855188786984907758327213215143253,2606289634069257846271518873485312)),(7,(7,855191932609890395592325630088533,2606339306413334172155046508101632)),(7,(7,1298075143235134361908400499932991,255214371357702366725612918345620783104)),(7,(7,1298094099351361374525967078211391,255214371378902543240621360294494470144)),(7,(7,1541463130240190156902795722044211,2596148429871894882621446971981824)),(7,(7,1541464058422281379514161593004851,2596226419641004520815135234719744)),(7,(7,1541464058422286279429678857925631,271165107303407537083142894199446175744)),(7,(7,1541484175217094872576431117775871,271165107330642671288262441904713498624)),(8,(7,1541486651701636386675547028009983,271165107328166186746820120003081142272)),(8,(7,1547484471195737189898144890958643,2606289634069257846271518873485312)),(7,(7,1547508083934845902835183971939123,2606329402893019889112847851978752)),(7,(7,1622592768825466114764147452219151,3245185537188748336152574641045504)),(7,(7,1622593696817998595318209054707471,3245263526806742246929618629033984)),(7,(7,1622593696818006665767708631437311,319017964177630213891261179626671570944))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk22 : chunk22.all checkEntry = true := by
  decide +kernel

def chunk23 : List (Nat × Key) := [(7,(7,1622627431142138886834152456261631,319017964213531079485088193267445530624)),(7,(7,1926828912946649449772217932906751,3245185537188748336152574641045504)),(7,(7,1926829840801938154449835028054271,3245263526806742246929618629033984)),(8,(7,2271654635543141000661647715405823,319017315186326678483046142986464264192)),(8,(7,2280503430948380117443837253586703,2606289634069257846271518873485312)),(7,(7,2280528325148857621887801453645583,2606339306413334172155046508101632)),(8,(7,2575866020867965846641911848173823,2596148429267432011060095003656192)),(8,(7,2585927996303073964383986939592703,2606289634069257846271518873485312)),(8,(7,21013530815717419430169513504797683,15992274324287269113203921350056476672)),(7,(7,21013550701039536591163302108934963,15992274364056092875246762679034970112)),(7,(7,22316675633662275394410604892730163,15994880613921338352853257284602560512)),(7,(7,166153499511800110581445306250952703,213341093373151341684018608443869888512)),(8,(7,166805071921075950610090226649882463,213343699662785410923667944378415972352)),(7,(7,166805075028062715151956639023977813,213343699662785410923667944378415972352)),(7,(7,166805096776970066945021525642645263,213343699662785410923667944378415972352)),(7,(7,167008688298785018089964030083945813,213343699662785410923667944378415972352))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk23 : chunk23.all checkEntry = true := by
  decide +kernel

def chunk24 : List (Nat × Key) := [(7,(7,168434002942748490449080654122389263,213343699662785410923667944378415972352)),(7,(7,176538093190347836161160318038278143,226674911656197077198733625546437066752)),(7,(7,176538094840367883144043813280907263,226674911680955235736835102783217631232)),(8,(7,176541420823787759082760919783440213,706162514120280906384686446492516352)),(7,(7,177230388874236289985984721158373375,45193751898942157168894550743439147008)),(7,(7,177230389204351123731581649146576895,45193751861638899845709224071921696768)),(8,(7,250207612832463846792179070496919503,63802943807579482228403952162619523072)),(7,(7,250207632717785963953172859101056783,63802943847348305990446793491598016512)),(7,(7,251510757650408702756420161884851983,63805550097213551468053288097165606912)),(7,(7,333610143768156181101400812286902271,255878995481953866301504193884200108032)),(7,(7,333610143768156181101435996122120191,255878995481953866301504158700364890112)),(7,(7,333610143821368470700773176458084351,255878995493085806361651294383617605632)),(7,(7,333610143821519586428225004568051711,255878995493085655245923842555507638272)),(8,(7,333610163648585705443407611819933503,255878995517999198540000885099517181952)),(7,(7,353076186380368278970741941352792063,271868663512883574633315693601721679872)),(7,(7,353076186380728580775849452877381631,271868663512884181457408601063887470592))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk24 : chunk24.all checkEntry = true := by
  decide +kernel

def chunk25 : List (Nat × Key) := [(7,(7,353076187370478525004538935374774271,271868663527738855101281492386690629632)),(8,(7,353076209993107387683678980433772543,271868663552652398395358534930700173312)),(7,(7,353076209994074513581975424805843763,271868663552652398395358534930700173312)),(7,(7,353076215934977791089581373792518143,271868663562555918709641577129356296192)),(8,(7,353082207812601488486901578296721203,706162514120280906384686446492516352)),(7,(7,353320549646358268659527544554648563,271868663552652398395358534930700173312)),(8,(7,354460798875977561419143260724247483,90387503713374279370755899288811732992)),(7,(7,354460801361529046546820843785403323,271868663552652398395358534930700173312)),(8,(7,354623670850596890012535152489529343,271871269802517643872965029536267763712)),(7,(7,354623670851564015910831596861600563,271871269802517643872965029536267763712)),(7,(7,354623674578981007462774847338443763,271871269802517643872965029536267763712)),(7,(7,354623691978106888897226756633377723,271871269802517643872965029536267763712)),(7,(7,354623691978751639496091052881425203,90390110003008348610405235223357816832)),(7,(7,354623694463335998725472191570509823,271871269842286467635007870865246257152)),(7,(7,354623694463696300530719886532654003,101062866054521884974435887189571141632)),(7,(7,355662114376671352685317438910234623,271871269802517643872965029536267763712))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk25 : chunk25.all checkEntry = true := by
  decide +kernel

def chunk26 : List (Nat × Key) := [(6,(7,415383748683017311096417809795678207,830767571642881472052407428427317248)),(6,(7,415383748683017311096422761817407487,835635275671355515831348719989587968)),(6,(7,415383748683317181725552750452113407,106341497524836463205959471095265394688)),(6,(7,415383748683317181725576161961607167,106338239712504906358951235604667465728)),(6,(7,415383748700922440313210312505458687,830767497365574799042154523000864768)),(6,(7,415383748700943709409127299542908927,835635275670496045131666555676950528)),(6,(7,415383750236256072954802559627132927,106341497524835903605531381334435463168)),(6,(7,415383750236356626156748350035755007,106338239662793572075333860809475391488)),(6,(7,415384937105226266984006468989124607,830767497365574799041954414938062848)),(6,(7,415384937105247536079918504004845567,830767571642022001352525156051877888)),(6,(7,415485556871617224423711604112130047,106338239712504346758523015553697742848)),(6,(7,415485556871717777625633983011258367,106338239662793572075333730519335600128)),(8,(7,417012704559973601625496455666970543,106338239662793269844736892883720732672)),(7,(7,417664276969249441654141376065900303,106340845952427339084386228818266816512)),(7,(7,581537248156280549967524525049380863,319679332986273025374053041505904361472)),(7,(7,581537248156431665694976353159348223,319679332986272874258325589677794394112))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk26 : chunk26.all checkEntry = true := by
  decide +kernel

def chunk27 : List (Nat × Key) := [(7,(7,581537249092818204596841643375591423,319679332989995758957778832329290022912)),(7,(7,581537249092818204596876827210809343,319679332989995758957778797145454804992)),(8,(7,581537273050101172118142845063266303,319679333035944611510558565743263219712)),(7,(7,581537273051238967292609250206879503,319679333035944611510558565743263219712)),(7,(7,581537277710510206732538313302933503,319679333035944611510558565743263219712)),(8,(7,581546121845506411234925034601447183,664624139252002285358694275672440832)),(7,(7,581546146604307196942530531241754383,319679343177149413336393777167133048832)),(7,(7,582195158953578843325715305504661263,213343699662785410923667944378415972352)),(7,(7,582514631663104696021537101546770383,319679333035944611510558565743263219712)),(7,(7,583166204071773711957133272535773103,319679333035944611510558565743263219712)),(8,(7,583817751585711279306867823591030783,319681939275906336673882018150174687232)),(7,(7,583817751586849074481334228734643983,319681939275906336673882018150174687232)),(7,(7,583817751625155435650846893941940063,319681939325578680750207901677809303552)),(7,(7,583817751721115398322283981443170063,319681939276061079178792690684528689152)),(7,(7,583817751722248766278172696294395663,667220287681269699172818786348695552)),(7,(7,583817756595727434824784404330565583,319681939285809856988165060348830810112))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk27 : chunk27.all checkEntry = true := by
  decide +kernel

def chunk28 : List (Nat × Key) := [(7,(7,583817776441605395641799122583793583,319681939275906336673882018150174687232)),(7,(7,583817776479911756811311787791089663,319681939325578680750207901677809303552)),(7,(7,584123176152203768328274378420649983,319681939275906336673882018150174687232)),(7,(7,602306464212567710322655305065037823,335671607360231880605565551508992294912)),(7,(7,604831278673044581036989152864763903,335674213600193605768889003915903762432)),(8,(7,604831307296766971166139217057350403,335674213649865949845214887443538378752)),(8,(7,617883326319178067102499935510134783,706152372915479080549475022622687232)),(7,(7,617883349840038813524725157318426623,271868663552652398395358534930700173312)),(7,(7,617883351077978852810105432150441983,319720871410812890131584557914083295232)),(8,(7,617893388142283799582315864951619583,706162513965538401474013912138514432)),(7,(7,619434851272161326534452293165645823,271871269802517643872965029536267763712)),(7,(7,620165018017892786669674811793342463,319723477650774615294908010320994762752)),(7,(7,620469254161947561726017527888216063,708758662394805815288138422814769152)),(8,(7,1330952026907853501032874773518985983,111655151645932933336063890748690399232)),(8,(7,1770573255169360750964299090612649983,111655151645932933336063890748690399232)),(7,(7,1770573257654912236091976673673805823,293136311485211052360666526390578839552))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk28 : chunk28.all checkEntry = true := by
  decide +kernel

def chunk29 : List (Nat × Key) := [(8,(7,1772303967970500325937361914622377983,111655151645932933336063890748690399232)),(7,(7,1773159156756679295197300268145311743,111657757935567002575713226683236483072)),(7,(7,1936726754681160861295935907481452543,324996245019084275001885563608232886272)),(7,(7,1939109039852132119953664581539201023,324998851259046000165209016015144353792)),(7,(7,2658455991879765382906611953323835391,223310303317863363061305692629390884864)),(7,(7,2658456002143096964229322931615137791,223310303334110570494506201829076926464)),(7,(7,2658496556430145663322233367244570623,223313710736843694045703006359463657472)),(7,(7,2658496557936865499415802158822457343,223313710761438080914216695363484516352)),(7,(7,2658658815975754673631183559521039861,10633824041794424958852373148782854144)),(7,(7,2658658815975754675934246959853819391,223313548503399191749900376986840203264)),(7,(7,2658658816296974948555110510314747381,10633823968755207079383445901311770624)),(7,(7,2658658826188556935902017508775777791,223313548519493016719772992247655563264)),(8,(7,2659307855868838016586605553698952703,223312899489812735639160181417010266112)),(8,(7,2669044204771549825059276246832510453,10675362341147605621876923485086810112)),(7,(7,2669044204810993981403255317183419733,10675362390819949698202807012721426432)),(7,(7,2669695777180825665087921167231440213,10677968630781674861526259419632893952))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk29 : chunk29.all checkEntry = true := by
  decide +kernel

def chunk30 : List (Nat × Key) := [(7,(7,2834994084760028466241322609817944063,224016455664627396568653463254657400832)),(7,(7,2834994084760063883701713757204905983,224016455664627361151193072107270438912)),(7,(7,2834994084760214999429165585314873343,224016455664627210035465620279160471552)),(7,(7,2834994085172259589666250721972977663,224016455690623344030312895874525560832)),(7,(7,2834994085172259589666285905808195583,224016455690623344030312860690690342912)),(7,(7,2834994086410199628951622749335322623,224016455689385403991027523847163215872)),(8,(7,2834994087905640867911039260267249663,224016455714298947287698596344629297152)),(7,(7,2834994087906446806159619630577309013,224016455714298947287698596344629297152)),(7,(7,2834994114314625397392613580292030463,224016455714298947287698596344629297152)),(7,(7,2835197704283349935390913063701313013,224016455714298947287698596344629297152)),(7,(7,2835645660314916707939684180666179423,224019062003933016527347932279175380992)),(8,(7,2835686381104300212214932608881909213,42535295875020828263095960702740856832)),(7,(7,2835686381104907036307981358291836253,213343699662785410923667944378415972352)),(7,(7,2835686383589851697342610191943065053,224016455714298947287698596344629297152)),(7,(7,2835686383590496447941474488191112533,42535295914789652025138802031719350272)),(8,(7,2835849273546194854533712501375238143,224019061954260672451022048751540764672))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk30 : chunk30.all checkEntry = true := by
  decide +kernel

def chunk31 : List (Nat × Key) := [(7,(7,2835849274207074290291880401039086933,42537902164654897502745296637286940672)),(7,(7,3188070295413196770217232168257716223,314403959427673226640257560049113628672)),(8,(7,3190310075568603336588892755442340113,314406565717307295879906895983659712512)),(8,(7,3252861981252599376795245950385063173,330357301666726286353887889578568712192)),(7,(7,3276339320983859910979449555075006463,224016455714298947287698596344629297152)),(7,(7,3987683987355196244035919081938911231,15950736023696148411182221115005108224)),(7,(7,3987683987355196252102147487658115071,334965454937799555560196471123047645184)),(7,(7,3987683989539276574755160555026153471,15950735951894870570710443766281437184)),(8,(7,3987684016755823551772838415369764863,334965454987316401543213012070697009152)),(7,(7,3987684016909357130863896320549126143,334965454987471144048123684605051011072)),(7,(7,3987684024183463787451588812702973951,334965454979888761307462484459085922304)),(7,(7,3987988223499180183590829614054732031,15950736023696148411182221115005108224)),(7,(7,3987988225665268298014526878179619071,15950735951894870570710443766281437184)),(8,(7,3987988228141148376618818679502532863,15950735949418990492177929179236401152)),(8,(7,3988718396124989881232804780189928703,63802943807579482228403952162619523072)),(7,(7,3989306580123110596453305194272263951,334968700123335384248863213074518114304))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk31 : chunk31.all checkEntry = true := by
  decide +kernel

def chunk32 : List (Nat × Key) := [(7,(7,3989306617105822832441133627611287311,334968700165580692542550619946372562944)),(7,(7,3989610816267094535508018264640786191,334968700123335384248286752322348908544)),(7,(7,3989610816267094536012298277485576191,334968700123335384248863072337029791744)),(7,(7,3989610851065348651453841425130524431,334968700163104812463979859396708532224)),(7,(7,3989610851083482815449221968394391311,334968700163104812463979859396708532224)),(7,(7,3989610853249344275232817253149868031,334968700165580088079640812631785242624)),(7,(7,3989610853249348979152556049085530111,334968700165580088079640812631785242624)),(8,(7,3990259853374411380888758551045996543,334968051086228067385611925588092649472)),(8,(7,4024030070024900446757195505816633343,15992274324287269113203921350056476672)),(7,(7,4024030094783701232464801002456940543,335006993362184680164239004241517084672)),(7,(7,4024030094919100924261639470016692223,15992274373959613189529804877691092992)),(8,(7,4024335489930983901164206592406585343,15992274324287269113203921350056476672)),(7,(7,4026615993360794485857375535134408703,15994880613921338352853257284602560512)),(7,(7,4164222109996782575557119566689992703,335671607360231880605565551508992294912)),(8,(7,4166801303600479276202624268237078613,335674213649865949845214887443538378752)),(7,(7,4190183569536700557088832322685435903,229333367697438610779025594209598963712))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk32 : chunk32.all checkEntry = true := by
  decide +kernel

def chunk33 : List (Nat × Key) := [(8,(7,4252491133081894231191659370446127103,63802943807579482228403952162619523072)),(7,(7,4252491135567445716319336953507282943,245284103646857601253006587804507963392)),(7,(7,4252491156694633339904596409527107583,63802943847348305990446793491598016512)),(8,(7,4253529570666098290458539263508086783,63802943797675961914120909963963400192)),(7,(7,4255077055136326901500332474644824063,63805550087310031153770245898509484032)),(7,(7,4340760203228070192784483684613095423,335671607360231880605565551508992294912)),(8,(7,4343342090589293005606764926750359603,335674213649865949845214887443538378752)),(7,(7,4356337088855541295986553536866484223,271868663552652398395358534930700173312)),(7,(7,4357945633694247489196811926240231423,271871269802517643872965029536267763712)),(7,(7,4439413843563201508293893044628946943,122330513987080538939743878649449807872)),(7,(7,4441348169635063386204963259698642943,122330513987080538939743878649449807872)),(7,(7,4569221265047123937933567274410573823,335630068985363601984539559338172219392)),(8,(7,4571806004622197928354788383055085583,335632675274997671224188895272718303232)),(7,(7,4584798151912535080421017401495977983,319679333035944611510558565743263219712)),(7,(7,4587139714429361878491144597341732863,319681939275906336673882018150174687232)),(8,(7,4605567313520392106506690429058023423,335671607310559536529239667981357678592))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk33 : chunk33.all checkEntry = true := by
  decide +kernel

def chunk34 : List (Nat × Key) := [(7,(7,4605567313673925685597748334237384703,335671607310714279034150340515711680512)),(7,(7,4605567316666017089143955541472968703,335671607360231880605565551508992294912)),(7,(7,4605567318180801141121085897297690623,335671607310559536529239667981357678592)),(7,(7,4605567319462262509912592822416769023,335671607320463056843522710180013801472)),(7,(7,4605567338414592584011134393258082303,335671607360231880605565551508992294912)),(7,(7,4605567339929376635988264749082804223,335671607310559536529239667981357678592)),(7,(7,4605567342921468039534471956318388223,335671607360077138100654878974638292992)),(7,(7,4605577375497031418077564263678869503,335671617451764338355074879405227507712)),(7,(7,4605872738086884595528096983887642623,335671607310559536529239667981357678592)),(8,(7,4606422531861986526134048585330742613,335674213649865949845214887443538378752)),(7,(7,4606605757046466569179472715478728703,335671607310559536529239667981357678592)),(8,(7,4607114827546197355565619517006558003,335674213649865949845214887443538378752)),(7,(7,4607298052730516210961327573092532223,335671607310559536529239667981357678592)),(7,(7,4607847816950202691199859371785846783,335674213600193605768889003915903762432)),(8,(7,4607847846505949998493165209369186063,335674213649865949845214887443538378752)),(8,(7,4608143209095869584222363283963773183,335674203508661148019379676019668549632))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk34 : chunk34.all checkEntry = true := by
  decide +kernel

def chunk35 : List (Nat × Key) := [(8,(7,4608153244663126101107111409340470613,335674213649865949845214887443538378752)),(8,(7,4608153265130401414832499410068517683,335674213639962429530931845244882255872)),(8,(7,4608153266412033452900176295959138063,335674213649865949845214887443538378752)),(8,(7,4608153270918975316702179213405257983,335674213649711207340304214909184376832)),(8,(7,4608153271071304692340105359055192063,335674213649865949845214887443538378752)),(7,(7,5316993112860288818391545025029734399,265849655639068318828763749275133804544)),(7,(7,5316993118039564105969557725480222719,265849655649426395248810214443559419904)),(7,(7,5318291187074922524145756145042030591,265848357564853685123009538155121508352)),(7,(7,5318291187074922524289836148611612671,265848357564853685122865458151551926272)),(7,(7,5318291187302437655735169250502868991,265848357580163521699044602918536773632)),(7,(7,5318291187921256559650407559171407871,265848357579544702795129364609868234752)),(7,(7,5669988169520054424196358829831618559,266551751529744855613988091686933233664)),(7,(7,5669988169520356654498340983055286271,266551751529744553383686109533709565952)),(7,(7,5669988169891171996977068792180867071,266551751545218161629308962529884536832)),(7,(7,5669988174842932154118519522496348159,266551751540266401472167511799569055744)),(7,(7,6646139978925141326163992312484429823,332306998946229610467831715941889114112))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk35 : chunk35.all checkEntry = true := by
  decide +kernel

def chunk36 : List (Nat × Key) := [(7,(7,6646139979068441537053307016149172223,332306998946393382137419504174648819712)),(7,(7,9304595970494821956244154604264095743,329648542954659929837751553650109448192)),(7,(7,9304595970638273282860885952203587583,329648542954823550391611925238594404352)),(7,(7,27913787911483493061170001619139428351,311039351013671258732825706635234115584)),(7,(7,27913787911627095503514149611353669631,311039351013834728170958661579444322304)),(7,(7,42535944902263313370351227303091986271,170143779658571598801041172391457193984)),(7,(7,42535944929150269265657293722869522271,170143779611374379235637749280338345984)),(7,(7,45194603718509510298319753619724785151,180777603627172063357355256136706555904)),(7,(7,45194603744197120284996746778752538111,180777603575177826140837877167941484544)),(7,(7,90387503713466157723424668850305851391,180775007490038243223382967490638290944)),(7,(7,90387503729158614598912195147253112831,180775007426749163192563345494275825664)),(7,(7,90389045176504515787938791554283410431,180777603638313372595196226781547864064)),(7,(7,90389045192288133225990408509973271551,180777603575177826143431915368330829824)),(7,(7,148873535528045977457527772015259246591,170141183534900376594297394234187096064)),(7,(7,148873535530077572574550655874857132031,170141183462945716290497722946592743424)),(7,(7,148875807157786564542136922066158292991,170143779683175657081838105353743499264))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk36 : chunk36.all checkEntry = true := by
  decide +kernel

def chunk37 : List (Nat × Key) := [(7,(7,148875807159952652656560619330283180031,170143779611374379241366328005019828224)),(7,(7,158178131498405588616312537400425275391,180775007426749163195986081210280484864)),(7,(7,158178131499333443905017215017520422911,180775007504738781189896858254268473344)),(7,(8,3004893228578014448945869238574487850533030606632823,58122201056482360385578726829680642409842879181541266868359938635985250680832)),(7,(8,3004893228578014451226347774184595039258009134397303,58123087917355293493615765628302222126930334746503969437198259080514190180352)),(7,(8,3004893228578018472975909708865422239080614601389943,61754838608134089087595462324257954916789668218387900088666476668230368755712)),(7,(8,28435409756979540724021137660566097082070811885384703,92271821110986343228158176570014579448331303284049202030919754738675841236992)),(7,(8,41904631685720267607087762890733332965193661676457983,108555083659983933209597846337044004194815905534582109981633475813074987384832)),(7,(8,3077010471924803319949846298504741415048106970012933983,58122201056482360386166438869785398491641857461745578831250333305529457180672)),(7,(8,3077010471924803319951393759362230917376963142068690783,58123087917355293494203477668406978208729313026718184920402936792257052803072)),(7,(8,6154021309213822046012032624156025930624574705250942783,58122201056482360386951076586526045882407116067032723078063626577035722227712)),(7,(8,6154021309213822046012887809796579917247247946358931263,58123087917355293494988115385147625599494571631995425646901947021564661727232)),(7,(8,6513106484258182865889911137785539282338388131043303263,58122201056482360387246033900584867850248027885291387024699121802891893932032)),(7,(8,6513106484258182868558955339410658186262010405768658943,61754838608134089089262769395162180357189500010154880581514332837272042340352)),(7,(8,6541652098660374843988134309462504420910426982642048863,58123087917355293495283120776030703890667014693566425914923292755185035640832)),(7,(8,6541652098660374846656323325447069338211376016259416063,61754838608134089089262817471986436680521031253467216902900183345036244549632))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk37 : chunk37.all checkEntry = true := by
  decide +kernel

def chunk38 : List (Nat × Key) := [(7,(8,10727469245278167136651183816144000519129142652293314423,58122201056482360388127985084535874592867759530657977341317430686361805914112)),(7,(8,10727469245278167139310328776424512972261314341391783423,72370055790172588808674869758734946182642608897894991183586017989736836104192)),(7,(8,10727469245278167140641280773930086336563467338738827263,108555083659983933209610058410888133742040656975992499110735673000274849431552)),(7,(8,10769536649190154718106166949865395339191735258472478583,58123087917355293496165071959799022928620383474157555627452066261198492925952)),(7,(8,10769536649190154722093688071032893327510139809241759743,108555083659983933209610106487529702360705825364670424887352912669472112771072)),(7,(8,49055571430417742133071962645442725363696209981781005823,72370055790172588806897222821813312670684704558529246281687992122485183086592)),(7,(8,52296410390074996298388883879428825541710231457441857343,58122201056482360386363316469228803572542518158283483326643190460077060390912)),(7,(8,52296410390074996298409897386630836726279358998111453183,61754838608134089088380051963806116079489307195140020067264011534520834588672)),(7,(8,52312185780721807057911293039237226155193314595043229503,58123087917355293494400403344491951908295142101783061612777826034913747402752)),(7,(8,52312185780721807057930759085581747837433585963657068543,61754838608134089088380100040447684698154475573666992264246043622629925978112)),(7,(8,73559786503916788430049229856949220483598324730140033023,108555083659983933209892037590404602796577894797415717697870063438714520993792)),(7,(8,73607302302795567517458832777546213779136361968622895103,108555083659983933209892085479976816332272901565643051399421051043885415923712)),(7,(8,84957721546752713585241026213233590930068615646311577463,61754838608134089090439725969813577686315311852317010562064452076905873539072)),(7,(8,84957721546752713585242404804296967003000857328739103743,92271821110986343229348111466280539269089778093202582898693659619276579930112)),(7,(8,84957721546752713585243134972280808507614843429426499583,108555083659983933209905063801588524328541461799179612647292271678210265055232)),(7,(8,845789342463099905679845233649839731805381007851680750493810906453,13532629479409598490865154262289882081266363937693411867234981117952))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk38 : chunk38.all checkEntry = true := by
  decide +kernel

def chunk39 : List (Nat × Key) := [(7,(8,845789342463487536846846376051411545331078038062751411170423469043,3632637565184358181721339376142857355689582195087043707332773319192977866752)),(7,(8,845789342469613012106062010572022304448654140934831292798328722773,13532629484424690148166087846329341199337310082680626521525056438272)),(7,(8,845789342515396316011878824004375485626239203937664334280954868723,3632637565184358185558708211387336075528085213320825817314900270234239762432)),(7,(8,8424983333495302404622001120165709396495660849491090434766970792703,36185027886661311073801381365074866811133648529357229501742187027878549389312)),(7,(8,8424983333509126666791477115273873184618394468107122443690357795583,36185027886661311069964012529830388091295145511123447391760060076837287493632)),(7,(8,113078218912131336798538950499541643601755381406279284504810949494889495483,28948022309329048855990825966787393850487039117453470793260421989307202404352)),(7,(8,113078218912131336802727772103792018366592343049069773589932482450474908603,28948022309329048860220513660493540118044011326705173400282485242662980943872)),(7,(8,964698497368997843952493206019119687338995920116488847380937485521071758813,14474011154664524427946373126268676186618247259425973337618051220497982554112)),(7,(8,964698497368997843985141746620337765935569171006573199937212662093377822173,14474011154664524433353783642031277318376175568514839979645202177102574518272)),(7,(8,1356938545749799165119991562044413679796861054168825659613329663151675788543,21711016731996786641919559689311670427426353653095949936117689308028067643392)),(7,(8,1356938545749799165131370416155751468539548873223676026653045822891092856063,21711016731996786646934651346612604011465812771166896081104903962318142963712))]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def checkedChunk39 : chunk39.all checkEntry = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_10760.KernelPN

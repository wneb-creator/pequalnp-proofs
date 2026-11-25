import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

-- The three unowned edges give three inputs on which a top AND is true.
-- For a residual vertex cover of size four, the edges form an induced matching.
-- On its six vertices we evaluate the circuit at the three edge inputs and
-- the eight independent inputs choosing one endpoint of each edge. At an
-- accepting top, one operand receives a true dirty AND. The other operand
-- supplies an input pin or the other dirty AND. The matching calculation
-- checks whether any choice can accept all three edges.
--
-- For larger minimum covers the gate budget leaves five stars and two
-- exceptional OR gates after the single-OR and centreless cases are excluded.
-- Each exceptional OR supplies one of the dirty signals and has a raw input
-- common to the operands it reaches. The finite check enumerates the possible
-- star centres, the input sets at their leaves, and the two common inputs.
-- It compares the three positive inputs with independent inputs of the graph.
-- All numerical certificates are verified by the kernel.

namespace PEqualNP.Outside.L_meta_5228_aux

namespace LocalMixerCertificate

def rows : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
def negatives : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
def pins : List ℕ := (List.range 11).map fun r => 1 <<< r

def hit (a b : ℕ) : Bool := (a &&& b) != 0
def within (a b : ℕ) : Bool := (a &&& b) == a

def neighbors (edges : List ℕ) : List ℕ := pins.map fun v =>
  edges.foldl (fun n e => if hit e v then n ||| (e ^^^ v) else n) 0

def allClauses : List ℕ := (List.range 2048).filter fun a =>
  a != 0 && ((pins.contains a) || (neighbors rows).any (within a))

def independent (x : ℕ) : Bool := rows.all fun e => !within e x

lemma independent_rows : negatives.all independent = true := by decide +kernel

def available (u : List ℕ) := neighbors (rows.filter fun e => !u.contains e)

def useful (u : List ℕ) (ns : List ℕ) (a : ℕ) : Bool :=
  u.all (hit a) && (pins.contains a || ns.any (within a))

def accepts (u : List ℕ) : Bool :=
  let ns := available u
  let clauses := allClauses.filter (useful u ns)
  let accepted := negatives.filter fun v => clauses.all (hit v)
  let points := accepted.foldl (fun z n => z ||| n) 0
  !accepted.isEmpty && ns.all fun n => u.any fun e => within (n &&& e) points

def triplesFrom (a : ℕ) : List (List ℕ) :=
  ((List.range 16).filter fun b => decide (a < b)).flatMap fun b =>
    ((List.range 16).filter fun c => decide (b < c)).map fun c =>
      [rows.getD a 0,rows.getD b 0,rows.getD c 0]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check0 : (triplesFrom 0).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check1 : (triplesFrom 1).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check2 : (triplesFrom 2).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check3 : (triplesFrom 3).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check4 : (triplesFrom 4).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check5 : (triplesFrom 5).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check6 : (triplesFrom 6).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check7 : (triplesFrom 7).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check8 : (triplesFrom 8).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check9 : (triplesFrom 9).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check10 : (triplesFrom 10).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check11 : (triplesFrom 11).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check12 : (triplesFrom 12).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check13 : (triplesFrom 13).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check14 : (triplesFrom 14).all accepts = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma check15 : (triplesFrom 15).all accepts = true := by decide +kernel

theorem checked {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < 16) :
    accepts [rows.getD i 0,rows.getD j 0,rows.getD k 0] = true := by
  have hi : i < 16 := by omega
  have finite : (triplesFrom i).all accepts = true := by
    interval_cases i
    · exact check0
    · exact check1
    · exact check2
    · exact check3
    · exact check4
    · exact check5
    · exact check6
    · exact check7
    · exact check8
    · exact check9
    · exact check10
    · exact check11
    · exact check12
    · exact check13
    · exact check14
    · exact check15
  apply List.all_eq_true.mp finite
  apply List.mem_flatMap.mpr
  refine ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),decide_eq_true hij⟩, ?_⟩
  apply List.mem_map.mpr
  exact ⟨k, List.mem_filter.mpr ⟨List.mem_range.mpr hk,decide_eq_true hjk⟩, rfl⟩

end LocalMixerCertificate

namespace LocalMixerCertificate

def liveClauses (u : List ℕ) := allClauses.filter (useful u (available u))
def independentInputs (u : List ℕ) := negatives.filter fun x => (liveClauses u).all (hit x)
def occupied (u : List ℕ) := (independentInputs u).foldl (fun z x => z ||| x) 0

lemma split_check (b : Bool) (ns es : List ℕ) (p : ℕ → ℕ → Bool)
    (h : (b && ns.all (fun n => es.any (p n))) = true) :
    b = true ∧ ∀ n ∈ ns, ∃ e ∈ es, p n e = true := by
  obtain ⟨hb,ha⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨hb,fun n hn => List.any_eq_true.mp (List.all_eq_true.mp ha n hn)⟩

set_option maxRecDepth 20000 in
lemma acceptable_rows {u : List ℕ} (h : accepts u = true) :
    (!(independentInputs u).isEmpty) = true ∧
    ∀ n ∈ available u, ∃ e ∈ u, within (n &&& e) (occupied u) = true := by
  change (!(independentInputs u).isEmpty && (available u).all
    (fun n => u.any fun e => within (n &&& e) (occupied u))) = true at h
  exact split_check (!(independentInputs u).isEmpty) (available u) u
    (fun n e => within (n &&& e) (occupied u)) h

lemma finite_raw_hit {u A : List ℕ} {x : ℕ} (hx : x ∈ independentInputs u)
    (ha : ∀ a ∈ A, a ∈ liveClauses u) : x ∈ negatives ∧ independent x = true ∧ A.all (hit x) = true := by
  obtain ⟨hneg,hpos⟩ := List.mem_filter.mp hx
  exact ⟨hneg, List.all_eq_true.mp independent_rows x hneg,
    List.all_eq_true.mpr (fun a h => List.all_eq_true.mp hpos a (ha a h))⟩

lemma within_bit {a b i : ℕ} (h : within a b = true) (hi : a.testBit i = true) : b.testBit i = true := by
  have eq : a &&& b = a := by simpa [within] using h
  have hb := congrArg (fun x : ℕ => x.testBit i) eq
  simpa [Nat.testBit_and, hi] using hb

lemma fold_or_bit (xs : List ℕ) (i z : ℕ)
    (ht : (xs.foldl (fun a b => a ||| b) z).testBit i = true) :
    z.testBit i = true ∨ ∃ x ∈ xs, x.testBit i = true := by
  induction xs generalizing z with
  | nil => exact Or.inl ht
  | cons x xs ih =>
    rcases ih (z ||| x) ht with h | ⟨n,hn,ht⟩
    · have ho : z.testBit i = true ∨ x.testBit i = true := by simpa [Nat.testBit_or] using h
      exact ho.elim Or.inl (fun h => Or.inr ⟨x,List.mem_cons_self,h⟩)
    · exact Or.inr ⟨n,List.mem_cons_of_mem _ hn,ht⟩

lemma raw_conjunction_obstruction {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < 16)
    (u : List ℕ) (hu : u = [rows.getD i 0,rows.getD j 0,rows.getD k 0])
    (A : List ℕ) (ha : ∀ a ∈ A, a ∈ liveClauses u) :
    ∃ x ∈ negatives, independent x = true ∧ A.all (hit x) = true := by
  obtain ⟨nonempty,_⟩ := acceptable_rows (hu ▸ checked hij hjk hk)
  cases eq : independentInputs u with
  | nil => simp [eq] at nonempty
  | cons x xs =>
    have hx : x ∈ independentInputs u := eq ▸ List.mem_cons_self
    exact ⟨x,finite_raw_hit hx ha⟩

lemma one_mixer_obstruction {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < 16)
    (u : List ℕ) (hu : u = [rows.getD i 0,rows.getD j 0,rows.getD k 0])
    (A : List ℕ) (ha : ∀ a ∈ A, a ∈ liveClauses u)
    (n : ℕ) (hn : n ∈ available u)
    (pass : ∀ e ∈ u, ∃ i : ℕ, (n &&& e).testBit i = true ∧
      ∀ x ∈ negatives, x.testBit i = true → A.all (hit x) = false) : False := by
  obtain ⟨_,all⟩ := acceptable_rows (hu ▸ checked hij hjk hk)
  obtain ⟨e,he,hwithin⟩ := all n hn
  obtain ⟨w,hw,filter⟩ := pass e he
  have p := within_bit hwithin hw
  rcases fold_or_bit (independentInputs u) w 0 p with zero | ⟨x,hx,bit⟩
  · simp at zero
  · obtain ⟨neg,_,positive⟩ := finite_raw_hit hx ha
    have invalid := filter x neg bit
    simp [positive] at invalid

end LocalMixerCertificate

namespace LocalSignatures
open LocalMixerCertificate

def signature (rs : List ℕ) (m : ℕ) : ℕ :=
  (BitVec.ofBoolListLE (rs.map (hit m))).toNat

def improves (a b : ℕ) : Bool := ((a &&& 7) == (b &&& 7)) && within a b

def Refines (a b : ℕ) : Prop :=
  (∀ i < 3, a.testBit i = b.testBit i) ∧ (∀ i, a.testBit i = true → b.testBit i = true)

lemma seven (i : ℕ) : (7 : ℕ).testBit i = decide (i < 3) := Nat.testBit_two_pow_sub_one 3 i

def represent (candidates values : List ℕ) : Bool :=
  values.all fun x => candidates.any fun a => improves a x

end LocalSignatures

namespace LocalPrune
open LocalSignatures

def insertMinimal (v : ℕ) (cs : List ℕ) : List ℕ :=
  if cs.any (fun q => improves q v) then cs else v :: cs.filter (fun q => !(improves v q))

def prune (vs : List ℕ) := vs.foldr insertMinimal []

def products (xs : List ℕ) := xs.flatMap fun a => xs.map (fun b => a &&& b)
def first (rs : List ℕ) := prune (products (prune rs))
def withSignal (rs : List ℕ) (d : ℕ) := prune (rs ++ rs.map (fun a => a ||| d))
def second (rs : List ℕ) (d : ℕ) := prune (products (withSignal (prune rs) d))
def optional (r d : ℕ) (flag : Bool) := if flag then r ||| d else r

end LocalPrune

namespace LocalWordGeometry
open LocalMixerCertificate LocalSignatures LocalPrune

def rawMasks (u : List ℕ) : List ℕ :=
  let ns := available u
  allClauses.filter fun v => pins.contains v || ns.any (within v)

def anchorPairs (l r : ℕ) : ℕ :=
  (List.range 11).foldl (fun word i => if l.testBit i then word ||| (r <<< (11*i)) else word) 0

abbrev TopChoice := ℕ × ℕ × ℕ × ℕ × ℕ

abbrev TopChoice.left (t : TopChoice) := t.1
abbrev TopChoice.right (t : TopChoice) := t.2.1
abbrev TopChoice.useA (t : TopChoice) := t.2.2.1
abbrev TopChoice.useB (t : TopChoice) := t.2.2.2.1
abbrev TopChoice.anchors (t : TopChoice) := t.2.2.2.2

def neededMask (cover neighbors : ℕ) : ℕ :=
  if (pins.filter (hit cover)).length < 5 then 0 else neighbors &&& (2047 ^^^ cover)

def anchorAt (center leaf side : ℕ) : ℕ :=
  if side = 0 then 2047 else if side = 1 then center else leaf

def options (u : List ℕ) (cover : ℕ) : List TopChoice :=
  let tests := u ++ negatives
  let masks := rawMasks u
  ((pins.zip (available u)).filter (fun c => hit c.1 cover)).flatMap fun c =>
    let needed := neededMask cover c.2
    (masks.filter (fun l => within l c.2 && within needed l)).flatMap fun leaf =>
      let anchors := anchorAt c.1 leaf
      let left := signature tests c.1
      let right := signature tests leaf
      (List.range 3).flatMap fun s => (List.range 3).map fun t =>
        ⟨left,right,s,t,anchorPairs (anchors s) (anchors t)⟩

def topValue (opt : TopChoice) (a b : ℕ) : ℕ :=
  let operand := fun p r => r ||| (if opt.useA = p then a else 0) ||| (if opt.useB = p then b else 0)
  operand 1 opt.left &&& operand 2 opt.right

def surviving (choices : List TopChoice) (a b : ℕ) : ℕ :=
  let v := choices.foldl (fun (acc : ℕ × ℕ × ℕ) opt =>
    let t := topValue opt a b
    if t=0 ∨ 7<t then acc else
      (if t.testBit 0 then acc.1 ||| opt.anchors else acc.1,
       if t.testBit 1 then acc.2.1 ||| opt.anchors else acc.2.1,
       if t.testBit 2 then acc.2.2 ||| opt.anchors else acc.2.2)) (0,0,0)
  v.1 &&& v.2.1 &&& v.2.2

def excludes (u : List ℕ) (cover : ℕ) : Bool :=
  let raw := 0 :: (rawMasks u).map (signature (u ++ negatives))
  let geo := options u cover
  (first raw).all fun a => surviving geo a a == 0 &&
    (second raw a).all fun b => surviving geo a b == 0 && surviving geo b b == 0

end LocalWordGeometry

namespace LocalGeometrySound
open LocalSignatures LocalPrune LocalWordGeometry

abbrev TripleWord := ℕ × ℕ × ℕ

def joinStep (a b : ℕ) (acc : TripleWord) (o : TopChoice) : TripleWord :=
  let t := topValue o a b
  if t=0 ∨ 7<t then acc else
    (if t.testBit 0 then acc.1 ||| o.anchors else acc.1,
     if t.testBit 1 then acc.2.1 ||| o.anchors else acc.2.1,
     if t.testBit 2 then acc.2.2 ||| o.anchors else acc.2.2)

def part (v : TripleWord) (i : Fin 3) : ℕ :=
  if i=0 then v.1 else if i=1 then v.2.1 else v.2.2

lemma part_step (a b : ℕ) (acc : TripleWord) (o : TopChoice) (i : Fin 3) :
    part (joinStep a b acc o) i =
      if topValue o a b ≤ 7 ∧ (topValue o a b).testBit i.val = true
      then part acc i ||| o.anchors else part acc i := by
  by_cases z : topValue o a b = 0
  · simp [joinStep,z]
  · by_cases h : topValue o a b ≤ 7
    · have le := Nat.not_lt.mpr h
      fin_cases i <;> simp [part,joinStep,z,h,le]
    · have gt := Nat.lt_of_not_ge h
      simp [joinStep,z,h,gt]

lemma keep_partial (xs : List TopChoice) (a b : ℕ) (acc : TripleWord) (i : Fin 3) (index : ℕ)
    (h : (part acc i).testBit index = true) :
    (part (xs.foldl (joinStep a b) acc) i).testBit index = true := by
  induction xs generalizing acc with
  | nil => exact h
  | cons o xs ih =>
    apply ih
    rw [part_step]
    split <;> simp [Nat.testBit_or,h]

lemma accepted_anchor (xs : List TopChoice) (a b : ℕ) (acc : TripleWord) (i : Fin 3) (index : ℕ)
    {o : TopChoice} (mem : o ∈ xs) (clean : topValue o a b ≤ 7)
    (positive : (topValue o a b).testBit i.val = true) (anchor : o.anchors.testBit index = true) :
    (part (xs.foldl (joinStep a b) acc) i).testBit index = true := by
  induction xs generalizing acc with
  | nil => simp at mem
  | cons q xs ih =>
    rcases List.mem_cons.mp mem with rfl | rest
    · rw [List.foldl_cons]
      apply keep_partial xs a b
      rw [part_step]
      simp [clean,positive,Nat.testBit_or,anchor]
    · exact ih _ rest

lemma surviving_nonzero (xs : List TopChoice) (a b index : ℕ)
    (accept : ∀ i : Fin 3, ∃ o ∈ xs, topValue o a b ≤ 7 ∧
      (topValue o a b).testBit i.val = true ∧ o.anchors.testBit index = true) :
    surviving xs a b ≠ 0 := by
  let result := xs.foldl (joinStep a b) (0,0,0)
  have each (i : Fin 3) : (part result i).testBit index = true := by
    obtain ⟨o,mo,cl,yes,an⟩ := accept i
    exact accepted_anchor xs a b _ i index mo cl yes an
  have p0 : result.1.testBit index = true := each 0
  have p1 : result.2.1.testBit index = true := each 1
  have p2 : result.2.2.testBit index = true := each 2
  have all : (surviving xs a b).testBit index = true := by
    change (result.1 &&& result.2.1 &&& result.2.2).testBit index = true
    simp [Nat.testBit_and,p0,p1,p2]
  intro zero
  simp [zero] at all

def model (o : List TopChoice) (a b index : ℕ) : Prop :=
  ∀ i : Fin 3, ∃ q ∈ o, topValue q a b ≤ 7 ∧ (topValue q a b).testBit i.val = true ∧ q.anchors.testBit index = true

end LocalGeometrySound

namespace LocalClip
open LocalSignatures LocalWordGeometry LocalGeometrySound LocalPrune LocalMixerCertificate

def clip (h w : ℕ) := h &&& w

def clipChoice (h : ℕ) (q : TopChoice) : TopChoice :=
  ⟨clip h q.left,clip h q.right,q.useA,q.useB,q.anchors⟩

def scan (raw : List ℕ) (geo : List TopChoice) : Bool :=
  (first raw).all fun a => surviving geo a a == 0 &&
    (second raw a).all fun b => surviving geo a b == 0 && surviving geo b b == 0

def clippedCheck (h : ℕ) (u : List ℕ) (K : ℕ) : Bool :=
  let raw := 0 :: (rawMasks u).map (signature (u++negatives))
  scan (raw.map (clip h)) ((options u K).map (clipChoice h))

lemma clip_and (h a b : ℕ) : clip h (a &&& b) = clip h a &&& clip h b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [clip,Nat.testBit_and,Bool.and_assoc,Bool.and_comm,Bool.and_left_comm]

lemma clip_optional (h a b : ℕ) (flag : Bool) :
    clip h (LocalPrune.optional a b flag) = LocalPrune.optional (clip h a) (clip h b) flag := by
  cases flag
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro i
    simp [clip,LocalPrune.optional,Nat.testBit_and,Nat.testBit_or,Bool.and_or_distrib_left]

lemma clip_top (h : ℕ) (q : TopChoice) (a b : ℕ) :
    topValue (clipChoice h q) (clip h a) (clip h b) = clip h (topValue q a b) := by
  unfold topValue
  rw [clip_and]
  have onSide (p r : ℕ) : clip h r ||| (if q.useA=p then clip h a else 0) ||| (if q.useB=p then clip h b else 0) =
      clip h (r ||| (if q.useA=p then a else 0) ||| (if q.useB=p then b else 0)) := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases x : q.useA=p <;> by_cases y : q.useB=p <;>
      simp [x,y,clip,Nat.testBit_or,Nat.testBit_and,Bool.and_or_distrib_left]
  exact congrArg₂ (fun x y : ℕ => x &&& y) (onSide 1 q.left) (onSide 2 q.right)

lemma clip_model (h : ℕ) (keep : ∀ i : Fin 3, h.testBit i.val = true) (xs : List TopChoice)
    (a b index : ℕ) (m : model xs a b index) : model (xs.map (clipChoice h)) (clip h a) (clip h b) index := by
  intro i
  obtain ⟨q,hq,safe,accept,anchor⟩ := m i
  refine ⟨clipChoice h q,List.mem_map.mpr ⟨q,hq,rfl⟩,?_,?_,anchor⟩
  · rw [clip_top]
    exact Nat.and_le_right.trans safe
  · rw [clip_top]
    simp [clip,Nat.testBit_and,keep i,accept]

end LocalClip

namespace LocalBetter
open LocalWordGeometry LocalGeometrySound LocalPrune LocalSignatures LocalMixerCertificate

def Better (a b : ℕ) : Prop :=
  (∀ i < 3, b.testBit i = true → a.testBit i = true) ∧
  (∀ i ≥ 3, a.testBit i = true → b.testBit i = true)

def beats (a b : ℕ) : Bool := within (b &&& 7) (a &&& 7) && within (a >>> 3) (b >>> 3)

lemma beats_sound {a b : ℕ} (h : beats a b=true) : Better a b := by
  obtain ⟨up,dn⟩ := Bool.and_eq_true_iff.mp h
  constructor
  · intro i hi bit
    have pos : (b &&& 7).testBit i = true := by simp [Nat.testBit_and,seven,hi,bit]
    simpa [Nat.testBit_and,seven,hi] using within_bit up pos
  · intro i hi bit
    have eq : 3 + (i-3) = i := by omega
    have pos : (a >>> 3).testBit (i-3) = true := by simpa [Nat.testBit_shiftRight,eq] using bit
    simpa [Nat.testBit_shiftRight,eq] using within_bit dn pos

lemma self (a : ℕ) : Better a a := ⟨fun _ _ h => h,fun _ _ h => h⟩

lemma chain {a b c : ℕ} (ab : Better a b) (bc : Better b c) : Better a c :=
  ⟨fun i hi v => ab.1 i hi (bc.1 i hi v),fun i hi v => bc.2 i hi (ab.2 i hi v)⟩

lemma conj {a b c d : ℕ} (ac : Better a c) (bd : Better b d) : Better (a &&& b) (c &&& d) := by
  constructor
  · intro i hi h
    rw [Nat.testBit_and,Bool.and_eq_true_iff] at h ⊢
    exact ⟨ac.1 i hi h.1,bd.1 i hi h.2⟩
  · intro i hi h
    rw [Nat.testBit_and,Bool.and_eq_true_iff] at h ⊢
    exact ⟨ac.2 i hi h.1,bd.2 i hi h.2⟩

lemma disj {a b c d : ℕ} (ac : Better a c) (bd : Better b d) : Better (a ||| b) (c ||| d) := by
  constructor
  · intro i hi h
    rw [Nat.testBit_or,Bool.or_eq_true_iff] at h ⊢
    exact h.imp (ac.1 i hi) (bd.1 i hi)
  · intro i hi h
    rw [Nat.testBit_or,Bool.or_eq_true_iff] at h ⊢
    exact h.imp (ac.2 i hi) (bd.2 i hi)

lemma flag {a b c d : ℕ} (ac : Better a c) (bd : Better b d) (f : Bool) :
    Better (LocalPrune.optional a b f) (LocalPrune.optional c d f) := by
  cases f
  · exact ac
  · exact disj ac bd

lemma top (q : TopChoice) {a b c d : ℕ} (ac : Better a c) (bd : Better b d) :
    Better (topValue q a b) (topValue q c d) := by
  have choose (p : Prop) [Decidable p] {u v : ℕ} (h : Better u v) : Better (if p then u else 0) (if p then v else 0) := by
    by_cases yes : p <;> simp [yes,h,self]
  have side (p r : ℕ) : Better (r ||| (if q.useA=p then a else 0) ||| (if q.useB=p then b else 0))
    (r ||| (if q.useA=p then c else 0) ||| (if q.useB=p then d else 0)) :=
    disj (disj (self r) (choose _ ac)) (choose _ bd)
  exact conj (side 1 _) (side 2 _)

lemma safe {a b : ℕ} (h : Better a b) (hb : b≤7) : a≤7 := by
  by_contra no
  have high : 2^3 ≤ a := by change 8 ≤ a; omega
  obtain ⟨i,lo,bit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow high
  have large : 2^i ≤ b := Nat.ge_two_pow_of_testBit (h.2 i lo bit)
  have pow : (2 : ℕ)^3 ≤ 2^i := Nat.pow_le_pow_of_le (by decide) lo
  omega

lemma better_model (geo : List TopChoice) {a b c d index : ℕ} (ac : Better a c) (bd : Better b d)
    (m : model geo c d index) : model geo a b index := by
  intro i
  obtain ⟨q,hq,clear,on,anchor⟩ := m i
  have met := top q ac bd
  exact ⟨q,hq,safe met clear,met.1 _ i.isLt on,anchor⟩

end LocalBetter

-- The OR-path characterization is from willakone, project PR 3118.
namespace LocalLambda
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

open PEqualNP.TopForm

lemma orIn_subset_of_reaches {n : ℕ} {C : Circuit} {w k : ℕ} (h : OrReaches n C w k) :
    orIn n C (n+k) ⊆ orIn n C w := fun v hv =>
  reach_mem_orIn v ((orReaches_reach k w h).1.trans (mem_orIn_reach v hv))

lemma cross_outside {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {a : ℕ} (ha : a ∈ tops G C)
    (hc : ∀ u ∈ side C a (0 : Fin 2), ∀ v ∈ side C a (1 : Fin 2), G.Adj u v)
    {u v : Fin n} (hu : u ∈ side C a (0 : Fin 2)) (hv : v ∈ side C a (1 : Fin 2)) :
    G.Adj u v ∧ s(u,v) ∉ Ustar G C := by
  refine ⟨hc u hu v hv, ?_⟩
  intro missing
  apply (Finset.mem_sdiff.mp missing).2
  exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr
    ⟨(u,v),Finset.mem_product.mpr ⟨hu,hv⟩,rfl⟩⟩

lemma lambda_raw_clause {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (cross : ∀ a ∈ tops G C, ∀ u ∈ side C a (0 : Fin 2), ∀ v ∈ side C a (1 : Fin 2), G.Adj u v)
    {k : ℕ} (hk : k ∈ lam G C) :
    ∃ c : Fin n, ∀ v ∈ orIn n C (n+k), (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj c v := by
  obtain ⟨_,_,a,ha,b,hcard,reach⟩ := (Finset.mem_filter.mp hk).2
  obtain ⟨c,hside⟩ := Finset.card_eq_one.mp hcard
  have hc : c ∈ side (n := n) C a (1-b) := hside ▸ Finset.mem_singleton_self _
  refine ⟨c,fun v hv => ?_⟩
  have hv' : v ∈ side (n := n) C a b := orIn_subset_of_reaches reach hv
  fin_cases b
  · have pair := cross_outside ha (cross a ha) hv' (show c ∈ side C a 1 from hc)
    apply SimpleGraph.deleteEdges_adj.mpr
    have swap : s(c,v) = s(v,c) := Sym2.eq_swap
    exact ⟨pair.1.symm, fun h => pair.2 (swap ▸ h)⟩
  · exact SimpleGraph.deleteEdges_adj.mpr (cross_outside ha (cross a ha) (show c ∈ side C a 0 from hc) hv')

end LocalLambda

-- The wire evaluation equations are from willakone, project PR 3118.
namespace LocalTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2


lemma tests_through_ands {n : ℕ} (C : Circuit) (basis : AndOrOnly C)
    (tests : List (Fin n → Bool)) (first : Fin n → Bool) (present : first ∈ tests)
    (y : Fin n → Bool) (stop : ℕ)
    (input : ∀ i : Fin n, (∀ x ∈ tests, x i = true) → y i = true)
    (ors : ∀ k < C.gates.length, n+k < stop → (gateAt C k).op = GateOp.or →
      (∀ x ∈ tests, val C (List.ofFn x) (n+k) = true) → val C (List.ofFn y) (n+k) = true) :
    ∀ w < stop, w < n+C.gates.length →
      (∀ x ∈ tests, val C (List.ofFn x) w = true) → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro before valid positive
    by_cases hpin : w < n
    · let i : Fin n := ⟨w,hpin⟩
      have hval (x : Fin n → Bool) : val C (List.ofFn x) w = x i := by
        rw [val_input (n := n) (by simp) hpin]
        simp [List.getD_eq_getElem?_getD,hpin,i]
      rw [hval]
      apply input i
      intro x hx
      exact hval x ▸ positive x hx
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      have hk : k < C.gates.length := by omega
      rcases basis _ (gateAt_mem hk) with hand | hor
      · apply (val_and (n := n) (by simp) hk hand).2
        intro v hv
        have earlier := ((val_and (n := n) (by simp) hk hand).1 (positive first present) v hv).1
        refine ⟨earlier,ih v earlier (by omega) (by omega) ?_⟩
        intro x hx
        exact ((val_and (n := n) (by simp) hk hand).1 (positive x hx) v hv).2
      · exact ors k hk before hor positive

end LocalTransfer

namespace LocalPure
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open LocalLambda LocalTransfer

lemma value_of_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (v : Fin n) :
    val C (List.ofFn x) v.val = x v := by
  rw [val_input (n := n) (by simp) v.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma upward {n : ℕ} {C : Circuit} (x : Fin n → Bool) {a b : ℕ}
    (path : Relation.ReflTransGen (OrStep n C) a b) (yes : val C (List.ofFn x) b = true) :
    val C (List.ofFn x) a = true := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact yes
  | head step _ ih =>
    obtain ⟨k,hk,rfl,hop,port,hprior⟩ := step
    exact (val_or (n := n) (by simp) hk hop).mpr ⟨_,port,hprior,ih⟩

lemma raw_pin {n : ℕ} {C : Circuit} {v : Fin n} (x : Fin n → Bool) {w : ℕ}
    (hv : v ∈ orIn n C w) (hon : x v = true) : val C (List.ofFn x) w = true :=
  upward x (mem_orIn_reach v hv) ((value_of_input C x v).trans hon)

lemma raw_above_singleton {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {k : ℕ} {v : Fin n} (hv : v ∈ orIn n C (n+k)) : ¬BelowF G C k := by
  intro below
  let x : Fin n → Bool := fun u => decide (u = v)
  have noedge : graphFun G ∅ x = false := by
    simp [graphFun,x]
  have on := raw_pin x hv (by simp [x])
  have bad := below x on
  simp [noedge] at bad

lemma raw_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ orIn n C (n+k) ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, w < n+k ∧ u ∈ orIn n C w := by
  constructor
  · intro hu
    rcases Relation.ReflTransGen.cases_head (mem_orIn_reach u hu) with he | ⟨w,hs,rest⟩
    · have := u.isLt; omega
    · obtain ⟨j,hj,eq,op,port,lt⟩ := hs
      have : j = k := by omega
      subst j
      exact ⟨hj,op,w,port,lt,reach_mem_orIn u rest⟩
  · rintro ⟨hk,op,w,port,lt,hu⟩
    apply reach_mem_orIn u
    exact Relation.ReflTransGen.head ⟨k,hk,rfl,op,port,lt⟩ (mem_orIn_reach u hu)

lemma lambda_port {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (ao : IsAO2 n C) {k w : ℕ} (hk : k ∈ lam G C)
    (hw : w ∈ (gateAt C k).inputs) : (orIn n C w).Nonempty := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨hor,h0,h1,_⟩ := Finset.mem_filter.mp hk
  have valid : k < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hor).1
  obtain ⟨p,q,eq⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem valid))
  have op0 : opnd C k 0 = p := by simp [opnd,eq]
  have op1 : opnd C k 1 = q := by simp [opnd,eq]
  rw [op0] at h0
  rw [op1] at h1
  simp only [eq,List.mem_cons,List.not_mem_nil,or_false] at hw
  exact hw.elim (fun h => h ▸ h0) (fun h => h ▸ h1)

lemma pure_before {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (stop : ℕ)
    (all : ∀ k, n+k < stop → k ∈ orN G C → k ∈ lam G C) (x : Fin n → Bool) :
    ∀ w < stop, (orIn n C w).Nonempty → val C (List.ofFn x) w = true →
      ∃ v ∈ orIn n C w, x v = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro before raw yes
    by_cases pin : w < n
    · let v : Fin n := ⟨w,pin⟩
      have mem : v ∈ orIn n C w := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩
      exact ⟨v,mem,(value_of_input C x v).symm.trans yes⟩
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      obtain ⟨a,ha⟩ := raw
      obtain ⟨hk,hop,_⟩ := (raw_gate C k a).mp ha
      have orn : k ∈ orN G C := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hk,hop,raw_above_singleton ha⟩
      obtain ⟨p,hp,hprior,hval⟩ := (val_or (n := n) (by simp) hk hop).mp yes
      obtain ⟨v,hv,hx⟩ := ih p hprior (by omega) (lambda_port ao (all k before orn) hp) hval
      exact ⟨v,(raw_gate C k v).mpr ⟨hk,hop,p,hp,hprior,hv⟩,hx⟩

end LocalPure

namespace LocalMixTrace
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer

lemma exceptional_source {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w, (orIn n C w).Nonempty → val C (List.ofFn x) w = true →
      (∀ v ∈ orIn n C w, x v = false) →
      ∃ k ∈ orN G C \ lam G C, OrReaches n C w k ∧ (orIn n C (n+k)).Nonempty ∧
        gateVal n C k x = true ∧ ∀ v ∈ orIn n C (n+k), x v = false := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro raw yes absent
    by_cases hw : w < n
    · let v : Fin n := ⟨w,hw⟩
      have mem : v ∈ orIn n C w := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩
      have high : x v = true := (value_of_input C x v).symm.trans yes
      exact (Bool.false_ne_true ((absent v mem).symm.trans high)).elim
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      obtain ⟨v,hv⟩ := raw
      obtain ⟨hk,hop,_⟩ := (raw_gate C k v).mp hv
      have orn : k ∈ orN G C := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hk,hop,raw_above_singleton hv⟩
      by_cases normal : k ∈ lam G C
      · obtain ⟨p,port,prior,on⟩ := (val_or (n := n) (by simp) hk hop).mp yes
        have absentP (v : Fin n) (h : v ∈ orIn n C p) : x v = false :=
          absent v ((raw_gate C k v).mpr ⟨hk,hop,p,port,prior,h⟩)
        obtain ⟨j,hj,path,atJ,onJ,off⟩ := ih p prior (lambda_port ao normal port) on absentP
        exact ⟨j,hj,(orReaches_iff n C k j).mpr ⟨hk,Or.inr ⟨hop,p,port,prior,path⟩⟩,atJ,onJ,off⟩
      · exact ⟨k,Finset.mem_sdiff.mpr ⟨orn,normal⟩,
          (orReaches_iff n C k k).mpr ⟨hk,Or.inl rfl⟩,⟨v,hv⟩,yes,absent⟩

end LocalMixTrace

namespace LocalBefore
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open LocalLambda LocalTransfer LocalPure

lemma earlier_exception {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    (cross : ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (nonempty : ∀ b : Fin 2, (side (n := n) C a b).Nonempty)
    {u v : Fin n} (missing : s(u,v) ∈ Ustar G C)
    (htrue : gateVal n C a (pairInput u v) = true) :
    ∃ k ∈ orN G C \ lam G C, k < a := by
  letI : DecidableEq GateOp := gateOpDecEq
  by_contra no
  have normal (k : ℕ) (before : n+k < n+a) (horn : k ∈ orN G C) : k ∈ lam G C := by
    by_contra outside
    exact no ⟨k,Finset.mem_sdiff.mpr ⟨horn,outside⟩,by omega⟩
  obtain ⟨hvalid,hand,_⟩ := Finset.mem_filter.mp ha
  have hk : a < C.gates.length := Finset.mem_range.mp hvalid
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  have vp := (val_and (n := n) (x := List.ofFn (pairInput u v)) (by simp) hk hand).mp htrue
  have hp := vp p (by simp [ports])
  have hq := vp q (by simp [ports])
  have np : (orIn n C p).Nonempty := by simpa [side,opnd,ports] using nonempty 0
  have nq : (orIn n C q).Nonempty := by simpa [side,opnd,ports] using nonempty 1
  obtain ⟨l,hl,lv⟩ := pure_before G C ao (n+a) normal (pairInput u v) p hp.1 np hp.2
  obtain ⟨r,hr,rv⟩ := pure_before G C ao (n+a) normal (pairInput u v) q hq.1 nq hq.2
  have left : l ∈ side C a (0 : Fin 2) := by simpa [side,opnd,ports] using hl
  have right : r ∈ side C a (1 : Fin 2) := by simpa [side,opnd,ports] using hr
  obtain ⟨adj,star⟩ := cross_outside ha cross left right
  have lcase : l = u ∨ l = v := of_decide_eq_true lv
  have rcase : r = u ∨ r = v := of_decide_eq_true rv
  rcases lcase with rfl | rfl <;> rcases rcase with rfl | rfl
  · exact G.irrefl adj
  · exact star missing
  · have swap : s(r,l) = s(l,r) := Sym2.eq_swap
    exact star (swap ▸ missing)
  · exact G.irrefl adj

end LocalBefore

namespace LocalReceiver
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalMixTrace LocalBefore

lemma sides_nonempty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (empty : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) :
    (side (n := n) C a b).Nonempty := by
  letI : DecidableEq GateOp := gateOpDecEq
  apply Finset.nonempty_iff_ne_empty.mpr
  intro h
  have bad : a ∈ centreless G C := by
    apply Finset.mem_filter.mpr
    refine ⟨ha,?_⟩
    fin_cases b
    · exact Or.inl h
    · exact Or.inr h
  simp [empty] at bad

lemma top_ports {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨valid,hand,_⟩ := Finset.mem_filter.mp ha
  have hk := Finset.mem_range.mp valid
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  change val C (List.ofFn x) (n+a) = true ↔ _
  rw [val_and (n := n) (by simp) hk hand]
  constructor
  · intro pos b
    apply (pos _ _).2
    fin_cases b <;> simp [opnd,ports]
  · intro h i hi
    refine ⟨ao.2.1 a hk i hi,?_⟩
    have choices : i = p ∨ i = q := by simpa [ports] using hi
    rcases choices with rfl | rfl
    · simpa [opnd,ports] using h 0
    · simpa [opnd,ports] using h 1

lemma one_blank {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {a : ℕ} (ha : a ∈ tops G C)
    (cross : ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    {u v : Fin n} (missing : s(u,v) ∈ Ustar G C) :
    ¬ ((∃ l ∈ side C a (0 : Fin 2), pairInput u v l = true) ∧
       (∃ r ∈ side C a (1 : Fin 2), pairInput u v r = true)) := by
  rintro ⟨⟨l,hl,lv⟩,r,hr,rv⟩
  obtain ⟨adj,star⟩ := cross_outside ha cross hl hr
  have lcase : l = u ∨ l = v := of_decide_eq_true lv
  have rcase : r = u ∨ r = v := of_decide_eq_true rv
  rcases lcase with rfl | rfl <;> rcases rcase with rfl | rfl
  · exact G.irrefl adj
  · exact star missing
  · have swap : s(r,l) = s(l,r) := Sym2.eq_swap
    exact star (swap ▸ missing)
  · exact G.irrefl adj

lemma receiver_transfer {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (ao : IsAO2 n C) {a m : ℕ} (ha : a ∈ tops G C)
    (cross : ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (b : Fin 2) (path : OrReaches n C (opnd C a b) m) {w : Fin n} (hw : w ∈ side C a (1-b)) :
    (∀ r ∈ orIn n C (n+m), (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj r w) ∧
    (∀ y : Fin n → Bool, gateVal n C m y = true → y w = true → graphFun G ∅ y = true) := by
  letI : DecidableEq GateOp := gateOpDecEq
  constructor
  · intro r hr
    have left : r ∈ side C a b := orIn_subset_of_reaches path hr
    fin_cases b
    · exact SimpleGraph.deleteEdges_adj.mpr (cross_outside ha cross left (show w ∈ side C a 1 from hw))
    · exact (SimpleGraph.deleteEdges_adj.mpr (cross_outside ha cross (show w ∈ side C a 0 from hw) left)).symm
  · intro y hm high
    have first := upward y (orReaches_reach m _ path).1 hm
    have second := raw_pin y hw high
    have below := (Finset.mem_filter.mp ha).2.2
    apply below y
    apply (top_ports ao ha y).mpr
    intro d
    fin_cases b <;> fin_cases d
    · exact first
    · exact second
    · exact second
    · exact first

lemma route_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ) (single : orN G C \ lam G C = {m})
    (allraw : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C)
    (cross : ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    {u v : Fin n} (missing : s(u,v) ∈ Ustar G C) (on : gateVal n C a (pairInput u v) = true) :
    (orIn n C (n+m)).Nonempty ∧ gateVal n C m (pairInput u v) = true ∧
    (∀ r ∈ orIn n C (n+m), pairInput u v r = false) ∧
    ∃ w : Fin n, pairInput u v w = true ∧
      (∀ r ∈ orIn n C (n+m), (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj r w) ∧
      ∀ y : Fin n → Bool, gateVal n C m y = true → y w = true → graphFun G ∅ y = true := by
  let seen := fun (b : Fin 2) => ∃ r ∈ side C a b, pairInput u v r = true
  have source (b : Fin 2) (off : ¬seen b) :
      OrReaches n C (opnd C a b) m ∧ (orIn n C (n+m)).Nonempty ∧
      gateVal n C m (pairInput u v) = true ∧ ∀ r ∈ orIn n C (n+m), pairInput u v r = false := by
    have absent (r : Fin n) (hr : r ∈ side C a b) : pairInput u v r = false := by
      cases h : pairInput u v r
      · rfl
      · exact (off ⟨r,hr,h⟩).elim
    obtain ⟨j,hj,prop⟩ := exceptional_source G C ao (pairInput u v) _ (sides_nonempty allraw ha b)
      ((top_ports ao ha _).mp on b) absent
    have eq : j = m := by simpa [single] using hj
    exact eq ▸ prop
  have splitter : ∃ b : Fin 2, ¬seen b ∧ seen (1-b) := by
    by_cases h0 : seen 0
    · exact ⟨1,fun h1 => one_blank ha cross missing ⟨h0,h1⟩,h0⟩
    · by_cases h1 : seen 1
      · exact ⟨0,h0,h1⟩
      · obtain ⟨left,⟨r,hr⟩,_⟩ := source 0 h0
        have right := (source 1 h1).1
        exact (G.irrefl (cross r (orIn_subset_of_reaches left hr) r (orIn_subset_of_reaches right hr))).elim
  obtain ⟨b,off,w,hw,xw⟩ := splitter
  obtain ⟨path,ne,pos,absent⟩ := source b off
  exact ⟨ne,pos,absent,w,xw,receiver_transfer ao ha cross b path hw⟩

end LocalReceiver

namespace LocalMixCore
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalReceiver

lemma unmixed_port {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) {k p : ℕ} (raw : (orIn n C (n+k)).Nonempty) (plain : k ∉ mixing G C)
    (hp : p ∈ (gateAt C k).inputs) : (orIn n C p).Nonempty := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨r,hr⟩ := raw
  obtain ⟨hk,hor,s,hs,_,source⟩ := (raw_gate C k r).mp hr
  obtain ⟨a,b,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  have orn : k ∈ orN G C := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hk,hor,raw_above_singleton hr⟩
  have same : (orIn n C a = ∅) = (orIn n C b = ∅) := by
    by_contra ne
    apply plain
    apply Finset.mem_filter.mpr
    exact ⟨orn,by simpa [opnd,ports] using ne⟩
  have options (w : ℕ) (hw : w ∈ (gateAt C k).inputs) : w=a ∨ w=b := by simpa [ports] using hw
  apply Finset.nonempty_iff_ne_empty.mpr
  intro empty
  have ea : orIn n C a = ∅ := (options p hp).elim (fun eq => eq ▸ empty)
    (fun eq => same.mpr (eq ▸ empty))
  have es : orIn n C s = ∅ := (options s hs).elim (fun eq => eq.symm ▸ ea)
    (fun eq => eq.symm ▸ same.mp ea)
  simp [es] at source

lemma mixing_source {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w, (orIn n C w).Nonempty → val C (List.ofFn x) w = true →
      (∀ v ∈ orIn n C w, x v = false) →
      ∃ k ∈ mixing G C, OrReaches n C w k ∧ (orIn n C (n+k)).Nonempty ∧
        gateVal n C k x = true ∧ ∀ v ∈ orIn n C (n+k), x v = false := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro raw yes absent
    by_cases hw : w < n
    · let v : Fin n := ⟨w,hw⟩
      have mem : v ∈ orIn n C w := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩
      exact (Bool.false_ne_true ((absent v mem).symm.trans ((value_of_input C x v).symm.trans yes))).elim
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      obtain ⟨v,hv⟩ := raw
      obtain ⟨hk,hop,_⟩ := (raw_gate C k v).mp hv
      by_cases mixed : k ∈ mixing G C
      · exact ⟨k,mixed,(orReaches_iff n C k k).mpr ⟨hk,Or.inl rfl⟩,⟨v,hv⟩,yes,absent⟩
      · obtain ⟨p,port,prior,on⟩ := (val_or (n := n) (by simp) hk hop).mp yes
        have absentP (v : Fin n) (h : v ∈ orIn n C p) : x v = false :=
          absent v ((raw_gate C k v).mpr ⟨hk,hop,p,port,prior,h⟩)
        obtain ⟨j,hj,path,atJ,onJ,off⟩ := ih p prior (unmixed_port G ao ⟨v,hv⟩ mixed port) on absentP
        exact ⟨j,hj,(orReaches_iff n C k j).mpr ⟨hk,Or.inr ⟨hop,p,port,prior,path⟩⟩,atJ,onJ,off⟩

lemma path_le {n : ℕ} {C : Circuit} {w v : ℕ} (path : Relation.ReflTransGen (OrStep n C) w v) : v ≤ w := by
  induction path with
  | refl => exact le_rfl
  | tail _ step ih =>
    obtain ⟨_,_,rfl,_,_,lt⟩ := step
    omega

lemma reach_le {n : ℕ} {C : Circuit} {w k : ℕ} (h : OrReaches n C w k) : n+k ≤ w :=
  path_le (orReaches_reach k w h).1

lemma raw_until_mixer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (stop : ℕ)
    (clean : ∀ k ∈ mixing G C, stop ≤ n+k) (x : Fin n → Bool)
    {w : ℕ} (prior : w < stop) (raw : (orIn n C w).Nonempty) (on : val C (List.ofFn x) w = true) :
    ∃ v ∈ orIn n C w, x v = true := by
  by_contra absent
  have off (v : Fin n) (hv : v ∈ orIn n C w) : x v = false := by
    cases h : x v
    · rfl
    · exact (absent ⟨v,hv,h⟩).elim
  obtain ⟨k,hk,path,_⟩ := mixing_source G C ao x w raw on off
  have bound := reach_le path
  have late := clean k hk
  omega

lemma top_needs_mixing {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) {a : ℕ} (top : a ∈ tops G C)
    (cross : ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (nonempty : ∀ b : Fin 2, (side (n := n) C a b).Nonempty)
    {u v : Fin n} (missing : s(u,v) ∈ Ustar G C) (yes : gateVal n C a (pairInput u v) = true) :
    ∃ k ∈ mixing G C, k < a ∧ gateVal n C k (pairInput u v) = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  have port (b : Fin 2) : opnd C a b < n+a := by
    have valid := Finset.mem_range.mp (Finset.mem_filter.mp top).1
    apply ao.2.1 a valid
    obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem valid))
    fin_cases b <;> simp [opnd,ports]
  have blank : ∃ b : Fin 2, ∀ r ∈ side C a b, pairInput u v r = false := by
    by_contra all
    push Not at all
    apply one_blank top cross missing
    exact ⟨by simpa using all 0,by simpa using all 1⟩
  obtain ⟨b,off⟩ := blank
  obtain ⟨k,hk,path,_,on,_⟩ := mixing_source G C ao _ _ (nonempty b) ((top_ports ao top _).mp yes b) off
  have h1 := reach_le path
  have h2 := port b
  exact ⟨k,hk,by omega,on⟩

end LocalMixCore

namespace LocalCone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open LocalLambda

-- The cone recursion, order, and transitivity lemmas are due to willakone, project PR 3111.
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma follow_only_ors {n : ℕ} {C : Circuit} (read : ReadsBack n C) (a : ℕ) :
    ∀ b, InCone n C a b →
      (∀ k, InCone n C a k → InCone n C k b → (gateAt C k).op = GateOp.or) →
      ∃ p ∈ (gateAt C b).inputs, OrReaches n C p a := by
  intro b
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    intro inside clean
    obtain ⟨hb,k,prior,port,h⟩ := (inCone_iff n C a b).mp inside
    have hk : k < C.gates.length := by omega
    have kb := (inCone_iff n C k b).mpr ⟨hb,k,prior,port,Or.inl rfl⟩
    refine ⟨n+k,port,?_⟩
    rcases h with rfl | ak
    · exact (orReaches_iff n C _ _).mpr ⟨hk,Or.inl rfl⟩
    · obtain ⟨p,hp,path⟩ := ih k prior ak (fun j aJ jK => clean j aJ (inCone_trans n C j k jK b kb))
      apply (orReaches_iff n C k a).mpr
      exact ⟨hk,Or.inr ⟨clean k ak kb,p,hp,read k hk p hp,path⟩⟩

end LocalCone

namespace LocalEmptyOR
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalBefore

lemma sole_centreless_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (z : ℕ) (hz : centreless G C = {z})
    (empty : orN G C \ lam G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (trace : ∀ u v : Fin n, s(u,v) ∈ Ustar G C → ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true) :
    ∀ u v : Fin n, s(u,v) ∈ Ustar G C → gateVal n C z (pairInput u v) = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro u v hu
  obtain ⟨a,ha,yes⟩ := trace u v hu
  by_cases hc : a ∈ centreless G C
  · have az : a=z := by simpa [hz] using hc
    exact az ▸ yes
  · have both : ∀ b : Fin 2, (side (n := n) C a b).Nonempty := by
      intro b
      apply Finset.nonempty_iff_ne_empty.mpr
      intro missing
      apply hc
      apply Finset.mem_filter.mpr
      refine ⟨ha,?_⟩
      fin_cases b
      · exact Or.inl missing
      · exact Or.inr missing
    obtain ⟨_,hk,_⟩ := earlier_exception G C ao ha (shape a ha) both hu yes
    simp [empty] at hk

end LocalEmptyOR

namespace LocalBelow
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open LocalTransfer LocalPure

lemma true_top_before {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w < n + C.gates.length,
      (∀ y : Fin n → Bool, val C (List.ofFn y) w = true → graphFun G ∅ y = true) →
      val C (List.ofFn x) w = true →
      ∃ a ∈ tops G C, n + a ≤ w ∧ gateVal n C a x = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro valid below on
    by_cases hw : w < n
    · let v : Fin n := ⟨w,hw⟩
      let one : Fin n → Bool := fun i => decide (i = v)
      have high : val C (List.ofFn one) w = true := by
        change val C (List.ofFn one) v.val = true
        rw [value_of_input]
        simp [one]
      have bad := below one high
      simp [graphFun,one] at bad
    · obtain ⟨k,rfl⟩ : ∃ k, w = n+k := ⟨w-n,by omega⟩
      have hk : k < C.gates.length := by omega
      rcases ao.1 _ (gateAt_mem hk) with hand | hor
      · exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hand,below⟩,le_rfl,on⟩
      · obtain ⟨p,port,prior,yes⟩ := (val_or (n := n) (by simp) hk hor).mp on
        have lower (y : Fin n → Bool) (h : val C (List.ofFn y) p = true) :
            graphFun G ∅ y = true :=
          below y ((val_or (n := n) (by simp) hk hor).mpr ⟨p,port,prior,h⟩)
        obtain ⟨a,ha,limit,yes⟩ := ih p prior (by omega) lower yes
        exact ⟨a,ha,by omega,yes⟩

end LocalBelow

namespace LocalSingleMix
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalBefore LocalBelow LocalReceiver LocalMixCore

lemma mixer_lower {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {m : ℕ} (single : mixing G C = {m}) (j : ℕ) (hj : j ∈ mixing G C) : n+m ≤ n+j := by
  have eq : j=m := by simpa [single] using hj
  omega

lemma routed_single {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ) (single : mixing G C = {m})
    (allraw : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C)
    (cross : ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    {u v : Fin n} (missing : s(u,v) ∈ Ustar G C) (on : gateVal n C a (pairInput u v) = true) :
    (orIn n C (n+m)).Nonempty ∧ gateVal n C m (pairInput u v) = true ∧
    (∀ r ∈ orIn n C (n+m), pairInput u v r = false) ∧
    ∃ w : Fin n, pairInput u v w = true ∧
      (∀ r ∈ orIn n C (n+m), (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj r w) ∧
      ∀ y : Fin n → Bool, gateVal n C m y = true → y w = true → graphFun G ∅ y = true := by
  let seen := fun (b : Fin 2) => ∃ r ∈ side C a b, pairInput u v r = true
  have source (b : Fin 2) (off : ¬seen b) :
      OrReaches n C (opnd C a b) m ∧ (orIn n C (n+m)).Nonempty ∧
      gateVal n C m (pairInput u v) = true ∧ ∀ r ∈ orIn n C (n+m), pairInput u v r = false := by
    have absent (r : Fin n) (hr : r ∈ side C a b) : pairInput u v r = false := by
      cases h : pairInput u v r
      · rfl
      · exact (off ⟨r,hr,h⟩).elim
    obtain ⟨j,hj,prop⟩ := mixing_source G C ao (pairInput u v) _ (sides_nonempty allraw ha b)
      ((top_ports ao ha _).mp on b) absent
    have eq : j = m := by simpa [single] using hj
    exact eq ▸ prop
  have splitter : ∃ b : Fin 2, ¬seen b ∧ seen (1-b) := by
    by_cases h0 : seen 0
    · exact ⟨1,fun h1 => one_blank ha cross missing ⟨h0,h1⟩,h0⟩
    · by_cases h1 : seen 1
      · exact ⟨0,h0,h1⟩
      · obtain ⟨left,⟨r,hr⟩,_⟩ := source 0 h0
        have right := (source 1 h1).1
        exact (G.irrefl (cross r (orIn_subset_of_reaches left hr) r (orIn_subset_of_reaches right hr))).elim
  obtain ⟨b,off,w,hw,xw⟩ := splitter
  obtain ⟨path,ne,pos,absent⟩ := source b off
  exact ⟨ne,pos,absent,w,xw,receiver_transfer ao ha cross b path hw⟩

lemma truth_single {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ) (single : mixing G C = {m})
    (tests : List (Fin n → Bool)) (raw : (orIn n C (n+m)).Nonempty)
    (pos : ∀ x ∈ tests, gateVal n C m x = true)
    (absent : ∀ x ∈ tests, ∀ r ∈ orIn n C (n+m), x r = false)
    (y : Fin n → Bool)
    (lift : ∀ w < n+m, w < n+C.gates.length →
      (∀ x ∈ tests, val C (List.ofFn x) w = true) → val C (List.ofFn y) w = true) :
    gateVal n C m y = true := by
  obtain ⟨r,hr⟩ := raw
  obtain ⟨hk,hor,z,zmem,_,rz⟩ := (raw_gate C m r).mp hr
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  have solve (l d : ℕ) (hl : l ∈ (gateAt C m).inputs) (hd : d ∈ (gateAt C m).inputs)
      (either : ∀ i ∈ (gateAt C m).inputs, i=l ∨ i=d) (hasRaw : (orIn n C l).Nonempty) :
      gateVal n C m y = true := by
    have ld := ao.2.1 m hk l hl
    have dd := ao.2.1 m hk d hd
    apply (val_or (n := n) (by simp) hk hor).mpr
    refine ⟨d,hd,dd,lift d dd (by omega) ?_⟩
    intro x hx
    obtain ⟨s,hs,_,on⟩ := (val_or (n := n) (by simp) hk hor).mp (pos x hx)
    rcases either s hs with rfl | rfl
    · obtain ⟨w,hw,wx⟩ := raw_until_mixer G C ao (n+m) (mixer_lower single)
        x ld hasRaw on
      have off := absent x hx w ((raw_gate C m w).mpr ⟨hk,hor,_,hl,ld,hw⟩)
      simp [off] at wx
    · exact on
  have hp : p ∈ (gateAt C m).inputs := by simp [ports]
  have hq : q ∈ (gateAt C m).inputs := by simp [ports]
  have all (i : ℕ) (hi : i ∈ (gateAt C m).inputs) : i=p ∨ i=q := by simpa [ports] using hi
  rcases all z zmem with rfl | rfl
  · exact solve _ _ hp hq all ⟨r,rz⟩
  · exact solve _ _ hq hp (fun i hi => (all i hi).symm) ⟨r,rz⟩

lemma prefix_with_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m d : ℕ)
    (only : orN G C \ lam G C ⊆ {m,d}) (single : mixing G C = {m})
    (dRaw : d < m → (orIn n C (n+d)).Nonempty)
    (allraw : centreless G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (tests : List (Fin n → Bool)) (u v : Fin n) (e : s(u,v) ∈ Ustar G C) (present : pairInput u v ∈ tests)
    (y : Fin n → Bool) (pins : ∀ i : Fin n, (∀ x ∈ tests, x i = true) → y i = true)
    (clauses : ∀ A : Finset (Fin n), A.Nonempty →
      (∃ c : Fin n, ∀ v ∈ A, (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj c v) →
      (∀ x ∈ tests, ∃ v ∈ A, x v = true) → ∃ v ∈ A, y v = true)
    (extra : (∀ x ∈ tests, ∃ v ∈ orIn n C (n+d), x v = true) → ∃ v ∈ orIn n C (n+d), y v = true) :
    ∀ w < n+m, w < n+C.gates.length →
      (∀ x ∈ tests, val C (List.ofFn x) w = true) → val C (List.ofFn y) w = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  apply tests_through_ands C ao.1 tests (pairInput u v) present y (n+m) pins
  intro k hk prior hor pos
  by_cases below : BelowF G C k
  · obtain ⟨a,ha,le,yes⟩ := true_top_before G C ao (pairInput u v) (n+k) (by omega) below (pos _ present)
    obtain ⟨j,hj,jlt,_⟩ := top_needs_mixing G C ao ha (shape a ha) (sides_nonempty allraw ha) e yes
    have eq : j=m := by simpa [single] using hj
    omega
  · have orn : k ∈ orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hor,below⟩
    have lift (raw : (orIn n C (n+k)).Nonempty)
        (extract : (∀ x ∈ tests, ∃ v ∈ orIn n C (n+k), x v = true) → ∃ v ∈ orIn n C (n+k), y v = true) :
        val C (List.ofFn y) (n+k) = true := by
      obtain ⟨v,hv,on⟩ := extract (fun x hx =>
        raw_until_mixer G C ao (n+m) (mixer_lower single) x prior raw (pos x hx))
      exact raw_pin y hv on
    by_cases normal : k ∈ lam G C
    · obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
      have port : p ∈ (gateAt C k).inputs := by simp [ports]
      obtain ⟨i,hi⟩ := lambda_port ao normal port
      have raw : (orIn n C (n+k)).Nonempty :=
        ⟨i,(raw_gate C k i).mpr ⟨hk,hor,p,port,ao.2.1 k hk p port,hi⟩⟩
      exact lift raw (clauses _ raw (lambda_raw_clause shape normal))
    · have options := only (Finset.mem_sdiff.mpr ⟨orn,normal⟩)
      have eq : k=d := by
        have cases : k=m ∨ k=d := by simpa using options
        omega
      subst k
      exact lift (dRaw (by omega)) extra

end LocalSingleMix

namespace LocalDark
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalReceiver LocalMixCore LocalCone LocalSingleMix

lemma and_cases {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {a : ℕ} (valid : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and) :
    a ∈ junk G C ∨ a ∈ tops G C := by
  letI : DecidableEq GateOp := gateOpDecEq
  by_cases h : a ∈ junk G C
  · exact Or.inl h
  · right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr valid,hand,?_⟩
    intro x yes
    cases f : graphFun G ∅ x
    · exact (h (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr valid,hand,valid,x,yes,f⟩)).elim
    · rfl

lemma and_reach_dark {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (stop : ℕ) (clean : ∀ k ∈ mixing G C, stop ≤ n+k)
    {a : ℕ} (hand : (gateAt C a).op = GateOp.and) :
    ∀ w < stop, OrReaches n C w a → orIn n C w = ∅ := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro prior path
    by_contra notEmpty
    have raw := Finset.nonempty_iff_ne_empty.mpr notEmpty
    have ge := path.1
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    obtain ⟨hk,rest⟩ := (orReaches_iff n C k a).mp path
    have plain : k ∉ mixing G C := fun h => (Nat.not_le_of_lt prior) (clean k h)
    rcases rest with rfl | ⟨_,p,hp,back,reach⟩
    · obtain ⟨v,hv⟩ := raw
      have hor := ((raw_gate C _ v).mp hv).2.1
      simp [hand] at hor
    · have empty := ih p back (by omega) reach
      exact (Finset.nonempty_iff_ne_empty.mp (unmixed_port G ao raw plain hp)) empty

lemma dark_terminal {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w < n+C.gates.length, orIn n C w = ∅ → val C (List.ofFn x) w = true →
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ OrReaches n C w a ∧ gateVal n C a x = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro valid empty yes
    by_cases pin : w < n
    · let v : Fin n := ⟨w,pin⟩
      have mem : v ∈ orIn n C w := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩
      simp [empty] at mem
    · obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
      have hk : k < C.gates.length := by omega
      rcases ao.1 _ (gateAt_mem hk) with hand | hor
      · exact ⟨k,hk,hand,(orReaches_iff n C k k).mpr ⟨hk,Or.inl rfl⟩,yes⟩
      · obtain ⟨p,hp,back,on⟩ := (val_or (n := n) (by simp) hk hor).mp yes
        have dark : orIn n C p = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro v hv
          have h := (raw_gate C k v).mpr ⟨hk,hor,p,hp,back,hv⟩
          simp [empty] at h
        obtain ⟨a,ha,haop,path,pos⟩ := ih p back (by omega) dark on
        exact ⟨a,ha,haop,(orReaches_iff n C k a).mpr ⟨hk,Or.inr ⟨hor,p,hp,back,path⟩⟩,pos⟩

lemma terminal_before_mixer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ) (single : mixing G C = {m}) (allraw : centreless G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    {w : ℕ} (valid : w < n+C.gates.length) (prior : w < n+m) (dark : orIn n C w = ∅)
    {u v : Fin n} (missing : s(u,v) ∈ Ustar G C) (yes : val C (List.ofFn (pairInput u v)) w = true) :
    ∃ a ∈ junk G C, OrReaches n C w a ∧ gateVal n C a (pairInput u v) = true := by
  obtain ⟨a,ha,hand,path,on⟩ := dark_terminal C ao _ w valid dark yes
  rcases and_cases G C ha hand with dirty | top
  · exact ⟨a,dirty,path,on⟩
  · obtain ⟨j,hj,earlier,_⟩ := top_needs_mixing G C ao top (shape a top) (sides_nonempty allraw top) missing on
    have eq : j=m := by simpa [single] using hj
    have ab := reach_le path
    omega

lemma nested_implies {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (tf : TopForm G C)
    (lo hi : ℕ) (J : junk G C = {lo,hi}) (nested : InCone n C lo hi)
    (m : ℕ) (single : mixing G C = {m}) (hh : hi < m) (allraw : centreless G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    {u v : Fin n} (missing : s(u,v) ∈ Ustar G C) (yes : gateVal n C hi (pairInput u v) = true) :
    gateVal n C lo (pairInput u v) = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  have j1 : lo ∈ junk G C := by simp [J]
  have j2 : hi ∈ junk G C := by simp [J]
  have and1 := (Finset.mem_filter.mp j1).2.1
  have and2 := (Finset.mem_filter.mp j2).2.1
  have hib := Finset.mem_range.mp (Finset.mem_filter.mp j2).1
  have clean (k : ℕ) (a : InCone n C lo k) (b : InCone n C k hi) : (gateAt C k).op = GateOp.or := by
    have bound := inCone_lt n C _ _ a
    have range := inCone_lt n C _ _ b
    rcases ao.1 _ (gateAt_mem bound.2) with hand | hor
    · rcases and_cases G C bound.2 hand with dirty | top
      · have two : k=lo ∨ k=hi := by simpa [J] using dirty
        omega
      · exact (tf k bound.2 hi hib hand (Finset.mem_filter.mp top).2.2 and2 b).elim
    · exact hor
  obtain ⟨p,port,path⟩ := follow_only_ors ao.2.1 lo hi nested clean
  obtain ⟨back,on⟩ := (val_and (n := n) (by simp) hib and2).mp yes p port
  have dark := and_reach_dark G C ao (n+m) (mixer_lower single) and1 p (by omega) path
  obtain ⟨a,ja,ap,yesA⟩ := terminal_before_mixer G C ao m single allraw shape (by omega) (by omega) dark missing on
  have two : a=lo ∨ a=hi := by simpa [J] using ja
  have lim := reach_le ap
  have eq : a=lo := by omega
  exact eq ▸ yesA

end LocalDark

namespace LocalNormal
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalReceiver LocalMixCore LocalCone LocalDark

lemma eval_sources {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w < n+C.gates.length, val C (List.ofFn x) w = true ↔
      (∃ v ∈ orIn n C w, x v = true) ∨
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ OrReaches n C w a ∧ gateVal n C a x = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro valid
    constructor
    · intro yes
      by_cases pin : w < n
      · let v : Fin n := ⟨w,pin⟩
        exact Or.inl ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩,(value_of_input C x v).symm.trans yes⟩
      · obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
        have hk : k < C.gates.length := by omega
        rcases ao.1 _ (gateAt_mem hk) with ha | ho
        · exact Or.inr ⟨k,hk,ha,(orReaches_iff n C k k).mpr ⟨hk,Or.inl rfl⟩,yes⟩
        · obtain ⟨p,hp,back,on⟩ := (val_or (n := n) (by simp) hk ho).mp yes
          rcases (ih p back (by omega)).mp on with ⟨v,hv,xv⟩ | ⟨a,ha,hand,path,xa⟩
          · exact Or.inl ⟨v,(raw_gate C k v).mpr ⟨hk,ho,p,hp,back,hv⟩,xv⟩
          · exact Or.inr ⟨a,ha,hand,(orReaches_iff n C k a).mpr ⟨hk,Or.inr ⟨ho,p,hp,back,path⟩⟩,xa⟩
    · rintro (⟨v,hv,on⟩ | ⟨a,_,_,path,on⟩)
      · exact raw_pin x hv on
      · exact upward x (orReaches_reach a w path).1 on

lemma or_inside {n : ℕ} (C : Circuit) (a : ℕ) :
    ∀ k, OrReaches n C (n+k) a → a=k ∨ InCone n C a k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro h
    obtain ⟨valid,eq | ⟨_,p,hp,back,rest⟩⟩ := (orReaches_iff n C k a).mp h
    · exact Or.inl eq
    · have ge := rest.1
      obtain ⟨j,rfl⟩ : ∃ j, p=n+j := ⟨p-n,by omega⟩
      have earlier : j<k := by omega
      exact Or.inr ((inCone_iff n C a k).mpr ⟨valid,j,earlier,hp,ih j earlier rest⟩)

lemma port_in_cone {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {j p a : ℕ}
    (hj : j < C.gates.length) (port : p ∈ (gateAt C j).inputs) (path : OrReaches n C p a) :
    InCone n C a j := by
  have ge := path.1
  have lim := ao.2.1 j hj p port
  obtain ⟨k,rfl⟩ : ∃ k, p=n+k := ⟨p-n,by omega⟩
  exact (inCone_iff n C a j).mpr ⟨hj,k,by omega,port,or_inside C a k path⟩

lemma port_sources {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (tf : TopForm G C)
    (lo hi : ℕ) (J : junk G C = {lo,hi}) {j p : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (port : p ∈ (gateAt C j).inputs) (x : Fin n → Bool) :
    val C (List.ofFn x) p = true ↔ (∃ v ∈ orIn n C p, x v = true) ∨
      (OrReaches n C p lo ∧ gateVal n C lo x = true) ∨ (OrReaches n C p hi ∧ gateVal n C hi x = true) := by
  letI : DecidableEq GateOp := gateOpDecEq
  constructor
  · intro yes
    have earlier := ao.2.1 j hj p port
    rcases (eval_sources C ao x p (by omega)).mp yes with raw | ⟨a,ha,op,path,pos⟩
    · exact Or.inl raw
    · rcases and_cases G C ha op with dirty | top
      · have which : a=lo ∨ a=hi := by simpa [J] using dirty
        rcases which with rfl | rfl
        · exact Or.inr (Or.inl ⟨path,pos⟩)
        · exact Or.inr (Or.inr ⟨path,pos⟩)
      · exact (tf a ha j hj op (Finset.mem_filter.mp top).2.2 hand (port_in_cone ao hj port path)).elim
  · rintro (⟨v,hv,on⟩ | ⟨path,on⟩ | ⟨path,on⟩)
    · exact raw_pin x hv on
    · exact upward x (orReaches_reach lo p path).1 on
    · exact upward x (orReaches_reach hi p path).1 on

lemma input_raw {n : ℕ} (C : Circuit) (v : Fin n) : orIn n C v.val = {v} := by
  letI : DecidableEq GateOp := gateOpDecEq
  ext w
  constructor
  · intro h
    obtain ⟨_,hv | ⟨k,_,reach,_⟩⟩ := Finset.mem_filter.mp h
    · exact Finset.mem_singleton.mpr (Fin.ext hv)
    · have ge := reach.1
      have lt := v.isLt
      omega
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl (congrArg Fin.val (Finset.mem_singleton.mp h))⟩

lemma raw_union {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {k p q : ℕ}
    (hk : k<C.gates.length) (hor : (gateAt C k).op=GateOp.or) (ports : (gateAt C k).inputs=[p,q]) :
    orIn n C (n+k) = orIn n C p ∪ orIn n C q := by
  ext v
  rw [raw_gate,Finset.mem_union]
  constructor
  · rintro ⟨_,_,s,hs,_,hv⟩
    have cases : s=p ∨ s=q := by simpa [ports] using hs
    exact cases.elim (fun t => Or.inl (t ▸ hv)) (fun t => Or.inr (t ▸ hv))
  · rintro (h | h)
    · have hp : p ∈ (gateAt C k).inputs := by simp [ports]
      exact ⟨hk,hor,p,hp,ao.2.1 k hk p hp,h⟩
    · have hq : q ∈ (gateAt C k).inputs := by simp [ports]
      exact ⟨hk,hor,q,hq,ao.2.1 k hk q hq,h⟩

lemma allowable_raw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (allMix : orN G C \ lam G C ⊆ mixing G C)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r) :
    ∀ w, (orIn n C w).Nonempty → (∃ v : Fin n, orIn n C w = {v}) ∨
      ∃ c : Fin n, ∀ v ∈ orIn n C w, (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj c v := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro raw
    by_cases pin : w<n
    · exact Or.inl ⟨⟨w,pin⟩,input_raw C ⟨w,pin⟩⟩
    · obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
      obtain ⟨v,hv⟩ := raw
      obtain ⟨hk,hor,_⟩ := (raw_gate C k v).mp hv
      have orn : k ∈ orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hor,raw_above_singleton hv⟩
      by_cases lamK : k ∈ lam G C
      · exact Or.inr (lambda_raw_clause shape lamK)
      · have mixed := allMix (Finset.mem_sdiff.mpr ⟨orn,lamK⟩)
        obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
        have diff : (orIn n C p = ∅) ≠ (orIn n C q = ∅) := by
          simpa [opnd,ports] using (Finset.mem_filter.mp mixed).2
        have union := raw_union ao hk hor ports
        by_cases hp : orIn n C p = ∅
        · have eq : orIn n C (n+k) = orIn n C q := by simpa [hp] using union
          rw [eq] at hv ⊢
          exact ih q (ao.2.1 k hk q (by simp [ports])) ⟨v,hv⟩
        · have hq : orIn n C q = ∅ := by
            by_contra nq
            exact diff (propext ⟨fun h => (hp h).elim,fun h => (nq h).elim⟩)
          have eq : orIn n C (n+k) = orIn n C p := by simpa [hq] using union
          rw [eq] at hv ⊢
          exact ih p (ao.2.1 k hk p (by simp [ports])) ⟨v,hv⟩

end LocalNormal

namespace LocalInjections
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalReceiver LocalMixCore LocalNormal

def darkChild (n : ℕ) (C : Circuit) (k : ℕ) : ℕ :=
  if orIn n C (opnd C k 0) = ∅ then opnd C k 0 else opnd C k 1

lemma opnd_mem {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {k : ℕ} (hk : k<C.gates.length) (b : Fin 2) :
    opnd C k b ∈ (gateAt C k).inputs := by
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  fin_cases b <;> simp [opnd,ports]

lemma child_port {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {k : ℕ} (hk : k<C.gates.length) :
    darkChild n C k ∈ (gateAt C k).inputs := by
  unfold darkChild
  split
  · exact opnd_mem ao hk 0
  · exact opnd_mem ao hk 1

lemma unique_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) {k p : ℕ} (mix : k ∈ mixing G C) (port : p ∈ (gateAt C k).inputs)
    (dark : orIn n C p = ∅) : darkChild n C k = p := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨orn,diff⟩ := Finset.mem_filter.mp mix
  have hk := Finset.mem_range.mp (Finset.mem_filter.mp orn).1
  obtain ⟨a,b,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  have different : (orIn n C a = ∅) ≠ (orIn n C b = ∅) := by simpa [opnd,ports] using diff
  have which : p=a ∨ p=b := by simpa [ports] using port
  rcases which with rfl | rfl
  · simp [darkChild,opnd,ports,dark]
  · have other : orIn n C a ≠ ∅ := fun h => different (propext ⟨fun _ => dark,fun _ => h⟩)
    simp [darkChild,opnd,ports,other]

lemma mixed_raw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) {k : ℕ} (mix : k ∈ mixing G C) : (orIn n C (n+k)).Nonempty := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨orn,diff⟩ := Finset.mem_filter.mp mix
  obtain ⟨valid,hor,_⟩ := Finset.mem_filter.mp orn
  have hk := Finset.mem_range.mp valid
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  apply Finset.nonempty_iff_ne_empty.mpr
  intro empty
  rw [raw_union ao hk hor ports,Finset.union_eq_empty] at empty
  apply diff
  simp [opnd,ports,empty.1,empty.2]

lemma lambda_raw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) {k : ℕ} (normal : k ∈ lam G C) : (orIn n C (n+k)).Nonempty := by
  letI : DecidableEq GateOp := gateOpDecEq
  have orn := (Finset.mem_filter.mp normal).1
  obtain ⟨valid,hor,_⟩ := Finset.mem_filter.mp orn
  have hk := Finset.mem_range.mp valid
  have port := opnd_mem ao hk 0
  obtain ⟨r,hr⟩ := lambda_port ao normal port
  exact ⟨r,(raw_gate C k r).mpr ⟨hk,hor,_,port,ao.2.1 k hk _ port,hr⟩⟩

lemma dark_direct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (allMix : orN G C \ lam G C ⊆ mixing G C)
    {p a : ℕ} (dark : orIn n C p = ∅) (reach : OrReaches n C p a) (dirty : a ∈ junk G C) :
    p = n+a := by
  letI : DecidableEq GateOp := gateOpDecEq
  have ge := reach.1
  obtain ⟨k,rfl⟩ : ∃ k, p=n+k := ⟨p-n,by omega⟩
  obtain ⟨hk,eq | ⟨hor,_⟩⟩ := (orReaches_iff n C k a).mp reach
  · rw [eq]
  · obtain ⟨_,_,_,x,pos,off⟩ := Finset.mem_filter.mp dirty
    have orn : k ∈ orN G C := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hor,?_⟩
      intro below
      have contradiction := below x (upward x (orReaches_reach _ _ reach).1 pos)
      simp [off] at contradiction
    have raw : (orIn n C (n+k)).Nonempty := by
      by_cases normal : k ∈ lam G C
      · exact lambda_raw G ao normal
      · exact mixed_raw G ao (allMix (Finset.mem_sdiff.mpr ⟨orn,normal⟩))
    exact (Finset.nonempty_iff_ne_empty.mp raw dark).elim

lemma injection {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (allMix : orN G C \ lam G C ⊆ mixing G C)
    {a : ℕ} (dirty : a ∈ junk G C) :
    ∀ w, (orIn n C w).Nonempty → OrReaches n C w a →
      ∃ k ∈ mixing G C, OrReaches n C w k ∧ darkChild n C k = n+a := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro raw reach
    have ge := reach.1
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    obtain ⟨hk,eq | ⟨hor,p,port,back,path⟩⟩ := (orReaches_iff n C k a).mp reach
    · subst a
      obtain ⟨v,hv⟩ := raw
      have hop := ((raw_gate C k v).mp hv).2.1
      have hand := (Finset.mem_filter.mp dirty).2.1
      simp [hand] at hop
    · by_cases nonempty : (orIn n C p).Nonempty
      · obtain ⟨j,hj,jp,child⟩ := ih p back nonempty path
        exact ⟨j,hj,(orReaches_iff n C k j).mpr ⟨hk,Or.inr ⟨hor,p,port,back,jp⟩⟩,child⟩
      · have empty : orIn n C p = ∅ := by simpa using nonempty
        have mixed : k ∈ mixing G C := by
          by_contra normal
          exact nonempty (unmixed_port G ao raw normal port)
        exact ⟨k,mixed,(orReaches_iff n C k k).mpr ⟨hk,Or.inl rfl⟩,
          (unique_empty G ao mixed port empty).trans (dark_direct G C ao allMix empty path dirty)⟩

end LocalInjections

namespace LocalMixerTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalBefore LocalBelow LocalReceiver

lemma earlier_lambda {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {m : ℕ} (single : orN G C \ lam G C = {m}) {k : ℕ} (prior : n+k < n+m)
    (hk : k ∈ orN G C) : k ∈ lam G C := by
  by_contra h
  have mem : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨hk,h⟩
  have eq : k = m := by simpa [single] using mem
  omega

lemma prefix_transfer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ) (single : orN G C \ lam G C = {m})
    (allraw : centreless G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (tests : List (Fin n → Bool)) (u v : Fin n) (e : s(u,v) ∈ Ustar G C) (present : pairInput u v ∈ tests)
    (y : Fin n → Bool) (pins : ∀ i : Fin n, (∀ x ∈ tests, x i = true) → y i = true)
    (clauses : ∀ A : Finset (Fin n), A.Nonempty →
      (∃ c : Fin n, ∀ v ∈ A, (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj c v) →
      (∀ x ∈ tests, ∃ v ∈ A, x v = true) → ∃ v ∈ A, y v = true) :
    ∀ w < n+m, w < n+C.gates.length →
      (∀ x ∈ tests, val C (List.ofFn x) w = true) → val C (List.ofFn y) w = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  apply tests_through_ands C ao.1 tests (pairInput u v) present y (n+m) pins
  intro k hk prior hor pos
  by_cases below : BelowF G C k
  · obtain ⟨a,ha,le,yes⟩ := true_top_before G C ao (pairInput u v) (n+k) (by omega) below
      (pos _ present)
    obtain ⟨j,hj,jlt⟩ := earlier_exception G C ao ha (shape a ha) (sides_nonempty allraw ha) e yes
    have eq : j = m := by simpa [single] using hj
    omega
  · have normal := earlier_lambda single prior (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hor,below⟩)
    obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
    have port : p ∈ (gateAt C k).inputs := by simp [ports]
    obtain ⟨i,hi⟩ := lambda_port ao normal port
    have raw : (orIn n C (n+k)).Nonempty :=
      ⟨i,(raw_gate C k i).mpr ⟨hk,hor,p,port,ao.2.1 k hk p port,hi⟩⟩
    obtain ⟨v,hv,on⟩ := clauses _ raw (lambda_raw_clause shape normal)
      (fun x hx => pure_before G C ao (n+m) (fun _ h => earlier_lambda single h) x _ prior raw (pos x hx))
    exact raw_pin y hv on

lemma mixer_truth {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ) (single : orN G C \ lam G C = {m})
    (tests : List (Fin n → Bool)) (raw : (orIn n C (n+m)).Nonempty)
    (pos : ∀ x ∈ tests, gateVal n C m x = true)
    (absent : ∀ x ∈ tests, ∀ r ∈ orIn n C (n+m), x r = false)
    (y : Fin n → Bool)
    (lift : ∀ w < n+m, w < n+C.gates.length →
      (∀ x ∈ tests, val C (List.ofFn x) w = true) → val C (List.ofFn y) w = true) :
    gateVal n C m y = true := by
  obtain ⟨r,hr⟩ := raw
  obtain ⟨hk,hor,z,zmem,_,rz⟩ := (raw_gate C m r).mp hr
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
  have solve (l d : ℕ) (hl : l ∈ (gateAt C m).inputs) (hd : d ∈ (gateAt C m).inputs)
      (either : ∀ i ∈ (gateAt C m).inputs, i=l ∨ i=d) (hasRaw : (orIn n C l).Nonempty) :
      gateVal n C m y = true := by
    have ld := ao.2.1 m hk l hl
    have dd := ao.2.1 m hk d hd
    apply (val_or (n := n) (by simp) hk hor).mpr
    refine ⟨d,hd,dd,lift d dd (by omega) ?_⟩
    intro x hx
    obtain ⟨s,hs,_,on⟩ := (val_or (n := n) (by simp) hk hor).mp (pos x hx)
    rcases either s hs with rfl | rfl
    · obtain ⟨w,hw,wx⟩ := pure_before G C ao (n+m) (fun _ h => earlier_lambda single h)
        x _ ld hasRaw on
      have off := absent x hx w ((raw_gate C m w).mpr ⟨hk,hor,_,hl,ld,hw⟩)
      simp [off] at wx
    · exact on
  have hp : p ∈ (gateAt C m).inputs := by simp [ports]
  have hq : q ∈ (gateAt C m).inputs := by simp [ports]
  have all (i : ℕ) (hi : i ∈ (gateAt C m).inputs) : i=p ∨ i=q := by simpa [ports] using hi
  rcases all z zmem with rfl | rfl
  · exact solve _ _ hp hq all ⟨r,rz⟩
  · exact solve _ _ hq hp (fun i hi => (all i hi).symm) ⟨r,rz⟩

end LocalMixerTransfer

namespace LocalCentreTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open LocalTransfer LocalPure LocalBefore LocalBelow LocalLambda LocalEmptyOR

lemma only_accepting_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) {z : ℕ} (hz : centreless G C = {z})
    (empty : orN G C \ lam G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    {a : ℕ} (ha : a ∈ tops G C) {u v : Fin n} (hu : s(u,v) ∈ Ustar G C)
    (yes : gateVal n C a (pairInput u v) = true) : a = z := by
  letI : DecidableEq GateOp := gateOpDecEq
  by_contra ne
  have both (b : Fin 2) : (side (n := n) C a b).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro blank
    apply ne
    have mem : a ∈ centreless G C := by
      apply Finset.mem_filter.mpr
      refine ⟨ha,?_⟩
      fin_cases b
      · exact Or.inl blank
      · exact Or.inr blank
    simpa [hz] using mem
  obtain ⟨_,hk,_⟩ := earlier_exception G C ao ha (shape a ha) both hu yes
  simp [empty] at hk

lemma centreless_transfer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (z : ℕ) (hz : centreless G C = {z})
    (empty : orN G C \ lam G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (trace : ∀ u v : Fin n, s(u,v) ∈ Ustar G C → ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true)
    (tests : List (Fin n → Bool)) (first : Fin n → Bool) (present : first ∈ tests)
    (pairs : ∀ x ∈ tests, ∃ u v, s(u,v) ∈ Ustar G C ∧ x = pairInput u v)
    (y : Fin n → Bool) (input : ∀ i : Fin n, (∀ x ∈ tests, x i = true) → y i = true)
    (clauses : ∀ A : Finset (Fin n), A.Nonempty →
      (∃ c : Fin n, ∀ v ∈ A, (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj c v) →
      (∀ x ∈ tests, ∃ v ∈ A, x v = true) → ∃ v ∈ A, y v = true) :
    graphFun G ∅ y = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  have atZ : z ∈ centreless G C := hz ▸ Finset.mem_singleton_self _
  have top : z ∈ tops G C := (Finset.mem_filter.mp atZ).1
  obtain ⟨valid,andZ,belowZ⟩ := Finset.mem_filter.mp top
  have zbound : z < C.gates.length := Finset.mem_range.mp valid
  have all (k : ℕ) (outside : k ∈ orN G C) : k ∈ lam G C := by
    by_contra h
    have mem : k ∈ orN G C \ lam G C := Finset.mem_sdiff.mpr ⟨outside,h⟩
    simp [empty] at mem
  apply belowZ
  apply tests_through_ands C ao.1 tests first present y (n+z+1) input _ (n+z) (by omega) (by omega)
  · intro x hx
    obtain ⟨u,v,missing,rfl⟩ := pairs x hx
    exact sole_centreless_true G C ao z hz empty shape trace u v missing
  · intro k hk before hor pos
    by_cases lower : BelowF G C k
    · obtain ⟨u,v,missing,eq⟩ := pairs first present
      have hfirst := pos first present
      rw [eq] at hfirst
      obtain ⟨a,ha,lim,yes⟩ := true_top_before G C ao (pairInput u v) (n+k) (by omega) lower hfirst
      have az := only_accepting_top G C ao hz empty shape ha missing yes
      have kz : k = z := by omega
      rw [kz,andZ] at hor
      contradiction
    · have normal := all k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hor,lower⟩)
      obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
      have port : p ∈ (gateAt C k).inputs := by simp [ports]
      obtain ⟨i,hi⟩ := lambda_port ao normal port
      have raw : (orIn n C (n+k)).Nonempty :=
        ⟨i,(raw_gate C k i).mpr ⟨hk,hor,p,port,ao.2.1 k hk p port,hi⟩⟩
      obtain ⟨v,hv,on⟩ := clauses _ raw (lambda_raw_clause shape normal)
        (fun x hx => pure_before G C ao (n+z+1) (fun j _ => all j) x _ before raw (pos x hx))
      exact raw_pin y hv on

end LocalCentreTransfer

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
namespace LocalCoverProfile

abbrev V := Fin 11
abbrev Edge := Sym2 V

def code : List ℕ := [9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97]
abbrev graph : SimpleGraph V := edgeGraph 11 (code.map fun n => (n / 11,n % 11))
def pairs : List (V × V) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
  (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def missing (K : Finset V) : Finset Edge :=
  ((pairs.filter fun p => decide (p.1 ∉ K ∧ p.2 ∉ K)).map fun p => s(p.1,p.2)).toFinset

abbrev fourProfiles (K : Finset V) (U : Finset Edge) : Prop :=
  (K = {5,7,8,10} ∧ U = {s(0,9),s(1,4),s(3,6)}) ∨
  (K = {7,8,9,10} ∧ U = {s(1,4),s(2,5),s(3,6)}) ∨
  (K = {6,8,9,10} ∧ U = {s(1,4),s(2,5),s(3,7)}) ∨
  (K = {3,8,9,10} ∧ U = {s(1,4),s(2,5),s(6,7)})

lemma listed_edges : ∀ p ∈ pairs, graph.Adj p.1 p.2 := by
  unfold graph
  decide +kernel

lemma missing_subset {U : Finset Edge} {K : Finset V}
    (h : (graph.deleteEdges (U : Set Edge)).IsVertexCover (K : Set V)) : missing K ⊆ U := by
  intro e he
  simp only [missing, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at he
  obtain ⟨p, ⟨hp, ha, hb⟩, rfl⟩ := he
  by_contra outside
  exact (h (SimpleGraph.deleteEdges_adj.mpr ⟨listed_edges p hp,outside⟩)).elim ha hb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma four_check : ∀ K : Finset V, K.card ≤ 4 → (missing K).card ≤ 3 →
    K.card = 4 ∧ (missing K).card = 3 ∧ fourProfiles K (missing K) := by decide +kernel

lemma four_only {U : Finset Edge} {K : Finset V} (hU : U.card = 3)
    (hK : (graph.deleteEdges (U : Set Edge)).IsVertexCover (K : Set V)) (hk : K.card ≤ 4) :
    K.card = 4 ∧ fourProfiles K U := by
  have sub := missing_subset hK
  obtain ⟨four,three,profile⟩ := four_check K hk ((Finset.card_le_card sub).trans hU.le)
  have eq : missing K = U := Finset.eq_of_subset_of_card_le sub (by omega)
  exact ⟨four,eq ▸ profile⟩

end LocalCoverProfile

namespace LocalCoverProfile

def edgeAt (i : Fin 16) : Edge :=
  let p := pairs.getD i.val (0,0)
  s(p.1,p.2)

lemma edgeAt_inj : Function.Injective edgeAt := by
  intro i j
  exact (by decide +kernel : ∀ i j : Fin 16, edgeAt i = edgeAt j → i = j) i j

lemma edgeAt_covers (e : Edge) (h : e ∈ graph.edgeFinset) : ∃ i : Fin 16, edgeAt i = e := by
  revert e
  decide +kernel

lemma actual_triple {U : Finset Edge} (sub : U ⊆ graph.edgeFinset) (card : U.card = 3) :
    ∃ i j k : Fin 16, i < j ∧ j < k ∧ U = {edgeAt i,edgeAt j,edgeAt k} := by
  let J : Finset (Fin 16) := Finset.univ.filter fun i => edgeAt i ∈ U
  have im : J.image edgeAt = U := by
    ext e
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hi).2
    · intro h
      obtain ⟨i,rfl⟩ := edgeAt_covers e (sub h)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩
  have size : J.card = 3 := by
    rw [← im,Finset.card_image_of_injective _ edgeAt_inj] at card
    exact card
  obtain ⟨i,j,k,sort⟩ := List.length_eq_three.mp ((J.length_sort (· ≤ ·)).trans size)
  have ord : List.Pairwise (· < ·) [i,j,k] := sort ▸ J.sortedLT_sort.pairwise
  have hij := (List.pairwise_cons.mp ord).1 j (by simp)
  have hjk := (List.pairwise_cons.mp (List.pairwise_cons.mp ord).2).1 k (by simp)
  have base : J = {i,j,k} := by
    calc J = (J.sort (· ≤ ·)).toFinset := (J.sort_toFinset _).symm
         _ = _ := by rw [sort]; simp
  refine ⟨i,j,k,hij,hjk,?_⟩
  rw [← im,base]
  simp

end LocalCoverProfile

namespace LocalMasks
open LocalMixerCertificate

def mask {n : ℕ} (A : Finset (Fin n)) : ℕ :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin n => decide (i ∈ A)))).toNat

lemma mask_small {n : ℕ} (A : Finset (Fin n)) : mask A < 2^n := by
  simpa [mask] using (BitVec.ofBoolListLE (List.ofFn (fun i : Fin n => decide (i ∈ A)))).isLt

lemma mask_bit {n : ℕ} (A : Finset (Fin n)) (v : Fin n) :
    (mask A).testBit v.val = decide (v ∈ A) := by
  unfold mask
  rw [BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD]

lemma mask_above {n : ℕ} (A : Finset (Fin n)) {i : ℕ} (h : n ≤ i) :
    (mask A).testBit i = false := by
  simp [mask,BitVec.testBit_toNat,List.getD_eq_getElem?_getD,Nat.not_lt.mpr h]

lemma hit_iff {n : ℕ} (A : Finset (Fin n)) (x : ℕ) :
    hit (mask A) x = true ↔ ∃ v ∈ A, x.testBit v.val = true := by
  constructor
  · intro h
    have ne : mask A &&& x ≠ 0 := by simpa [hit] using h
    obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero ne
    rw [Nat.testBit_and,Bool.and_eq_true_iff] at hi
    by_cases bound : i < n
    · let v : Fin n := ⟨i,bound⟩
      exact ⟨v,of_decide_eq_true ((mask_bit A v).symm.trans hi.1),hi.2⟩
    · have off := mask_above A (Nat.le_of_not_gt bound)
      exact (Bool.false_ne_true (off.symm.trans hi.1)).elim
  · rintro ⟨v,hv,hx⟩
    simp only [hit,bne_iff_ne]
    intro zero
    have h := congrArg (fun a : ℕ => a.testBit v.val) zero
    simp [Nat.testBit_and,mask_bit,hv,hx] at h

lemma within_iff {n : ℕ} (A : Finset (Fin n)) (x : ℕ) :
    within (mask A) x = true ↔ ∀ v ∈ A, x.testBit v.val = true := by
  constructor
  · intro h v hv
    apply within_bit h
    simp [mask_bit,hv]
  · intro incl
    apply beq_iff_eq.mpr
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    by_cases bound : i < n
    · let v : Fin n := ⟨i,bound⟩
      change ((mask A).testBit v.val && x.testBit v.val) = (mask A).testBit v.val
      by_cases h : v ∈ A
      · simp [mask_bit,h,incl v h]
      · simp [mask_bit,h]
    · simp [mask_above A (Nat.le_of_not_gt bound)]

end LocalMasks

namespace LocalGraphRows
open LocalCoverProfile LocalMixerCertificate LocalMasks
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def rowAt (i : Fin 16) := rows.getD i.val 0
def endpointAt (i : Fin 16) := pairs.getD i.val (0,0)
def testsAt (i : Fin 16) := pairInput (endpointAt i).1 (endpointAt i).2

lemma row_injective : Function.Injective rowAt := by
  intro i j
  exact (by decide +kernel : ∀ i j : Fin 16, rowAt i = rowAt j → i = j) i j

lemma row_mem : ∀ i, rowAt i ∈ rows := by decide +kernel

lemma row_matches : ∀ (i : Fin 16) (v : V), (rowAt i).testBit v.val = testsAt i v := by
  decide +kernel

lemma singleton_pin : ∀ v : V, mask {v} ∈ pins := by decide +kernel

lemma negative_graph : ∀ x ∈ negatives, graphFun graph ∅ (fun v => x.testBit v.val) = false := by
  decide +kernel

lemma edge_contributor : ∀ c v : V, graph.Adj c v →
    ∃ i : Fin 16, edgeAt i = s(c,v) ∧ hit (rowAt i) (1 <<< c.val) = true ∧
      ((rowAt i) ^^^ (1 <<< c.val)).testBit v.val = true := by decide +kernel

def appendNeighbor (pin acc edge : ℕ) :=
  if hit edge pin then acc ||| (edge ^^^ pin) else acc

def neighbor (es : List ℕ) (c : V) := es.foldl (appendNeighbor (1 <<< c.val)) 0

lemma neighbor_mem (es : List ℕ) (c : V) : neighbor es c ∈ neighbors es := by
  apply List.mem_map.mpr
  refine ⟨1 <<< c.val,List.mem_map.mpr ⟨c.val,List.mem_range.mpr c.isLt,rfl⟩,rfl⟩

lemma keep_bit (es : List ℕ) (pin i z : ℕ) (on : z.testBit i = true) :
    (es.foldl (appendNeighbor pin) z).testBit i = true := by
  induction es generalizing z with
  | nil => exact on
  | cons e es ih =>
    apply ih
    by_cases h : hit e pin = true <;> simp [appendNeighbor,h,Nat.testBit_or,on]

lemma contributor_bit (es : List ℕ) (pin i e z : ℕ) (mem : e ∈ es)
    (touches : hit e pin = true) (on : (e ^^^ pin).testBit i = true) :
    (es.foldl (appendNeighbor pin) z).testBit i = true := by
  induction es generalizing z with
  | nil => simp at mem
  | cons a es ih =>
    rcases List.mem_cons.mp mem with rfl | mem
    · rw [List.foldl_cons]
      apply keep_bit es pin i
      simp [appendNeighbor,touches,Nat.testBit_or,on]
    · exact ih _ mem

lemma all_adjacent (c v : V) (h : graph.Adj c v) : (neighbor rows c).testBit v.val = true := by
  obtain ⟨i,_,hit,bit⟩ := edge_contributor c v h
  exact contributor_bit rows _ _ _ 0 (row_mem i) hit bit

lemma remaining_adjacent (i j k : Fin 16) (c v : V)
    (h : (graph.deleteEdges ({edgeAt i,edgeAt j,edgeAt k} : Finset Edge)).Adj c v) :
    (neighbor (rows.filter fun e => !([rowAt i,rowAt j,rowAt k].contains e)) c).testBit v.val = true := by
  obtain ⟨adj,notRemoved⟩ := SimpleGraph.deleteEdges_adj.mp h
  obtain ⟨l,edge,hit,bit⟩ := edge_contributor c v adj
  apply contributor_bit _ _ _ (rowAt l) 0 _ hit bit
  apply List.mem_filter.mpr
  refine ⟨row_mem l,?_⟩
  have distinct (t : Fin 16) (ht : edgeAt t ∈ ({edgeAt i,edgeAt j,edgeAt k} : Finset Edge)) :
      rowAt l ≠ rowAt t := by
    intro eq
    have lt := row_injective eq
    apply notRemoved
    rw [← edge,lt]
    exact ht
  have h1 := distinct i (by simp)
  have h2 := distinct j (by simp)
  have h3 := distinct k (by simp)
  simp [h1,h2,h3]

end LocalGraphRows

namespace LocalCentreCase
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalMasks LocalCentreTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

def tripleRows (i j k : Fin 16) := [rowAt i,rowAt j,rowAt k]
def tripleTests (i j k : Fin 16) := [testsAt i,testsAt j,testsAt k]
def omitted (i j k : Fin 16) : Finset Edge := {edgeAt i,edgeAt j,edgeAt k}

lemma live_of_set (i j k : Fin 16) (A : Finset V) (nonempty : A.Nonempty)
    (form : mask A ∈ pins ∨ ∃ c : V, ∀ v ∈ A, (graph.deleteEdges (omitted i j k : Set Edge)).Adj c v)
    (on : ∀ x ∈ tripleTests i j k, ∃ v ∈ A, x v = true) :
    mask A ∈ liveClauses (tripleRows i j k) := by
  obtain ⟨v,hv⟩ := nonempty
  have nz : mask A ≠ 0 := by
    intro zero
    have h := mask_bit A v
    simp [zero,hv] at h
  let allowed := fun (xs : List ℕ) => pins.contains (mask A) || xs.any (within (mask A))
  have permit : allowed (neighbors rows) = true ∧ allowed (available (tripleRows i j k)) = true := by
    rcases form with pin | ⟨c,adj⟩
    · have hp := List.contains_iff_mem.mpr pin
      exact ⟨Bool.or_eq_true_iff.mpr (Or.inl hp),Bool.or_eq_true_iff.mpr (Or.inl hp)⟩
    · constructor
      · apply Bool.or_eq_true_iff.mpr
        right
        apply List.any_eq_true.mpr
        refine ⟨neighbor rows c,neighbor_mem _ _,(within_iff A _).mpr ?_⟩
        exact fun v hv => all_adjacent c v (SimpleGraph.deleteEdges_adj.mp (adj v hv)).1
      · apply Bool.or_eq_true_iff.mpr
        right
        apply List.any_eq_true.mpr
        refine ⟨_,neighbor_mem _ c,(within_iff A _).mpr ?_⟩
        exact fun v hv => remaining_adjacent i j k c v (adj v hv)
  have touched (l : Fin 16) (hl : testsAt l ∈ tripleTests i j k) :
      hit (mask A) (rowAt l) = true := by
    obtain ⟨v,hv,high⟩ := on (testsAt l) hl
    exact (hit_iff _ _).mpr ⟨v,hv,(row_matches l v).trans high⟩
  apply List.mem_filter.mpr
  refine ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (mask_small A),
    Bool.and_eq_true_iff.mpr ⟨bne_iff_ne.mpr nz,permit.1⟩⟩,?_⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_,permit.2⟩
  apply List.all_eq_true.mpr
  intro e he
  simp [tripleRows] at he
  rcases he with rfl | rfl | rfl <;> apply touched <;> simp [tripleTests]

lemma centreless_case (C : Circuit) (ao : IsAO2 11 C) (z : ℕ) (hz : centreless graph C = {z})
    (empty : orN graph C \ lam graph C = ∅)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, gateVal 11 C a (pairInput u v) = true)
    (three : (Ustar graph C).card = 3) : False := by
  obtain ⟨i,j,k,hij,hjk,edges⟩ := actual_triple (U := Ustar graph C) Finset.sdiff_subset three
  have eq : Ustar graph C = omitted i j k := edges
  let u := tripleRows i j k
  let tests := tripleTests i j k
  obtain ⟨y,negative,_,all⟩ := raw_conjunction_obstruction hij hjk k.isLt u rfl
    (liveClauses u) (fun _ h => h)
  have accepts (A : Finset V) (ne : A.Nonempty)
      (form : mask A ∈ pins ∨ ∃ c : V, ∀ v ∈ A, (graph.deleteEdges (Ustar graph C : Set Edge)).Adj c v)
      (meet : ∀ x ∈ tests, ∃ v ∈ A, x v = true) : ∃ v ∈ A, y.testBit v.val = true := by
    rw [eq] at form
    have live := live_of_set i j k A ne form meet
    have h := List.all_eq_true.mp all (mask A) live
    apply (hit_iff A y).mp
    simpa [hit,Nat.and_comm] using h
  have pos := centreless_transfer graph C ao z hz empty shape trace tests (testsAt i)
    (by simp [tests,tripleTests]) (y := fun v => y.testBit v.val)
  have pairs (x : V → Bool) (hx : x ∈ tests) : ∃ a b, s(a,b) ∈ Ustar graph C ∧ x = pairInput a b := by
    have single (l : Fin 16) (mem : edgeAt l ∈ omitted i j k) :
        ∃ a b, s(a,b) ∈ Ustar graph C ∧ testsAt l = pairInput a b :=
      ⟨(endpointAt l).1,(endpointAt l).2,eq ▸ mem,rfl⟩
    simp [tests,tripleTests] at hx
    rcases hx with rfl | rfl | rfl <;> apply single <;> simp [omitted]
  have pinsOk (v : V) (all : ∀ x ∈ tests, x v = true) : y.testBit v.val = true := by
    obtain ⟨w,hw,h⟩ := accepts {v} (by simp) (Or.inl (singleton_pin v))
      (fun x hx => ⟨v,Finset.mem_singleton_self v,all x hx⟩)
    simpa [Finset.mem_singleton.mp hw] using h
  have bad := pos pairs pinsOk (fun A h c => accepts A h (Or.inr c))
  simp [negative_graph y negative] at bad

end LocalCentreCase

namespace LocalMixerCase
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalMasks LocalCentreCase
open LocalLambda LocalReceiver LocalMixerTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

lemma live_semantics (i j k : Fin 16) (U : Finset Edge) (eq : U = omitted i j k)
    (y : ℕ) (all : (liveClauses (tripleRows i j k)).all (hit y) = true) :
    (∀ v : V, (∀ x ∈ tripleTests i j k, x v = true) → y.testBit v.val = true) ∧
    (∀ A : Finset V, A.Nonempty →
      (∃ c : V, ∀ v ∈ A, (graph.deleteEdges (U : Set Edge)).Adj c v) →
      (∀ x ∈ tripleTests i j k, ∃ v ∈ A, x v = true) → ∃ v ∈ A, y.testBit v.val = true) := by
  have accepts (A : Finset V) (ne : A.Nonempty)
      (form : mask A ∈ pins ∨ ∃ c : V, ∀ v ∈ A, (graph.deleteEdges (U : Set Edge)).Adj c v)
      (meet : ∀ x ∈ tripleTests i j k, ∃ v ∈ A, x v = true) : ∃ v ∈ A, y.testBit v.val = true := by
    rw [eq] at form
    have h := List.all_eq_true.mp all (mask A) (live_of_set i j k A ne form meet)
    apply (hit_iff A y).mp
    simpa [hit,Nat.and_comm] using h
  refine ⟨?_,fun A h c => accepts A h (Or.inr c)⟩
  intro v yes
  obtain ⟨w,hw,h⟩ := accepts {v} (by simp) (Or.inl (singleton_pin v))
    (fun x hx => ⟨v,Finset.mem_singleton_self v,yes x hx⟩)
  simpa [Finset.mem_singleton.mp hw] using h

lemma mixer_case (C : Circuit) (ao : IsAO2 11 C) (m : ℕ) (single : orN graph C \ lam graph C = {m})
    (allraw : centreless graph C = ∅)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, gateVal 11 C a (pairInput u v) = true)
    (three : (Ustar graph C).card = 3) : False := by
  obtain ⟨i,j,k,hij,hjk,edges⟩ := actual_triple (U := Ustar graph C) Finset.sdiff_subset three
  have eq : Ustar graph C = omitted i j k := edges
  let tests := tripleTests i j k
  let u := tripleRows i j k
  let routed := fun (x : V → Bool) => (orIn 11 C (11+m)).Nonempty ∧ gateVal 11 C m x = true ∧
    (∀ r ∈ orIn 11 C (11+m), x r = false) ∧ ∃ w : V, x w = true ∧
      (∀ r ∈ orIn 11 C (11+m), (graph.deleteEdges (Ustar graph C : Set Edge)).Adj r w) ∧
      ∀ y : V → Bool, gateVal 11 C m y = true → y w = true → graphFun graph ∅ y = true
  have forIndex (l : Fin 16) (mem : edgeAt l ∈ omitted i j k) : routed (testsAt l) := by
    have missing : s((endpointAt l).1,(endpointAt l).2) ∈ Ustar graph C := eq ▸ mem
    obtain ⟨a,ha,on⟩ := trace _ _ missing
    exact route_pair graph C ao m single allraw ha (shape a ha) missing on
  have routes (x : V → Bool) (hx : x ∈ tests) : routed x := by
    simp [tests,tripleTests] at hx
    rcases hx with rfl | rfl | rfl <;> apply forIndex <;> simp [omitted]
  have fst : testsAt i ∈ tests := by simp [tests,tripleTests]
  have raw := (routes _ fst).1
  obtain ⟨c,hc⟩ := raw
  let N := neighbor (rows.filter fun e => !(u.contains e)) c
  have supported : N ∈ available u := neighbor_mem _ _
  apply one_mixer_obstruction hij hjk k.isLt u rfl (liveClauses u) (fun _ h => h) N supported
  intro e he
  have source : ∃ l : Fin 16, e = rowAt l ∧ testsAt l ∈ tests := by
    simp [u,tripleRows] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨i,rfl,fst⟩
    · exact ⟨j,rfl,by simp [tests,tripleTests]⟩
    · exact ⟨k,rfl,by simp [tests,tripleTests]⟩
  obtain ⟨l,rfl,hl⟩ := source
  obtain ⟨w,high,adj,positive⟩ := (routes _ hl).2.2.2
  have cw := adj c hc
  rw [eq] at cw
  have wn : N.testBit w.val = true := remaining_adjacent i j k c w cw
  have we := (row_matches l w).trans high
  refine ⟨w.val,by simp [Nat.testBit_and,wn,we],?_⟩
  intro y neg wy
  cases all : (liveClauses u).all (hit y)
  · rfl
  · obtain ⟨pins,clauses⟩ := live_semantics i j k _ eq y all
    have firstEdge : s((endpointAt i).1,(endpointAt i).2) ∈ Ustar graph C := eq ▸ (by
      change edgeAt i ∈ omitted i j k
      simp [omitted])
    have lift := prefix_transfer graph C ao m single allraw shape tests _ _ firstEdge fst
      (fun v => y.testBit v.val) pins clauses
    have atM := mixer_truth graph C ao m single tests ⟨c,hc⟩
      (fun x hx => (routes x hx).2.1) (fun x hx => (routes x hx).2.2.1)
      (fun v => y.testBit v.val) lift
    have bad := positive (fun v => y.testBit v.val) atM wy
    simp [negative_graph y neg] at bad

end LocalMixerCase

namespace LocalMixerCertificate

def testsFor (u : List ℕ) : List ℕ :=
  u.foldr (fun e rest => (pins.filter (hit e)).flatMap fun v => rest.map fun z => v ||| z) [0]

def witnessesFor (u : List ℕ) : List ℕ :=
  negatives.filter fun x => (allClauses.filter (useful u (available u))).all (hit x)

def meetsSelected (w ts : List ℕ) (J : Finset (Fin 8)) : Bool :=
  w.any fun x => decide (∀ j ∈ J, hit x (ts.getD j.val 0) = true)

def triple0 : List ℕ := [513, 18, 72]
def triple1 : List ℕ := [18, 36, 72]
def triple2 : List ℕ := [18, 36, 136]
def triple3 : List ℕ := [18, 36, 192]
end LocalMixerCertificate

namespace LocalMixerCertificate

def hasSmallCover (u : List ℕ) : Bool :=
  let es := rows.filter fun e => !u.contains e
  (List.range 2048).any fun m => decide ((pins.filter (hit m)).length ≤ 5) && es.all (hit m)

def extraPass (u : List ℕ) : Bool :=
  let ns := available u
  let base := witnessesFor u
  (testsFor u).all fun q =>
    let filtered := base.filter (hit q)
    let seen := filtered.foldl (fun a b => a ||| b) 0
    !filtered.isEmpty && ns.all fun n => u.any fun e => within (n &&& e) seen

def validExtra (u : List ℕ) : Bool := extraPass u || !hasSmallCover u

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add0 : (triplesFrom 0).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add1 : (triplesFrom 1).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add2 : (triplesFrom 2).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add3 : (triplesFrom 3).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add4 : (triplesFrom 4).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add5 : (triplesFrom 5).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add6 : (triplesFrom 6).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add7 : (triplesFrom 7).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add8 : (triplesFrom 8).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add9 : (triplesFrom 9).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add10 : (triplesFrom 10).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add11 : (triplesFrom 11).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add12 : (triplesFrom 12).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add13 : (triplesFrom 13).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add14 : (triplesFrom 14).all validExtra = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma add15 : (triplesFrom 15).all validExtra = true := by decide +kernel

lemma extra_for_small_cover {i j k : ℕ} (hij : i < j) (hjk : j < k) (hk : k < 16)
    (u : List ℕ) (hu : u = [rows.getD i 0,rows.getD j 0,rows.getD k 0])
    (hc : hasSmallCover u = true) : extraPass u = true := by
  have hi : i < 16 := by omega
  have batch : (triplesFrom i).all validExtra = true := by
    interval_cases i
    · exact add0
    · exact add1
    · exact add2
    · exact add3
    · exact add4
    · exact add5
    · exact add6
    · exact add7
    · exact add8
    · exact add9
    · exact add10
    · exact add11
    · exact add12
    · exact add13
    · exact add14
    · exact add15
  have mem : u ∈ triplesFrom i := by
    rw [hu]
    apply List.mem_flatMap.mpr
    refine ⟨j, List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),decide_eq_true hij⟩, ?_⟩
    exact List.mem_map.mpr ⟨k,List.mem_filter.mpr ⟨List.mem_range.mpr hk,decide_eq_true hjk⟩,rfl⟩
  have good := List.all_eq_true.mp batch u mem
  simpa only [validExtra,hc,Bool.not_true,Bool.or_false] using good

end LocalMixerCertificate

namespace LocalSmallCover
open LocalCoverProfile LocalMixerCertificate LocalMasks LocalGraphRows LocalCentreCase
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma pin_count (K : Finset V) : (pins.filter (hit (mask K))).length = K.card := by
  revert K
  decide +kernel

lemma all_rows_indexed : ∀ e ∈ rows, ∃ l : Fin 16, rowAt l = e := by decide +kernel
lemma all_rows_adjacent : ∀ l : Fin 16, graph.Adj (endpointAt l).1 (endpointAt l).2 := by decide +kernel

lemma small_cover (i j k : Fin 16) (K : Finset V) (size : K.card ≤ 5)
    (cover : (graph.deleteEdges (omitted i j k : Set Edge)).IsVertexCover (K : Set V)) :
    hasSmallCover (tripleRows i j k) = true := by
  apply List.any_eq_true.mpr
  refine ⟨mask K,List.mem_range.mpr (mask_small K),Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
  · exact decide_eq_true ((pin_count K).symm ▸ size)
  · apply List.all_eq_true.mpr
    intro e he
    obtain ⟨row,keep⟩ := List.mem_filter.mp he
    obtain ⟨l,rfl⟩ := all_rows_indexed _ row
    have keepEdge : edgeAt l ∉ omitted i j k := by
      intro removed
      simp [omitted] at removed
      have dropped : rowAt l ∈ tripleRows i j k := by
        rcases removed with hi | hj | hk
        · have := edgeAt_inj hi
          simp [tripleRows,this]
        · have := edgeAt_inj hj
          simp [tripleRows,this]
        · have := edgeAt_inj hk
          simp [tripleRows,this]
      have forbid : rowAt l ∉ tripleRows i j k := by simpa using keep
      exact forbid dropped
    have adj : (graph.deleteEdges (omitted i j k : Set Edge)).Adj (endpointAt l).1 (endpointAt l).2 :=
      SimpleGraph.deleteEdges_adj.mpr ⟨all_rows_adjacent l,keepEdge⟩
    apply (hit_iff _ _).mpr
    rcases cover adj with h | h
    · exact ⟨_,h,(row_matches l _).trans (by simp [testsAt,pairInput])⟩
    · exact ⟨_,h,(row_matches l _).trans (by simp [testsAt,pairInput])⟩

lemma mask_union {n : ℕ} (A B : Finset (Fin n)) : mask (A ∪ B) = mask A ||| mask B := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  by_cases h : i < n
  · let v : Fin n := ⟨i,h⟩
    change (mask (A ∪ B)).testBit v.val = ((mask A).testBit v.val || (mask B).testBit v.val)
    simp [mask_bit]
  · simp [mask_above _ (Nat.le_of_not_gt h)]

lemma select_cons {e p q : ℕ} {es : List ℕ} (pin : p ∈ pins) (met : hit e p = true)
    (old : q ∈ testsFor es) : p ||| q ∈ testsFor (e::es) := by
  exact List.mem_flatMap.mpr ⟨p,List.mem_filter.mpr ⟨pin,met⟩,List.mem_map.mpr ⟨q,old,rfl⟩⟩

lemma select_three (i j k : Fin 16) (A : Finset V)
    (on : ∀ x ∈ tripleTests i j k, ∃ v ∈ A, x v = true) :
    ∃ q ∈ testsFor (tripleRows i j k), ∀ y : ℕ, hit q y = true → ∃ v ∈ A, y.testBit v.val = true := by
  obtain ⟨a,ha,ya⟩ := on (testsAt i) (by simp [tripleTests])
  obtain ⟨b,hb,yb⟩ := on (testsAt j) (by simp [tripleTests])
  obtain ⟨c,hc,yc⟩ := on (testsAt k) (by simp [tripleTests])
  have singlePin (w : V) (l : Fin 16) (yes : testsAt l w = true) : hit (rowAt l) (mask {w}) = true := by
    have h := (hit_iff ({w} : Finset V) (rowAt l)).mpr
      ⟨w,Finset.mem_singleton_self w,(row_matches l w).trans yes⟩
    simpa [hit,Nat.and_comm] using h
  let B : Finset V := {a} ∪ ({b} ∪ {c})
  refine ⟨mask B,?_,?_⟩
  · have mem := select_cons (singleton_pin a) (singlePin a i ya)
        (select_cons (singleton_pin b) (singlePin b j yb)
          (select_cons (singleton_pin c) (singlePin c k yc) (show 0 ∈ testsFor [] from List.mem_singleton.mpr rfl)))
    simpa only [B,tripleRows,mask_union,Nat.or_zero] using mem
  · intro y h
    obtain ⟨v,hv,pos⟩ := (hit_iff B y).mp h
    refine ⟨v,?_,pos⟩
    simp [B] at hv
    rcases hv with rfl | rfl | rfl <;> assumption

end LocalSmallCover

namespace LocalWireWords
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalPure LocalTransfer LocalReceiver LocalMixCore LocalNormal LocalInjections LocalMasks LocalMixerCertificate
open LocalSignatures LocalPrune LocalCoverProfile LocalGraphRows LocalCentreCase LocalSmallCover

def packed (rs : List ℕ) (f : ℕ → Bool) := (BitVec.ofBoolListLE (rs.map f)).toNat
def rowInput {n : ℕ} (r : ℕ) : Fin n → Bool := fun v => r.testBit v.val
def wireWord (n : ℕ) (C : Circuit) (rs : List ℕ) (w : ℕ) :=
  packed rs (fun r => val C (List.ofFn (rowInput (n := n) r)) w)

lemma packed_bit (rs : List ℕ) (f : ℕ → Bool) (i : ℕ) :
    (packed rs f).testBit i = if h : i < rs.length then f rs[i] else false := by
  unfold packed
  rw [BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE]
  by_cases h : i<rs.length <;> simp [List.getD_eq_getElem?_getD,h]

lemma pack_congr (rs : List ℕ) {f g : ℕ → Bool} (h : ∀ r ∈ rs, f r = g r) : packed rs f = packed rs g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [packed_bit,packed_bit]
  split
  · exact h _ (by simp)
  · rfl

lemma pack_and (rs : List ℕ) (f g : ℕ → Bool) :
    packed rs (fun x => f x && g x) = packed rs f &&& packed rs g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases h : i<rs.length <;> simp [packed_bit,h]

lemma pack_or (rs : List ℕ) (f g : ℕ → Bool) :
    packed rs (fun x => f x || g x) = packed rs f ||| packed rs g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  by_cases h : i<rs.length <;> simp [packed_bit,h]

lemma pack_off (rs : List ℕ) : packed rs (fun _ => false) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i<rs.length <;> simp [packed_bit,h]

lemma pack_optional (rs : List ℕ) (f g : ℕ → Bool) (flag : Bool) :
    packed rs (fun x => f x || (flag && g x)) = LocalPrune.optional (packed rs f) (packed rs g) flag := by
  cases flag <;> simp [LocalPrune.optional,pack_or]

lemma product_word {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {k p q : ℕ} (valid : k<C.gates.length)
    (hand : (gateAt C k).op=GateOp.and) (ports : (gateAt C k).inputs=[p,q]) (rs : List ℕ) :
    wireWord n C rs (n+k) = wireWord n C rs p &&& wireWord n C rs q := by
  unfold wireWord
  rw [← pack_and]
  apply pack_congr
  intro r _
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true_iff,val_and (n := n) (by simp) valid hand]
  constructor
  · intro h
    exact ⟨(h p (by simp [ports])).2,(h q (by simp [ports])).2⟩
  · rintro ⟨hp,hq⟩ t ht
    have which : t=p ∨ t=q := by simpa [ports] using ht
    refine ⟨ao.2.1 k valid t ht,?_⟩
    exact which.elim (fun eq => eq.symm ▸ hp) (fun eq => eq.symm ▸ hq)

lemma port_word {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (tf : TopForm G C) (lo hi : ℕ) (J : junk G C = {lo,hi})
    {j p : ℕ} (valid : j<C.gates.length) (hand : (gateAt C j).op=GateOp.and)
    (port : p ∈ (gateAt C j).inputs) (rs : List ℕ) :
    wireWord n C rs p =
      LocalPrune.optional (LocalPrune.optional (signature rs (mask (orIn n C p))) (wireWord n C rs (n+lo)) (decide (OrReaches n C p lo)))
        (wireWord n C rs (n+hi)) (decide (OrReaches n C p hi)) := by
  unfold wireWord
  change packed rs _ = LocalPrune.optional (LocalPrune.optional (packed rs (hit (mask (orIn n C p)))) _ _) _ _
  rw [← pack_optional,← pack_optional]
  apply pack_congr
  intro r _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true_iff,Bool.and_eq_true_iff,decide_eq_true_eq,hit_iff]
  simpa only [gateVal,LocalTransfer.val,rowInput,or_assoc] using
    (port_sources G C ao tf lo hi J valid hand port (rowInput r))

lemma dirty_words {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (tf : TopForm G C) (lo hi : ℕ) (order : lo<hi)
    (J : junk G C = {lo,hi}) (rs raw : List ℕ)
    (support : ∀ p : ℕ, signature rs (mask (orIn n C p)) ∈ raw) :
    ∃ r ∈ raw, ∃ s ∈ raw, ∃ l ∈ raw, ∃ t ∈ raw, ∃ lf rf : Bool,
      wireWord n C rs (n+lo) = r &&& s ∧
      wireWord n C rs (n+hi) = LocalPrune.optional l (r &&& s) lf &&& LocalPrune.optional t (r &&& s) rf := by
  letI : DecidableEq GateOp := gateOpDecEq
  have jl : lo ∈ junk G C := by simp [J]
  have jh : hi ∈ junk G C := by simp [J]
  have low := Finset.mem_filter.mp jl
  have high := Finset.mem_filter.mp jh
  have lb := Finset.mem_range.mp low.1
  have hb := Finset.mem_range.mp high.1
  obtain ⟨p,q,lp⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem lb))
  obtain ⟨l,t,hp⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hb))
  let w := fun j => signature rs (mask (orIn n C j))
  let d := wireWord n C rs (n+lo)
  have lowPort (v : ℕ) (pv : v ∈ (gateAt C lo).inputs) : wireWord n C rs v = w v := by
    have back := ao.2.1 lo lb v pv
    have noL : ¬OrReaches n C v lo := fun h => Nat.not_le_of_lt back (reach_le h)
    have noH : ¬OrReaches n C v hi := by
      intro h
      have lim := reach_le h
      omega
    simpa [LocalPrune.optional,noL,noH,w] using port_word G C ao tf lo hi J lb low.2.1 pv rs
  have highPort (v : ℕ) (pv : v ∈ (gateAt C hi).inputs) :
      wireWord n C rs v = LocalPrune.optional (w v) d (decide (OrReaches n C v lo)) := by
    have back := ao.2.1 hi hb v pv
    have noH : ¬OrReaches n C v hi := fun h => Nat.not_le_of_lt back (reach_le h)
    simpa [noH,LocalPrune.optional,w,d] using port_word G C ao tf lo hi J hb high.2.1 pv rs
  have dword : d = w p &&& w q := by
    rw [show d = _ from product_word ao lb low.2.1 lp rs,lowPort p (by simp [lp]),lowPort q (by simp [lp])]
  refine ⟨w p,support p,w q,support q,w l,support l,w t,support t,decide (OrReaches n C l lo),decide (OrReaches n C t lo),dword,?_⟩
  rw [product_word ao hb high.2.1 hp rs,highPort l (by simp [hp]),highPort t (by simp [hp]),dword]

end LocalWireWords

namespace LocalActive
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalReceiver LocalMixCore LocalNormal LocalInjections LocalMasks
open LocalMixerCertificate LocalSignatures LocalPrune LocalWireWords

def active (n : ℕ) (C : Circuit) (lo hi w m : ℕ) : Bool :=
  decide (OrReaches n C w m) && (darkChild n C m == n+lo || darkChild n C m == n+hi)

def tag (n : ℕ) (C : Circuit) (lo hi m : ℕ) := if darkChild n C m = n+hi then hi else lo

lemma active_path {n : ℕ} {C : Circuit} {lo hi w m : ℕ} (h : active n C lo hi w m = true) :
    OrReaches n C w m := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

lemma selected {n : ℕ} {C : Circuit} {lo hi m g : ℕ} (guard : g=lo ∨ g=hi)
    (child : darkChild n C m = n+g) : tag n C lo hi m = g := by
  unfold tag
  split
  next eq => omega
  next other =>
    rcases guard with rfl | rfl
    · rfl
    · exact (other child).elim

lemma has_child {n : ℕ} {C : Circuit} {lo hi w m : ℕ} (h : active n C lo hi w m = true) :
    darkChild n C m = n + tag n C lo hi m := by
  have opts : darkChild n C m = n+lo ∨ darkChild n C m = n+hi := by
    simpa using (Bool.and_eq_true_iff.mp h).2
  unfold tag
  split
  next eq => exact eq
  next neq => exact opts.resolve_right neq

lemma effect {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) {lo hi w m : ℕ} (mixed : m ∈ mixing G C) (used : active n C lo hi w m = true)
    (x : Fin n → Bool) (on : gateVal n C (tag n C lo hi m) x = true) : val C (List.ofFn x) w = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  have orn := (Finset.mem_filter.mp mixed).1
  obtain ⟨valid,hor,_⟩ := Finset.mem_filter.mp orn
  have hk := Finset.mem_range.mp valid
  have port := child_port ao hk
  apply upward x (orReaches_reach _ _ (active_path used)).1
  apply (val_or (n := n) (by simp) hk hor).mpr
  refine ⟨_,port,ao.2.1 m hk _ port,?_⟩
  rw [has_child used]
  exact on

lemma two_sources {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (tf : TopForm G C) (lo hi : ℕ) (J : junk G C={lo,hi})
    (m k : ℕ) (pair : mixing G C = {m,k}) (allMix : orN G C \ lam G C ⊆ mixing G C)
    {j p : ℕ} (valid : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (port : p ∈ (gateAt C j).inputs) (raw : (orIn n C p).Nonempty) (x : Fin n → Bool) :
    val C (List.ofFn x) p = true ↔ (∃ v ∈ orIn n C p, x v = true) ∨
      (active n C lo hi p m = true ∧ gateVal n C (tag n C lo hi m) x = true) ∨
      (active n C lo hi p k = true ∧ gateVal n C (tag n C lo hi k) x = true) := by
  have source (g : ℕ) (two : g=lo ∨ g=hi) (path : OrReaches n C p g) (on : gateVal n C g x = true) :
      ∃ h ∈ mixing G C, active n C lo hi p h = true ∧ gateVal n C (tag n C lo hi h) x = true := by
    have dirty : g ∈ junk G C := by simpa [J] using two
    obtain ⟨h,mixed,reach,child⟩ := injection G C ao allMix dirty p raw path
    refine ⟨h,mixed,?_,(selected two child).symm ▸ on⟩
    rcases two with rfl | rfl <;> simp [active,reach,child]
  constructor
  · intro on
    rcases (port_sources G C ao tf lo hi J valid hand port x).mp on with pin | lower | upper
    · exact Or.inl pin
    · obtain ⟨h,mixed,act⟩ := source lo (Or.inl rfl) lower.1 lower.2
      have cases : h=m ∨ h=k := by simpa [pair] using mixed
      exact Or.inr (cases.elim (fun eq => Or.inl (eq ▸ act)) (fun eq => Or.inr (eq ▸ act)))
    · obtain ⟨h,mixed,act⟩ := source hi (Or.inr rfl) upper.1 upper.2
      have cases : h=m ∨ h=k := by simpa [pair] using mixed
      exact Or.inr (cases.elim (fun eq => Or.inl (eq ▸ act)) (fun eq => Or.inr (eq ▸ act)))
  · rintro (⟨v,hv,on⟩ | ⟨used,on⟩ | ⟨used,on⟩)
    · exact raw_pin x hv on
    · exact effect G C ao (by simp [pair]) used x on
    · exact effect G C ao (by simp [pair]) used x on

lemma two_source_word {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (tf : TopForm G C) (lo hi : ℕ) (J : junk G C={lo,hi})
    (m k : ℕ) (pair : mixing G C = {m,k}) (allMix : orN G C \ lam G C ⊆ mixing G C)
    {j p : ℕ} (valid : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (port : p ∈ (gateAt C j).inputs) (raw : (orIn n C p).Nonempty) (rs : List ℕ) :
    wireWord n C rs p = LocalPrune.optional
      (LocalPrune.optional (signature rs (mask (orIn n C p)))
        (wireWord n C rs (n+tag n C lo hi m)) (active n C lo hi p m))
      (wireWord n C rs (n+tag n C lo hi k)) (active n C lo hi p k) := by
  unfold wireWord
  change packed rs _ = LocalPrune.optional (LocalPrune.optional (packed rs (hit (mask (orIn n C p)))) _ _) _ _
  rw [← pack_optional,← pack_optional]
  apply pack_congr
  intro r _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true_iff,Bool.and_eq_true_iff,hit_iff]
  simpa only [gateVal,LocalTransfer.val,rowInput,or_assoc] using
    (two_sources G C ao tf lo hi J m k pair allMix valid hand port raw (rowInput r))

end LocalActive

namespace LocalCenters
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalReceiver LocalCoverProfile

def orientation (C : Circuit) (a : ℕ) : Fin 2 :=
  if (side (n := 11) C a 0).card = 1 then 0 else 1

noncomputable def vertex (C : Circuit) (a : ℕ) : V :=
  if h : ∃ v : V, side C a (orientation C a) = {v} then h.choose else 0

def leaves (C : Circuit) (a : ℕ) := side (n := 11) C a (1-orientation C a)
noncomputable def centers (C : Circuit) := (tops graph C).image (vertex C)

def thin (C : Circuit) : Prop := ∀ a ∈ tops graph C,
  (side (n := 11) C a 0).card ≤ 1 ∨ (side (n := 11) C a 1).card ≤ 1

lemma two_sides (b : Fin 2) : b=0 ∨ b=1 := by fin_cases b <;> simp

lemma singleton_center {C : Circuit} (nz : centreless graph C = ∅) (narrow : thin C)
    {a : ℕ} (ha : a ∈ tops graph C) :
    side C a (orientation C a) = {vertex C a} := by
  have pos (b : Fin 2) := Finset.card_pos.mpr (sides_nonempty nz ha b)
  have one : (side (n := 11) C a (orientation C a)).card=1 := by
    unfold orientation
    split
    next yes => exact yes
    next no =>
      have choices := narrow a ha
      have l := pos 0
      have r := pos 1
      omega
  have h := Finset.card_eq_one.mp one
  simpa [vertex,dif_pos h] using h.choose_spec

lemma center_member {C : Circuit} {a : ℕ} (ha : a ∈ tops graph C) : vertex C a ∈ centers C :=
  Finset.mem_image.mpr ⟨a,ha,rfl⟩

lemma raw_star {C : Circuit} (nz : centreless graph C = ∅) (narrow : thin C)
    {u v : V} (h : s(u,v) ∈ starEdges graph C) :
    ∃ a ∈ tops graph C, (u=vertex C a ∧ v ∈ leaves C a) ∨ (v=vertex C a ∧ u ∈ leaves C a) := by
  obtain ⟨a,ha,im⟩ := Finset.mem_biUnion.mp h
  obtain ⟨p,hp,eq⟩ := Finset.mem_image.mp im
  obtain ⟨left,right⟩ := Finset.mem_product.mp hp
  have order : p=(u,v) ∨ p=(v,u) := Sym2.mk_eq_mk_iff.mp eq
  have sides (x y : V) (hx : x ∈ side C a 0) (hy : y ∈ side C a 1) :
      (x=vertex C a ∧ y ∈ leaves C a) ∨ (y=vertex C a ∧ x ∈ leaves C a) := by
    have fixed := singleton_center nz narrow ha
    rcases two_sides (orientation C a) with h0 | h1
    · rw [h0] at fixed
      exact Or.inl ⟨Finset.mem_singleton.mp (fixed ▸ hx),by simpa [leaves,h0] using hy⟩
    · rw [h1] at fixed
      exact Or.inr ⟨Finset.mem_singleton.mp (fixed ▸ hy),by simpa [leaves,h1] using hx⟩
  refine ⟨a,ha,?_⟩
  rcases order with rfl | rfl
  · exact sides u v left right
  · exact (sides v u left right).symm

lemma residual_star {C : Circuit} {u v : V} (adj : (graph.deleteEdges (Ustar graph C : Set Edge)).Adj u v) :
    s(u,v) ∈ starEdges graph C := by
  obtain ⟨edge,retained⟩ := SimpleGraph.deleteEdges_adj.mp adj
  by_contra lost
  apply retained
  exact Finset.mem_sdiff.mpr ⟨by simpa using edge,lost⟩

lemma center_cover {C : Circuit} (nz : centreless graph C = ∅) (narrow : thin C) :
    (graph.deleteEdges (Ustar graph C : Set Edge)).IsVertexCover (centers C : Set V) := by
  intro u v adj
  obtain ⟨a,ha,h | h⟩ := raw_star nz narrow (residual_star adj)
  · exact Or.inl (h.1.symm ▸ center_member ha)
  · exact Or.inr (h.1.symm ▸ center_member ha)

lemma private_leaf {C : Circuit} (nz : centreless graph C = ∅) (narrow : thin C) (num : (tops graph C).card ≤ 5)
    {a : ℕ} (ha : a ∈ tops graph C) (size : 5 ≤ (centers C).card) {v : V}
    (adj : (graph.deleteEdges (Ustar graph C : Set Edge)).Adj (vertex C a) v) (outside : v ∉ centers C) :
    v ∈ leaves C a := by
  have bound : (centers C).card ≤ (tops graph C).card := Finset.card_image_le
  have inj : Set.InjOn (vertex C) (tops graph C : Set ℕ) := Finset.injOn_of_card_image_eq (le_antisymm bound (num.trans size))
  obtain ⟨b,hb,h | h⟩ := raw_star nz narrow (residual_star adj)
  · have ab := inj ha hb h.1
    exact ab.symm ▸ h.2
  · exact (outside (h.1.symm ▸ center_member hb)).elim

lemma leaf_adj {C : Circuit} (nz : centreless graph C = ∅) (narrow : thin C)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    {a : ℕ} (ha : a ∈ tops graph C) {v : V} (leaf : v ∈ leaves C a) :
    (graph.deleteEdges (Ustar graph C : Set Edge)).Adj (vertex C a) v := by
  have cen : vertex C a ∈ side C a (orientation C a) := (singleton_center nz narrow ha) ▸ Finset.mem_singleton_self _
  rcases two_sides (orientation C a) with h0 | h1
  · rw [h0] at cen
    exact SimpleGraph.deleteEdges_adj.mpr (cross_outside ha (shape a ha) cen (by simpa [leaves,h0] using leaf))
  · rw [h1] at cen
    exact (SimpleGraph.deleteEdges_adj.mpr (cross_outside ha (shape a ha) (by simpa [leaves,h1] using leaf) cen)).symm

end LocalCenters

namespace LocalGeoBridge
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalMasks LocalCentreCase LocalSmallCover
open LocalNormal LocalWireWords LocalSignatures LocalWordGeometry

def remain (i j k : Fin 16) := rows.filter (fun e => !((tripleRows i j k).contains e))

lemma support_mask (i j k : Fin 16) (A : Finset V) (ne : A.Nonempty)
    (supported : (∃ v : V, A={v}) ∨ ∃ c : V, ∀ v ∈ A, (graph.deleteEdges (omitted i j k : Set Edge)).Adj c v) :
    mask A ∈ rawMasks (tripleRows i j k) := by
  obtain ⟨v,hv⟩ := ne
  have nz : mask A ≠ 0 := by
    intro h
    have t := mask_bit A v
    simp [h,hv] at t
  let ok := fun (ns : List ℕ) => pins.contains (mask A) || ns.any (within (mask A))
  have h : ok (neighbors rows) = true ∧ ok (available (tripleRows i j k)) = true := by
    rcases supported with ⟨w,rfl⟩ | ⟨c,adj⟩
    · have pin := List.contains_iff_mem.mpr (singleton_pin w)
      exact ⟨Bool.or_eq_true_iff.mpr (Or.inl pin),Bool.or_eq_true_iff.mpr (Or.inl pin)⟩
    · constructor
      · apply Bool.or_eq_true_iff.mpr
        right
        exact List.any_eq_true.mpr ⟨_,neighbor_mem rows c,(within_iff _ _).mpr
          (fun v hv => all_adjacent c v (SimpleGraph.deleteEdges_adj.mp (adj v hv)).1)⟩
      · apply Bool.or_eq_true_iff.mpr
        right
        exact List.any_eq_true.mpr ⟨_,neighbor_mem _ c,(within_iff _ _).mpr (fun v hv => remaining_adjacent i j k c v (adj v hv))⟩
  exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (mask_small A),
    Bool.and_eq_true_iff.mpr ⟨bne_iff_ne.mpr nz,h.1⟩⟩,h.2⟩

lemma zero_mask : mask (∅ : Finset V) = 0 := by decide +kernel

lemma raw_word_member (C : Circuit) (ao : IsAO2 11 C) (allMix : orN graph C \ lam graph C ⊆ mixing graph C)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    (i j k : Fin 16) (eq : Ustar graph C = omitted i j k) (w : ℕ) :
    let u := tripleRows i j k
    signature (u ++ negatives) (mask (orIn 11 C w)) ∈ 0 :: (rawMasks u).map (signature (u ++ negatives)) := by
  intro u
  by_cases ne : (orIn 11 C w).Nonempty
  · have classif := allowable_raw graph C ao allMix shape w ne
    rw [eq] at classif
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_,support_mask i j k _ ne classif,rfl⟩)
  · have empty : orIn 11 C w=∅ := by simpa using ne
    rw [empty,zero_mask]
    have z : signature (u ++ negatives) 0 = 0 := by
      calc signature (u ++ negatives) 0 = packed (u ++ negatives) (fun _ => false) :=
             pack_congr _ (fun r _ => by simp [hit])
           _ = 0 := pack_off _
    rw [z]
    exact List.mem_cons_self

lemma inverse_fold (es : List ℕ) (c q z : ℕ)
    (bit : (es.foldl (appendNeighbor c) z).testBit q = true) :
    z.testBit q = true ∨ ∃ e ∈ es, hit e c = true ∧ (e ^^^ c).testBit q = true := by
  induction es generalizing z with
  | nil => exact Or.inl bit
  | cons e es ih =>
    rcases ih (appendNeighbor c z e) bit with first | ⟨a,ha,hc,on⟩
    · by_cases hc : hit e c = true
      · have h : z.testBit q = true ∨ (e ^^^ c).testBit q = true := by simpa [appendNeighbor,hc,Nat.testBit_or] using first
        exact h.elim Or.inl (fun g => Or.inr ⟨e,List.mem_cons_self,hc,g⟩)
      · exact Or.inl (by simpa [appendNeighbor,hc] using first)
    · exact Or.inr ⟨a,List.mem_cons_of_mem _ ha,hc,on⟩

lemma fixed_edge_test : ∀ (l : Fin 16) (c v : V), hit (rowAt l) (1 <<< c.val) = true →
    (rowAt l ^^^ (1 <<< c.val)).testBit v.val = true → edgeAt l = s(c,v) ∧ graph.Adj c v := by decide +kernel

lemma actual_neighbor (i j k : Fin 16) (c v : V)
    (h : (neighbor (remain i j k) c).testBit v.val = true) :
    (graph.deleteEdges (omitted i j k : Set Edge)).Adj c v := by
  rcases inverse_fold _ _ _ 0 h with zero | ⟨e,he,hit,bit⟩
  · simp at zero
  · obtain ⟨row,keep⟩ := List.mem_filter.mp he
    obtain ⟨l,rfl⟩ := all_rows_indexed e row
    obtain ⟨edge,adj⟩ := fixed_edge_test l c v hit bit
    refine SimpleGraph.deleteEdges_adj.mpr ⟨adj,?_⟩
    intro gone
    have remove : edgeAt l ∈ omitted i j k := edge.symm ▸ gone
    have out : rowAt l ∉ tripleRows i j k := by simpa using keep
    apply out
    simp [omitted] at remove
    rcases remove with p | p | p <;> have eq := edgeAt_inj p <;> simp [tripleRows,eq]

lemma singleton_word (v : V) : mask {v} = 1 <<< v.val := by revert v; decide +kernel

lemma pin_neighbors (es : List ℕ) (c : V) : (mask {c},neighbor es c) ∈ pins.zip (neighbors es) := by
  let xs := pins.zip (neighbors es)
  have h : c.val < xs.length := by simpa [xs,pins,neighbors] using c.isLt
  have val : xs[c.val] = (mask {c},neighbor es c) := by
    simp [xs,pins,neighbors,neighbor,singleton_word]
    rfl
  exact val ▸ List.getElem_mem h

lemma needed_within (i j k : Fin 16) (K L : Finset V) (c : V)
    (privateNeighbors : 5 ≤ K.card → ∀ v : V, (graph.deleteEdges (omitted i j k : Set Edge)).Adj c v → v ∉ K → v ∈ L) :
    within (neededMask (mask K) (neighbor (remain i j k) c)) (mask L) = true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro t
  rw [Nat.testBit_and]
  by_cases h : (neededMask (mask K) (neighbor (remain i j k) c)).testBit t = true
  · have sz : 5 ≤ K.card := by
      by_contra small
      have sm : K.card < 5 := Nat.lt_of_not_ge small
      simp [neededMask,pin_count,sm] at h
    have bit : (neighbor (remain i j k) c).testBit t = true ∧ ((2047 : ℕ) ^^^ mask K).testBit t = true := by
      simpa [neededMask,pin_count,Nat.not_lt.mpr sz,Nat.testBit_and] using h
    have maxBit (q : ℕ) : (2047 : ℕ).testBit q = decide (q<11) := Nat.testBit_two_pow_sub_one 11 q
    have bound : t<11 := by
      by_contra over
      have no := mask_above K (Nat.le_of_not_gt over)
      have contrary := bit.2
      simp [Nat.testBit_xor,maxBit,over,no] at contrary
    let v : V := ⟨t,bound⟩
    have outside : v ∉ K := by
      intro inside
      have one : (mask K).testBit t = true := (mask_bit K v).trans (decide_eq_true inside)
      have contrary := bit.2
      simp [Nat.testBit_xor,maxBit,bound,one] at contrary
    have leaf := privateNeighbors sz v (actual_neighbor i j k c v bit.1) outside
    have yes : (mask L).testBit t = true := (mask_bit L v).trans (decide_eq_true leaf)
    simp [h,yes]
  · have off : (neededMask (mask K) (neighbor (remain i j k) c)).testBit t = false := by simpa using h
    simp [off]

end LocalGeoBridge

namespace LocalAnchorChoice
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalMasks LocalCentreCase
open LocalGeoBridge LocalSignatures LocalWordGeometry
open PEqualNP.MetaComplexity.NestedCover

def mark (a b z i : ℕ) := if a.testBit i then z ||| (b <<< (11*i)) else z

lemma keepMark (is : List ℕ) (a b q z : ℕ) (h : z.testBit q = true) :
    (is.foldl (mark a b) z).testBit q = true := by
  induction is generalizing z with
  | nil => exact h
  | cons v is ih =>
    apply ih
    by_cases t : a.testBit v = true <;> simp [mark,t,Nat.testBit_or,h]

lemma chosenMark (is : List ℕ) (a b z i j : ℕ) (mem : i ∈ is) (ha : a.testBit i = true) (hb : b.testBit j = true) :
    (is.foldl (mark a b) z).testBit (11*i+j) = true := by
  induction is generalizing z with
  | nil => simp at mem
  | cons v is ih =>
    rcases List.mem_cons.mp mem with rfl | rest
    · rw [List.foldl_cons]
      apply keepMark is a b
      simp [mark,ha,Nat.testBit_or,Nat.testBit_shiftLeft,hb]
    · exact ih _ rest

lemma anchor_live {a b : ℕ} (c d : V) (hc : a.testBit c.val = true) (hd : b.testBit d.val = true) :
    (anchorPairs a b).testBit (11*c.val+d.val) = true :=
  chosenMark (List.range 11) a b 0 c.val d.val (List.mem_range.mpr c.isLt) hc hd

def position (l r : Bool) : Fin 3 := if l then 1 else if r then 2 else 0

lemma location (c a : V) (L : Finset V) (l r : Bool)
    (left : l=true → a=c) (right : r=true → a ∈ L) :
    (anchorAt (mask {c}) (mask L) (position l r).val).testBit a.val = true := by
  cases l with
  | true =>
    have eq := left rfl
    simp [anchorAt,position,mask_bit,eq]
  | false =>
    cases r with
    | true => simp [anchorAt,position,mask_bit,right rfl]
    | false =>
      change (2047 : ℕ).testBit a.val = true
      exact (Nat.testBit_two_pow_sub_one 11 a.val).trans (decide_eq_true a.isLt)

def makeChoice (u : List ℕ) (c : V) (L : Finset V) (x y : Fin 3) : TopChoice :=
  ⟨signature (u++negatives) (mask {c}),signature (u++negatives) (mask L),x.val,y.val,
    anchorPairs (anchorAt (mask {c}) (mask L) x.val) (anchorAt (mask {c}) (mask L) y.val)⟩

lemma choice_mem (i j k : Fin 16) (K L : Finset V) (c : V) (center : c ∈ K) (ne : L.Nonempty)
    (adj : ∀ v ∈ L, (graph.deleteEdges (omitted i j k : Set Edge)).Adj c v)
    (required : 5 ≤ K.card → ∀ v : V, (graph.deleteEdges (omitted i j k : Set Edge)).Adj c v → v ∉ K → v ∈ L)
    (s t : Fin 3) : makeChoice (tripleRows i j k) c L s t ∈ options (tripleRows i j k) (mask K) := by
  let n := neighbor (remain i j k) c
  have allowed := support_mask i j k L ne (Or.inr ⟨c,adj⟩)
  have inside : within (mask L) n = true := (within_iff _ _).mpr (fun v hv => remaining_adjacent i j k c v (adj v hv))
  have essential := needed_within i j k K L c required
  have pin : hit (mask {c}) (mask K) = true := (hit_iff _ _).mpr
    ⟨c,Finset.mem_singleton_self c,(mask_bit K c).trans (decide_eq_true center)⟩
  apply List.mem_flatMap.mpr
  refine ⟨(mask {c},n),List.mem_filter.mpr ⟨pin_neighbors _ _,pin⟩,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨mask L,List.mem_filter.mpr ⟨allowed,Bool.and_eq_true_iff.mpr ⟨inside,essential⟩⟩,?_⟩
  exact List.mem_flatMap.mpr ⟨s.val,List.mem_range.mpr s.isLt,List.mem_map.mpr ⟨t.val,List.mem_range.mpr t.isLt,rfl⟩⟩

lemma top_flags (u : List ℕ) (c : V) (L : Finset V) (a b : ℕ) (al ar bl br : Bool)
    (exA : ¬(al=true ∧ ar=true)) (exB : ¬(bl=true ∧ br=true)) :
    topValue (makeChoice u c L (position al ar) (position bl br)) a b =
      LocalPrune.optional (LocalPrune.optional (signature (u++negatives) (mask {c})) a al) b bl &&&
        LocalPrune.optional (LocalPrune.optional (signature (u++negatives) (mask L)) a ar) b br := by
  cases al <;> cases ar <;> cases bl <;> cases br <;>
    simp_all [topValue,makeChoice,position,LocalPrune.optional,
      TopChoice.left,TopChoice.right,TopChoice.useA,TopChoice.useB]

end LocalAnchorChoice

namespace LocalTopWord
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalCoverProfile LocalLambda LocalTransfer LocalReceiver LocalNormal LocalActive LocalCenters
open LocalWireWords LocalCentreCase LocalMixerCertificate LocalMasks LocalSignatures LocalWordGeometry
open LocalAnchorChoice

lemma oriented_product {C : Circuit} (ao : IsAO2 11 C) {a : ℕ} (ha : a ∈ tops graph C)
    (b : Fin 2) (rs : List ℕ) :
    wireWord 11 C rs (11+a) = wireWord 11 C rs (opnd C a b) &&& wireWord 11 C rs (opnd C a (1-b)) := by
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨mem,hand,_⟩ := Finset.mem_filter.mp ha
  have valid := Finset.mem_range.mp mem
  obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem valid))
  have word := product_word ao valid hand ports rs
  fin_cases b <;> simpa [opnd,ports,Nat.and_comm] using word

lemma real_choice (C : Circuit) (ao : IsAO2 11 C) (tf : TopForm graph C)
    (lo hi m k : ℕ) (J : junk graph C={lo,hi}) (pair : mixing graph C={m,k})
    (allMix : orN graph C \ lam graph C ⊆ mixing graph C)
    (nz : centreless graph C = ∅) (narrow : thin C) (num : (tops graph C).card ≤ 5)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    (i j h : Fin 16) (eq : Ustar graph C=omitted i j h) (α β : V)
    (hα : α ∈ orIn 11 C (11+m)) (hβ : β ∈ orIn 11 C (11+k))
    {a : ℕ} (ha : a ∈ tops graph C) :
    let u := tripleRows i j h
    let rs := u ++ negatives
    ∃ opt ∈ options u (mask (centers C)),
      topValue opt (wireWord 11 C rs (11+tag 11 C lo hi m)) (wireWord 11 C rs (11+tag 11 C lo hi k)) =
        wireWord 11 C rs (11+a) ∧ opt.anchors.testBit (11*α.val+β.val) = true := by
  intro u rs
  letI : DecidableEq GateOp := gateOpDecEq
  obtain ⟨mem,hand,_⟩ := Finset.mem_filter.mp ha
  have valid := Finset.mem_range.mp mem
  let b := orientation C a
  let c := vertex C a
  let L := leaves C a
  let act := fun (g : ℕ) (s : Fin 2) => active 11 C lo hi (opnd C a s) g
  let pos := fun g => position (act g b) (act g (1-b))
  let src := fun g => wireWord 11 C rs (11+tag 11 C lo hi g)
  have centerSide : side C a b = {c} := singleton_center nz narrow ha
  have adj (v : V) (hv : v ∈ L) : (graph.deleteEdges (omitted i j h : Set Edge)).Adj c v :=
    eq ▸ leaf_adj nz narrow shape ha hv
  have necessary (size : 5 ≤ (centers C).card) (v : V)
      (av : (graph.deleteEdges (omitted i j h : Set Edge)).Adj c v) (out : v ∉ centers C) : v ∈ L :=
    private_leaf nz narrow num ha size (eq.symm ▸ av) out
  have anchorFacts (g : ℕ) (v : V) (raw : v ∈ orIn 11 C (11+g)) :
      ((act g b = true → v = c) ∧ (act g (1-b) = true → v ∈ L)) := by
    constructor
    · intro on
      have z : v ∈ side C a b := orIn_subset_of_reaches (active_path on) raw
      exact Finset.mem_singleton.mp (centerSide ▸ z)
    · exact fun on => orIn_subset_of_reaches (active_path on) raw
  have mx := anchorFacts m α hα
  have ky := anchorFacts k β hβ
  have disjoint (g : ℕ) (v : V) (raw : v ∈ orIn 11 C (11+g)) :
      ¬(act g b = true ∧ act g (1-b) = true) := by
    rintro ⟨l,r⟩
    obtain ⟨left,right⟩ := anchorFacts g v raw
    exact (graph.deleteEdges (omitted i j h : Set Edge)).irrefl ((left l) ▸ adj v (right r))
  let opt := makeChoice u c L (pos m) (pos k)
  refine ⟨opt,choice_mem i j h (centers C) L c (center_member ha)
    (sides_nonempty nz ha (1-b)) adj necessary (pos m) (pos k),?_,?_⟩
  · have sideWord (s : Fin 2) : wireWord 11 C rs (opnd C a s) = LocalPrune.optional
        (LocalPrune.optional (signature rs (mask (side (n := 11) C a s))) (src m) (act m s)) (src k) (act k s) := by
      have port := LocalInjections.opnd_mem ao valid s
      exact two_source_word graph C ao tf lo hi J m k pair allMix valid hand port (sides_nonempty nz ha s) rs
    have left := sideWord b
    rw [centerSide] at left
    have right := sideWord (1-b)
    change wireWord 11 C rs (opnd C a (1-b)) =
      LocalPrune.optional (LocalPrune.optional (signature rs (mask L)) (src m) (act m (1-b))) (src k) (act k (1-b)) at right
    exact (top_flags u c L (src m) (src k) _ _ _ _ (disjoint m α hα) (disjoint k β hβ)).trans
      ((congrArg₂ (fun x y : ℕ => x &&& y) left.symm right.symm).trans (oriented_product ao ha b rs).symm)
  · exact anchor_live α β (location c α L _ _ mx.1 mx.2) (location c β L _ _ ky.1 ky.2)

end LocalTopWord

namespace LocalRowWitness
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalGraphRows LocalCoverProfile LocalWireWords LocalMixerCertificate LocalCentreCase

lemma clean_word {C : Circuit} {a : ℕ} (ha : a ∈ tops graph C) (i j k : Fin 16) :
    wireWord 11 C (tripleRows i j k ++ negatives) (11+a) ≤ 7 := by
  letI : DecidableEq GateOp := gateOpDecEq
  have below := (Finset.mem_filter.mp ha).2.2
  let u := tripleRows i j k
  let w := wireWord 11 C (u++negatives) (11+a)
  by_contra over
  change ¬w ≤ 7 at over
  have high : 2^3 ≤ w := by change 8 ≤ w; omega
  obtain ⟨b,hb,on⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow high
  change (packed (u++negatives) (fun r => gateVal 11 C a (rowInput r))).testBit b = true at on
  rw [packed_bit] at on
  split at on
  next inrange =>
    have low : u.length ≤ b := hb
    have neg : (u++negatives)[b] ∈ negatives := by
      rw [List.getElem_append_right low]
      exact List.getElem_mem _
    have no := negative_graph _ neg
    have yes := below _ on
    exact Bool.noConfusion (yes.symm.trans no)
  next out => contradiction

def edgeIndex (i j k : Fin 16) (r : Fin 3) : Fin 16 := if r=0 then i else if r=1 then j else k

lemma positive_word (C : Circuit) (i j k : Fin 16) (r : Fin 3) (a : ℕ) :
    (wireWord 11 C (tripleRows i j k ++ negatives) (11+a)).testBit r.val =
      gateVal 11 C a (testsAt (edgeIndex i j k r)) := by
  have val (l : Fin 16) : rowInput (rowAt l) = testsAt l := funext (row_matches l)
  change (packed _ (fun x => gateVal 11 C a (rowInput x))).testBit r.val = _
  rw [packed_bit]
  fin_cases r <;> simp [edgeIndex,tripleRows,val]

lemma witnessed (C : Circuit)
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, gateVal 11 C a (pairInput u v) = true)
    (i j k : Fin 16) (eq : Ustar graph C=omitted i j k) (r : Fin 3) :
    ∃ a ∈ tops graph C, wireWord 11 C (tripleRows i j k ++ negatives) (11+a) ≤ 7 ∧
      (wireWord 11 C (tripleRows i j k ++ negatives) (11+a)).testBit r.val = true := by
  let l := edgeIndex i j k r
  have mem : edgeAt l ∈ omitted i j k := by fin_cases r <;> simp [l,edgeIndex,omitted]
  have edge : s((endpointAt l).1,(endpointAt l).2) ∈ Ustar graph C := eq ▸ mem
  obtain ⟨a,ha,yes⟩ := trace _ _ edge
  exact ⟨a,ha,clean_word ha i j k,(positive_word C i j k r a).trans yes⟩

end LocalRowWitness

namespace LocalDarkTransfer
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalTransfer LocalBefore LocalBelow LocalReceiver LocalMixCore LocalSingleMix LocalDark

lemma prefix_mode {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (m : ℕ) (single : mixing G C = {m})
    (allraw : centreless G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (tests : List (Fin n → Bool)) (u v : Fin n) (e : s(u,v) ∈ Ustar G C) (present : pairInput u v ∈ tests)
    (y : Fin n → Bool) (pins : ∀ i : Fin n, (∀ x ∈ tests, x i = true) → y i = true)
    (clauses : ∀ A : Finset (Fin n), A.Nonempty →
      (∃ c : Fin n, ∀ v ∈ A, (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj c v) →
      (∀ x ∈ tests, ∃ v ∈ A, x v = true) → ∃ v ∈ A, y v = true)
    (stop : ℕ) (limit : stop ≤ n+m)
    (rare : ∀ k < C.gates.length, n+k < stop → (gateAt C k).op = GateOp.or → k ∈ orN G C \ lam G C →
      (∀ x ∈ tests, gateVal n C k x = true) → gateVal n C k y = true) :
    ∀ w < stop, w < n+C.gates.length →
      (∀ x ∈ tests, val C (List.ofFn x) w = true) → val C (List.ofFn y) w = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  apply tests_through_ands C ao.1 tests (pairInput u v) present y stop pins
  intro k hk prior hor pos
  by_cases below : BelowF G C k
  · obtain ⟨a,ha,le,yes⟩ := true_top_before G C ao (pairInput u v) (n+k) (by omega) below (pos _ present)
    obtain ⟨j,hj,jlt,_⟩ := top_needs_mixing G C ao ha (shape a ha) (sides_nonempty allraw ha) e yes
    have eq : j=m := by simpa [single] using hj
    omega
  · have orn : k ∈ orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hor,below⟩
    by_cases normal : k ∈ lam G C
    · obtain ⟨p,q,ports⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem hk))
      have port : p ∈ (gateAt C k).inputs := by simp [ports]
      obtain ⟨i,hi⟩ := lambda_port ao normal port
      have raw : (orIn n C (n+k)).Nonempty :=
        ⟨i,(raw_gate C k i).mpr ⟨hk,hor,p,port,ao.2.1 k hk p port,hi⟩⟩
      obtain ⟨v,hv,on⟩ := clauses _ raw (lambda_raw_clause shape normal) (fun x hx =>
        raw_until_mixer G C ao (n+m) (mixer_lower single) x (by omega) raw (pos x hx))
      exact raw_pin y hv on
    · exact rare k hk prior hor (Finset.mem_sdiff.mpr ⟨orn,normal⟩) pos

lemma extra_dark_truth {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (tf : TopForm G C)
    (lo hi : ℕ) (J : junk G C = {lo,hi}) (nested : InCone n C lo hi)
    (m : ℕ) (single : mixing G C = {m}) (allraw : centreless G C = ∅)
    (shape : ∀ a ∈ tops G C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), G.Adj l r)
    (tests : List (Fin n → Bool)) (first : Fin n → Bool) (present : first ∈ tests)
    (pairs : ∀ x ∈ tests, ∃ u v, s(u,v) ∈ Ustar G C ∧ x = pairInput u v)
    (d : ℕ) (valid : d < C.gates.length) (prior : d<m) (hor : (gateAt C d).op = GateOp.or)
    (dark : orIn n C (n+d) = ∅) (y : Fin n → Bool)
    (lift : ∀ w < n+d, w < n+C.gates.length →
      (∀ x ∈ tests, val C (List.ofFn x) w = true) → val C (List.ofFn y) w = true)
    (pos : ∀ x ∈ tests, gateVal n C d x = true) : gateVal n C d y = true := by
  letI : DecidableEq GateOp := gateOpDecEq
  have ja : lo ∈ junk G C := by simp [J]
  have jb : hi ∈ junk G C := by simp [J]
  have terminals (x : Fin n → Bool) (hx : x ∈ tests) :
      ∃ a ∈ junk G C, OrReaches n C (n+d) a ∧ gateVal n C a x = true := by
    obtain ⟨u,v,edge,rfl⟩ := pairs x hx
    exact terminal_before_mixer G C ao m single allraw shape (by omega) (by omega) dark edge (pos _ hx)
  have earlier (a : ℕ) (ja : a ∈ junk G C) (path : OrReaches n C (n+d) a) : a<d := by
    have hand := (Finset.mem_filter.mp ja).2.1
    have diff : a≠d := by rintro rfl; simp [hor] at hand
    have upper := reach_le path
    omega
  have raise (a : ℕ) (ja : a ∈ junk G C) (path : OrReaches n C (n+d) a)
      (all : ∀ x ∈ tests, gateVal n C a x = true) : gateVal n C d y = true := by
    have priorA := earlier a ja path
    have validA := Finset.mem_range.mp (Finset.mem_filter.mp ja).1
    exact upward y (orReaches_reach _ _ path).1 (lift (n+a) (by omega) (by omega) all)
  by_cases reach : OrReaches n C (n+d) lo
  · apply raise lo ja reach
    intro x hx
    obtain ⟨a,j,q,on⟩ := terminals x hx
    have which : a=lo ∨ a=hi := by simpa [J] using j
    rcases which with rfl | rfl
    · exact on
    · have pre := earlier _ j q
      obtain ⟨u,v,edge,rfl⟩ := pairs x hx
      exact nested_implies G C ao tf lo _ J nested m single (by omega) allraw shape edge on
  · have high (x : Fin n → Bool) (hx : x ∈ tests) :
        OrReaches n C (n+d) hi ∧ gateVal n C hi x = true := by
      obtain ⟨a,j,q,on⟩ := terminals x hx
      have which : a=lo ∨ a=hi := by simpa [J] using j
      rcases which with rfl | rfl
      · exact (reach q).elim
      · exact ⟨q,on⟩
    exact raise hi jb (high first present).1 (fun x hx => (high x hx).2)

end LocalDarkTransfer

namespace LocalExtraObstruction
open LocalMixerCertificate

lemma single_extra_obstruction {u : List ℕ} (passes : extraPass u = true) {q : ℕ}
    (hq : q ∈ testsFor u) {N : ℕ} (hn : N ∈ available u)
    (rule : ∀ e ∈ u, ∃ w : ℕ, (N &&& e).testBit w = true ∧
      ∀ y ∈ negatives, y.testBit w = true → (liveClauses u).all (hit y) = true →
        hit q y = true → False) : False := by
  let valid := (witnessesFor u).filter (hit q)
  let covered := valid.foldl (fun a b => a ||| b) 0
  have checked : (!valid.isEmpty &&
      (available u).all (fun n => u.any fun e => within (n &&& e) covered)) = true :=
    List.all_eq_true.mp passes q hq
  obtain ⟨_,rows⟩ := split_check (!valid.isEmpty) (available u) u _ checked
  obtain ⟨e,he,hcover⟩ := rows N hn
  obtain ⟨w,hw,blocks⟩ := rule e he
  have bit := within_bit hcover hw
  rcases fold_or_bit valid w 0 bit with zero | ⟨y,hy,wy⟩
  · simp at zero
  · obtain ⟨base,qy⟩ := List.mem_filter.mp hy
    have inBase : y ∈ independentInputs u := base
    obtain ⟨neg,_,raw⟩ := finite_raw_hit inBase (A := liveClauses u) (fun _ h => h)
    exact blocks y neg wy raw qy

end LocalExtraObstruction

namespace LocalExtraCase
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalMasks LocalCentreCase LocalMixerCase
open LocalReceiver LocalSingleMix LocalSmallCover LocalExtraObstruction
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

lemma extra_choice (i j k : Fin 16) (A : Finset V) :
    ∃ q ∈ testsFor (tripleRows i j k), ∀ y : ℕ, hit q y = true →
      (∀ x ∈ tripleTests i j k, ∃ v ∈ A, x v = true) → ∃ v ∈ A, y.testBit v.val = true := by
  by_cases all : ∀ x ∈ tripleTests i j k, ∃ v ∈ A, x v = true
  · obtain ⟨q,hq,yes⟩ := select_three i j k A all
    exact ⟨q,hq,fun y h _ => yes y h⟩
  · have witnessed (l : Fin 16) : ∃ v ∈ (Finset.univ : Finset V), testsAt l v = true :=
      ⟨(endpointAt l).1,Finset.mem_univ _,by simp [testsAt,pairInput]⟩
    have univ : ∀ x ∈ tripleTests i j k, ∃ v ∈ (Finset.univ : Finset V), x v = true := by
      intro x hx
      simp [tripleTests] at hx
      rcases hx with rfl | rfl | rfl <;> exact witnessed _
    obtain ⟨q,hq,_⟩ := select_three i j k Finset.univ univ
    exact ⟨q,hq,fun _ _ yes => (all yes).elim⟩

lemma extra_case (C : Circuit) (ao : IsAO2 11 C) (m d : ℕ)
    (only : orN graph C \ lam graph C ⊆ {m,d}) (single : mixing graph C = {m})
    (dRaw : d < m → (orIn 11 C (11+d)).Nonempty)
    (allraw : centreless graph C = ∅)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, gateVal 11 C a (pairInput u v) = true)
    (three : (Ustar graph C).card = 3) (K : Finset V) (cap : K.card ≤ 5)
    (cover : (graph.deleteEdges (Ustar graph C : Set Edge)).IsVertexCover (K : Set V)) : False := by
  obtain ⟨i,j,k,hij,hjk,edges⟩ := actual_triple (U := Ustar graph C) Finset.sdiff_subset three
  have eq : Ustar graph C = omitted i j k := edges
  let tests := tripleTests i j k
  let u := tripleRows i j k
  let routed := fun (x : V → Bool) => (orIn 11 C (11+m)).Nonempty ∧ gateVal 11 C m x = true ∧
    (∀ r ∈ orIn 11 C (11+m), x r = false) ∧ ∃ w : V, x w = true ∧
      (∀ r ∈ orIn 11 C (11+m), (graph.deleteEdges (Ustar graph C : Set Edge)).Adj r w) ∧
      ∀ y : V → Bool, gateVal 11 C m y = true → y w = true → graphFun graph ∅ y = true
  have forIndex (l : Fin 16) (mem : edgeAt l ∈ omitted i j k) : routed (testsAt l) := by
    have missing : s((endpointAt l).1,(endpointAt l).2) ∈ Ustar graph C := eq ▸ mem
    obtain ⟨a,ha,on⟩ := trace _ _ missing
    exact routed_single graph C ao m single allraw ha (shape a ha) missing on
  have routes (x : V → Bool) (hx : x ∈ tests) : routed x := by
    simp [tests,tripleTests] at hx
    rcases hx with rfl | rfl | rfl <;> apply forIndex <;> simp [omitted]
  have fst : testsAt i ∈ tests := by simp [tests,tripleTests]
  have raw := (routes _ fst).1
  obtain ⟨c,hc⟩ := raw
  let N := neighbor (rows.filter fun e => !(u.contains e)) c
  have supported : N ∈ available u := neighbor_mem _ _
  have small := small_cover i j k K cap (eq ▸ cover)
  have passes := extra_for_small_cover hij hjk k.isLt u rfl small
  obtain ⟨q,hq,protect⟩ := extra_choice i j k (orIn 11 C (11+d))
  apply single_extra_obstruction passes hq supported
  intro e he
  have source : ∃ l : Fin 16, e = rowAt l ∧ testsAt l ∈ tests := by
    simp [u,tripleRows] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨i,rfl,fst⟩
    · exact ⟨j,rfl,by simp [tests,tripleTests]⟩
    · exact ⟨k,rfl,by simp [tests,tripleTests]⟩
  obtain ⟨l,rfl,hl⟩ := source
  obtain ⟨w,high,adj,positive⟩ := (routes _ hl).2.2.2
  have cw := adj c hc
  rw [eq] at cw
  have wn : N.testBit w.val = true := remaining_adjacent i j k c w cw
  have we := (row_matches l w).trans high
  refine ⟨w.val,by simp [Nat.testBit_and,wn,we],?_⟩
  intro y neg wy all qy
  obtain ⟨pins,clauses⟩ := live_semantics i j k _ eq y all
  have firstEdge : s((endpointAt i).1,(endpointAt i).2) ∈ Ustar graph C := eq ▸ (by
    change edgeAt i ∈ omitted i j k
    simp [omitted])
  have lift := prefix_with_one graph C ao m d only single dRaw allraw shape tests _ _ firstEdge fst
    (fun v => y.testBit v.val) pins clauses (protect y qy)
  have atM := truth_single graph C ao m single tests ⟨c,hc⟩
    (fun x hx => (routes x hx).2.1) (fun x hx => (routes x hx).2.2.1)
    (fun v => y.testBit v.val) lift
  have bad := positive (fun v => y.testBit v.val) atM wy
  simp [negative_graph y neg] at bad

end LocalExtraCase

namespace LocalRoutedGraph
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalMasks LocalCentreCase LocalMixerCase
open LocalReceiver LocalSingleMix
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

lemma routed_graph (C : Circuit) (ao : IsAO2 11 C) (m : ℕ) (single : mixing graph C = {m})
    (allraw : centreless graph C = ∅)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, gateVal 11 C a (pairInput u v) = true)
    (three : (Ustar graph C).card = 3)
    (force : ∀ i j k : Fin 16, Ustar graph C = omitted i j k →
      (orIn 11 C (11+m)).Nonempty → (∀ x ∈ tripleTests i j k, gateVal 11 C m x = true) →
      (∀ x ∈ tripleTests i j k, ∀ r ∈ orIn 11 C (11+m), x r = false) →
      ∀ y : ℕ, (liveClauses (tripleRows i j k)).all (hit y) = true → gateVal 11 C m (fun v => y.testBit v.val) = true) : False := by
  obtain ⟨i,j,k,hij,hjk,edges⟩ := actual_triple (U := Ustar graph C) Finset.sdiff_subset three
  have eq : Ustar graph C = omitted i j k := edges
  let tests := tripleTests i j k
  let u := tripleRows i j k
  let routed := fun (x : V → Bool) => (orIn 11 C (11+m)).Nonempty ∧ gateVal 11 C m x = true ∧
    (∀ r ∈ orIn 11 C (11+m), x r = false) ∧ ∃ w : V, x w = true ∧
      (∀ r ∈ orIn 11 C (11+m), (graph.deleteEdges (Ustar graph C : Set Edge)).Adj r w) ∧
      ∀ y : V → Bool, gateVal 11 C m y = true → y w = true → graphFun graph ∅ y = true
  have forIndex (l : Fin 16) (mem : edgeAt l ∈ omitted i j k) : routed (testsAt l) := by
    have missing : s((endpointAt l).1,(endpointAt l).2) ∈ Ustar graph C := eq ▸ mem
    obtain ⟨a,ha,on⟩ := trace _ _ missing
    exact routed_single graph C ao m single allraw ha (shape a ha) missing on
  have routes (x : V → Bool) (hx : x ∈ tests) : routed x := by
    simp [tests,tripleTests] at hx
    rcases hx with rfl | rfl | rfl <;> apply forIndex <;> simp [omitted]
  have fst : testsAt i ∈ tests := by simp [tests,tripleTests]
  have raw := (routes _ fst).1
  obtain ⟨c,hc⟩ := raw
  let N := neighbor (rows.filter fun e => !(u.contains e)) c
  have supported : N ∈ available u := neighbor_mem _ _
  apply one_mixer_obstruction hij hjk k.isLt u rfl (liveClauses u) (fun _ h => h) N supported
  intro e he
  have source : ∃ l : Fin 16, e = rowAt l ∧ testsAt l ∈ tests := by
    simp [u,tripleRows] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨i,rfl,fst⟩
    · exact ⟨j,rfl,by simp [tests,tripleTests]⟩
    · exact ⟨k,rfl,by simp [tests,tripleTests]⟩
  obtain ⟨l,rfl,hl⟩ := source
  obtain ⟨w,high,adj,positive⟩ := (routes _ hl).2.2.2
  have cw := adj c hc
  rw [eq] at cw
  have wn : N.testBit w.val = true := remaining_adjacent i j k c w cw
  have we := (row_matches l w).trans high
  refine ⟨w.val,by simp [Nat.testBit_and,wn,we],?_⟩
  intro y neg wy
  cases all : (liveClauses u).all (hit y)
  · rfl
  · have atM := force i j k eq ⟨c,hc⟩ (fun x hx => (routes x hx).2.1)
      (fun x hx => (routes x hx).2.2.1) y all
    have bad := positive (fun v => y.testBit v.val) atM wy
    simp [negative_graph y neg] at bad

end LocalRoutedGraph

namespace LocalAllSingle
open LocalCoverProfile LocalGraphRows LocalMixerCertificate LocalCentreCase LocalMixerCase
open LocalReceiver LocalSingleMix LocalDarkTransfer LocalExtraCase LocalRoutedGraph
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

lemma all_single (C : Circuit) (ao : IsAO2 11 C) (tf : TopForm graph C)
    (lo hi : ℕ) (J : junk graph C = {lo,hi}) (nested : InCone 11 C lo hi)
    (m d : ℕ) (only : orN graph C \ lam graph C ⊆ {m,d}) (single : mixing graph C = {m})
    (allraw : centreless graph C = ∅)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, gateVal 11 C a (pairInput u v) = true)
    (three : (Ustar graph C).card = 3) (K : Finset V) (cap : K.card ≤ 5)
    (cover : (graph.deleteEdges (Ustar graph C : Set Edge)).IsVertexCover (K : Set V)) : False := by
  by_cases rawD : d<m → (orIn 11 C (11+d)).Nonempty
  · exact extra_case C ao m d only single rawD allraw shape trace three K cap cover
  push Not at rawD
  obtain ⟨before,dark⟩ := rawD
  apply routed_graph C ao m single allraw shape trace three
  intro i j k eq raw pos off y all
  let tests := tripleTests i j k
  have fst : testsAt i ∈ tests := by simp [tests,tripleTests]
  have firstEdge : s((endpointAt i).1,(endpointAt i).2) ∈ Ustar graph C := eq ▸ (by
    change edgeAt i ∈ omitted i j k
    simp [omitted])
  have pairs (x : V → Bool) (hx : x ∈ tests) : ∃ a b, s(a,b) ∈ Ustar graph C ∧ x = pairInput a b := by
    have index (l : Fin 16) (h : edgeAt l ∈ omitted i j k) :
        ∃ a b, s(a,b) ∈ Ustar graph C ∧ testsAt l = pairInput a b :=
      ⟨(endpointAt l).1,(endpointAt l).2,eq ▸ h,rfl⟩
    simp [tests,tripleTests] at hx
    rcases hx with rfl | rfl | rfl <;> apply index <;> simp [omitted]
  obtain ⟨pins,clauses⟩ := live_semantics i j k _ eq y all
  have mode := prefix_mode graph C ao m single allraw shape tests _ _ firstEdge fst
    (fun v => y.testBit v.val) pins clauses
  have choices (j : ℕ) (hj : j ∈ orN graph C \ lam graph C) : j=m ∨ j=d := by simpa using only hj
  have lower := mode (11+d) (by omega) (fun j _ hlt _ hj _ => by
    have h := choices j hj
    omega)
  apply truth_single graph C ao m single tests raw pos off (fun v => y.testBit v.val)
  apply mode (11+m) le_rfl
  intro a ha prior hor rare on
  have which := choices a rare
  have ad : a=d := by omega
  subst a
  exact extra_dark_truth graph C ao tf lo hi J nested m single allraw shape tests (testsAt i) fst pairs
    d ha before hor dark (fun v => y.testBit v.val) lower on

end LocalAllSingle

namespace LocalTwoMixers
open LocalCoverProfile LocalGraphRows LocalCentreCase LocalReceiver LocalMixCore LocalAllSingle
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

lemma mixing_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    mixing G C ⊆ orN G C \ lam G C := by
  letI : DecidableEq GateOp := gateOpDecEq
  intro m hm
  obtain ⟨orn,diff⟩ := Finset.mem_filter.mp hm
  refine Finset.mem_sdiff.mpr ⟨orn,?_⟩
  intro normal
  obtain ⟨_,left,right,_⟩ := Finset.mem_filter.mp normal
  apply diff
  apply propext
  exact ⟨fun h => (Finset.nonempty_iff_ne_empty.mp left h).elim,
    fun h => (Finset.nonempty_iff_ne_empty.mp right h).elim⟩

lemma two_are_mixers (C : Circuit) (ao : IsAO2 11 C) (tf : TopForm graph C)
    (lo hi : ℕ) (J : junk graph C = {lo,hi}) (nested : InCone 11 C lo hi)
    (two : (orN graph C \ lam graph C).card = 2) (allraw : centreless graph C = ∅)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, gateVal 11 C a (pairInput u v) = true)
    (three : (Ustar graph C).card = 3) (K : Finset V) (cap : K.card ≤ 5)
    (cover : (graph.deleteEdges (Ustar graph C : Set Edge)).IsVertexCover (K : Set V)) :
    mixing graph C = orN graph C \ lam graph C := by
  have sub := mixing_subset graph C
  by_contra different
  have smaller : (mixing graph C).card < 2 := by
    apply Nat.lt_of_not_ge
    intro ge
    exact different (Finset.eq_of_subset_of_card_le sub (two ▸ ge))
  obtain ⟨i,j,k,_,_,eq⟩ := actual_triple (U := Ustar graph C) Finset.sdiff_subset three
  have firstEdge : s((endpointAt i).1,(endpointAt i).2) ∈ Ustar graph C := eq ▸ (by
    change edgeAt i ∈ ({edgeAt i,edgeAt j,edgeAt k} : Finset Edge)
    simp)
  obtain ⟨a,ha,on⟩ := trace _ _ firstEdge
  obtain ⟨m,hm,_,_⟩ := top_needs_mixing graph C ao ha (shape a ha) (sides_nonempty allraw ha) firstEdge on
  have pos := Finset.card_pos.mpr (show (mixing graph C).Nonempty from ⟨m,hm⟩)
  obtain ⟨v,one⟩ := Finset.card_eq_one.mp (show (mixing graph C).card=1 by omega)
  have vm : v ∈ mixing graph C := by simp [one]
  obtain ⟨p,q,_,pq⟩ := Finset.card_eq_two.mp two
  have which : v=p ∨ v=q := by simpa [pq] using sub vm
  rcases which with hp | hq
  · exact all_single C ao tf lo hi J nested v q (by rw [pq,hp]) one allraw shape trace three K cap cover
  · have ss : orN graph C \ lam graph C ⊆ {v,p} := by
      intro t ht
      have options : t=p ∨ t=q := by simpa [pq] using ht
      simpa [hq] using options.symm
    exact all_single C ao tf lo hi J nested v p ss one allraw shape trace three K cap cover

end LocalTwoMixers

namespace LocalModelBridge
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalCoverProfile LocalWireWords LocalActive LocalCenters LocalRowWitness LocalTopWord
open LocalCentreCase LocalWordGeometry LocalGeometrySound LocalInjections LocalMixerCertificate
open LocalMasks LocalPrune LocalNormal LocalGeoBridge LocalSignatures

lemma physical_model (C : Circuit) (ao : IsAO2 11 C) (tf : TopForm graph C)
    (lo hi m k : ℕ) (J : junk graph C={lo,hi}) (pair : mixing graph C={m,k})
    (allMix : orN graph C \ lam graph C ⊆ mixing graph C)
    (nz : centreless graph C = ∅) (narrow : thin C) (num : (tops graph C).card ≤ 5)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, gateVal 11 C a (pairInput u v) = true)
    (i j h : Fin 16) (eq : Ustar graph C=omitted i j h) :
    let u := tripleRows i j h
    let rs := u++negatives
    ∃ index : ℕ, model (options u (mask (centers C)))
      (wireWord 11 C rs (11+tag 11 C lo hi m)) (wireWord 11 C rs (11+tag 11 C lo hi k)) index := by
  intro u rs
  obtain ⟨α,hα⟩ := mixed_raw graph ao (show m ∈ mixing graph C by simp [pair])
  obtain ⟨β,hβ⟩ := mixed_raw graph ao (show k ∈ mixing graph C by simp [pair])
  refine ⟨11*α.val+β.val,?_⟩
  intro r
  obtain ⟨a,ha,clean,positive⟩ := witnessed C trace i j h eq r
  obtain ⟨opt,mem,word,anchor⟩ := real_choice C ao tf lo hi m k J pair allMix nz narrow num
    shape i j h eq α β hα hβ ha
  exact ⟨opt,mem,word.symm ▸ clean,word.symm ▸ positive,anchor⟩

def rejectsProducts (u : List ℕ) (K : ℕ) : Prop :=
  let raw := 0 :: (rawMasks u).map (signature (u++negatives))
  let geo := options u K
  ∀ r ∈ raw, ∀ s ∈ raw, ∀ l ∈ raw, ∀ t ∈ raw, ∀ (lf rf : Bool) (id : ℕ),
    let a := r &&& s
    let b := LocalPrune.optional l a lf &&& LocalPrune.optional t a rf
    ¬(model geo a a id ∨ model geo a b id ∨ model geo b b id)

lemma no_pair_of_rejection (C : Circuit) (ao : IsAO2 11 C) (tf : TopForm graph C)
    (lo hi : ℕ) (order : lo<hi) (J : junk graph C={lo,hi}) (nested : InCone 11 C lo hi)
    (two : (orN graph C \ lam graph C).card = 2)
    (nz : centreless graph C = ∅) (narrow : thin C) (num : (tops graph C).card ≤ 5)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, gateVal 11 C a (pairInput u v) = true)
    (three : (Ustar graph C).card=3) (i j h : Fin 16) (eq : Ustar graph C=omitted i j h)
    (rejection : rejectsProducts (tripleRows i j h) (mask (centers C))) : False := by
  let u := tripleRows i j h
  let rs := u++negatives
  let geo := options u (mask (centers C))
  let raw := 0 :: (rawMasks u).map (signature rs)
  have small : (centers C).card ≤ 5 := Finset.card_image_le.trans num
  have same := LocalTwoMixers.two_are_mixers C ao tf lo hi J nested two nz shape trace three (centers C) small (center_cover nz narrow)
  obtain ⟨m,k,_,mk⟩ := Finset.card_eq_two.mp (same.symm ▸ two)
  have includeMix : orN graph C \ lam graph C ⊆ mixing graph C := by rw [same]
  have support (p : ℕ) : signature rs (mask (orIn 11 C p)) ∈ raw :=
    raw_word_member C ao includeMix shape i j h eq p
  obtain ⟨r,hr,s,hs,l,hl,t,ht,lf,rf,low,high⟩ := dirty_words graph C ao tf lo hi order J rs raw support
  let d := wireWord 11 C rs (11+lo)
  let e := wireWord 11 C rs (11+hi)
  have reject (index : ℕ) : ¬(model geo d d index ∨ model geo d e index ∨ model geo e e index) := by
    dsimp only [d,e]
    rw [low,high]
    exact rejection r hr s hs l hl t ht lf rf index
  have make (p q : ℕ) (pq : mixing graph C={p,q}) :=
    physical_model C ao tf lo hi p q J pq includeMix nz narrow num shape trace i j h eq
  have tags (p : ℕ) : tag 11 C lo hi p = lo ∨ tag 11 C lo hi p = hi := by
    unfold tag
    split <;> simp
  obtain ⟨id,direct⟩ := make m k mk
  rcases tags m with ml | mh <;> rcases tags k with kl | kh
  · exact reject id (Or.inl (by simpa only [ml,kl] using direct))
  · exact reject id (Or.inr (Or.inl (by simpa only [ml,kh] using direct)))
  · obtain ⟨rev,swapped⟩ := make k m (mk.trans (Finset.pair_comm _ _))
    exact reject rev (Or.inr (Or.inl (by simpa only [kl,mh] using swapped)))
  · exact reject id (Or.inr (Or.inr (by simpa only [mh,kh] using direct)))

end LocalModelBridge

namespace LocalDeck
open LocalMixerCertificate LocalWordGeometry

def smallMasks := (List.range 2048).filter fun m =>
  let n := (pins.filter (hit m)).length
  n == 4 || n == 5

def coverMasks (u : List ℕ) := smallMasks.filter fun m =>
  (rows.filter (fun e => !(u.contains e))).all (hit m)

def checkDeck (u : List ℕ) : Bool := (coverMasks u).all (excludes u)
def checkChunk (a b : ℕ) : Bool :=
  (((List.range 16).filter (fun c => decide (b<c))).map (fun c =>
    [rows.getD a 0,rows.getD b 0,rows.getD c 0])).all checkDeck

end LocalDeck

namespace LocalClipBridge
open LocalWordGeometry LocalModelBridge LocalClip LocalDeck

def projectedDeck (u : List ℕ) (h : ℕ) := (coverMasks u).all (clippedCheck h u)

end LocalClipBridge

namespace LocalSignalCert
open LocalBetter LocalClip LocalGeometrySound LocalWordGeometry LocalSignatures LocalPrune LocalMixerCertificate

abbrev Pairs := List (ℕ × ℕ)

def reps (rs xs : List ℕ) := xs.all fun x => rs.any (fun r => beats r x)

def representsPair (ps : Pairs) (a b : ℕ) := ps.any fun p =>
  (beats p.1 a && beats p.2 b) || (beats p.2 a && beats p.1 b)

def sourceCheck (rs firsts : List ℕ) (ps : Pairs) : Bool :=
  rs.all (fun x => rs.all (fun y => firsts.any (fun a => beats a (x &&& y)))) &&
  firsts.all (fun a =>
    let xs := rs ++ rs.map (fun r => r ||| a)
    representsPair ps a a && xs.all (fun x => xs.all (fun y =>
      representsPair ps a (x &&& y) && representsPair ps (x &&& y) (x &&& y))))

def geometryCheck (geo : List TopChoice) (ps : Pairs) := ps.all fun p =>
  surviving geo p.1 p.2 == 0 && surviving geo p.2 p.1 == 0

lemma rep {rs raw : List ℕ} (ok : reps rs raw=true) {w : ℕ} (mem : w ∈ raw) :
    ∃ x ∈ rs, Better x w := by
  obtain ⟨x,hx,le⟩ := List.any_eq_true.mp (List.all_eq_true.mp ok w mem)
  exact ⟨x,hx,beats_sound le⟩

lemma possible {rs : List ℕ} {p a : ℕ} (hp : p ∈ rs) (f : Bool) :
    LocalPrune.optional p a f ∈ rs ++ rs.map (fun r => r ||| a) := by
  cases f
  · exact List.mem_append_left _ hp
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨p,hp,rfl⟩)

lemma check_reject {geo : List TopChoice} {ps : Pairs} (ok : geometryCheck geo ps=true)
    {a b : ℕ} (represented : representsPair ps a b=true) (index : ℕ) : ¬model geo a b index := by
  obtain ⟨⟨c,d⟩,mem,how⟩ := List.any_eq_true.mp represented
  obtain ⟨direct,reverse⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ok _ mem)
  intro m
  rcases Bool.or_eq_true_iff.mp how with first | second
  · obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp first
    exact surviving_nonzero _ _ _ index (better_model _ (beats_sound left) (beats_sound right) m) (beq_iff_eq.mp direct)
  · obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp second
    exact surviving_nonzero _ _ _ index (better_model _ (beats_sound left) (beats_sound right) m) (beq_iff_eq.mp reverse)

lemma cert_reject {raw rs firsts : List ℕ} {geo : List TopChoice} {ps : Pairs}
    (cover : reps rs raw=true) (sources : sourceCheck rs firsts ps=true) (geometry : geometryCheck geo ps=true)
    (r s l t : ℕ) (hr : r ∈ raw) (hs : s ∈ raw) (hl : l ∈ raw) (ht : t ∈ raw) (lf rf : Bool) (index : ℕ) :
    let a := r &&& s
    let b := LocalPrune.optional l a lf &&& LocalPrune.optional t a rf
    ¬(model geo a a index ∨ model geo a b index ∨ model geo b b index) := by
  intro a b
  obtain ⟨r',mr,cr⟩ := rep cover hr
  obtain ⟨s',ms,cs⟩ := rep cover hs
  obtain ⟨l',ml,cl⟩ := rep cover hl
  obtain ⟨t',mt,ct⟩ := rep cover ht
  obtain ⟨firstOK,options⟩ := Bool.and_eq_true_iff.mp sources
  obtain ⟨d,md,lower⟩ := List.any_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp firstOK _ mr) _ ms)
  have cd : Better d a := chain (beats_sound lower) (conj cr cs)
  let x := LocalPrune.optional l' d lf
  let y := LocalPrune.optional t' d rf
  have ce : Better (x &&& y) b := conj (flag cl cd lf) (flag ct cd rf)
  obtain ⟨dd,more⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp options d md)
  obtain ⟨de,ee⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp more x (possible ml lf)) y (possible mt rf))
  rintro (m | m | m)
  · exact check_reject geometry dd index (better_model _ cd cd m)
  · exact check_reject geometry de index (better_model _ cd ce m)
  · exact check_reject geometry ee index (better_model _ ce ce m)

lemma projected_cert (u : List ℕ) (K h : ℕ) (keep : ∀ i : Fin 3, h.testBit i.val=true)
    (rs firsts : List ℕ) (ps : Pairs)
    (cover : reps rs ((0 :: (rawMasks u).map (signature (u++negatives))).map (clip h))=true)
    (sources : sourceCheck rs firsts ps=true)
    (geometry : geometryCheck ((options u K).map (clipChoice h)) ps=true) :
    LocalModelBridge.rejectsProducts u K := by
  intro r hr s hs l hl t ht lf rf index
  let raw := 0 :: (rawMasks u).map (signature (u++negatives))
  have included (q : ℕ) (mq : q ∈ raw) : clip h q ∈ raw.map (clip h) := List.mem_map.mpr ⟨q,mq,rfl⟩
  have forbid := cert_reject cover sources geometry _ _ _ _ (included r hr) (included s hs) (included l hl) (included t ht) lf rf index
  let a := r &&& s
  let b := LocalPrune.optional l a lf &&& LocalPrune.optional t a rf
  have ha : clip h a = clip h r &&& clip h s := clip_and h r s
  have hb : clip h b = LocalPrune.optional (clip h l) (clip h a) lf &&& LocalPrune.optional (clip h t) (clip h a) rf := by
    change clip h (LocalPrune.optional l a lf &&& LocalPrune.optional t a rf)=_
    rw [clip_and,clip_optional,clip_optional]
  rw [ha] at hb
  change ¬(model (options u K) a a index ∨ model (options u K) a b index ∨ model (options u K) b b index)
  rintro (m | m | m)
  · exact forbid (Or.inl (by simpa only [ha] using clip_model h keep _ _ _ _ m))
  · exact forbid (Or.inr (Or.inl (by simpa only [ha,hb] using clip_model h keep _ _ _ _ m)))
  · exact forbid (Or.inr (Or.inr (by simpa only [hb] using clip_model h keep _ _ _ _ m)))

end LocalSignalCert

namespace LocalMatchingCheck
open LocalBetter LocalSignalCert

def usable (w i : ℕ) := decide (w ≤ 7) && w.testBit i
def wins (pins : List ℕ) (a b i : ℕ) :=
  usable (a &&& b) i || pins.any fun p => usable (a &&& p) i || usable (b &&& p) i
def allThree (pins : List ℕ) (a b : ℕ) :=
  wins pins a b 0 && wins pins a b 1 && wins pins a b 2
def entryOK (pins rs : List ℕ) (e : ℕ × List ℕ) :=
  reps e.2 (rs ++ rs.map (fun r => r ||| e.1)) &&
    e.2.all (fun l => e.2.all fun r => !(allThree pins e.1 (l &&& r)))

lemma usable_better {a b i : ℕ} (h : Better a b) (low : i<3) (yes : usable b i=true) : usable a i=true := by
  obtain ⟨ok,on⟩ := Bool.and_eq_true_iff.mp yes
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (safe h (of_decide_eq_true ok)),h.1 i low on⟩

lemma wins_better (pins : List ℕ) {a b c d i : ℕ} (ac : Better a c) (bd : Better b d) (low : i<3)
    (h : wins pins c d i=true) : wins pins a b i=true := by
  apply Bool.or_eq_true_iff.mpr
  rcases Bool.or_eq_true_iff.mp h with both | anyPin
  · exact Or.inl (usable_better (conj ac bd) low both)
  · obtain ⟨p,hp,term⟩ := List.any_eq_true.mp anyPin
    exact Or.inr (List.any_eq_true.mpr ⟨p,hp,Bool.or_eq_true_iff.mpr
      ((Bool.or_eq_true_iff.mp term).imp (usable_better (conj ac (self p)) low)
        (usable_better (conj bd (self p)) low))⟩)

lemma all_of_wins (pins : List ℕ) {a b : ℕ} (yes : ∀ i : Fin 3, wins pins a b i.val=true) :
    allThree pins a b=true :=
  Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨yes 0,yes 1⟩,yes 2⟩

lemma cert_forbids (pins raw rs : List ℕ) (entries : List (ℕ × List ℕ))
    (cover : reps rs raw=true)
    (firsts : rs.all (fun x => rs.all fun y => (entries.map Prod.fst).any fun a => beats a (x &&& y))=true)
    (checked : entries.all (entryOK pins rs)=true)
    {r s l t : ℕ} (hr : r ∈ raw) (hs : s ∈ raw) (hl : l ∈ raw) (ht : t ∈ raw) (lf rf : Bool) :
    let a := r &&& s
    let b := LocalPrune.optional l a lf &&& LocalPrune.optional t a rf
    ¬(∀ i : Fin 3, wins pins a b i.val=true) := by
  intro a b model
  obtain ⟨r',mr,cr⟩ := rep cover hr
  obtain ⟨s',ms,cs⟩ := rep cover hs
  obtain ⟨l',ml,cl⟩ := rep cover hl
  obtain ⟨t',mt,ct⟩ := rep cover ht
  obtain ⟨d,mem,lower⟩ := List.any_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp firsts r' mr) s' ms)
  obtain ⟨⟨d,ports⟩,hd,rfl⟩ := List.mem_map.mp mem
  have ca : Better d a := chain (beats_sound lower) (conj cr cs)
  obtain ⟨pmap,guard⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp checked (d,ports) hd)
  obtain ⟨x,hx,bx⟩ := rep pmap (possible ml lf)
  obtain ⟨y,hy,byy⟩ := rep pmap (possible mt rf)
  have cb : Better (x &&& y) b := conj (chain bx (flag cl ca lf)) (chain byy (flag ct ca rf))
  have bad := List.all_eq_true.mp (List.all_eq_true.mp guard x hx) y hy
  have good := all_of_wins pins (fun i => wins_better pins ca cb i.isLt (model i))
  simp [good] at bad

end LocalMatchingCheck

namespace LocalMatchingData
open LocalMatchingCheck LocalSignalCert

def pins : List ℕ := [0,121,1921,410,1634,684,1364]
def raw : List ℕ := [0,121,410,507,684,765,958,1023,1364,1405,1502,1535,1634,1659,1774,1791,1910,1919,1921,1947,1965,1983,2005,2015,2019,2031,2039,2041,2042,2043,2044,2045,2046,2047]
def rs : List ℕ := [0,121,410,684,1364,1634,1921,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015,2019,2031,2039]
def entry0 : ℕ × List ℕ := (1,[1,411,685,1365,1635,959,1503,1775,1911])
def entry1 : ℕ × List ℕ := (2,[2,123,686,1366,1923,767,1407,1967,2007])
def entry2 : ℕ × List ℕ := (4,[4,125,414,1638,1925,511,1663,1951,2023])
def entry3 : ℕ × List ℕ := (123,[0,123,410,684,767,1364,1407,1634,1921,958,1502,1774,1910,1947,1965,1983,2005,2015,2019,2031,2039])
def entry4 : ℕ × List ℕ := (125,[0,125,410,511,684,1364,1634,1663,1921,958,1502,1774,1910,1947,1965,1983,2005,2015,2019,2031,2039])
def entry5 : ℕ × List ℕ := (411,[0,411,121,684,959,1364,1503,1634,1921,765,1405,1659,1774,1791,1910,1919,1965,2005,2019,2031,2039])
def entry6 : ℕ × List ℕ := (414,[0,414,121,511,684,1364,1634,1921,1951,765,1405,1659,1774,1791,1910,1919,1965,2005,2019,2031,2039])
def entry7 : ℕ × List ℕ := (483,[0,483,121,410,684,1007,1364,1527,1634,1921,765,958,1405,1502,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015])
def entry8 : ℕ × List ℕ := (685,[0,685,121,410,959,1364,1634,1775,1921,507,1405,1502,1535,1659,1910,1919,1947,2005,2015,2019,2039])
def entry9 : ℕ × List ℕ := (686,[0,686,121,410,767,1364,1634,1921,1967,507,1405,1502,1535,1659,1910,1919,1947,2005,2015,2019,2039])
def entry10 : ℕ × List ℕ := (725,[0,725,121,410,684,991,1364,1634,1783,1921,507,958,1405,1502,1535,1659,1774,1910,1919,1947,1965,1983,2019,2031])
def entry11 : ℕ × List ℕ := (822,[0,822,121,410,684,895,1364,1634,1921,1975,507,765,1405,1502,1535,1659,1774,1791,1947,1965,2005,2015,2019,2031])
def entry12 : ℕ × List ℕ := (1230,[0,1230,121,410,684,1279,1364,1634,1921,1999,507,765,958,1023,1405,1659,1910,1919,1947,1965,1983,2005,2019,2039])
def entry13 : ℕ × List ℕ := (1325,[0,1325,121,410,684,1364,1471,1634,1903,1921,507,765,958,1023,1502,1659,1774,1791,1910,1947,2005,2015,2019,2039])
def entry14 : ℕ × List ℕ := (1365,[0,1365,121,410,684,1503,1634,1911,1921,507,765,958,1023,1659,1774,1791,1947,1965,1983,2019,2031])
def entry15 : ℕ × List ℕ := (1366,[0,1366,121,410,684,1407,1634,1921,2007,507,765,958,1023,1659,1774,1791,1947,1965,1983,2019,2031])
def entry16 : ℕ × List ℕ := (1563,[0,1563,121,410,684,1364,1634,1727,1887,1921,507,765,958,1023,1405,1502,1535,1774,1910,1965,2005,2019,2031,2039])
def entry17 : ℕ × List ℕ := (1635,[0,1635,121,410,684,1364,1775,1911,1921,507,765,958,1023,1405,1502,1535,1947,1965,1983,2005,2015])
def entry18 : ℕ × List ℕ := (1638,[0,1638,121,410,684,1364,1663,1921,2023,507,765,958,1023,1405,1502,1535,1947,1965,1983,2005,2015])
def entry19 : ℕ × List ℕ := (1923,[0,1923,121,410,684,1364,1634,1967,2007,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919])
def entry20 : ℕ × List ℕ := (1925,[0,1925,121,410,684,1364,1634,1951,2023,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919])
def entry21 : ℕ × List ℕ := (511,[0,121,410,511,684,1364,1634,1921,765,958,1405,1502,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015,2019,2031,2039])
def entry22 : ℕ × List ℕ := (767,[0,121,410,684,767,1364,1634,1921,507,958,1405,1502,1535,1659,1774,1910,1919,1947,1965,1983,2005,2015,2019,2031,2039])
def entry23 : ℕ × List ℕ := (895,[0,121,410,684,895,1364,1634,1921,507,765,958,1405,1502,1535,1659,1774,1791,1910,1947,1965,1983,2005,2015,2019,2031,2039])
def entry24 : ℕ × List ℕ := (959,[0,121,410,684,959,1364,1634,1921,507,765,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,2005,2015,2019,2031,2039])
def entry25 : ℕ × List ℕ := (991,[0,121,410,684,991,1364,1634,1921,507,765,958,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2005,2019,2031,2039])
def entry26 : ℕ × List ℕ := (1007,[0,121,410,684,1007,1364,1634,1921,507,765,958,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015,2019,2039])
def entry27 : ℕ × List ℕ := (1015,[0,121,410,684,1015,1364,1634,1921,507,765,958,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015,2019,2031])
def entry28 : ℕ × List ℕ := (1279,[0,121,410,684,1279,1364,1634,1921,507,765,958,1023,1405,1502,1659,1774,1910,1919,1947,1965,1983,2005,2015,2019,2031,2039])
def entry29 : ℕ × List ℕ := (1407,[0,121,410,684,1364,1407,1634,1921,507,765,958,1023,1502,1659,1774,1791,1910,1947,1965,1983,2005,2015,2019,2031,2039])
def entry30 : ℕ × List ℕ := (1471,[0,121,410,684,1364,1471,1634,1921,507,765,958,1023,1405,1502,1659,1774,1791,1910,1919,1947,1965,2005,2015,2019,2031,2039])
def entry31 : ℕ × List ℕ := (1503,[0,121,410,684,1364,1503,1634,1921,507,765,958,1023,1405,1659,1774,1791,1910,1919,1947,1965,1983,2005,2019,2031,2039])
def entry32 : ℕ × List ℕ := (1519,[0,121,410,684,1364,1519,1634,1921,507,765,958,1023,1405,1502,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015,2019,2039])
def entry33 : ℕ × List ℕ := (1527,[0,121,410,684,1364,1527,1634,1921,507,765,958,1023,1405,1502,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015,2019,2031])
def entry34 : ℕ × List ℕ := (1663,[0,121,410,684,1364,1634,1663,1921,507,765,958,1023,1405,1502,1535,1774,1910,1947,1965,1983,2005,2015,2019,2031,2039])
def entry35 : ℕ × List ℕ := (1727,[0,121,410,684,1364,1634,1727,1921,507,765,958,1023,1405,1502,1535,1659,1774,1910,1919,1947,1965,2005,2015,2019,2031,2039])
def entry36 : ℕ × List ℕ := (1759,[0,121,410,684,1364,1634,1759,1921,507,765,958,1023,1405,1502,1535,1659,1774,1910,1919,1947,1965,1983,2005,2019,2031,2039])
def entry37 : ℕ × List ℕ := (1775,[0,121,410,684,1364,1634,1775,1921,507,765,958,1023,1405,1502,1535,1659,1910,1919,1947,1965,1983,2005,2015,2019,2039])
def entry38 : ℕ × List ℕ := (1783,[0,121,410,684,1364,1634,1783,1921,507,765,958,1023,1405,1502,1535,1659,1774,1910,1919,1947,1965,1983,2005,2015,2019,2031])
def entry39 : ℕ × List ℕ := (1855,[0,121,410,684,1364,1634,1855,1921,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1947,1965,2005,2015,2019,2031,2039])
def entry40 : ℕ × List ℕ := (1887,[0,121,410,684,1364,1634,1887,1921,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1947,1965,1983,2005,2019,2031,2039])
def entry41 : ℕ × List ℕ := (1903,[0,121,410,684,1364,1634,1903,1921,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1947,1965,1983,2005,2015,2019,2039])
def entry42 : ℕ × List ℕ := (1911,[0,121,410,684,1364,1634,1911,1921,507,765,958,1023,1405,1502,1535,1659,1774,1791,1947,1965,1983,2005,2015,2019,2031])
def entry43 : ℕ × List ℕ := (1951,[0,121,410,684,1364,1634,1921,1951,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1965,2005,2019,2031,2039])
def entry44 : ℕ × List ℕ := (1967,[0,121,410,684,1364,1634,1921,1967,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1947,2005,2015,2019,2039])
def entry45 : ℕ × List ℕ := (1975,[0,121,410,684,1364,1634,1921,1975,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,2005,2015,2019,2031])
def entry46 : ℕ × List ℕ := (1999,[0,121,410,684,1364,1634,1921,1999,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2005,2019,2039])
def entry47 : ℕ × List ℕ := (2007,[0,121,410,684,1364,1634,1921,2007,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2019,2031])
def entry48 : ℕ × List ℕ := (2023,[0,121,410,684,1364,1634,1921,2023,507,765,958,1023,1405,1502,1535,1659,1774,1791,1910,1919,1947,1965,1983,2005,2015])
def entries : List (ℕ × List ℕ) := [entry0,entry1,entry2,entry3,entry4,entry5,entry6,entry7,entry8,entry9,entry10,entry11,entry12,entry13,entry14,entry15,entry16,entry17,entry18,entry19,entry20,entry21,entry22,entry23,entry24,entry25,entry26,entry27,entry28,entry29,entry30,entry31,entry32,entry33,entry34,entry35,entry36,entry37,entry38,entry39,entry40,entry41,entry42,entry43,entry44,entry45,entry46,entry47,entry48]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma closed : raw.contains 0 && raw.all (fun w => pins.all fun p => raw.contains (w ||| p)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma dominates : reps rs raw=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma firsts : rs.all (fun a => rs.all fun b => (entries.map Prod.fst).any fun w => LocalBetter.beats w (a &&& b)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested0 : entryOK pins rs entry0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested1 : entryOK pins rs entry1=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested2 : entryOK pins rs entry2=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested3 : entryOK pins rs entry3=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested4 : entryOK pins rs entry4=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested5 : entryOK pins rs entry5=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested6 : entryOK pins rs entry6=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested7 : entryOK pins rs entry7=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested8 : entryOK pins rs entry8=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested9 : entryOK pins rs entry9=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested10 : entryOK pins rs entry10=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested11 : entryOK pins rs entry11=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested12 : entryOK pins rs entry12=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested13 : entryOK pins rs entry13=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested14 : entryOK pins rs entry14=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested15 : entryOK pins rs entry15=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested16 : entryOK pins rs entry16=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested17 : entryOK pins rs entry17=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested18 : entryOK pins rs entry18=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested19 : entryOK pins rs entry19=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested20 : entryOK pins rs entry20=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested21 : entryOK pins rs entry21=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested22 : entryOK pins rs entry22=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested23 : entryOK pins rs entry23=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested24 : entryOK pins rs entry24=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested25 : entryOK pins rs entry25=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested26 : entryOK pins rs entry26=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested27 : entryOK pins rs entry27=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested28 : entryOK pins rs entry28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested29 : entryOK pins rs entry29=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested30 : entryOK pins rs entry30=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested31 : entryOK pins rs entry31=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested32 : entryOK pins rs entry32=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested33 : entryOK pins rs entry33=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested34 : entryOK pins rs entry34=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested35 : entryOK pins rs entry35=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested36 : entryOK pins rs entry36=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested37 : entryOK pins rs entry37=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested38 : entryOK pins rs entry38=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested39 : entryOK pins rs entry39=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested40 : entryOK pins rs entry40=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested41 : entryOK pins rs entry41=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested42 : entryOK pins rs entry42=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested43 : entryOK pins rs entry43=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested44 : entryOK pins rs entry44=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested45 : entryOK pins rs entry45=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested46 : entryOK pins rs entry46=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested47 : entryOK pins rs entry47=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma tested48 : entryOK pins rs entry48=true := by decide +kernel
lemma checked : entries.all (entryOK pins rs) = true := by
  simp only [entries,List.all_cons,List.all_nil,tested0,tested1,tested2,tested3,tested4,tested5,tested6,tested7,tested8,tested9,tested10,tested11,tested12,tested13,tested14,tested15,tested16,tested17,tested18,tested19,tested20,tested21,tested22,tested23,tested24,tested25,tested26,tested27,tested28,tested29,tested30,tested31,tested32,tested33,tested34,tested35,tested36,tested37,tested38,tested39,tested40,tested41,tested42,tested43,tested44,tested45,tested46,tested47,tested48,Bool.and_true]
def rows0 : List ℕ := [513,18,72,11,67,25,81,522,578,536,592]
def rows1 : List ℕ := [18,36,72,14,70,42,98,28,84,56,112]
def rows2 : List ℕ := [18,36,136,14,134,42,162,28,148,56,176]
def rows3 : List ℕ := [18,36,192,70,134,98,162,84,148,112,176]

end LocalMatchingData

namespace LocalPinWitness
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalLambda LocalPure LocalReceiver LocalInjections LocalNormal

def gatePin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (x : Fin n → Bool) : Prop :=
  gateVal n C g x=true ∧ ∃ v : Fin n, x v=true ∧
    ∀ y, gateVal n C g y=true → y v=true → graphFun G ∅ y=true

def twoGates {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (lo hi : ℕ) (x : Fin n → Bool) : Prop :=
  gateVal n C lo x=true ∧ gateVal n C hi x=true ∧
    ∀ y, gateVal n C lo y=true → gateVal n C hi y=true → graphFun G ∅ y=true

lemma witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (tf : TopForm G C) (lo hi : ℕ) (J : junk G C={lo,hi})
    (x : Fin n → Bool) (a : ℕ) (top : a ∈ tops G C) (b : Fin 2) (g : ℕ) (dirty : g ∈ junk G C)
    (on : gateVal n C a x=true) (path : OrReaches n C (opnd C a b) g) (gOn : gateVal n C g x=true) :
    gatePin G C lo x ∨ gatePin G C hi x ∨ twoGates G C lo hi x := by
  letI : DecidableEq GateOp := gateOpDecEq
  have which : g=lo ∨ g=hi := by simpa [J] using dirty
  obtain ⟨hb,hand,below⟩ := Finset.mem_filter.mp top
  have bound := Finset.mem_range.mp hb
  let p := opnd C a (1-b)
  have pair (y : Fin n → Bool) (yg : gateVal n C g y=true) (yp : LocalTransfer.val C (List.ofFn y) p=true) :
      graphFun G ∅ y=true := by
    apply below y
    apply (top_ports ao top y).mpr
    intro d
    have left := upward y (orReaches_reach g _ path).1 yg
    fin_cases b <;> fin_cases d
    · exact left
    · exact yp
    · exact yp
    · exact left
  have pOn := (top_ports ao top x).mp on (1-b)
  have deal (h : ℕ) (hs : h=lo ∨ h=hi) (hp : OrReaches n C p h) (hh : gateVal n C h x=true) :
      twoGates G C lo hi x := by
    have both (y : Fin n → Bool) (yg : gateVal n C g y=true) (yh : gateVal n C h y=true) :=
      pair y yg (upward y (orReaches_reach h p hp).1 yh)
    have distinct : g≠h := by
      intro eq
      obtain ⟨_,_,_,y,yg,bad⟩ := Finset.mem_filter.mp dirty
      have good := both y yg (eq ▸ yg)
      simp [bad] at good
    rcases which with gl | gh <;> rcases hs with hl | he
    · exact (distinct (gl.trans hl.symm)).elim
    · subst g; subst h
      exact ⟨gOn,hh,both⟩
    · subst g; subst h
      exact ⟨hh,gOn,fun y yl yh => both y yh yl⟩
    · exact (distinct (gh.trans he.symm)).elim
  rcases (port_sources G C ao tf lo hi J bound hand (opnd_mem ao bound (1-b)) x).mp pOn with
    ⟨v,mem,high⟩ | ⟨reach,low⟩ | ⟨reach,high⟩
  · have term : gatePin G C g x := ⟨gOn,v,high,fun y yg yv => pair y yg (raw_pin y mem yv)⟩
    exact which.elim (fun e => Or.inl (e ▸ term)) (fun e => Or.inr (Or.inl (e ▸ term)))
  · exact Or.inr (Or.inr (deal lo (Or.inl rfl) reach low))
  · exact Or.inr (Or.inr (deal hi (Or.inr rfl) reach high))

end LocalPinWitness

namespace LocalMatchingCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover
open LocalMasks LocalCoverProfile LocalGraphRows LocalCentreCase LocalRowWitness LocalWireWords
open LocalSignatures LocalMatchingCheck LocalPinWitness

def pinColumn (rows : List ℕ) (v : V) := packed rows (fun r => r.testBit v.val)

abbrev profile (i j k : Fin 16) (rows : List ℕ) : Prop :=
  (∀ v : V, pinColumn rows v ∈ LocalMatchingData.pins) ∧
  (∀ t : Fin rows.length, 3 ≤ t.val → graphFun graph ∅ (rowInput rows[t.val]) = false) ∧
  3 ≤ rows.length ∧ ∀ b : Fin 3, rows.getD b.val 0 = rowAt (edgeIndex i j k b)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma profiles : profile 0 2 6 LocalMatchingData.rows0 ∧ profile 2 4 6 LocalMatchingData.rows1 ∧
    profile 2 4 7 LocalMatchingData.rows2 ∧ profile 2 4 12 LocalMatchingData.rows3 := by decide +kernel

lemma raw_mem (rows : List ℕ) (pinMem : ∀ v : V, pinColumn rows v ∈ LocalMatchingData.pins)
    (A : Finset V) : signature rows (mask A) ∈ LocalMatchingData.raw := by
  obtain ⟨zero,closed⟩ := Bool.and_eq_true_iff.mp LocalMatchingData.closed
  induction A using Finset.induction_on with
  | empty =>
    have eq : signature rows (mask (∅ : Finset V)) = 0 := by
      change packed rows _ = 0
      rw [← pack_off rows]
      apply pack_congr
      intro r _
      cases h : LocalMixerCertificate.hit (mask (∅ : Finset V)) r
      · rfl
      · obtain ⟨v,hv,_⟩ := (hit_iff _ _).mp h
        simp at hv
    exact eq ▸ List.contains_iff_mem.mp zero
  | @insert v A fresh ih =>
    have eq : signature rows (mask (insert v A)) = signature rows (mask A) ||| pinColumn rows v := by
      change packed rows _ = packed rows (LocalMixerCertificate.hit (mask A)) ||| packed rows (fun r => r.testBit v.val)
      rw [← pack_or]
      apply pack_congr
      intro r _
      apply Bool.eq_iff_iff.mpr
      rw [Bool.or_eq_true_iff,hit_iff,hit_iff]
      constructor
      · rintro ⟨u,hu,on⟩
        rcases Finset.mem_insert.mp hu with rfl | mem
        · exact Or.inr on
        · exact Or.inl ⟨u,mem,on⟩
      · rintro (⟨u,mem,on⟩ | on)
        · exact ⟨u,Finset.mem_insert_of_mem mem,on⟩
        · exact ⟨v,Finset.mem_insert_self _ _,on⟩
    rw [eq]
    exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp closed _ ih) _ (pinMem v))

lemma clean_term (rows : List ℕ)
    (negative : ∀ t : Fin rows.length, 3 ≤ t.val → graphFun graph ∅ (rowInput rows[t.val])=false)
    (f : (V → Bool) → Bool) (sound : ∀ x, f x=true → graphFun graph ∅ x=true)
    (i : Fin 3) (hi : i.val<rows.length) (pos : f (rowInput rows[i.val])=true) :
    usable (packed rows (fun r => f (rowInput r))) i.val = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    by_contra over
    have large : 2^3 ≤ packed rows (fun r => f (rowInput r)) := by omega
    obtain ⟨t,ht,bit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow large
    rw [packed_bit] at bit
    split at bit
    next inside =>
      have bad := negative ⟨t,inside⟩ ht
      have good := sound _ bit
      simp [bad] at good
    next => contradiction
  · simpa only [packed_bit,dif_pos hi] using pos

lemma pin_on (C : Circuit) (rows : List ℕ)
    (negative : ∀ t : Fin rows.length, 3 ≤ t.val → graphFun graph ∅ (rowInput rows[t.val])=false)
    (i : Fin 3) (hi : i.val<rows.length) (g : ℕ) (term : gatePin graph C g (rowInput rows[i.val])) :
    ∃ v : V, usable (wireWord 11 C rows (11+g) &&& pinColumn rows v) i.val=true := by
  obtain ⟨yg,v,yv,sound⟩ := term
  refine ⟨v,?_⟩
  let f := fun y : V → Bool => gateVal 11 C g y && y v
  have good := clean_term rows negative f (fun y h => (Bool.and_eq_true_iff.mp h).elim (sound y))
    i hi (Bool.and_eq_true_iff.mpr ⟨yg,yv⟩)
  simpa only [f,pack_and,pinColumn,wireWord,gateVal,LocalTransfer.val,rowInput] using good

lemma both_on (C : Circuit) (rows : List ℕ)
    (negative : ∀ t : Fin rows.length, 3 ≤ t.val → graphFun graph ∅ (rowInput rows[t.val])=false)
    (i : Fin 3) (hi : i.val<rows.length) (lo high : ℕ) (term : twoGates graph C lo high (rowInput rows[i.val])) :
    usable (wireWord 11 C rows (11+lo) &&& wireWord 11 C rows (11+high)) i.val=true := by
  obtain ⟨yl,yh,sound⟩ := term
  let f := fun y : V → Bool => gateVal 11 C lo y && gateVal 11 C high y
  have good := clean_term rows negative f (fun y h => (Bool.and_eq_true_iff.mp h).elim (sound y))
    i hi (Bool.and_eq_true_iff.mpr ⟨yl,yh⟩)
  simpa only [f,pack_and,wireWord,gateVal,LocalTransfer.val,rowInput] using good

lemma rejects (C : Circuit) (ao : IsAO2 11 C) (tf : TopForm graph C)
    (lo high : ℕ) (order : lo<high) (J : junk graph C={lo,high})
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, ∃ b : Fin 2, ∃ g ∈ junk graph C,
      gateVal 11 C a (pairInput u v)=true ∧ OrReaches 11 C (opnd C a b) g ∧ gateVal 11 C g (pairInput u v)=true)
    (i j k : Fin 16) (U : Ustar graph C=omitted i j k) (rows : List ℕ) (cert : profile i j k rows) : False := by
  obtain ⟨pinMem,negative,long,first⟩ := cert
  obtain ⟨r,hr,s,hs,l,hl,t,ht,lf,rf,lower,upper⟩ :=
    dirty_words graph C ao tf lo high order J rows LocalMatchingData.raw (fun w => raw_mem rows pinMem _)
  apply cert_forbids LocalMatchingData.pins LocalMatchingData.raw LocalMatchingData.rs LocalMatchingData.entries
    LocalMatchingData.dominates LocalMatchingData.firsts LocalMatchingData.checked hr hs hl ht lf rf
  intro m
  simp only [← lower] at upper
  rw [← lower,← upper]
  let h := edgeIndex i j k m
  have member : edgeAt h ∈ omitted i j k := by fin_cases m <;> simp [h,edgeIndex,omitted]
  have missing : s((endpointAt h).1,(endpointAt h).2) ∈ Ustar graph C := U ▸ member
  obtain ⟨a,top,b,g,dirty,on,path,gOn⟩ := trace _ _ missing
  have term := witness graph C ao tf lo high J (testsAt h) a top b g dirty on path gOn
  have hm : m.val<rows.length := Nat.lt_of_lt_of_le m.isLt long
  have mr : rows[m.val]=rowAt h := by simpa [List.getD_eq_getElem?_getD,hm,h] using first m
  have hx : rowInput rows[m.val] = testsAt h := mr ▸ funext (row_matches h)
  rw [← hx] at term
  apply Bool.or_eq_true_iff.mpr
  rcases term with low | up | both
  · obtain ⟨v,yes⟩ := pin_on C rows negative m hm lo low
    exact Or.inr (List.any_eq_true.mpr ⟨_,pinMem v,Bool.or_eq_true_iff.mpr (Or.inl yes)⟩)
  · obtain ⟨v,yes⟩ := pin_on C rows negative m hm high up
    exact Or.inr (List.any_eq_true.mpr ⟨_,pinMem v,Bool.or_eq_true_iff.mpr (Or.inr yes)⟩)
  · exact Or.inl (both_on C rows negative m hm lo high both)

lemma four (C : Circuit) (ao : IsAO2 11 C) (tf : TopForm graph C)
    (lo high : ℕ) (order : lo<high) (J : junk graph C={lo,high})
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, ∃ b : Fin 2, ∃ g ∈ junk graph C,
      gateVal 11 C a (pairInput u v)=true ∧ OrReaches 11 C (opnd C a b) g ∧ gateVal 11 C g (pairInput u v)=true)
    (three : (Ustar graph C).card=3) (K : Finset V) (small : K.card≤4)
    (cover : (graph.deleteEdges (Ustar graph C : Set Edge)).IsVertexCover (K : Set V)) : False := by
  obtain ⟨_,cases⟩ := four_only three cover small
  rcases cases with ⟨_,U⟩ | ⟨_,U⟩ | ⟨_,U⟩ | ⟨_,U⟩
  · exact rejects C ao tf lo high order J trace 0 2 6 U _ profiles.1
  · exact rejects C ao tf lo high order J trace 2 4 6 U _ profiles.2.1
  · exact rejects C ao tf lo high order J trace 2 4 7 U _ profiles.2.2.1
  · exact rejects C ao tf lo high order J trace 2 4 12 U _ profiles.2.2.2

end LocalMatchingCircuit

namespace LocalShapes
open LocalWordGeometry LocalClip LocalSignatures LocalSignalCert LocalMixerCertificate

abbrev Shape := ℕ × ℕ
abbrev Description := ℕ × ℕ × ℕ × ℕ

def baseMasks : List ℕ :=
  [1,2,4,5,8,16,17,18,20,21,32,33,34,48,50,64,65,68,69,72,80,81,84,85,
   128,129,136,160,161,192,256,257,258,260,272,288,289,384,385,416,417,512,514,
   516,520,528,530,544,546,560,562,576,584,768,772,1024,1026,1032,1056,1152,1160,1280,1282,1536]

set_option maxRecDepth 30000 in
lemma base_eq : allClauses=baseMasks := by decide +kernel

def rawFor (ns : List ℕ) := baseMasks.filter fun m => pins.contains m || ns.any (within m)

lemma raw_eq (u : List ℕ) : rawMasks u = rawFor (available u) := by simp only [rawMasks,rawFor,base_eq]

def shapes (ns masks : List ℕ) (K : ℕ) : List Shape :=
  ((pins.zip ns).filter (fun p => hit p.1 K)).flatMap fun p =>
    (masks.filter (fun l => within l p.2 && within (neededMask K p.2) l)).map (fun l => (p.1,l))

def describe (word : ℕ → ℕ) (s : Shape) : Description := (s.1,s.2,word s.1,word s.2)

def expand (d : Description) : List TopChoice :=
  let anchor := anchorAt d.1 d.2.1
  (List.range 3).flatMap fun s => (List.range 3).map fun t =>
    ⟨d.2.2.1,d.2.2.2,s,t,anchorPairs (anchor s) (anchor t)⟩

def descriptions (u : List ℕ) (K h : ℕ) : List Description :=
  (shapes (available u) (rawFor (available u)) K).map (describe fun m => clip h (signature (u++negatives) m))

lemma same_geometry (u : List ℕ) (K h : ℕ) :
    (options u K).map (clipChoice h) = (descriptions u K h).flatMap expand := by
  simp only [options,descriptions,shapes,expand,describe,clipChoice,raw_eq,
    TopChoice.left,TopChoice.right,TopChoice.useA,TopChoice.useB,TopChoice.anchors,
    List.map_flatMap,List.map_map,List.flatMap_map,List.flatMap_assoc,Function.comp_def]

end LocalShapes

namespace LocalColumns
open LocalShapes LocalClip LocalSignatures LocalWordGeometry LocalMixerCertificate

def negativeColumns : List (ℕ × ℕ) :=
  [(1,32767),(2,10126677),(4,521011),(5,524287),(8,11112463),(16,330410),(17,360447),
   (18,10457087),(20,523195),(21,524287),(32,1576140),(33,1605631),(34,10128861),(48,1904366),
   (50,10457087),(64,401648),(65,425983),(68,521203),(69,524287),(72,11514111),(80,469754),
   (81,491519),(84,523259),(85,524287),(128,5263104),(129,5275647),(136,16375567),(160,5787596),
   (161,5799935),(192,5664752),(256,6320128),(257,6324223),(258,16446805),(260,6812467),
   (272,6650538),(288,7896268),(289,7897087),(384,7372544),(385,7372799),(416,7897036),
   (417,7897087),(512,8880128),(514,10454357),(516,8909619),(520,11505679),(528,8882858),
   (530,10457087),(544,10456268),(546,10456541),(560,10456814),(562,10457087),(576,8888560),
   (584,11514111),(768,15200256),(772,15201075),(1024,16252928),(1026,16418133),(1032,16355343),
   (1056,16256204),(1152,16273152),(1160,16375567),(1280,16281600),(1282,16446805),(1536,16744448)]

def negAt (m : ℕ) := (negativeColumns.lookup m).getD 0

set_option maxRecDepth 15000 in
lemma neg_correct : ∀ m ∈ baseMasks, negAt m=signature negatives m := by decide +kernel

lemma pins_base : ∀ p ∈ pins, p ∈ baseMasks := by decide +kernel

def word (a b c h m : ℕ) :=
  clip h ((((negAt m*2+(hit m c).toNat)*2+(hit m b).toNat)*2)+(hit m a).toNat)

lemma sig_cons (r : ℕ) (rs : List ℕ) (m : ℕ) :
    signature (r::rs) m = signature rs m * 2 + (hit m r).toNat := by
  exact BitVec.toNat_concat (BitVec.ofBoolListLE (rs.map (hit m))) (hit m r)

lemma word_eq (a b c h m : ℕ) (mem : m ∈ baseMasks) :
    clip h (signature ([a,b,c]++negatives) m) = word a b c h m := by
  simp only [List.cons_append,List.nil_append,sig_cons,word,neg_correct m mem]

lemma raw_base {ns : List ℕ} {m : ℕ} (mem : m ∈ rawFor ns) : m ∈ baseMasks := (List.mem_filter.mp mem).1

lemma shape_base {ns : List ℕ} {K : ℕ} {s : Shape} (mem : s ∈ shapes ns (rawFor ns) K) :
    s.1 ∈ baseMasks ∧ s.2 ∈ baseMasks := by
  obtain ⟨⟨c,n⟩,found,leaves⟩ := List.mem_flatMap.mp mem
  obtain ⟨l,ok,rfl⟩ := List.mem_map.mp leaves
  exact ⟨pins_base c (List.of_mem_zip (List.mem_filter.mp found).1).1,raw_base (List.mem_filter.mp ok).1⟩

lemma raw_words (a b c h : ℕ) :
    (0 :: (rawMasks [a,b,c]).map (signature ([a,b,c]++negatives))).map (clip h) =
      0 :: (rawFor (available [a,b,c])).map (word a b c h) := by
  simp only [raw_eq,List.map_cons,List.map_map,show clip h 0=0 by simp [clip],List.cons.injEq,true_and]
  exact List.map_congr_left (fun m hm => word_eq a b c h m (raw_base hm))

lemma describe_words (a b c h K : ℕ) :
    descriptions [a,b,c] K h = (shapes (available [a,b,c]) (rawFor (available [a,b,c])) K).map (describe (word a b c h)) := by
  apply List.map_congr_left
  intro s hs
  obtain ⟨left,right⟩ := shape_base hs
  simp only [describe,word_eq a b c h s.1 left,word_eq a b c h s.2 right]

end LocalColumns

namespace LocalDeck
end LocalDeck

namespace LocalCircuitSlice
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalCoverProfile LocalGraphRows LocalCentreCase LocalSmallCover LocalMasks LocalDeck LocalCenters
open LocalMixerCertificate LocalModelBridge

lemma cover_membership (i j k : Fin 16) (K : Finset V) (size : K.card=4 ∨ K.card=5)
    (cover : (graph.deleteEdges (omitted i j k : Set Edge)).IsVertexCover (K : Set V)) :
    mask K ∈ coverMasks (tripleRows i j k) := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (mask_small K),?_⟩,?_⟩
  · rcases size with h | h <;> simp [pin_count,h]
  · apply List.all_eq_true.mpr
    intro e he
    obtain ⟨row,keep⟩ := List.mem_filter.mp he
    obtain ⟨l,rfl⟩ := all_rows_indexed _ row
    have kept : edgeAt l ∉ omitted i j k := by
      intro removed
      have left : rowAt l ∉ tripleRows i j k := by simpa using keep
      apply left
      simp [omitted] at removed
      rcases removed with h | h | h <;> have eq := edgeAt_inj h <;> simp [tripleRows,eq]
    have edge : (graph.deleteEdges (omitted i j k : Set Edge)).Adj (endpointAt l).1 (endpointAt l).2 :=
      SimpleGraph.deleteEdges_adj.mpr ⟨all_rows_adjacent l,kept⟩
    apply (hit_iff _ _).mpr
    rcases cover edge with h | h
    · exact ⟨_,h,(row_matches l _).trans (by simp [testsAt,pairInput])⟩
    · exact ⟨_,h,(row_matches l _).trans (by simp [testsAt,pairInput])⟩

end LocalCircuitSlice

namespace LocalSparseDeck
open PEqualNP.MetaComplexity.NestedCover
open LocalMixerCertificate LocalMasks LocalCoverProfile LocalCircuitSlice LocalCentreCase LocalClip

def eligible : List ℕ :=
  [241,341,369,405,433,453,465,468,481,496,597,598,604,625,626,628,632,724,752,796,
   837,838,844,849,852,856,880,916,964,976,1187,1194,1201,1202,1208,1250,1264,1321,
   1322,1336,1377,1378,1384,1392,1411,1413,1414,1417,1418,1420,1425,1428,1432,1440,
   1441,1442,1444,1448,1456,1473,1474,1476,1488,1504,1550,1562,1564,1578,1586,1592,
   1606,1610,1618,1620,1624,1634,1640,1648,1670,1674,1682,1684,1688,1698,1704,1712,
   1730,1744,1760,1798,1800,1801,1802,1804,1812,1816,1826,1832,1840,1856,1857,1858,
   1860,1864,1872,1888,1920,1921,1922,1924,1928,1936,1952,1984]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
lemma eligible_complete : ∀ K : Finset V, (K.card=4 ∨ K.card=5) → (missing K).card ≤ 3 →
    mask K ∈ eligible := by decide +kernel

def masksFor (u : List ℕ) : List ℕ := eligible.filter fun m =>
  (rows.filter (fun e => !(u.contains e))).all (hit m)

lemma sparse_mem (i j k : Fin 16) (K : Finset V) (size : K.card=4 ∨ K.card=5)
    (cover : (graph.deleteEdges (omitted i j k : Set Edge)).IsVertexCover (K : Set V)) :
    mask K ∈ masksFor (tripleRows i j k) := by
  have small : (omitted i j k).card ≤ 3 := by
    unfold omitted
    calc _ ≤ ({edgeAt j,edgeAt k} : Finset Edge).card+1 := Finset.card_insert_le ..
         _ ≤ (({edgeAt k} : Finset Edge).card+1)+1 := Nat.add_le_add_right (Finset.card_insert_le ..) 1
         _ = 3 := by simp
  have possible := eligible_complete K size ((Finset.card_le_card (missing_subset cover)).trans small)
  have original := cover_membership i j k K size cover
  exact List.mem_filter.mpr ⟨possible,(List.mem_filter.mp original).2⟩

def sparseDeck (u : List ℕ) (h : ℕ) := (masksFor u).all (clippedCheck h u)

end LocalSparseDeck

namespace LocalFastCert
open LocalWordGeometry LocalMixerCertificate LocalClip LocalShapes LocalColumns LocalSignalCert LocalSparseDeck

abbrev Cases := List (ℕ × List Description)

def checkCase (a b c h : ℕ) (ns masks : List ℕ) (ps : Pairs) (entry : ℕ × List Description) : Bool :=
  ((shapes ns masks entry.1).map (describe (word a b c h)) == entry.2) &&
    geometryCheck (entry.2.flatMap expand) ps

def audit (a b c h : ℕ) (ns masks rs firsts : List ℕ) (ps : Pairs) (cases : Cases) : Bool :=
  (available [a,b,c] == ns) &&
  ((rawFor ns == masks) &&
  ((masksFor [a,b,c] == cases.map Prod.fst) &&
  (reps rs (0::masks.map (word a b c h)) &&
  (sourceCheck rs firsts ps && cases.all (checkCase a b c h ns masks ps)))))

lemma audit_sound (a b c h K : ℕ) (keep : ∀ i : Fin 3, h.testBit i.val=true)
    (ns masks rs firsts : List ℕ) (ps : Pairs) (cases : Cases)
    (checked : audit a b c h ns masks rs firsts ps cases=true) (mem : K ∈ masksFor [a,b,c]) :
    LocalModelBridge.rejectsProducts [a,b,c] K := by
  simp only [audit,Bool.and_eq_true_iff,beq_iff_eq] at checked
  obtain ⟨neigh,allow,keys,raw,sources,each⟩ := checked
  rw [keys] at mem
  obtain ⟨⟨_,ds⟩,found,rfl⟩ := List.mem_map.mp mem
  have witness := List.all_eq_true.mp each _ found
  obtain ⟨described,geometry⟩ := Bool.and_eq_true_iff.mp witness
  apply projected_cert _ _ h keep rs firsts ps
  · rwa [raw_words,neigh,allow]
  · exact sources
  · rw [same_geometry,describe_words,neigh,allow,beq_iff_eq.mp described]
    exact geometry

end LocalFastCert

namespace LocalPacket
open LocalFastCert LocalSignalCert LocalMixerCertificate LocalSparseDeck LocalSignatures

abbrev Packet := ℕ × List ℕ × List ℕ × List ℕ × List ℕ × Pairs × Cases
abbrev Group := List (ℕ × Packet)

def run (a b c : ℕ) : Packet → Bool
  | (h,ns,masks,rs,fs,ps,cs) => ((h &&& 7) == 7) && audit a b c h ns masks rs fs ps cs

def absent (a b c : ℕ) : Prop := ∀ K ∈ masksFor [a,b,c], LocalModelBridge.rejectsProducts [a,b,c] K

lemma run_sound (a b c : ℕ) (p : Packet) (passed : run a b c p=true) : absent a b c := by
  obtain ⟨h,ns,masks,rs,fs,ps,cs⟩ := p
  obtain ⟨pos,ok⟩ := Bool.and_eq_true_iff.mp passed
  have keep (i : Fin 3) : h.testBit i.val=true := by
    have eq : h &&& 7 = 7 := beq_iff_eq.mp pos
    simpa [Nat.testBit_and,seven,i.isLt] using congrArg (fun w : ℕ => w.testBit i.val) eq
  exact fun K mem => audit_sound a b c h K keep ns masks rs fs ps cs ok mem

def group (a b : ℕ) (cases : Group) : Bool :=
  ((List.range 16).filter (fun c => decide (b<c))).all fun c =>
    let x := rows.getD a 0
    let y := rows.getD b 0
    let z := rows.getD c 0
    match cases.lookup c with
    | none => (masksFor [x,y,z]).isEmpty
    | some p => run x y z p

end LocalPacket

namespace LocalPhysicalDeck
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover
open LocalCoverProfile LocalGraphRows LocalCentreCase LocalModelBridge LocalCenters LocalMasks LocalPacket LocalSparseDeck

def coveredTests := ∀ i j k : Fin 16, i<j → j<k → absent (rowAt i) (rowAt j) (rowAt k)

lemma two_exceptional (complete : coveredTests) (C : Circuit) (ao : IsAO2 11 C) (tf : TopForm graph C)
    (lo hi : ℕ) (order : lo<hi) (J : junk graph C={lo,hi}) (nested : InCone 11 C lo hi)
    (two : (orN graph C \ lam graph C).card = 2)
    (nz : centreless graph C = ∅) (narrow : thin C) (num : (tops graph C).card ≤ 5)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, gateVal 11 C a (pairInput u v) = true)
    (three : (Ustar graph C).card=3) : False := by
  obtain ⟨i,j,k,hij,hjk,edges⟩ := actual_triple (U := Ustar graph C) Finset.sdiff_subset three
  have eq : Ustar graph C = omitted i j k := edges
  have centered := center_cover nz narrow
  have cap : (centers C).card≤5 := Finset.card_image_le.trans num
  have size : (centers C).card=4 ∨ (centers C).card=5 := by
    by_cases b : (centers C).card ≤ 4
    · exact Or.inl (four_only three centered b).1
    · exact Or.inr (by omega)
  have member := sparse_mem i j k (centers C) size (eq ▸ centered)
  exact no_pair_of_rejection C ao tf lo hi order J nested two nz narrow num shape trace three i j k eq
    (complete i j k hij hjk _ member)

end LocalPhysicalDeck

namespace LocalRemaining
open LocalCoverProfile LocalCentreCase LocalMixerCase
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

lemma arithmetic {s k t z o : ℕ} (size : s ≤ 21) (hk : 4 ≤ k) (ht : k ≤ t)
    (pos : 0 < 2*z+o) (budget : t+2*z+o ≤ s+3-17)
    (nc : ¬(z=1 ∧ o=0)) (nm : ¬(z=0 ∧ o=1)) :
    (k=4 ∧ z=0 ∧ o=2 ∧ t≤5) ∨ (k=4 ∧ z=0 ∧ o=3 ∧ t=4 ∧ s=21) ∨
    (k=4 ∧ z=1 ∧ o=1 ∧ t=4 ∧ s=21) ∨ (k=5 ∧ z=0 ∧ o=2 ∧ t=5 ∧ s=21) := by
  have cap : t+2*z+o ≤ 7 := by omega
  by_cases cz : z=0
  · have low : 2 ≤ o := by omega
    by_cases co : o=2
    · by_cases ck : k=4
      · exact Or.inl ⟨ck,cz,co,by omega⟩
      · exact Or.inr (Or.inr (Or.inr ⟨by omega,cz,co,by omega,by omega⟩))
    · exact Or.inr (Or.inl ⟨by omega,cz,by omega,by omega,by omega⟩)
  · have one : z=1 := by omega
    have nonzero : o≠0 := fun h => nc ⟨one,h⟩
    exact Or.inr (Or.inr (Or.inl ⟨by omega,one,by omega,by omega,by omega⟩))

lemma remaining_cases (C : Circuit) (ao : IsAO2 11 C)
    (shape : ∀ a ∈ tops graph C, ∀ l ∈ side C a (0 : Fin 2), ∀ r ∈ side C a (1 : Fin 2), graph.Adj l r)
    (trace : ∀ u v : V, s(u,v) ∈ Ustar graph C → ∃ a ∈ tops graph C, gateVal 11 C a (pairInput u v) = true)
    (three : (Ustar graph C).card = 3)
    (size : C.size ≤ 21) (k : ℕ) (hk : 4 ≤ k) :
    let t := (tops graph C \ centreless graph C).card
    let z := (centreless graph C).card
    let o := (orN graph C \ lam graph C).card
    k ≤ t → 0 < 2*z+o → t+2*z+o ≤ C.size+(Ustar graph C).card-17 →
    (k=4 ∧ z=0 ∧ o=2 ∧ t≤5) ∨
    (k=4 ∧ z=0 ∧ o=3 ∧ t=4 ∧ C.size=21) ∨
    (k=4 ∧ z=1 ∧ o=1 ∧ t=4 ∧ C.size=21) ∨
    (k=5 ∧ z=0 ∧ o=2 ∧ t=5 ∧ C.size=21) := by
  dsimp only
  intro kt pos budget
  have nc : ¬((centreless graph C).card=1 ∧ (orN graph C \ lam graph C).card=0) := by
    rintro ⟨hz,ho⟩
    obtain ⟨z,eq⟩ := Finset.card_eq_one.mp hz
    exact centreless_case C ao z eq (Finset.card_eq_zero.mp ho) shape trace three
  have nm : ¬((centreless graph C).card=0 ∧ (orN graph C \ lam graph C).card=1) := by
    rintro ⟨hz,ho⟩
    obtain ⟨m,eq⟩ := Finset.card_eq_one.mp ho
    exact mixer_case C ao m eq (Finset.card_eq_zero.mp hz) shape trace three
  rw [three] at budget
  exact arithmetic size hk kt pos budget nc nm

end LocalRemaining

namespace LocalFromDeck

abbrev graphDecision : DecidableRel LocalCoverProfile.graph.Adj := by
  unfold LocalCoverProfile.graph
  infer_instance

lemma finish (whole : LocalPhysicalDeck.coveredTests) : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x4 < x5 →           PEqualNP.TopForm.junk x1 x3 = {x4, x5} →             PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →               have x12 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;               have x13 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;               have x14 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;               have x15 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;               (∀ x16 ∈ x15,                   have x18 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x16;                   (∀ x19 ∈ x18 (0 : Fin (2 : ℕ)), ∀ x21 ∈ x18 (1 : Fin (2 : ℕ)), x1.Adj x19 x21) ∧ ((x18 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x18 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →                 (∀ (x17 x18 : Fin (11 : ℕ)), s(x17, x18) ∈ x12 → ∃ x20 ∈ x15, ∃ (x21 : Fin (2 : ℕ)), ∃ x22 ∈ PEqualNP.TopForm.junk x1 x3, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x20 (PEqualNP.EdgeOwnership.pairInput x17 x18) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x20 x21) x22 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x22 (PEqualNP.EdgeOwnership.pairInput x17 x18) = Bool.true) → x3.size ≤ (21 : ℕ) → x12.card = (3 : ℕ) → ∀ (x20 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x12) x20 → (4 : ℕ) ≤ x20.card → x20.card ≤ (x15 \ x13).card → (0 : ℕ) < (2 : ℕ) * x13.card + x14.card → (x15 \ x13).card + (2 : ℕ) * x13.card + x14.card ≤ x3.size + x12.card - (17 : ℕ) → False := by
  intro G decG C lo hi eq least tf order J nested
  subst G
  have same : decG = LocalFromDeck.graphDecision := Subsingleton.elim _ _
  subst decG
  letI : DecidableRel LocalCoverProfile.graph.Adj := LocalFromDeck.graphDecision
  dsimp only
  intro sides trace size three K cover lower enough positive budget
  let G := LocalCoverProfile.graph
  have compact (u v : LocalCoverProfile.V) (missing : s(u,v) ∈ PEqualNP.TopForm.Ustar G C) :
      ∃ a ∈ PEqualNP.TopForm.tops G C, PEqualNP.EdgeOwnership.gateVal 11 C a (PEqualNP.EdgeOwnership.pairInput u v)=true := by
    obtain ⟨a,ha,b,g,hg,on,path,gOn⟩ := trace u v missing
    exact ⟨a,ha,on⟩
  by_cases small : K.card ≤ 4
  · exact LocalMatchingCircuit.four C least.1 tf lo hi order J trace three K small cover.1
  · have cases := LocalRemaining.remaining_cases C least.1 (fun a ha => (sides a ha).1)
        compact three size K.card lower enough positive budget
    rcases cases with ⟨k,_,_,_⟩ | ⟨k,_,_,_,_⟩ | ⟨k,_,_,_,_⟩ | ⟨_,z,o,t,_⟩
    · omega
    · omega
    · omega
    · have empty := Finset.card_eq_zero.mp z
      have num : (PEqualNP.TopForm.tops G C).card ≤ 5 := by simpa [empty] using t.le
      exact LocalPhysicalDeck.two_exceptional whole C least.1 tf lo hi order J nested o empty
        (fun a ha => (sides a ha).2) num (fun a ha => (sides a ha).1) compact three

end LocalFromDeck

namespace LocalReverseGeo
open LocalGeometrySound LocalWordGeometry LocalShapes LocalFastCert LocalSignalCert

lemma recover (xs : List TopChoice) (a b : ℕ) (acc : TripleWord) (i : Fin 3) (ix : ℕ)
    (h : (part (xs.foldl (joinStep a b) acc) i).testBit ix=true) :
    (part acc i).testBit ix=true ∨ ∃ q ∈ xs, topValue q a b ≤ 7 ∧
      (topValue q a b).testBit i.val=true ∧ q.anchors.testBit ix=true := by
  induction xs generalizing acc with
  | nil => exact Or.inl h
  | cons q rest ih =>
    rcases ih (joinStep a b acc q) h with before | ⟨o,mem,yes⟩
    · rw [part_step] at before
      split at before
      next accepted =>
        rw [Nat.testBit_or,Bool.or_eq_true_iff] at before
        rcases before with was | new
        · exact Or.inl was
        · exact Or.inr ⟨q,List.mem_cons_self,accepted.1,accepted.2,new⟩
      next dropped => exact Or.inl before
    · exact Or.inr ⟨o,List.mem_cons_of_mem _ mem,yes⟩

lemma surviving_model (xs : List TopChoice) (a b : ℕ) (h : surviving xs a b ≠ 0) :
    ∃ ix : ℕ, model xs a b ix := by
  have low : 2^0 ≤ surviving xs a b := by change 1 ≤ _; omega
  obtain ⟨ix,_,bit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow low
  let t := xs.foldl (joinStep a b) (0,0,0)
  change (t.1 &&& t.2.1 &&& t.2.2).testBit ix=true at bit
  simp only [Nat.testBit_and,Bool.and_eq_true_iff] at bit
  refine ⟨ix,?_⟩
  intro i
  have on : (part t i).testBit ix=true := by
    fin_cases i
    · exact bit.1.1
    · exact bit.1.2
    · exact bit.2
  rcases recover xs a b (0,0,0) i ix on with zero | witness
  · fin_cases i <;> simp [part] at zero
  · exact witness

def words (l r a b : ℕ) : List ℕ :=
  [l &&& r,(l ||| a) &&& r,l &&& (r ||| a),(l ||| b) &&& r,l &&& (r ||| b),
   (l ||| a ||| b) &&& r,l &&& (r ||| a ||| b),(l ||| a) &&& (r ||| b),(l ||| b) &&& (r ||| a)]

def atRow (ds : List Description) (a b i : ℕ) : Bool :=
  ds.any fun d => (words d.2.2.1 d.2.2.2 a b).any fun t => decide (t≤7) && t.testBit i

lemma word_member {d : Description} {q : TopChoice} (mem : q ∈ expand d) (a b : ℕ) :
    topValue q a b ∈ words d.2.2.1 d.2.2.2 a b := by
  obtain ⟨s,hs,rest⟩ := List.mem_flatMap.mp mem
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp rest
  have sb := List.mem_range.mp hs
  have tb := List.mem_range.mp ht
  interval_cases s <;> interval_cases t <;> simp [topValue,words,
    TopChoice.left,TopChoice.right,TopChoice.useA,TopChoice.useB]

lemma row_necessary {ds : List Description} {a b ix : ℕ} (m : model (ds.flatMap expand) a b ix)
    (i : Fin 3) : atRow ds a b i.val=true := by
  obtain ⟨q,hq,safe,pos,_⟩ := m i
  obtain ⟨d,mem,shape⟩ := List.mem_flatMap.mp hq
  exact List.any_eq_true.mpr ⟨d,mem,List.any_eq_true.mpr ⟨_,word_member shape a b,
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true safe,pos⟩⟩⟩

def separated (ds : List Description) (a b : ℕ) :=
  !(atRow ds a b 0 && atRow ds a b 1 && atRow ds a b 2) ||
    surviving (ds.flatMap expand) a b == 0

def quickGeometry (ds : List Description) (ps : Pairs) := ps.all fun p =>
  separated ds p.1 p.2 && separated ds p.2 p.1

end LocalReverseGeo

namespace LocalHints
open LocalWordGeometry LocalGeometrySound LocalShapes LocalColumns LocalReverseGeo LocalSignalCert LocalFastCert
open LocalPacket LocalSparseDeck LocalMixerCertificate

def directed (ds : List Description) (a b hint : ℕ) : Bool :=
  if hint<3 then !(atRow ds a b hint) else surviving (ds.flatMap expand) a b == 0

lemma directed_sound {ds : List Description} {a b hint : ℕ} (ok : directed ds a b hint=true) :
    surviving (ds.flatMap expand) a b = 0 := by
  by_cases h : hint<3
  · by_contra nz
    obtain ⟨ix,m⟩ := surviving_model _ _ _ nz
    have yes := row_necessary m (⟨hint,h⟩ : Fin 3)
    simp [directed,h,yes] at ok
  · exact beq_iff_eq.mp (by simpa [directed,h] using ok)

def hinted (ds : List Description) : Pairs → ℕ → Bool
  | [], _ => true
  | (a,b)::ps, code =>
    directed ds a b (code % 4) && ((a==b || directed ds b a ((code/4)%4)) && hinted ds ps (code/16))

lemma hinted_sound (ds : List Description) (ps : Pairs) (code : ℕ) (ok : hinted ds ps code=true) :
    geometryCheck (ds.flatMap expand) ps=true := by
  induction ps generalizing code with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    obtain ⟨first,rest⟩ := Bool.and_eq_true_iff.mp ok
    obtain ⟨rev,tail⟩ := Bool.and_eq_true_iff.mp rest
    have ab := directed_sound first
    have ba : surviving (ds.flatMap expand) b a=0 := by
      rcases Bool.or_eq_true_iff.mp rev with eq | checked
      · exact (beq_iff_eq.mp eq) ▸ ab
      · exact directed_sound checked
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr ab,beq_iff_eq.mpr ba⟩,ih _ tail⟩

abbrev HCases := List (ℕ × ℕ × List Description)

def plain (e : ℕ × ℕ × List Description) : ℕ × List Description := (e.1,e.2.2)

def caseTest (a b c h : ℕ) (ns masks : List ℕ) (ps : Pairs) (e : ℕ × ℕ × List Description) :=
  ((shapes ns masks e.1).map (describe (word a b c h)) == e.2.2) && hinted e.2.2 ps e.2.1

abbrev HPacket := ℕ × List ℕ × List ℕ × List ℕ × List ℕ × Pairs × HCases
abbrev HGroup := List (ℕ × HPacket)

def run (a b c : ℕ) : HPacket → Bool
  | (h,ns,masks,rs,fs,ps,hs) =>
    ((h &&& 7) == 7) && ((available [a,b,c] == ns) && ((rawFor ns == masks) &&
      ((masksFor [a,b,c] == hs.map Prod.fst) && (reps rs (0::masks.map (word a b c h)) &&
      (sourceCheck rs fs ps && hs.all (caseTest a b c h ns masks ps))))))

lemma sound (a b c : ℕ) (p : HPacket) (ok : run a b c p=true) : absent a b c := by
  obtain ⟨h,ns,masks,rs,fs,ps,hs⟩ := p
  simp only [run,Bool.and_eq_true_iff,beq_iff_eq] at ok
  obtain ⟨pos,neighbors,allows,keys,reps,src,hints⟩ := ok
  apply LocalPacket.run_sound a b c (h,ns,masks,rs,fs,ps,hs.map plain)
  apply Bool.and_eq_true_iff.mpr
  refine ⟨beq_iff_eq.mpr pos,?_⟩
  simp only [audit,Bool.and_eq_true_iff,beq_iff_eq]
  refine ⟨neighbors,allows,?_,reps,src,?_⟩
  · simpa [List.map_map,plain,Function.comp_def] using keys
  · apply List.all_eq_true.mpr
    intro e mem
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp mem
    obtain ⟨desc,proof⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hints q hq)
    exact Bool.and_eq_true_iff.mpr ⟨desc,hinted_sound _ _ _ proof⟩

def group (a b : ℕ) (hs : HGroup) : Bool :=
  ((List.range 16).filter (fun c => decide (b<c))).all fun c =>
    let x := rows.getD a 0
    let y := rows.getD b 0
    let z := rows.getD c 0
    match hs.lookup c with
    | none => (masksFor [x,y,z]).isEmpty
    | some p => run x y z p

end LocalHints

namespace LocalLightMasks
open LocalMixerCertificate LocalSparseDeck

def misses (k : ℕ) := rows.filter (fun e => !hit k e)

def missingTable : List (ℕ × List ℕ) :=
  [(241,[258,1028,768]),(341,[136,544,640]),(369,[1028,136,640]),(405,[72,544,1088]),(433,[1028,72,1088]),(453,[18,1040,544]),(465,[36,1028,544]),(468,[513,1025,544]),(481,[18,1028,1040]),(496,[513,1025,1028]),(597,[258,136,288]),(598,[1025,136,288]),(604,[1025,258,288]),(625,[258,1028,136]),(626,[1025,1028,136]),(628,[1025,258,136]),(632,[1025,258,1028]),(724,[1025,258,288]),(752,[1025,258,1028]),(796,[1025,192,1088]),(837,[18,136,1040]),(838,[1025,136,1040]),(844,[1025,18,1040]),(849,[36,1028,136]),(852,[1025,136]),(856,[1025,36,1028]),(880,[1025,1028,136]),(916,[1025,72,1088]),(964,[1025,18,1040]),(976,[1025,36,1028]),(1187,[72,272,768]),(1194,[513,272,768]),(1201,[258,72,768]),(1202,[513,72,768]),(1208,[513,258,768]),(1250,[513,272,768]),(1264,[513,258,768]),(1321,[18,192,640]),(1322,[513,192,640]),(1336,[513,192,640]),(1377,[18,136,640]),(1378,[513,136,640]),(1384,[513,18,640]),(1392,[513,136,640]),(1411,[36,72,544]),(1413,[18,72,544]),(1414,[513,72,544]),(1417,[18,36,544]),(1418,[513,36,544]),(1420,[513,18,544]),(1425,[36,72,544]),(1428,[513,72,544]),(1432,[513,36,544]),(1440,[513,18,72]),(1441,[18,72]),(1442,[513,72]),(1444,[513,18,72]),(1448,[513,18]),(1456,[513,72]),(1473,[18,36,544]),(1474,[513,36,544]),(1476,[513,18,544]),(1488,[513,36,544]),(1504,[513,18]),(1550,[272,288,192]),(1562,[36,288,192]),(1564,[258,288,192]),(1578,[272,192]),(1586,[72,136,192]),(1592,[258,192]),(1606,[136,272,288]),(1610,[36,272,288]),(1618,[36,136,288]),(1620,[258,136,288]),(1624,[258,36,288]),(1634,[136,272]),(1640,[18,258,272]),(1648,[258,136]),(1670,[72,272,288]),(1674,[36,272,288]),(1682,[36,72,288]),(1684,[258,72,288]),(1688,[258,36,288]),(1698,[72,272]),(1704,[18,258,272]),(1712,[258,72]),(1730,[36,272,288]),(1744,[258,36,288]),(1760,[18,258,272]),(1798,[72,136,192]),(1800,[18,36,192]),(1801,[18,36,192]),(1802,[36,192]),(1804,[18,192]),(1812,[72,136,192]),(1816,[36,192]),(1826,[72,136,192]),(1832,[18,192]),(1840,[72,136,192]),(1856,[18,36,136]),(1857,[18,36,136]),(1858,[36,136]),(1860,[18,136]),(1864,[18,36]),(1872,[36,136]),(1888,[18,136]),(1920,[18,36,72]),(1921,[18,36,72]),(1922,[36,72]),(1924,[18,72]),(1928,[18,36]),(1936,[36,72]),(1952,[18,72]),(1984,[18,36])]

set_option maxRecDepth 20000 in
lemma table_ok : missingTable = eligible.map (fun k => (k,misses k)) := by decide +kernel

def availableCovers (u : List ℕ) :=
  (missingTable.filter (fun e => e.2.all u.contains)).map Prod.fst

lemma dual (k : ℕ) (u : List ℕ) :
    (rows.filter (fun e => !(u.contains e))).all (hit k) = (misses k).all u.contains := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro ok
    apply List.all_eq_true.mpr
    intro e mem
    obtain ⟨row,off⟩ := List.mem_filter.mp mem
    cases h : u.contains e
    · have bad := List.all_eq_true.mp ok e (List.mem_filter.mpr ⟨row,congrArg Bool.not h⟩)
      simp [bad] at off
    · rfl
  · intro ok
    apply List.all_eq_true.mpr
    intro e mem
    obtain ⟨row,out⟩ := List.mem_filter.mp mem
    cases h : hit k e
    · have bad := List.all_eq_true.mp ok e (List.mem_filter.mpr ⟨row,by simp [h]⟩)
      exact (congrArg Bool.not bad).symm.trans out
    · rfl

lemma computed (u : List ℕ) : availableCovers u = masksFor u := by
  unfold availableCovers masksFor
  rw [table_ok]
  generalize eligible = xs
  induction xs with
  | nil => rfl
  | cons k xs ih =>
    simp only [List.map_cons,List.filter_cons]
    rw [dual k u]
    cases (misses k).all u.contains <;> simp only [Bool.false_eq_true,ite_true,ite_false,List.map_cons,ih]

end LocalLightMasks

namespace LocalLightSources
open LocalMixerCertificate LocalBetter LocalSignalCert

lemma within_of_bits {a b : ℕ} (h : ∀ i, a.testBit i=true → b.testBit i=true) : within a b=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  cases hi : a.testBit i <;> simp [Nat.testBit_and,hi,h]

lemma beats_of_better {a b : ℕ} (h : Better a b) : beats a b=true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply within_of_bits
    intro i v
    simp only [Nat.testBit_and,Bool.and_eq_true_iff] at v ⊢
    have low : i<3 := by simpa [LocalSignatures.seven] using v.2
    exact ⟨h.1 i low v.1,v.2⟩
  · apply within_of_bits
    intro i v
    simp only [Nat.testBit_shiftRight] at v ⊢
    exact h.2 _ (by omega) v

def add (r : ℕ) (ys : List ℕ) := if ys.any (fun y => beats y r) then ys else r::(ys.filter (fun y => !beats r y))

def maxima : List ℕ → List ℕ
  | [] => []
  | r::rs => add r (maxima rs)

lemma dominates {rs : List ℕ} {r : ℕ} (mem : r ∈ rs) : ∃ y ∈ maxima rs, Better y r := by
  induction rs with
  | nil => simp at mem
  | cons x rest ih =>
    change ∃ y ∈ add x (maxima rest), Better y r
    unfold add
    split
    next yes =>
      rcases List.mem_cons.mp mem with rfl | tail
      · obtain ⟨y,hy,ok⟩ := List.any_eq_true.mp yes
        exact ⟨y,hy,beats_sound ok⟩
      · exact ih tail
    next _ =>
      rcases List.mem_cons.mp mem with rfl | tail
      · exact ⟨_,List.mem_cons_self,self _⟩
      · obtain ⟨y,hy,byr⟩ := ih tail
        by_cases covers : beats x y=true
        · exact ⟨x,List.mem_cons_self,chain (beats_sound covers) byr⟩
        · exact ⟨y,List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hy,by simpa using covers⟩),byr⟩

lemma represents_weaker {ps : Pairs} {a b c d : ℕ} (mode : representsPair ps a b=true)
    (ac : Better a c) (bd : Better b d) : representsPair ps c d=true := by
  obtain ⟨p,mem,h⟩ := List.any_eq_true.mp mode
  apply List.any_eq_true.mpr
  refine ⟨p,mem,Bool.or_eq_true_iff.mpr ?_⟩
  have reduce {x y : ℕ} (ok : (beats x a && beats y b)=true) :
      (beats x c && beats y d)=true := by
    obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp ok
    exact Bool.and_eq_true_iff.mpr ⟨beats_of_better (chain (beats_sound l) ac),beats_of_better (chain (beats_sound r) bd)⟩
  exact (Bool.or_eq_true_iff.mp h).imp reduce reduce

def products (xs : List ℕ) := xs.flatMap (fun x => xs.map (fun y => x &&& y))

def check (rs firsts : List ℕ) (ps : Pairs) :=
  rs.all (fun x => rs.all (fun y => firsts.any (fun a => beats a (x &&& y)))) &&
    firsts.all (fun a =>
      let sides := maxima (rs ++ rs.map (fun r => r ||| a))
      representsPair ps a a && (maxima (products sides)).all (fun b => representsPair ps a b && representsPair ps b b))

lemma sound (rs firsts : List ℕ) (ps : Pairs) (ok : check rs firsts ps=true) : sourceCheck rs firsts ps=true := by
  obtain ⟨first,second⟩ := Bool.and_eq_true_iff.mp ok
  apply Bool.and_eq_true_iff.mpr
  refine ⟨first,List.all_eq_true.mpr ?_⟩
  intro a ha
  obtain ⟨aa,ands⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp second a ha)
  apply Bool.and_eq_true_iff.mpr
  refine ⟨aa,List.all_eq_true.mpr ?_⟩
  intro x hx
  apply List.all_eq_true.mpr
  intro y hy
  obtain ⟨x',mx,bx⟩ := dominates hx
  obtain ⟨y',my,byy⟩ := dominates hy
  have mem : x' &&& y' ∈ products (maxima (rs ++ rs.map (fun r => r ||| a))) :=
    List.mem_flatMap.mpr ⟨x',mx,List.mem_map.mpr ⟨y',my,rfl⟩⟩
  obtain ⟨z,mz,bz⟩ := dominates mem
  have better := chain bz (conj bx byy)
  obtain ⟨az,zz⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ands z mz)
  exact Bool.and_eq_true_iff.mpr ⟨represents_weaker az (self a) better,represents_weaker zz better better⟩

end LocalLightSources

namespace LocalLightPackets
open LocalMixerCertificate LocalShapes LocalColumns LocalPacket LocalHints LocalSignalCert LocalLightMasks

def run (a b c : ℕ) : HPacket → Bool
  | (h,ns,masks,rs,fs,ps,hs) =>
    ((h &&& 7) == 7) && ((available [a,b,c] == ns) && ((rawFor ns == masks) &&
      ((availableCovers [a,b,c] == hs.map Prod.fst) && (reps rs (0::masks.map (word a b c h)) &&
      (LocalLightSources.check rs fs ps && hs.all (caseTest a b c h ns masks ps))))))

lemma run_sound (a b c : ℕ) (p : HPacket) (pass : run a b c p=true) : absent a b c := by
  apply LocalHints.sound a b c p
  obtain ⟨h,ns,masks,rs,fs,ps,hs⟩ := p
  simp only [run,Bool.and_eq_true_iff,beq_iff_eq] at pass
  obtain ⟨pos,nsOk,maskOk,keys,sigs,source,rest⟩ := pass
  simp only [LocalHints.run,Bool.and_eq_true_iff,beq_iff_eq]
  exact ⟨pos,nsOk,maskOk,computed _ ▸ keys,sigs,LocalLightSources.sound rs fs ps source,rest⟩

def atCode (a z : ℕ) : Prop := absent (rows.getD a 0) (rows.getD (z/16) 0) (rows.getD (z % 16) 0)

def covers (a : ℕ) (codes : List ℕ) :=
  ((List.range 15).filter (fun b => decide (a<b))).all fun b =>
    ((List.range 16).filter (fun c => decide (b<c))).all fun c =>
      codes.contains (16*b+c) || (availableCovers [rows.getD a 0,rows.getD b 0,rows.getD c 0]).isEmpty

lemma intro_cons (a z : ℕ) (zs : List ℕ) (h : atCode a z) (hs : ∀ t ∈ zs, atCode a t) :
    ∀ t ∈ z::zs, atCode a t := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact h
  · exact hs t ht

lemma band (a b c : ℕ) (ab : a<b) (bc : b<c) (hc : c<16) (codes : List ℕ)
    (domain : covers a codes=true) (yes : ∀ z ∈ codes, atCode a z) :
    absent (rows.getD a 0) (rows.getD b 0) (rows.getD c 0) := by
  have mb : b ∈ (List.range 15).filter (fun q => decide (a<q)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),decide_eq_true ab⟩
  have mc : c ∈ (List.range 16).filter (fun q => decide (b<q)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hc,decide_eq_true bc⟩
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp (List.all_eq_true.mp domain b mb) c mc) with hit | empty
  · have h := yes (16*b+c) (List.contains_iff_mem.mp hit)
    have left : (16*b+c)/16=b := by omega
    have right : (16*b+c) % 16=c := by omega
    simpa only [atCode,left,right] using h
  · intro K mem
    rw [← computed,List.isEmpty_iff.mp empty] at mem
    exact (List.not_mem_nil mem).elim

end LocalLightPackets

namespace LocalCompactPackets
open LocalShapes LocalHints LocalMixerCertificate

def digits (width : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n+1, data => (data % (2^width)) :: digits width n (data >>> width)

def unpack (width data : ℕ) := digits width (data.log2 / width) data

def decodedShape (words : List ℕ) (z : ℕ) : Description :=
  (1 <<< (z % 16),baseMasks.getD ((z >>> 4) % 64) 0,
   words.getD ((z >>> 10) % 256) 0,words.getD ((z >>> 18) % 256) 0)

def decode (cut : ℕ) (neighbors : List ℕ) (allowed : ℕ) (words : List ℕ)
    (raw firsts pairs : ℕ) (cases : List (ℕ × ℕ × ℕ)) : HPacket :=
  let masks := (baseMasks.zipIdx.filter (fun p => allowed.testBit p.2)).map Prod.fst
  let atWord := fun i => words.getD i 0
  let two := fun z : ℕ => (atWord (z % 256), atWord (z >>> 8))
  let shapes := fun e : ℕ × ℕ × ℕ => (e.1,e.2.1,(unpack 26 e.2.2).map (decodedShape words))
  (cut,neighbors,masks,(unpack 8 raw).map atWord,(unpack 8 firsts).map atWord,(unpack 16 pairs).map two,cases.map shapes)

end LocalCompactPackets

namespace LocalLightBand0
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def p18 : HPacket := LocalCompactPackets.decode 3162119 [0,256,1056,192,1280,772,1160,584,562,416,84] 4539626957345322423 [0,1,2,3,4,5,6,16384,16386,16387,16391,1048580,1048581,2097157,2113540,3145728,3145729,3145733,3145735,3162112,3162116,3162117] 1159927105794 1172677329409 1564665151758290552517595505766050208679918371587 [(1448,45802790930,29764772570780744817897722256818669522912990419506623005977534502011123),(1504,45802790930,8995850518460422010654590336780710015653956553739992781778914511992436804783611895187972824757)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c18 : atCode 0 18 := LocalLightPackets.run_sound 513 1025 18 p18 (by decide +kernel)

def p21 : HPacket := LocalCompactPackets.decode 67149831 [0,272,32,192,1282,772,1160,584,562,416,80] 8935140215129437367 [0,1,2,3,4,5,6,8192,32768,32771,32772,32773,40963,40967,67108865,67108870,67108871,67117057,67117062,67141633,67141637,67141638,67141639,67149830] 303525540790287 303517000794625 6499700845898588808788487993955620338241935141261669630723 [(496,181419429396498,8898892130183914935301045627681417216710166240741301036661082108190464903182759244816361980804)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c21 : atCode 0 21 := LocalLightPackets.run_sound 513 1025 1028 p21 (by decide +kernel)

def p22 : HPacket := LocalCompactPackets.decode 2686983 [0,272,1056,128,1282,772,1152,584,562,416,84] 7926333897998792119 [0,1,2,3,4,5,6,65536,65538,65539,65543,524292,524293,2097157,2162692,2621440,2621441,2621445,2621447,2686976,2686977,2686980,2686981] 1159927105794 1172677329409 1564665151758290552517595505766050208679918371587 [(1442,45802790930,2004717079484537442850226730727785535146609377428253447080040570580110522712145),(1456,45802790930,605888559765083438862804297675291601663383306370197837396540948983996670693540841074032072162239593492)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c22 : atCode 0 22 := LocalLightPackets.run_sound 513 1025 72 p22 (by decide +kernel)

def p23 : HPacket := LocalCompactPackets.decode 37879815 [0,272,1056,64,1282,772,1160,576,562,416,84] 9218849398934664631 [0,1,2,3,4,5,6,131072,131075,131079,4194304,4194305,4194308,4194310,33554438,33685504,33685508,37748738,37748742,37748743,37879810,37879812,37879814] 1168533882881 1176955519489 1570396443615919345488324742369739716437272232707 [(852,114527510546,2004696291961061364987556733329103973731409129464765613288474474902290094628770)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c23 : atCode 0 23 := LocalLightPackets.run_sound 513 1025 136 p23 (by decide +kernel)

def p27 : HPacket := LocalCompactPackets.decode 67149831 [0,272,1056,192,1282,260,1160,584,562,384,84] 9196339613178459575 [0,1,2,3,4,5,6,8192,8195,8196,8198,32768,40963,40967,67108866,67108869,67108871,67117058,67117061,67117062,67117063,67141634,67141637,67149826] 302426029096975 302417489166849 6475084762129011225177674012284407305188548168245865415427 [(468,175943429652498,29553067708949786924226938658408179014138907424381718825755579740073890)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c27 : atCode 0 27 := LocalLightPackets.run_sound 513 1025 544 p27 (by decide +kernel)

def p35 : HPacket := LocalCompactPackets.decode 11550727 [1024,0,1056,192,1280,772,1160,584,560,416,85] 4538144815681873791 [0,1,2,3,4,5,6,16385,16387,1048581,1048582,2097155,2097157,2113539,2113543,3145728,3145729,3145733,3145735,3162115,8388608,8404992,9437190,9437191,11550720,11550723] 1194286974724 305737465332225 120806463916844764335006318260470288176732465501523845070601749192944656909059 [(1448,67553994410577938,29664521857583270117730562607650307853521763597236539779050642163368179),(1504,67553994410577938,8965551597153903094668142303443044482634459907363369640552340411006927977047709498871986017973)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c35 : atCode 0 35 := LocalLightPackets.run_sound 513 18 258 p35 (by decide +kernel)

def p36 : HPacket := LocalCompactPackets.decode 2113543 [1024,256,1024,192,1280,768,1160,584,562,416,85] 4233373378011985919 [0,1,2,3,4,5,6,16384,16385,16388,16390,16391,2097152,2097153,2097155,2097156,2097159,2113536,2113539,2113542,2113543] 298002347330050 303525506843137 1575726581679485429184061174205872084065529955075 [(1448,2689601554,29763936652858687529133587708407642580761682406432224114268040860795123),(1504,2689601554,8995597878252561199398085877601413250207514349008421222581953408029536865085321542357874910869),(1864,2689601554,8995597878252561120153696528771202825966154640280683711926640806861337046848649648438523986307),(1928,2689601554,603684354253535996217425799059443322741780318449274555332266921269303631232889962334676921086293049587),(1984,2689601554,182452400796458335605729611976825899358151976454034592653237731012913234436402397616623166060930357061816573509723900824531014)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c36 : atCode 0 36 := LocalLightPackets.run_sound 513 18 36 p36 (by decide +kernel)

def p37 : HPacket := LocalCompactPackets.decode 2097159 [1024,256,32,192,1280,772,1160,584,562,416,81] 4251396581191447799 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097157,2097159] 1142612558337 1142612558337 82637385309298127961816630019 [(1448,18,28579370814457979021150988234224834740087904041130979490340118166503667),(1504,18,8637584821491044080251174533909181015870225055210084415690739537717564931628885786099085476533)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c37 : atCode 0 37 := LocalLightPackets.run_sound 513 18 1028 p37 (by decide +kernel)

def p38 : HPacket := LocalCompactPackets.decode 2097159 [1024,256,1056,128,1280,772,1152,584,562,416,85] 3242590264069453823 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097157,2097158,2097159] 4362207502 4362207502 5476571840910129800134190390641411 [(1440,268382226,252023569377107380835192177396980035238181413758354047136958662902667651777999793783330055847717910749883214964981074809038691214108320010307535235327548167114424117500825399291842758864297857077015811312289027956573554178953966932794973704496764977064719602070551748704105284972966973140876976663632613493569464430050067999952765913251742220325),(1441,94703634,433875589394506390402430966344381623100639318466393580184274800),(1442,655378,29116897916777691539914117407253766983839810153448941464785752466393569),(1444,327698,8800042421610802837705801884446344157147025879500145177031056176833428251326684514781918928034),(1448,327698,433875589322711401282395923377498068857872106616208514705527171),(1456,327698,8800042420639379463268403090161688723218960451916452546209295414728054702608040980561749091812),(1504,327698,131130850608166727903216120275475696329141498359157882785218542838593151058764659425973),(1924,327698,8800042421610802765557070237872718404456412419928087475625410703718229672459620322176200088738),(1952,327698,803829774865706400991369980318237176132447115808394753809684063292958842273042053457909863648601968052033326834049720114567051130682547634213)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c38 : atCode 0 38 := LocalLightPackets.run_sound 513 18 72 p38 (by decide +kernel)

def p39 : HPacket := LocalCompactPackets.decode 2097159 [1024,256,1056,64,1280,772,1160,576,562,416,85] 4535105765005326335 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097159] 4463002113 4463002113 1260946433638872195072771 [(1448,18,6369469123269251587692321148861011865336905905387344115),(1504,18,8669672117182371122660755254116334435208416852706565411850767470861291247295075163165041885877),(1860,18,8669672117182726835940837320763007149705139724324512449806821023493779931725838435595669478562),(1888,18,175841841010050833388437819500283585751090685975494252408076294085939224010847642244093867539465344877224240612553681998184485)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c39 : atCode 0 39 := LocalLightPackets.run_sound 513 18 136 p39 (by decide +kernel)

def p40 : HPacket := LocalCompactPackets.decode 2097159 [1024,256,1056,192,1024,772,1160,584,546,416,85] 2231989545165887359 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097157,2097159] 4362207499 4362207499 5415723683629978008361326482883331 [(1448,327698,28793378555189858042050109208120374342024622740802868713929861676925171),(1504,327698,8702264693289390115972671757960797053613361817051504113648303001931162915704235539746107949749)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c40 : atCode 0 40 := LocalLightPackets.run_sound 513 18 272 p40 (by decide +kernel)

def p41 : HPacket := LocalCompactPackets.decode 2097159 [1024,256,1056,192,256,772,1160,584,562,416,69] 2233783948126713023 [0,1,2,3,4,5,6,2097152,2097153,2097159] 4362207497 4362207497 5375158245443210147179417211044611 [(1448,327698,28471511281734688607499814314246565529187137214283039885540721631690995),(1504,327698,8604986277505099234050207011739702424220953956463786846396693912694036707059464064630406513333)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c41 : atCode 0 41 := LocalLightPackets.run_sound 513 18 1040 p41 (by decide +kernel)

def p42 : HPacket := LocalCompactPackets.decode 2097159 [1024,256,1056,192,1280,516,1160,584,530,416,85] 4510494288676620287 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097159] 4446224897 4446224897 1256223994816933535220483 [(1448,18,6345523880091898214485785763231034001477680043891884275),(1504,18,1917816914404147280470332643238551790110774963849627590377210963856062442115765)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c42 : atCode 0 42 := LocalLightPackets.run_sound 513 18 288 p42 (by decide +kernel)

def p43 : HPacket := LocalCompactPackets.decode 2121735 [1024,256,1056,192,1280,260,1160,584,562,384,85] 4512595979249121279 [0,1,2,3,4,5,6,8194,8198,8199,16390,16391,24576,24577,24580,24582,2097152,2097157,2097159,2105351,2113543,2121728,2121731,2121735] 75733291475669777 292504519966994 27911879151292683484351573466208044644410698995718130186165556675331 [(1420,69231116057382930,29979616229406936803981445788491065208440808673577980312213028832034978),(1448,69231116057382930,29979616231016706899994110220093949914414938520065551440584118508716275),(1476,69231116057382930,608058856125114734759002082615418238002925902282568279581142721525559154786300045341469714042913833122),(1504,69231116057382930,9060783030466599221982557946285970748843058334944342750781278122796586563877732282066461014053)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c43 : atCode 0 43 := LocalLightPackets.run_sound 513 18 544 p43 (by decide +kernel)

def p44 : HPacket := LocalCompactPackets.decode 2097159 [1024,256,1056,192,1280,772,1032,520,562,416,85] 2803489300937177087 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097159] 4362207500 4362207500 5436006402723361938952281118802691 [(1448,327698,28901218343440486421552396073552029351849363252044033476764943870853363),(1504,327698,28901218343436477413223337622941464854452926658296991172575235567256245),(1804,327698,28901218346651530315377547754513065186342135618700760938435984685538466),(1832,327698,39338299926162478547086048555972454715214555179619051829560321383687537242623413051254315253671531348073644499)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c44 : atCode 0 44 := LocalLightPackets.run_sound 513 18 192 p44 (by decide +kernel)

def p45 : HPacket := LocalCompactPackets.decode 2097159 [1024,256,1056,192,1280,772,136,584,562,416,21] 2666129512353822719 [0,1,2,3,4,5,6,2097153,2097155,2097156,2097157,2097159] 1142595781121 1142595781121 82637385309298127961816630019 [(1448,18,28471452041963686975878064347408374947182450514352366188120973313835251),(1504,18,28471452041963686975878064347408358994174319272874707012813229968327349)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c45 : atCode 0 45 := LocalLightPackets.run_sound 513 18 1088 p45 (by decide +kernel)

def p46 : HPacket := LocalCompactPackets.decode 2097159 [1024,256,1056,192,1280,772,1160,72,562,288,85] 4532853278400051199 [0,1,2,3,4,5,6,2097152,2097155,2097156,2097157,2097159] 4362207499 4362207499 5415723683629978008361326482883331 [(1384,327698,8604486964968333129024306141799545855174376297926030300500554221605581930183408030328256725379),(1448,327698,28469859198373014253041956576374810476348724958461079770919404373278963),(1504,327698,8604486964968333129024306141799550653141969409797321879960280484393430795368162235539192808117)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c46 : atCode 0 46 := LocalLightPackets.run_sound 513 18 640 p46 (by decide +kernel)

def p47 : HPacket := LocalCompactPackets.decode 2097159 [1024,256,1056,192,1280,772,1160,584,50,160,85] 4537405222313523199 [0,1,2,3,4,5,6,2097152,2097154,2097155,2097157,2097159] 1142612558337 1142612558337 82637385309298127961816630019 [(1448,18,28577698980242380145140463968014229413980889450220465002683097274908915),(1504,18,8637079541075352107847193075018933425521919167230128795202425707623581275849208515240070218421)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c47 : atCode 0 47 := LocalLightPackets.run_sound 513 18 768 p47 (by decide +kernel)

def p54 : HPacket := LocalCompactPackets.decode 2097159 [1024,16,1056,128,1282,772,1152,584,560,416,85] 7924851739155474303 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097157,2097159] 1151219270145 1151219270145 83256364773818461976585896707 [(1442,18,6417359608210452572648763146476187644714123729955457105),(1456,18,586186348551352884628557425895110377290537757792082456171393884985044391821313528227798056471112457236),(1712,18,8734857269396675850833092551903067063645354592075976367107555840001436550124805336102391520772)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c54 : atCode 0 54 := LocalLightPackets.run_sound 513 258 72 p54 (by decide +kernel)

def p55 : HPacket := LocalCompactPackets.decode 33554439 [1024,16,1056,64,1282,772,1160,576,560,416,85] 9217367240091346815 [0,1,2,3,4,5,6,33554432,33554434,33554435,33554436,33554438,33554439] 1146907525633 1146907525633 82946875023111550895491711747 [(1648,5574674,8377230135472393139543783945670348132108589521082865041770659287176170282861346030835621429764)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c55 : atCode 0 55 := LocalLightPackets.run_sound 513 258 136 p55 (by decide +kernel)

def p60 : HPacket := LocalCompactPackets.decode 35651591 [1024,16,1056,192,1282,772,1032,520,560,416,85] 7485750776023197567 [0,1,2,3,4,5,6,2097152,2097153,2097157,2097159,33554432,33554434,33554438,33554439,35651586,35651587,35651588,35651591] 1168449798657 299123148587521 1564353114179648882539203559199844223797415969539 [(1592,21480144914,28582332722727079116731877023593155633874389907999050671987538694242771)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c60 : atCode 0 60 := LocalLightPackets.run_sound 513 258 192 p60 (by decide +kernel)

def p63 : HPacket := LocalCompactPackets.decode 35651591 [1024,16,1056,192,1282,772,1160,584,48,160,85] 9221148839073785727 [0,1,2,3,4,5,6,2097152,2097153,2097157,2097159,33554432,33554438,33554439,35651584,35651591] 1164138054145 298019341992449 1547226141526894997045256174352441102716975252227 [(1208,21480144914,28474492934451538417812671108769092550487155079479760073661652232044787),(1264,21480144914,577531328952831516738907880503529542927236138997599777823388498803776850771954929383362218068580244996)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c63 : atCode 0 63 := LocalLightPackets.run_sound 513 258 768 p63 (by decide +kernel)

def p70 : HPacket := LocalCompactPackets.decode 2097159 [1024,272,1024,128,1282,768,1152,584,562,416,85] 7620080318665455615 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097157,2097159] 4362207501 4362207501 5456289121816745869543235754722051 [(1442,655378,1946764936821585157572073842309896302082493466653737094995980483182691952099409),(1456,655378,588373599308728473141851533628017800506455189253763159831573516660466065514971625364235859983650003988),(1922,655378,588373598951270306245595014759860786473797748538173452345882849939154025853599325872126732844324880465),(1936,655378,177825008945978494581132308523850569692127361453737292439559046842405070070468019481275818665443533520492712767864912589364244)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c70 : atCode 0 70 := LocalLightPackets.run_sound 513 36 72 p70 (by decide +kernel)

def p71 : HPacket := LocalCompactPackets.decode 35651591 [1024,272,1024,64,1282,768,1160,576,562,416,85] 8912595819601328127 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097159,33554432,33554436,33554438,33554439,35651584] 1159809204737 1159809204737 22566854036977168376653002489752315614266115 [(1858,42960289810,8671199894187387667475574796714903870065984219846567763418334198905419827999184045773686571089),(1872,42960289810,175872828009055030476467170121825152644468819339859390160487755779436899428493785327522026190052065381561203613679929339681812)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c71 : atCode 0 71 := LocalLightPackets.run_sound 513 36 136 p71 (by decide +kernel)

def p75 : HPacket := LocalCompactPackets.decode 2113543 [1024,272,1024,192,1282,256,1160,584,562,384,85] 8908109228447627263 [0,1,2,3,4,5,6,16384,16385,16390,16391,2097152,2097154,2097157,2097159,2113536,2113539,2113543] 294703477099785 300222660215297 1558644210519781827907832620640438254238372791043 [(1418,1347424274,29332577501363463135701086319271921509865594597675727801040602763362385),(1432,1347424274,8865227573824751960913762219314597774562612272879303080505340213125955163320632450655386861811),(1474,1347424274,8865227573824485175940159442806923885242437069880209629316548607370963464681240581369124094033),(1488,1347424274,179808176881900747075403497668301721568547987017872783724127586378582844574549861585930037621962846685311281341703401381051412)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c75 : atCode 0 75 := LocalLightPackets.run_sound 513 36 544 p75 (by decide +kernel)

def p76 : HPacket := LocalCompactPackets.decode 2228231 [1024,272,1024,192,1282,768,1032,520,562,416,85] 7180979355533178879 [0,1,2,3,4,5,6,131072,131073,131078,131079,2097152,2097153,2097154,2097155,2097156,2097159,2228224,2228228,2228231] 298002330552578 302425978438145 1570017590908656397362660010490551888885930328835 [(1802,2694848530,1990186970182721941829254041864974025239284155723826902259725685318333261152337),(1816,2694848530,601497103852981997952971414539949193272950637296967573984050446793708135390603628318355364206101397971)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c76 : atCode 0 76 := LocalLightPackets.run_sound 513 36 192 p76 (by decide +kernel)

def p86 : HPacket := LocalCompactPackets.decode 2097159 [1024,272,32,128,1282,772,1152,584,562,416,81] 7638103521844917495 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097157,2097159] 1142612558337 1142612558337 82637385309298127961816630019 [(1442,18,1925109575556449313485454949616724049513162046376371045513418631375493588058193),(1456,18,581828667934760237611393627482486251118458641873956758274406546914685695983751283470418312590679612436)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c86 : atCode 0 86 := LocalLightPackets.run_sound 513 1028 72 p86 (by decide +kernel)

def p103 : HPacket := LocalCompactPackets.decode 19464199 [1024,272,1056,0,1282,772,1152,576,562,416,85] 7921812706195666943 [0,1,2,3,4,5,6,65537,65539,2097155,2162691,2162695,2621440,2621441,2686977,2686979,16777216,16842752,17301510,17301511,19464192,19464193] 1155648849668 1176989073921 1513284670730615293337306328351020146579925697283 [(1442,64424529938,1961691261155513549155188089422509203559787028943210018879382136014226712428625),(1456,64424529938,592884803995815623944160890710294290735222887391742076123804550218074229484668645545278866388846391316)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c103 : atCode 0 103 := LocalLightPackets.run_sound 513 72 136 p103 (by decide +kernel)

def p104 : HPacket := LocalCompactPackets.decode 2097159 [1024,272,1056,128,1026,772,1152,584,546,416,85] 1007010463097001855 [0,1,2,3,4,5,6,2097153,2097154,2097155,2097156,2097157,2097159] 4362207500 4362207500 5436006402723361938952281118802691 [(1442,327698,1939527930922405363186629414708078873396502814904788108983106018839871097405521),(1456,327698,28901218341830422014931377972227735996338856351751661232974688881223700),(1698,327698,1939527930600090919089962623996380781065332573427522373746096442682379784946209)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c104 : atCode 0 104 := LocalLightPackets.run_sound 513 72 272 p104 (by decide +kernel)

def p105 : HPacket := LocalCompactPackets.decode 2097159 [1024,272,1056,128,258,772,1152,584,562,416,69] 936747276314866879 [0,1,2,3,4,5,6,2097153,2097155,2097156,2097157,2097159] 1142595781121 1142595781121 82637385309298127961816630019 [(1442,18,1910690778588238690118889309303339314698066680090526090461432071477955372777553),(1456,18,1910690778588238685297977096811752000684141724938569684407626478919792185058324)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c105 : atCode 0 105 := LocalLightPackets.run_sound 513 72 1040 p105 (by decide +kernel)

def p106 : HPacket := LocalCompactPackets.decode 2097159 [1024,272,1056,128,1282,516,1152,584,530,416,85] 7897201229330089983 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097156,2097159] 4446224897 4446224897 1260946433638872195072771 [(1442,18,6345523879735086291390121274470012633297584948206370897),(1456,18,1917816914404206517027458162756700197081310451242151252678369377200324535655444)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c106 : atCode 0 106 := LocalLightPackets.run_sound 513 72 288 p106 (by decide +kernel)

def p107 : HPacket := LocalCompactPackets.decode 2097159 [1024,272,1056,128,1282,260,1152,584,562,384,85] 7899302919902590975 [0,1,2,3,4,5,6,2097152,2097155,2097157,2097159] 4362207498 4362207498 5395440964536594077770371846963971 [(1414,327698,28469859193549368020620826650332353968962616851513504338268269420740689),(1428,327698,577437345521856502319787728981528258233668729389263588472476943308308718275824802274257884125770816674),(1442,327698,1910579908827084058226667330002266177829731935925110817081640461120474353238097),(1456,327698,577437345521850534927562905297516301384599674076668883624903184102163117746248475909514574660190084116)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c107 : atCode 0 107 := LocalLightPackets.run_sound 513 72 544 p107 (by decide +kernel)

def p108 : HPacket := LocalCompactPackets.decode 2097159 [1024,272,1056,128,1282,772,1024,520,562,416,85] 7343117746264602623 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097159] 4362207498 4362207498 5395440964536594077770371846963971 [(1442,327698,1925053919873908794379073075745450647579908244202158402978879571816293896814673),(1456,327698,581811847036601709533344234218903853242490147872408986943064567334452565388735336223097878168335293460)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c108 : atCode 0 108 := LocalLightPackets.run_sound 513 72 192 p108 (by decide +kernel)

def p109 : HPacket := LocalCompactPackets.decode 2097159 [1024,272,1056,128,1282,772,128,584,562,416,21] 7349873145689995263 [0,1,2,3,4,5,6,2097152,2097153,2097159] 4362207497 4362207497 5375158245443210147179417211044611 [(1442,327698,1910686802966663362203066492118159605668456978414113000131085488767789856194641),(1456,327698,577469652326248257806790934030421951445630609052732695123011100241283369161147961868898215264549608468)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c109 : atCode 0 109 := LocalLightPackets.run_sound 513 72 1088 p109 (by decide +kernel)

def p110 : HPacket := LocalCompactPackets.decode 2097159 [1024,272,1056,128,1282,772,1152,72,562,288,85] 7919560219053520895 [0,1,2,3,4,5,6,2097152,2097154,2097155,2097157,2097159] 1142612558337 1142612558337 82637385309298127961816630019 [(1442,18,1917816914512256108716181143948210690802027951885474830944520680172859913142353),(1456,18,579624596279226122958954415198367006666418860304007753152194159054914280095591422515764205552012368916)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c110 : atCode 0 110 := LocalLightPackets.run_sound 513 72 640 p110 (by decide +kernel)

def p111 : HPacket := LocalCompactPackets.decode 2097159 [1024,272,1056,128,1282,772,1152,584,50,160,85] 7924112162966992895 [0,1,2,3,4,5,6,2097152,2097155,2097156,2097157,2097159] 4362207499 4362207499 5415723683629978008361326482883331 [(1202,327698,1910579908719034472941170538689545730733045081880783519051001115260878438007265),(1442,327698,1910579908612852525707606274086097088377988214239537105315286819399303033520209),(1456,327698,577437345521850533962749804614623592372285628103453772328342996125390138890974838175089302086455663636)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c111 : atCode 0 111 := LocalLightPackets.run_sound 513 72 768 p111 (by decide +kernel)

def p120 : HPacket := LocalCompactPackets.decode 35651591 [1024,272,1056,64,1026,772,1160,576,546,416,85] 2299525964032874367 [0,1,2,3,4,5,6,2097152,2097153,2097157,2097159,33554432,33554434,33554438,33554439,35651588,35651589] 4513661441 1155497460225 22740738321261029897529528379609237407728387 [(1634,21480144914,28582332722726196399300338271610720105690288990149229422189602529870369)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c120 : atCode 0 120 := LocalLightPackets.run_sound 513 136 272 p120 (by decide +kernel)

def p126 : HPacket := LocalCompactPackets.decode 35651591 [1024,272,1056,64,1282,772,1160,64,562,288,85] 9216596911802808319 [0,1,2,3,4,5,6,2097152,2097153,2097157,2097159,33554432,33554438,33554439,35651584,35651589] 4496884225 1151202492929 22740398038894108649576314370429793559970563 [(1378,21480144914,8605887427222931587536275489924737783259736792166781471756991734302488814456723164115072974929),(1392,21480144914,174548133801856964455959075613070114619794416343357639058343720024562636145359185009532729863942672960522721940683648806165524)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c126 : atCode 0 126 := LocalLightPackets.run_sound 513 136 640 p126 (by decide +kernel)

def p140 : HPacket := LocalCompactPackets.decode 65543 [1024,272,1056,192,1026,772,1032,520,546,416,85] 567909499964725119 [0,1,2,3,4,5,6,65538,65539,65540,65542,65543] 4362207499 4362207499 5415723683629978008361326482883331 [(1578,94703634,6393414366096436700040102629818935613676659862822191649)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c140 : atCode 0 140 := LocalLightPackets.run_sound 513 272 192 p140 (by decide +kernel)

def p143 : HPacket := LocalCompactPackets.decode 2228231 [1024,272,1056,192,1026,772,1160,584,34,160,85] 2303619824317601663 [0,1,2,3,4,5,6,131072,131073,131078,131079,2097152,2097154,2097157,2097159,2228224,2228227,2228230,2228231] 294703477165321 301322171843073 1564353201290605667432065764518236234783903777539 [(1194,1347424274,6513140581305663224828464800318209306606434315317543457),(1250,1347424274,1968475954200351629095528814347453863898753737625698869035345638637513050685985)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c143 : atCode 0 143 := LocalLightPackets.run_sound 513 272 768 p143 (by decide +kernel)

def p206 : HPacket := LocalCompactPackets.decode 2228231 [1024,272,1056,192,1282,772,1032,8,562,288,85] 7487214655362299903 [0,1,2,3,4,5,6,131072,131073,131078,131079,2097152,2097154,2097157,2097159,2228224,2228227,2228229,2228230,2228231] 299118836583689 299123148587521 1570062192061429506956298908396034215329434764035 [(1322,1347424274,1968475953880050053251274646068217420085126790530272590002924773604804419911761),(1336,1347424274,594935351580855237249306026658906326056151063718568160504489913749944646034771162555429605501093544403)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c206 : atCode 0 206 := LocalLightPackets.run_sound 513 192 640 p206 (by decide +kernel)

def codes : List ℕ := [18,21,22,23,27,35,36,37,38,39,40,41,42,43,44,45,46,47,54,55,60,63,70,71,75,76,86,103,104,105,106,107,108,109,110,111,120,126,140,143,206]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 0 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 0 z := by
  unfold codes
  apply intro_cons _ _ _ c18
  apply intro_cons _ _ _ c21
  apply intro_cons _ _ _ c22
  apply intro_cons _ _ _ c23
  apply intro_cons _ _ _ c27
  apply intro_cons _ _ _ c35
  apply intro_cons _ _ _ c36
  apply intro_cons _ _ _ c37
  apply intro_cons _ _ _ c38
  apply intro_cons _ _ _ c39
  apply intro_cons _ _ _ c40
  apply intro_cons _ _ _ c41
  apply intro_cons _ _ _ c42
  apply intro_cons _ _ _ c43
  apply intro_cons _ _ _ c44
  apply intro_cons _ _ _ c45
  apply intro_cons _ _ _ c46
  apply intro_cons _ _ _ c47
  apply intro_cons _ _ _ c54
  apply intro_cons _ _ _ c55
  apply intro_cons _ _ _ c60
  apply intro_cons _ _ _ c63
  apply intro_cons _ _ _ c70
  apply intro_cons _ _ _ c71
  apply intro_cons _ _ _ c75
  apply intro_cons _ _ _ c76
  apply intro_cons _ _ _ c86
  apply intro_cons _ _ _ c103
  apply intro_cons _ _ _ c104
  apply intro_cons _ _ _ c105
  apply intro_cons _ _ _ c106
  apply intro_cons _ _ _ c107
  apply intro_cons _ _ _ c108
  apply intro_cons _ _ _ c109
  apply intro_cons _ _ _ c110
  apply intro_cons _ _ _ c111
  apply intro_cons _ _ _ c120
  apply intro_cons _ _ _ c126
  apply intro_cons _ _ _ c140
  apply intro_cons _ _ _ c143
  apply intro_cons _ _ _ c206
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand0

namespace LocalLightBand1
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def p36 : HPacket := LocalCompactPackets.decode 16391 [512,256,1024,192,1280,768,1160,584,562,417,84] 4233374823559658935 [0,1,2,3,4,5,6,16384,16385,16389,16390,16391] 1142612558337 1142612558337 82634967439212154629757666051 [(1864,10817554,8669797442639813876468402650075989342449770827225666800775914341191992963768621579557496684931),(1928,10817554,581820257453006713094690930124658479779848480362820026282680129615095949280140444310382567054049804531),(1984,10817554,175844382912312453213197268159598081190250038839059750343681776676614474631270069602767610985214789633217626492805268809711686)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c36 : atCode 1 36 := LocalLightPackets.run_sound 1025 18 36 p36 (by decide +kernel)

def p38 : HPacket := LocalCompactPackets.decode 2097159 [512,256,1056,128,1280,772,1152,584,562,417,84] 3242591709617126839 [0,1,2,3,4,5,6,2097152,2097154,2097156,2097158,2097159] 4463002113 4463002113 1260891093406651066417923 [(1441,331794,6369561197158779577589364152192060020877717704449722000),(1924,331794,8669797442640169532068381078308504428722435944456741493625297417037772173469386005006528814242),(1952,331794,53145703657505403192038097465952080739623866134822406894761000137041294878006172851069747893627159018622686394722024858428824762096347703871945834533)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c38 : atCode 1 38 := LocalLightPackets.run_sound 1025 18 72 p38 (by decide +kernel)

def p39 : HPacket := LocalCompactPackets.decode 33554439 [512,256,1056,64,1280,772,1160,576,562,417,84] 4535107210552999351 [0,1,2,3,4,5,6,33554432,33554433,33554436,33554437,33554439] 4463002113 4463002113 1260909540150724775969539 [(852,18,1925061401582483886064928220842539555839604670314120833364676288795435463607202),(1860,18,8409948037036943836618921722055893339388095588663049005114388560960139679601466841473071710370),(1888,18,170574010832602410187437657701104375003311140056808244330438450631165076981425059394306086333234953832307283473207388733964325)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c39 : atCode 1 39 := LocalLightPackets.run_sound 1025 18 136 p39 (by decide +kernel)

def p41 : HPacket := LocalCompactPackets.decode 10485767 [512,256,1056,192,256,772,1160,584,562,417,68] 2233785393684872375 [0,1,2,3,4,5,6,2097152,2097158,2097159,8388608,8388609,8388610,8388613,8388615,10485760,10485766] 4497147905 1155480683009 22827849272853625591715009249405589826896643 [(844,1347424274,28796438785521088251655252861067538193881836762924133487258995053043618),(964,1347424274,584061166574436277113773215462593805060517931783816873547729757932077759470148860573530699284645945250)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c41 : atCode 1 41 := LocalLightPackets.run_sound 1025 18 1040 p41 (by decide +kernel)

def p44 : HPacket := LocalCompactPackets.decode 35651591 [512,256,1056,192,1280,772,1032,520,562,417,84] 2803490746484850103 [0,1,2,3,4,5,6,2097152,2097154,2097158,2097159,33554432,33554433,33554437,33554439,35651584,35651588] 4513661441 1155497460225 22827849278045922759734846771620223895536387 [(1804,1347424274,28582747389881997321727042985623177333870290206299042690369109752814754),(1832,1347424274,38904819748438232687475789418622635642443582034491652285109109255531224319314240087211161222754163159587619283)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c44 : atCode 1 44 := LocalLightPackets.run_sound 1025 18 192 p44 (by decide +kernel)

def p53 : HPacket := LocalCompactPackets.decode 33554439 [512,16,32,192,1282,772,1160,584,560,417,80] 8933659501833792567 [0,1,2,3,4,5,6,33554432,33554435,33554437,33554438,33554439] 4362207499 4362207499 5415723683629978008361326482883331 [(632,327698,28469970676484787757510913601900633800457000234367284741349967176401283),(752,327698,577439606664416502870493744661918408685608701866302475961720659657325325467436659169345749798240388068)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c53 : atCode 1 53 := LocalLightPackets.run_sound 1025 258 1028 p53 (by decide +kernel)

def p54 : HPacket := LocalCompactPackets.decode 33554439 [512,16,1056,128,1282,772,1152,584,560,417,84] 7924853184703147319 [0,1,2,3,4,5,6,33554432,33554433,33554434,33554435,33554439] 4463002113 4463002113 1260946433638872195072771 [(1712,18,8475133189250892966851838484171038761878755920488259788804108535981831260710710076776042988036)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c54 : atCode 1 54 := LocalLightPackets.run_sound 1025 258 72 p54 (by decide +kernel)

def p55 : HPacket := LocalCompactPackets.decode 33554439 [512,16,1056,64,1282,772,1160,576,560,417,84] 9217368685639019831 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554437,33554439] 4362207500 4362207500 5436006402723361938952281118802691 [(628,327698,1939535412952893818431843926957882152954091572043388731825165876865325327975282),(852,327698,1939535412844988193953780038851672556303300208513053500358180614626460070314914),(1648,327698,8344635570072398849948195775506087687241983375327325884874360604611729680305958350834288820740)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c55 : atCode 1 55 := LocalLightPackets.run_sound 1025 258 136 p55 (by decide +kernel)

def p58 : HPacket := LocalCompactPackets.decode 42082311 [512,16,1056,192,1282,516,1160,584,528,417,84] 9194164584193887543 [0,1,2,3,4,5,6,8199,131072,131077,131078,139265,139269,139271,8388615,8396802,8396804,8396805,8396807,8519685,8519687,8527877,33554435,33554437,33554438,33562627,33562629,33562631,33685510,33685511,33693703,41943041,41943043,41943045,41943047,41951235,41951237,42074119,42082304,42082305,42082311] 353172195521168056558427136 349531159018232195815047681 4143614787604871870185013051465555473130217036225647479436327891238877294099709888162003910138511931597528717606350233662695775522252184909458490006745856473439505023747 [(604,92233720368553000978,7087851172581880266984704785075230934221981681340916642),(724,27222589354071320648428191246357747470354,2142171572137698005668938921416489651029299607522725720311328407233961170838434)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c58 : atCode 1 58 := LocalLightPackets.run_sound 1025 258 288 p58 (by decide +kernel)

def p60 : HPacket := LocalCompactPackets.decode 33554439 [512,16,1056,192,1282,772,1032,520,560,417,84] 7485752221570870583 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554439] 4362207499 4362207499 5415723683629978008361326482883331 [(1592,327698,28041442202639243364438774182393403879514984168351714586020194390901203)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c60 : atCode 1 60 := LocalLightPackets.run_sound 1025 258 192 p60 (by decide +kernel)

def p69 : HPacket := LocalCompactPackets.decode 9568263 [512,272,0,192,1282,768,1160,584,562,417,80] 8917118457495485623 [0,1,2,3,4,5,6,131072,131073,131075,131078,1048576,1179654,1179655,8388610,8388613,8388615,8519680,8519683,8519685,8519687,9437186,9437189,9568256,9568261] 301326517403663 301317977539073 6524028464320996393889651114315258769950016334039250961155 [(856,11016675000338,8931846881942949801728168021658829039233286194976322995395385923132801474493563625004628967811),(976,16582952615954,181159376976670722177860778705382415004425804137546619514104278726383393539922619321328051739132021992954334580733066392109956)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c69 : atCode 1 69 := LocalLightPackets.run_sound 1025 36 1028 p69 (by decide +kernel)

def p70 : HPacket := LocalCompactPackets.decode 10485767 [512,272,1024,128,1282,768,1152,584,562,417,84] 7620081764213128631 [0,1,2,3,4,5,6,2097152,2097156,2097158,2097159,8388608,8388609,8388610,8388611,8388615,10485762] 4530439169 1159792427521 22828186901977292994299985350939612797010691 [(1922,2694848530,579726990321658305001965148212356377303210344558631560299569889780168864159026098261037101306991094865),(1936,2694848530,175211731682759334578114681081674728006084636831844099774727900119079821892286652090006962866431057371347328527649922597264404)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c70 : atCode 1 70 := LocalLightPackets.run_sound 1025 36 72 p70 (by decide +kernel)

def p71 : HPacket := LocalCompactPackets.decode 8388615 [512,272,1024,64,1282,768,1160,576,562,417,84] 8912597265149001143 [0,1,2,3,4,5,6,8388608,8388609,8388610,8388612,8388613,8388615] 4362207500 4362207500 5436006402723361938952281118802691 [(852,655378,1939535412952827995034706476953136365073577243873356295911152313606924306221938),(1858,655378,8409948037036588195478792280446227777051450547802693272390433007980066912006019348364276014161),(1872,655378,170574010832607820059577929632659971920123248334805211676802616530686731046384368853881703235058414088365331775170820961992724)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c71 : atCode 1 71 := LocalLightPackets.run_sound 1025 36 136 p71 (by decide +kernel)

def p76 : HPacket := LocalCompactPackets.decode 131079 [512,272,1024,192,1282,768,1032,520,562,417,84] 7180980801080851895 [0,1,2,3,4,5,6,131072,131073,131076,131078,131079] 4362207499 4362207499 5415723683629978008361326482883331 [(1802,262807570,1925081748038633009950678618018266057990047265971764013932041010989910399647825),(1816,262807570,581820257485680975029076046647181582563537773852884053624421291961547762745660825012668453416809529811)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c76 : atCode 1 76 := LocalLightPackets.run_sound 1025 36 192 p76 (by decide +kernel)

def p87 : HPacket := LocalCompactPackets.decode 33554439 [512,272,32,64,1282,772,1160,576,562,417,80] 8930620468337114295 [0,1,2,3,4,5,6,33554432,33554434,33554435,33554437,33554439] 4362207499 4362207499 5415723683629978008361326482883331 [(626,327698,28685650253035869012276715568817556550215477872119895169522253428425185),(852,655378,1925061401582483882851052084434072639072796675129623449566826062601525747779746),(880,655378,53145141982879539894168048899297535650006955586685088469557752133844602824479782243513253291884854826279866443220227077182059915747462356695964189572)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c87 : atCode 1 87 := LocalLightPackets.run_sound 1025 1028 136 p87 (by decide +kernel)

def p103 : HPacket := LocalCompactPackets.decode 38404103 [512,272,1056,0,1282,772,1152,576,562,417,84] 7921814151743339959 [1,2,3,4,5,6,131073,131077,524288,655360,4194304,4718592,4718598,4718599,33554437,33685504,33685509,33685511,37748737,37879809,37879813] 1177090262529 1168432627968 1541695730956894212052311745411095777408578748930 [(852,64424550418,1997657614861866015930925598783561993209699045792799895083199824178771265071010)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c103 : atCode 1 103 := LocalLightPackets.run_sound 1025 72 136 p103 (by decide +kernel)

def p104 : HPacket := LocalCompactPackets.decode 35651591 [512,272,1056,128,1026,772,1152,584,546,417,84] 1007011908644674871 [0,1,2,3,4,5,6,2097152,2097154,2097158,2097159,33554432,33554433,33554437,33554439,35651588] 4513661441 1155497460225 22827849278045922759734846771620223895536387 [(1698,1347424274,1918155707763330064141433672589378459974318251275607701425206557782851494609441)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c104 : atCode 1 104 := LocalLightPackets.run_sound 1025 72 272 p104 (by decide +kernel)

def p109 : HPacket := LocalCompactPackets.decode 10485767 [512,272,1056,128,1282,772,128,584,562,417,20] 7349874591248481719 [0,1,2,3,4,5,6,2097152,2097158,2097159,8388608,8388609,8388613,8388615,10485760] 4496818689 1151185715713 22827508990466422243643153391147267452633859 [(916,1347424274,584061166574436277113773215462593589380941384037486921049303884485446677224788666441081522498103680930)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c109 : atCode 1 109 := LocalLightPackets.run_sound 1025 72 1088 p109 (by decide +kernel)

def p120 : HPacket := LocalCompactPackets.decode 33554439 [512,272,1056,64,1026,772,1160,576,546,417,84] 2299527409580547383 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554439] 4362207499 4362207499 5415723683629978008361326482883331 [(852,327698,6393439119921973660691920876100211479942733641746744226),(1634,327698,28041442202638360647007235430410994790506722427933142364029731782263329)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c120 : atCode 1 120 := LocalLightPackets.run_sound 1025 136 272 p120 (by decide +kernel)

def p121 : HPacket := LocalCompactPackets.decode 33554439 [512,272,1056,64,258,772,1160,576,562,417,68] 2229264222808898743 [0,1,2,3,4,5,6,33554432,33554435,33554436,33554437,33554439] 4362207499 4362207499 5415723683629978008361326482883331 [(838,327698,1910587390212139791513652865769045865065927775269196686096964450648105205891153),(852,327698,1910587390212139791513652769986613059310521956981852692054005810994719347966882)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c121 : atCode 1 121 := LocalLightPackets.run_sound 1025 136 1040 p121 (by decide +kernel)

def p122 : HPacket := LocalCompactPackets.decode 42090503 [512,272,1056,64,1282,516,1160,576,530,417,84] 9189718175813635511 [0,1,2,3,4,5,6,16384,131072,147457,147461,147463,8388608,8388611,8404992,8404996,8404997,8404999,8519685,8519687,8536069,33554435,33570821,33570823,33685508,33685509,33685511,33701892,33701893,41943041,41943043,41943045,41943047,41959429,42074117,42090499,42090503] 1379560588104819557342722 353153287898415049835020801 10464238956143004780595868176606126691154604132743857704748248679642273041811799902381561302911844618666755 [(598,96714065569181329092771858,6992070199850514494193105128795054749063819527125479905),(852,96714065569198921278857234,2113223549396957176401472792911799524264621762457835053259105347495164742214562)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c122 : atCode 1 122 := LocalLightPackets.run_sound 1025 136 288 p122 (by decide +kernel)

def p123 : HPacket := LocalCompactPackets.decode 33554439 [512,272,1056,64,1282,260,1160,576,562,385,84] 9191818697886594487 [0,1,2,3,4,5,6,33554432,33554433,33554435,33554437,33554439] 1142612558337 1142612558337 82637385309298127961816630019 [(852,18,1917936590687590518413166211415253422156007852700961234720922319889078273180578)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c123 : atCode 1 123 := LocalLightPackets.run_sound 1025 136 544 p123 (by decide +kernel)

def p124 : HPacket := LocalCompactPackets.decode 33554439 [512,272,1056,64,1282,772,1032,512,562,417,84] 7487216787702087095 [0,1,2,3,4,5,6,33554432,33554433,33554435,33554439] 4362207498 4362207498 5395440964536594077770371846963971 [(852,327698,1925061401582483882851052084434072639072796675129466216673546392292753867277218)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c124 : atCode 1 124 := LocalLightPackets.run_sound 1025 136 192 p124 (by decide +kernel)

def p125 : HPacket := LocalCompactPackets.decode 33554439 [512,272,1056,64,1282,772,136,576,562,417,20] 7345353399501651383 [0,1,2,3,4,5,6,33554432,33554434,33554435,33554437,33554439] 1142612558337 1142612558337 82637385309298127961816630019 [(852,18,1917824395897311833968476338692361584483888778393235725663963290092852843381666)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c125 : atCode 1 125 := LocalLightPackets.run_sound 1025 136 1088 p125 (by decide +kernel)

def p126 : HPacket := LocalCompactPackets.decode 33554439 [512,272,1056,64,1282,772,1160,64,562,289,84] 9216596982658956727 [0,1,2,3,4,5,6,33554432,33554433,33554439] 4362207497 4362207497 5375158245443210147179417211044611 [(852,99946514,1910698700823915425402997772235753468149355198124928989989267449809719137403810)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c126 : atCode 1 126 := LocalLightPackets.run_sound 1025 136 640 p126 (by decide +kernel)

def p127 : HPacket := LocalCompactPackets.decode 33554439 [512,272,1056,64,1282,772,1160,576,50,161,84] 9216627664194043319 [0,1,2,3,4,5,6,33554433,33554435,33554436,33554437,33554439] 1142595781121 1142595781121 82637385309298127961816630019 [(852,18,6321959994644324467191498732416694701543577725387408290)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c127 : atCode 1 127 := LocalLightPackets.run_sound 1025 136 768 p127 (by decide +kernel)

def p140 : HPacket := LocalCompactPackets.decode 65543 [512,272,1056,192,1026,772,1032,520,546,417,84] 567910945512398135 [0,1,2,3,4,5,6,65538,65540,65542,65543] 4362207498 4362207498 5395440964536594077770371846963971 [(1578,94703634,6345615955046157501576381145371621853049953684549272097)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c140 : atCode 1 140 := LocalLightPackets.run_sound 1025 272 192 p140 (by decide +kernel)

def p205 : HPacket := LocalCompactPackets.decode 33619975 [512,272,1056,192,1282,772,8,520,562,417,20] 7343119192343772599 [0,1,2,3,4,5,6,65536,65537,65542,65543,33554434,33554437,33554439,33619968,33619971,33619973,33619974,33619975] 298015029988361 298019341992449 1564353200950323280228717692662377976461529514755 [(796,1347424274,1961246430008344127307870525945087420645007361869939297529685942735715173408674)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c205 : atCode 1 205 := LocalLightPackets.run_sound 1025 192 1088 p205 (by decide +kernel)

def codes : List ℕ := [36,38,39,41,44,53,54,55,58,60,69,70,71,76,87,103,104,109,120,121,122,123,124,125,126,127,140,205]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 1 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 1 z := by
  unfold codes
  apply intro_cons _ _ _ c36
  apply intro_cons _ _ _ c38
  apply intro_cons _ _ _ c39
  apply intro_cons _ _ _ c41
  apply intro_cons _ _ _ c44
  apply intro_cons _ _ _ c53
  apply intro_cons _ _ _ c54
  apply intro_cons _ _ _ c55
  apply intro_cons _ _ _ c58
  apply intro_cons _ _ _ c60
  apply intro_cons _ _ _ c69
  apply intro_cons _ _ _ c70
  apply intro_cons _ _ _ c71
  apply intro_cons _ _ _ c76
  apply intro_cons _ _ _ c87
  apply intro_cons _ _ _ c103
  apply intro_cons _ _ _ c104
  apply intro_cons _ _ _ c109
  apply intro_cons _ _ _ c120
  apply intro_cons _ _ _ c121
  apply intro_cons _ _ _ c122
  apply intro_cons _ _ _ c123
  apply intro_cons _ _ _ c124
  apply intro_cons _ _ _ c125
  apply intro_cons _ _ _ c126
  apply intro_cons _ _ _ c127
  apply intro_cons _ _ _ c140
  apply intro_cons _ _ _ c205
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand1

namespace LocalLightBand2
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def p52 : HPacket := LocalCompactPackets.decode 11550727 [1536,0,1024,192,1280,768,1160,584,560,417,85] 13455264718750986111 [0,1,2,3,4,5,6,16390,1064965,2113537,2113541,2113543,3145728,3145732,3145733,3162117,8388608,8388611,8388614,8404992,8404996,8404997,8404998,8404999,9437187,9437191,10485765,10502149,11550720,11550725] 79673967070680578 307957913092609 548015378099958481678723727242946186458268513997177112922309391188742155131126030861059 [(1864,175922028257298,8834672033724154899550600847342801069550216748070212003857639908832099490052239209839576482179),(1928,175922028257298,592884804223498038774640893520698354209052028957491893055141062530667435579619866390092139544397742323),(1984,175922028257298,179188436901919633657356556120317174842755117637293736423977659846367358551770426954615312963344149782021921741483692062158918)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c52 : atCode 2 52 := LocalLightPackets.run_sound 18 258 36 p52 (by decide +kernel)

def p54 : HPacket := LocalCompactPackets.decode 1048583 [1536,0,1056,128,1280,772,1152,584,560,417,85] 12464481604808454015 [0,1,2,3,4,5,6,1048576,1048577,1048578,1048579,1048580,1048581,1048583] 1151219270145 1151219270145 83256364773818461976585896707 [(1441,18,28901218346651628490326442938579525626384869343804339866908240656466576),(1712,16392210,8734857268911008627748832442488274879124571894309397616044870210705359187476788750807816734180),(1924,16392210,8734857269396764779129798969043058407227594490325352186444534933440848662119055207727437454498),(1952,16392210,53544519232115677330519271937101383325853026163632706499882009646880802110864402783579994988320039256466883742073547807628159337885367628441749028901)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c54 : atCode 2 54 := LocalLightPackets.run_sound 18 258 72 p54 (by decide +kernel)

def p55 : HPacket := LocalCompactPackets.decode 8388615 [1536,0,1056,64,1280,772,1160,576,560,417,85] 13756997105744326527 [0,1,2,3,4,5,6,8388608,8388609,8388610,8388611,8388612,8388614,8388615] 1151219270145 1151219270145 83256364755371717902876345091 [(1648,16392210,8377230134986725916487351570100697587559196707141794338585360243748323631973340231579300529636),(1860,16392210,8377230135472482067868318204528181090071952797430637050114567799817597745122996564007346503842),(1888,16392210,169910412951700041237537030883498137575353050553571996646972090344162196003156302001718823939628338715471653559441737270696997)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c55 : atCode 2 55 := LocalLightPackets.run_sound 18 258 136 p55 (by decide +kernel)

def p56 : HPacket := LocalCompactPackets.decode 36724743 [1536,0,1056,192,1024,772,1160,584,544,417,85] 11455077154555924351 [0,1,2,3,4,5,6,24576,1056771,1056775,2113541,2113543,3145728,3170309,33554432,33554438,33554439,33579008,33579014,36700166,36724736] 4463263759 292504704647681 1843063469998814399622730496601018516905621727295509481813740215947559683 [(1640,2815093464436754,8769232252009280783788211592108458038453762511820676164367800509191948035290715347881524724099),(1704,2815093464436754,588493214747274343217219998225115989892895772263934843776908858434562798590434828632958548760438243571),(1760,2815093464436754,177861160444805001913588186650362351294916646154328004169884245950374574276943195629757759842663210764310768098185603564969493)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c56 : atCode 2 56 := LocalLightPackets.run_sound 18 258 272 p56 (by decide +kernel)

def p60 : HPacket := LocalCompactPackets.decode 45088775 [1536,0,1056,192,1280,772,1032,520,560,417,85] 12025380641676177279 [0,1,2,3,4,5,6,1048579,1048581,2097153,2097157,3145728,3145729,3145732,3145733,3145735,8388608,8388611,8388614,9437187,9437191,10485761,11534337,33554434,33554438,36700162,41943040,41943042,41943044,41943046,41943047,45088772] 313459917850880 313442653438465 8095840077628484859344885769281295190632792494326238179720636185241774147745678083 [(1592,277133226230533869586,29127850400092114430299814466291019341361700439242672425260946948882899),(1804,277065672235570712594,29127850401699346713702650635464066538099007258385917274971102473366690),(1832,277133226230533869586,39646775544720177443792133787609403503942402695896038733098190278627372517335418478153014104547565112099865043)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c60 : atCode 2 60 := LocalLightPackets.run_sound 18 258 192 p60 (by decide +kernel)

def p69 : HPacket := LocalCompactPackets.decode 3162119 [1536,256,0,192,1280,768,1160,584,562,417,81] 13456746860412271863 [0,1,2,3,4,5,6,16384,16386,16387,16388,16391,1048577,1048579,1064963,2097155,2113537,2113539,3145728,3145734,3145735,3162112,3162113,3162115] 302438947751940 1181267264001 1547561352003803488870065473415482314824417084163 [(1864,64676167698,9061288307968287740857493877479401168114838482894392123438477084559441195515473464193997078915),(1928,251658258,608092764465343251451775313725013608738887467473384093116418646696800147594032510092882332777248719091),(1984,64676167698,183784760998992594287797174621524441204735760606320037096990223407658579998824409035835178431872163535017033333330243093547078)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c69 : atCode 2 69 := LocalLightPackets.run_sound 18 36 1028 p69 (by decide +kernel)

def p70 : HPacket := LocalCompactPackets.decode 9977863 [1536,256,1024,128,1280,768,1152,584,562,417,85] 12159710167138566143 [0,1,2,3,4,5,6,16384,524292,524294,540673,540675,540679,1048580,1048582,1064963,1064964,1064967,1572864,1572866,1572868,1572870,1572871,1589249,1589250,1589251,1589253,1589254,1589255,8388608,8404992,8404994,8404995,8404999,8912899,8929283,9437185,9437187,9453571,9961472,9961473,9977857,9977858,9977859] 1389042359502960570730496 20760491536624648705 2445392695472908803943660839344637339207902533205846383286476721655519107332836859344934760940291 [(1441,40978,30638871185075867567210048521302362095607249707061021257683022251564688),(1864,40978,30638871180253778112469286033054969137183317506015208902168861847593347),(1920,755595935303837256359954,109095770292019957058817968848471131127135013036671507629894405976742015354025424898300453106270061076525775569377399236008344648284864487918881511573460959988994575118255149094502417572699031383929880315344720600737732294778398374439702628149491032204788038377063771724199018763749405011817622164698336276285748452744902821113368015557779364181155063469967137015215193638093812935315374383377426245782370375),(1921,40978,12604100541554930137987315733827739313979105030393068927110410638006684889731830335833269080673633332927066660442695373721267654368912),(1922,5767422273070145554,9260030616307886758170236723600484332668701490085342598471374497137765428677923868452593897953),(1924,40978,137985208837685850207983341770726377755956617451467394917960828922842649890771017420658),(1928,40978,9260030616307886758170236723600484332668701490085341836117219004490094173362447751670050333059),(1936,755578637259143234232338,2798672525038117870583784064356012948998388220300390228302278886407570202729446333841574624754349224519390032824379876),(1952,40978,845846869216766658505785351394625854850477073845198930610908982947666333536179809353587307985446547076228668425934041700376931440891357330917),(1984,40978,2798672524744469416926336509918247806477620627884417530450835119927726444989387304909336257510782797171895577769162118)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c70 : atCode 2 70 := LocalLightPackets.run_sound 18 36 72 p70 (by decide +kernel)

def p71 : HPacket := LocalCompactPackets.decode 16391 [1536,256,1024,64,1280,768,1160,576,562,417,85] 13452225668074438655 [0,1,2,3,4,5,6,16384,16385,16386,16387,16388,16390,16391] 1151219270145 1151219270145 83256364755371717902876345091 [(1856,16723986,102140543281179399948958384059402202608150891094154557735076336508363328951475985644641095943002430562873271753700962351780421238259104141402604798172952632354259278392644754823578768001054720615938356910954399167504053162880186256159228162301856924311795967492098641645357298198029284272145533534023084413935905694583462662221711890890968769055917055528968582660871195192917889623271314239554291340061704262),(1857,327698,2620247617513815316766523804424515632047394377828929845052106921304060955678414423008841284516907340190415629336977040),(1858,5574674,129188181715940999047910826111820513583408037870887548162514967857229757584342647834081),(1860,655378,129188181701472288218557425880785519845397362593213245363388716146034623205220959652722),(1864,327698,129188181715940999047910826111820513583408037108660378058964048443488057006553084989683),(1872,327698,2620247617366995569427284350211532089591598600512216116580313152285652350076931474931032747121036372000188957944979940),(1888,327698,2620247617513698854418562172006458269579569061330319124852809639287906778917114566764914723522900934321218357542528485),(1928,327698,1925053920305202533852999028225856523085722748942349717098214764876788578390259),(1984,327698,2620247617513698854418562106817328440984721527407694646521971556304727931293471450517923843877227412649647998006984774)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c71 : atCode 2 71 := LocalLightPackets.run_sound 18 36 136 p71 (by decide +kernel)

def p72 : HPacket := LocalCompactPackets.decode 16391 [1536,256,1024,192,1024,768,1160,584,546,417,85] 11149109448234999679 [0,1,2,3,4,5,6,16384,16386,16387,16390,16391] 4362207499 4362207499 5415723683629978008361326482883331 [(1864,327698,8702264693289390123093092926386554481379355678335845693481129272612635899269388068079061959043),(1928,327698,583999097761428362542632995153529772106115464325793617951229926657617800397151672622113235740963897587),(1984,327698,176502896988691584412613797953581539180763889894404864895846444531261823132961595555529313569480061821653558225558884472324166)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c72 : atCode 2 72 := LocalLightPackets.run_sound 18 36 272 p72 (by decide +kernel)

def p73 : HPacket := LocalCompactPackets.decode 16391 [1536,256,1024,192,256,768,1160,584,562,417,69] 11150903851195825343 [0,1,2,3,4,5,6,16384,16386,16388,16391] 4362207498 4362207498 5395440964536594077770371846963971 [(1864,327698,8604986277505099226808811815773033004774710094146606990439513525981358419065711581913753059715),(1928,327698,577470853818520183832395059501737645370024313420722329409564187460058090709783469131069926995277119731),(1984,327698,174529856314160262494816947533630969004351196532696054732929765827335148416814369003604694684515530228516219338451047413710918)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c73 : atCode 2 73 := LocalLightPackets.run_sound 18 36 1040 p73 (by decide +kernel)

def p74 : HPacket := LocalCompactPackets.decode 16391 [1536,256,1024,192,1280,512,1160,584,530,417,85] 13445628598845149183 [0,1,2,3,4,5,6,16384,16385,16387,16390,16391] 1142612558337 1142612558337 82637385290851383888107078403 [(1864,327698,8637079541075352122219638344577295156884839952982009478091861205875979388263487468196687774083),(1928,327698,579624596311862338693888005173305899719505283481271035729044031260704165872413321163842527694157775091),(1984,327698,175180785031410084116512727731376542236187487663930068387733175089627543293296725966078059311660304165452959738697447603437638)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c74 : atCode 2 74 := LocalLightPackets.run_sound 18 36 288 p74 (by decide +kernel)

def p75 : HPacket := LocalCompactPackets.decode 3162119 [1536,256,1024,192,1280,256,1160,584,562,385,85] 13447737908421195775 [0,1,2,3,4,5,6,16384,16390,16391,1048577,1048581,1048583,1064967,2097157,2097159,2113543,3145728,3145730,3145732,3145733,3162112,3162115,3162119] 77146176802000136 296915451379977 28229463163000494887065629841431895982370639446162729329670226248451 [(1417,20498,29979616229407034883696061912032874151067696199410415927616424563711632),(1473,20498,608058856125116724051947721762870283064310864221347594006610082238183325147196669578356430296270511760),(1864,22605959067095058,9060783030466599106722315564882802199338701724828152985418289551239272798451658098709119107459),(1928,20498,608058855638678767061576835911734459882539094584799821692537776809502014705540331383732032245963423987),(1984,22605959067095058,183774512753739835611694143973546382164124987692116682938837683155761087734098254515926024931069571020297168062338143893865542)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c75 : atCode 2 75 := LocalLightPackets.run_sound 18 36 544 p75 (by decide +kernel)

def p76 : HPacket := LocalCompactPackets.decode 10508295 [1536,256,1024,192,1280,768,1032,520,562,417,85] 11720609204006289407 [0,1,2,3,4,5,6,4101,6150,6151,18435,18439,20485,20486,22528,22535,2097152,2097156,2097158,2099206,2101254,2103298,2103302,2113541,2113543,2117633,2117635,2117637,2117639,2119681,2119682,2119683,2119684,2119685,2119686,2119687,8388608,8390657,8390659,8392707,8404994,8404995,8404999,8407043,8409094,8411138,8411140,8411142,10485760,10487809,10502146,10504195,10506243,10508289,10508291,10508292] 1455358983471690482585856 5369955443960958943745 55840895756053121068638920133470171384038796131012530256477887878149061945996579503355452458166522740403643787304883506845017509198228161283 [(1800,29417025340101056860828968520052754,5511877857021611161057670173161800243919431773286160598147539980141806521541230992835125054417071457716026339115866296850015445218830811187979671887551451902279963292759421976966572059402243429878666583856999200281981154749235682408196112706826958443942162576278040963022973537183266490333935776428619661796013863624298961976860244740700664655598948600146329327481322018701555),(1801,20498,9489069850873281304805470497440428599133649430336687970979328604701974970866243491123995622032),(1802,27692225147315146953703003873366034,31396698466374785003175461001509099051269526594523060637813873682978273),(1804,20498,467847264468689814711799276555918503097761572161584525816649586),(1816,92235127743431331858,9489069850387495510649659217854058335501387842518187636972386466981067188426564873552704307667),(1832,40978,636800698497355611260221980605042023791779541195376726552428009053309239444894307565082800573409657299),(1864,20498,141398159398588941343229407640549629894410974258597388961176701967927362882459508670851),(1928,20498,9489069856663876932479373693450095388858352189252521591120158896265991382415421721594720157939),(1984,20498,9489069848930227056506759422523277656179000866625286866749217843816946925298487148646366200902)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c76 : atCode 2 76 := LocalLightPackets.run_sound 18 36 192 p76 (by decide +kernel)

def p77 : HPacket := LocalCompactPackets.decode 16391 [1536,256,1024,192,1280,768,136,584,562,417,21] 11583249415422935039 [0,1,2,3,4,5,6,16384,16386,16387,16388,16391] 4446224897 4446224897 1260946433638872195072771 [(1864,18,28579291828631314867866525659968790971185400152094915009438654136058243),(1928,18,579656903050595490244846214529145546362311411892253511997132539094033061506014942375330520785755308275),(1984,18,579656903050595490244846214529145546362311411892253511997132539072763141943580674698622956820362170438)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c77 : atCode 2 77 := LocalLightPackets.run_sound 18 36 1088 p77 (by decide +kernel)

def p78 : HPacket := LocalCompactPackets.decode 3162119 [1536,256,1024,192,1280,768,1160,72,562,289,85] 13449971806777638911 [0,1,2,3,4,5,6,16386,16387,16388,16391,1048577,1048579,1064963,2097155,2113539,3145728,3145730,3145732,3145733,3145735,3162115,3162116,3162119] 5037623821358831568640 306845483008513 101046830637028655067449763821967911937992563758531331 [(1864,21480079378,9028190454359580106256435189056145908733609919469347926209597010252564672222375079494688178563),(1928,21480079378,29871776418748716096394811212344409782784890643098388610135376487514355),(1984,21480079378,9028190454359580106256435189056145908733609919471834961507991329639844823622778059503674867782)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c78 : atCode 2 78 := LocalLightPackets.run_sound 18 36 640 p78 (by decide +kernel)

def p79 : HPacket := LocalCompactPackets.decode 16391 [1536,256,1024,192,1280,768,1160,584,50,161,85] 13454523680126140415 [0,1,2,3,4,5,6,16384,16386,16387,16391] 4446224897 4446224897 1256223994816933535220483 [(1864,18,1917816914404147278861635318362588644514602829016250389985941020028829286793603),(1928,18,1917816914298117135828279400380317363595075115537361266962718938497764344987891),(1984,18,579624596279208218358047464376236086627590089160447142980866896696808285405150348918927436276018708550)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c79 : atCode 2 79 := LocalLightPackets.run_sound 18 36 768 p79 (by decide +kernel)

def p86 : HPacket := LocalCompactPackets.decode 2097159 [1536,256,32,128,1280,772,1152,584,562,417,81] 12177733370318028023 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097156,2097157,2097159] 4479779329 4479779329 1265631978972663435821827 [(1441,18,28794207892685335818589962524204450560573370611278548235080112264708752),(1924,18,1932346580273946604898340006872327804946533250677513928962130982534824033526946),(1952,18,53346263804555799561982189662923066084098143381576560519936711402312477346601323312227067418784526836818191758762446368198183902203877408778563616805)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c86 : atCode 2 86 := LocalLightPackets.run_sound 18 1028 72 p86 (by decide +kernel)

def p87 : HPacket := LocalCompactPackets.decode 67108871 [1536,256,32,64,1280,772,1160,576,562,417,81] 13470248871253900535 [0,1,2,3,4,5,6,67108864,67108865,67108866,67108868,67108870,67108871] 4479779329 4479779329 1265613532228589726270211 [(1860,995346,27718758754139215886443268138012392168275456162205937231740164930275490),(1888,995346,169915496756222677031213992390528104569517125239178260315990626986609128536864748251337124389655185948127253774839634576539685)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c87 : atCode 2 87 := LocalLightPackets.run_sound 18 1028 136 p87 (by decide +kernel)

def p89 : HPacket := LocalCompactPackets.decode 69206023 [1536,256,32,192,256,772,1160,584,562,417,65] 11168927054387870903 [0,1,2,3,4,5,6,2097152,2097154,2097157,2097159,67108865,67108870,67108871,69206016,69206018,69206021,69206022] 1146890488841 1151202492929 22740398038894108649576314370429793559970563 [(481,21480079378,29332754391496044730401731065221581153896941785367137497289346477458416)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c89 : atCode 2 89 := LocalLightPackets.run_sound 18 1028 1040 p89 (by decide +kernel)

def p92 : HPacket := LocalCompactPackets.decode 2097159 [1536,256,32,192,1280,772,1032,520,562,417,81] 11738632407185751287 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097156,2097157,2097159] 4479779329 4479779329 1265631978972663435821827 [(1804,18,6393598513170253380490010955025660594829258362309321890),(1832,18,39192644846080761134585812928690336172081056842031183981856736247777935379059207017131206620960309201504567763)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c92 : atCode 2 92 := LocalLightPackets.run_sound 18 1028 192 p92 (by decide +kernel)

def p103 : HPacket := LocalCompactPackets.decode 524295 [1536,256,1056,0,1280,772,1152,576,562,417,85] 12461442554668777471 [0,1,2,3,4,5,6,524288,524289,524290,524291,524294,524295] 1146924302849 1146924302849 82946875023111550895491711747 [(1441,327698,28685538770100547283265515556092594096296297625841136117365226564485776),(1860,983058,8669672117182726821466825950418909378374626128055822619391618598964141889740546501859763821730),(1888,983058,175841840990349830289676164210704809960694362726045213792752034211690009084029480747025920520791431588636711790460938965745701),(1924,983058,8669672117182726792730355110539184871155619853117805994470279573674536231715277679131747163298),(1952,983058,53144935423629493243057468028822036897945283673959518985432508207131271520115759621032529898055965510150306732789997785745842306688969554092502024229)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c103 : atCode 2 103 := LocalLightPackets.run_sound 18 72 136 p103 (by decide +kernel)

def p104 : HPacket := LocalCompactPackets.decode 2097159 [1536,256,1056,128,1024,772,1152,584,546,417,85] 10158326334292467583 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097156,2097159] 4362207499 4362207499 5415723683629978008361326482883331 [(1441,327698,28793378558376087887074395313352757983504646793889470420032593805968016),(1698,99946514,1932290925022765238894316801973583325247277337398900363880550407917323588470241),(1924,99946514,8702264693289745793167082940642740645096382752788207440302234825326140667258292348549949562018),(1952,99946514,53344727330849716745865892895752714104513199021576079088005649291933144905211252608935523551931434044632070641939555002765819914034233488756237402149)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c104 : atCode 2 104 := LocalLightPackets.run_sound 18 72 272 p104 (by decide +kernel)

def p105 : HPacket := LocalCompactPackets.decode 2097159 [1536,256,1056,128,256,772,1152,584,562,417,69] 10160120737253293247 [0,1,2,3,4,5,6,2097152,2097154,2097156,2097157,2097159] 4463002113 4463002113 1260909540150724775969539 [(1441,18,28471511280149634623515478477675336709790091303978992857327695164080784),(1924,18,8604986277505484525183634996951574918281469231249347360857960217350806055413115904023173536930),(1952,18,52748412374179463034138652290325138097879641345871734189416508713798598063266285272189768994238350740932146569140662969836608138297415055627360403493)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c105 : atCode 2 105 := LocalLightPackets.run_sound 18 72 1040 p105 (by decide +kernel)

def p106 : HPacket := LocalCompactPackets.decode 2097159 [1536,256,1056,128,1280,516,1152,584,530,417,85] 12436831077803200511 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097159] 4463002113 4463002113 1260946433638872195072771 [(1441,18,6369469123268644513398987056094480479183167176100807312),(1924,18,8669672117182726792730355541898331545565952348761356992912112254572210476159027193326351686818),(1952,18,2620247616637286159429736453065669871722984337545366317145633458200415398283656292510482124026615237993805420892524581)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c106 : atCode 2 106 := LocalLightPackets.run_sound 18 72 288 p106 (by decide +kernel)

def p107 : HPacket := LocalCompactPackets.decode 77611015 [1536,256,1056,128,1280,260,1152,584,562,385,85] 12438931599876159487 [0,1,2,3,4,5,6,16384,16387,2097152,2097154,2097155,2097158,2113539,2113541,2113543,8404992,8404996,8404997,8404999,10485765,10485767,10502149,67108866,67108870,67125253,67125255,69206018,69206020,69206021,69206022,69206023,69222405,75497472,75497473,75497477,75497479,75513860,75513861,77594628,77594629,77611009,77611013] 358022122033632067990653440 351939621265010518812525057 3416081739114920164738440384934562270847726329176644099978279207869545472871600471394472248541504679368594274881402314732949439904744001757315843 [(1413,1246151246048359405610570902008778770,1947697832409025258271234375871645555841502639894834468204078962166535252090512),(1441,1246151246048359405610570902008778770,29022959357634563813628644425232497397672802792121316387061920129097360),(1924,1246151246048359405610570902008778770,8771651232267579299502429079928971781332842330596920934343566653959907486061213555975556179106),(1952,1246151246048359405610570902008778770,588655549698852233219028907277126302326267241386184527554238313482881787317386405904225892203948688421)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c107 : atCode 2 107 := LocalLightPackets.run_sound 18 72 544 p107 (by decide +kernel)

def p108 : HPacket := LocalCompactPackets.decode 2097159 [1536,256,1056,128,1280,772,1024,520,562,417,85] 11882747594737713151 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097159] 4362207498 4362207498 5395440964536594077770371846963971 [(1441,327698,28685538770100547283265515556092594094024667750232149029883134420451984),(1804,983058,28685538770100449108410156478209107935174611721632825350563325953449122),(1832,983058,39044732103307338944520599440481596111953903373393807726571940967550286553252645063562599098362243979051796867),(1924,983058,8669672117182726792730355110539184871155619853117805994470279573674502381791535835980438183074),(1952,983058,53144935423629493243057468028822036897945283673959518985432508207131271520115759621032529898055965510150306580343493835461320432403150809944116953125)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c108 : atCode 2 108 := LocalLightPackets.run_sound 18 72 192 p108 (by decide +kernel)

def p109 : HPacket := LocalCompactPackets.decode 2097159 [1536,256,1056,128,1280,772,128,584,562,417,21] 11889502994163105791 [0,1,2,3,4,5,6,2097152,2097153,2097156,2097158,2097159] 4463002113 4463002113 1260891093406651066417923 [(1441,327698,28471452041984688294775935781119487694429954499134902172341553342448272),(1924,327698,8604968373868677345116069873730357291009603373783100661322401517055344747677919907781252488354),(1952,327698,52748302625206990987536767781047528181876704871718281124024486321561736219317081019460585660699287023154936784565300683819801063347721783697752195109)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c109 : atCode 2 109 := LocalLightPackets.run_sound 18 72 1088 p109 (by decide +kernel)

def p110 : HPacket := LocalCompactPackets.decode 2097159 [1536,256,1056,128,1280,772,1152,72,562,289,85] 12459188692835106815 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097157,2097159] 1151219270145 1151219270145 83256364773818461976585896707 [(1441,18,28685538770100547379046488287458340439268591076606553709874177991508624),(1924,18,28685538770100449012997482164655729469275977340092691541241632714136738),(1952,18,39044732094591977711329335599262048885942248221129955475027869075505881153143532335698815786997278422742073381)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c110 : atCode 2 110 := LocalLightPackets.run_sound 18 72 640 p110 (by decide +kernel)

def p111 : HPacket := LocalCompactPackets.decode 2097159 [1536,256,1056,128,1280,772,1152,584,50,161,85] 12463740566183608319 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097158,2097159] 1151219270145 1151219270145 83256364755371717902876345091 [(1441,327698,28685538770100547283587045921031250118083136818364503869585479328072336),(1924,327698,28685538770100449012985790151557061049676814203735406445592023022967970),(1952,327698,581811846712096180286995163359448559517815774083257615361299428751693857611665175911194856126173413413)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c111 : atCode 2 111 := LocalLightPackets.run_sound 18 72 768 p111 (by decide +kernel)

def p120 : HPacket := LocalCompactPackets.decode 16391 [1536,256,1056,64,1024,772,1160,576,546,417,85] 11450841835228340095 [0,1,2,3,4,5,6,16384,16385,16386,16389,16390,16391] 1146924302849 1146924302849 82944457171472321637142299395 [(1634,16060434,28685538770099272318796721012392910346265443560510079332980225622410721),(1860,327698,8669672117182726835940837320763018348152834348164497399044323482445429563867027886318320091298),(1888,16060434,175841841010050834411347176453361340614070264626297865448318288474687638741332843069366349890316320963771728413243633571994661)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c120 : atCode 2 120 := LocalLightPackets.run_sound 18 136 272 p120 (by decide +kernel)

def p121 : HPacket := LocalCompactPackets.decode 35651591 [1536,256,1056,64,256,772,1160,576,562,417,69] 11452636238189165759 [0,1,2,3,4,5,6,2097152,2097157,2097159,33554432,33554434,33554436,33554438,33554439,35651584,35651588] 4513595905 1155480683009 22740738316048450629391049008315724812583683 [(837,21480144914,1932496294141932274819950020265854502212960500889769494002783430713361531143024),(1860,21480144914,8573412219401809919294626409431937958363751676639569533407248282730199735095691770561185193122),(1888,21480144914,173889458334852036233258355114653655813103390075589429450065858511203774299857415858702660121214586393458890437413700248535077)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c121 : atCode 2 121 := LocalLightPackets.run_sound 18 136 1040 p121 (by decide +kernel)

def p122 : HPacket := LocalCompactPackets.decode 33554439 [1536,256,1056,64,1280,516,1160,576,530,417,85] 13729346578739073023 [0,1,2,3,4,5,6,33554432,33554434,33554436,33554438,33554439] 4463002113 4463002113 1260891093406651066417923 [(1860,331794,8377230135472482067868318204528177876195840334204771944419470799936735802685661713417634840738),(1888,331794,8377230135472126419519010919497211919998575190963872559511010029074242552001977395831837298725)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c122 : atCode 2 122 := LocalLightPackets.run_sound 18 136 288 p122 (by decide +kernel)

def p123 : HPacket := LocalCompactPackets.decode 77594631 [1536,256,1056,64,1280,260,1160,576,562,385,85] 13731447100812031999 [0,1,2,3,4,5,6,2097152,2097153,2097157,2097159,8388610,8388612,8388613,8388615,10485765,67108866,67108869,67108871,69206020,69206021,75497472,75497474,75497476,75497477,77594625,77594629] 20181773486966638592 300222660215297 23869465529815672308912510002032391372473091 [(1860,68454252562,8607160574727467723566607069970112118625960520702579777266249791230643129657774377789597686946),(1888,68454252562,8607160574727112031935730017577438004720453506311203551598142650763333978705495160970435899429)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c123 : atCode 2 123 := LocalLightPackets.run_sound 18 136 544 p123 (by decide +kernel)

def p124 : HPacket := LocalCompactPackets.decode 3276807 [1536,256,1056,64,1280,772,1032,512,562,417,85] 12026845190627524607 [0,1,2,3,4,5,6,131072,131078,131079,1048577,1048581,2097153,2097157,2228225,3145728,3145729,3145732,3145733,3145735,3276800,3276801,3276805] 1177023023106 1176955519489 1570396704951447872208461767935672951488521765635 [(1804,995346,29979616229406936446191318089719179243026127492473734650452091976306850),(1832,995346,40806139049205068481108049139620623170290501890312571320029456802978149771434885301243757702978856308695107827),(1860,252653586,9060783030466954920788627887710030977002932619451745077937918061340690967577496915316563792034),(1888,995346,183774512743889334207103857089798008430033006323117379336287186463461671907501496528081246409468848177437831658711863320903717)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c124 : atCode 2 124 := LocalLightPackets.run_sound 18 136 192 p124 (by decide +kernel)

def p125 : HPacket := LocalCompactPackets.decode 7 [1536,256,1056,64,1280,772,136,576,562,417,21] 11884981802416275455 [0,1,2,3,4,5,6] 17039873 17039873 288097900495619 [(1860,18,27716573524055707767597113826155046132913680625034295325669694143201442),(1888,18,37725844968973176715660421410898802887562970406088918067999477238658563093545047009846101691905579769921536037)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c125 : atCode 2 125 := LocalLightPackets.run_sound 18 136 1088 p125 (by decide +kernel)

def p126 : HPacket := LocalCompactPackets.decode 35651591 [1536,256,1056,64,1280,772,1160,64,562,289,85] 13756225385584394239 [0,1,2,3,4,5,6,2097152,2097153,2097156,2097157,2097159,33554432,33554438,33554439,35651584,35651588] 4513726977 1155514237441 22740738326473609165668007750902750002873091 [(1377,21480144914,8606014741973734979352922144197864737640651913924852430346884964482715385177658842377105965712),(1860,21480144914,8606014741973705336578077391238675460687477546752486371744027738374858461650416811949900700834),(1888,21480144914,174550716051768119430344424721168073931634226991033655337540260780817328307643212702874938156387132298551150650828447301763109)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c126 : atCode 2 126 := LocalLightPackets.run_sound 18 136 640 p126 (by decide +kernel)

def p127 : HPacket := LocalCompactPackets.decode 7 [1536,256,1056,64,1280,772,1160,576,50,161,85] 13756256067119480831 [0,1,2,3,4,5,6] 17039873 17039873 288097900495619 [(1860,18,1859920868922849860744248477021317405214618670112488448359298284311950705819810),(1888,18,8376338932219200060937551345862300682425861616498830648967595762333044948691635442254597849125)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c127 : atCode 2 127 := LocalLightPackets.run_sound 18 136 768 p127 (by decide +kernel)

def p140 : HPacket := LocalCompactPackets.decode 16391 [1536,256,1056,192,1024,772,1032,520,546,417,85] 9719225371160190847 [0,1,2,3,4,5,6,16384,16385,16388,16390,16391] 4362207499 4362207499 5415723683629978008361326482883331 [(1578,262807570,6393414366095064681516232263851184515959244605840950753),(1804,655378,28793378558375989854864520811055024412932147960831641628899677778477218),(1832,262807570,39191516027794400427620230945229397188979240428275878931493941795446171566126883986201135852626989081283527123)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c140 : atCode 2 140 := LocalLightPackets.run_sound 18 272 192 p140 (by decide +kernel)

def p155 : HPacket := LocalCompactPackets.decode 78659591 [1536,256,1056,192,256,260,1160,584,562,385,69] 11430125283933418687 [0,1,2,3,4,5,6,16384,16387,16389,16390,2097155,2097157,2097158,2113539,2113543,3145728,8388615,8404992,8404996,8404997,8404998,8404999,10485765,10485766,10485767,10502151,67125254,67125255,68157447,68173829,68173831,69206021,69206023,70254596,70254597,70254598,70254599,70270983,75497474,75497478,75497479,75513858,75513862,76546049,76546053,76546055,76562437,78643205,78643206,78659591] 94451179200195286943760256512 6107868372982179106561904064332289 33684936484025949266326912851629552713746383496504196582358959729419891121871604136653396532435605351145385505305651154392287528262605553646657603520005506686010005301306377986543560445879476423939307195613232832189971285093643863911342629989269177091 [(453,223007451985306233156210362971549649543495698,7327318122755552209758885545777359569548829893968797680)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c155 : atCode 2 155 := LocalLightPackets.run_sound 18 1040 544 p155 (by decide +kernel)

def p156 : HPacket := LocalCompactPackets.decode 2097159 [1536,256,1056,192,256,772,1032,520,562,417,69] 9721019774121016511 [0,1,2,3,4,5,6,2097152,2097155,2097156,2097159] 4429447681 4429447681 1256223994816933535220483 [(1804,18,28578508570079174343242934664249882444385079281365692597573420272589986),(1832,18,38899050146297125847449101164784302222327759063671677182223906076467197674783602675031245302689885565814571475)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c156 : atCode 2 156 := LocalLightPackets.run_sound 18 1040 192 p156 (by decide +kernel)

def p172 : HPacket := LocalCompactPackets.decode 44040199 [1536,256,1056,192,1280,516,1032,520,530,417,85] 11997730114670923775 [0,1,2,3,4,5,6,2097152,2097157,2097159,8388609,8388610,8388614,10485761,33554434,33554438,41943040,41943042,41943044,41943046,41943047,44040196] 302426012385288 1181250486785 1576127909698125153790815975871145197875736412931 [(1804,90199556114,28476599180316589548428341195043729942660925768304413392422240481189026),(1832,90199556114,1911032222756948542773879977176474940595781829531307875452752167102417984553427)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c172 : atCode 2 172 := LocalLightPackets.run_sound 18 288 192 p172 (by decide +kernel)

def p188 : HPacket := LocalCompactPackets.decode 77611015 [1536,256,1056,192,1280,260,1032,520,562,385,85] 11999830636743882751 [0,1,2,3,4,5,6,16389,2097152,2097156,2097157,2113539,2113541,2113543,8404994,8404995,8404996,8404999,10485763,10485767,10502147,10502148,67108864,67125251,67125255,69206018,69206019,69206023,69222403,75497472,75497473,75497475,75497479,75513858,75513859,77594627,77611009,77611011] 351958529395268435730761984 1355800458337261476643329 9536697022135356002827562868790247177843699191273401896606434309367598966690080604382693516157774356349699 [(1804,102758695820165328054255634,28913434572667119188292290485402668569019936078572641964028872646729890),(1832,102758695820165328054255634,1940347748939801451819095012128385726700937068515688460115153351743094027213267)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c188 : atCode 2 188 := LocalLightPackets.run_sound 18 544 192 p188 (by decide +kernel)

def p205 : HPacket := LocalCompactPackets.decode 2097159 [1536,256,1056,192,1280,772,8,520,562,417,21] 11882747595258396671 [0,1,2,3,4,5,6,2097152,2097153,2097158,2097159] 4446224897 4446224897 1256168654584712406565635 [(1804,983058,28471452041984491992315474920666188188260493890789910902933916110298274),(1832,983058,38753332348996536390759057907227499435891969923559769509917319908205090957650377195209102172453690263201907155)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c205 : atCode 2 205 := LocalLightPackets.run_sound 18 192 1088 p205 (by decide +kernel)

def p206 : HPacket := LocalCompactPackets.decode 3276807 [1536,256,1056,192,1280,772,1032,8,562,289,85] 12026843129143885823 [0,1,2,3,4,5,6,131072,131078,131079,1048577,1048579,1048581,2097153,2097155,2097157,3145729,3145731,3145732,3145733,3145735,3276800,3276803,3276804,3276806] 302438930841608 302438846562817 29074429784350341557498439362724691033677913230545534283261520708355 [(1321,331794,29979616229407034788569843341309778834793071077541276582023137795251856),(1804,331794,29979616229406936422520837218507130863559737887017848877430722021840034),(1832,331794,40806139047042915571772551001827982561280333578095242343360690488789377098849610905733694196181953086541005267)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c206 : atCode 2 206 := LocalLightPackets.run_sound 18 192 640 p206 (by decide +kernel)

def p207 : HPacket := LocalCompactPackets.decode 2097159 [1536,256,1056,192,1280,772,1032,520,50,161,85] 12024639603051331583 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097159] 4463002113 4463002113 1265668872460810854925059 [(1804,18,6369469123268622703565595399503890391317187012224621730),(1832,18,1925053919231359412601041371752033245092917732423434263952427489887590545621459)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c207 : atCode 2 207 := LocalLightPackets.run_sound 18 192 768 p207 (by decide +kernel)

def codes : List ℕ := [52,54,55,56,60,69,70,71,72,73,74,75,76,77,78,79,86,87,89,92,103,104,105,106,107,108,109,110,111,120,121,122,123,124,125,126,127,140,155,156,172,188,205,206,207]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 2 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 2 z := by
  unfold codes
  apply intro_cons _ _ _ c52
  apply intro_cons _ _ _ c54
  apply intro_cons _ _ _ c55
  apply intro_cons _ _ _ c56
  apply intro_cons _ _ _ c60
  apply intro_cons _ _ _ c69
  apply intro_cons _ _ _ c70
  apply intro_cons _ _ _ c71
  apply intro_cons _ _ _ c72
  apply intro_cons _ _ _ c73
  apply intro_cons _ _ _ c74
  apply intro_cons _ _ _ c75
  apply intro_cons _ _ _ c76
  apply intro_cons _ _ _ c77
  apply intro_cons _ _ _ c78
  apply intro_cons _ _ _ c79
  apply intro_cons _ _ _ c86
  apply intro_cons _ _ _ c87
  apply intro_cons _ _ _ c89
  apply intro_cons _ _ _ c92
  apply intro_cons _ _ _ c103
  apply intro_cons _ _ _ c104
  apply intro_cons _ _ _ c105
  apply intro_cons _ _ _ c106
  apply intro_cons _ _ _ c107
  apply intro_cons _ _ _ c108
  apply intro_cons _ _ _ c109
  apply intro_cons _ _ _ c110
  apply intro_cons _ _ _ c111
  apply intro_cons _ _ _ c120
  apply intro_cons _ _ _ c121
  apply intro_cons _ _ _ c122
  apply intro_cons _ _ _ c123
  apply intro_cons _ _ _ c124
  apply intro_cons _ _ _ c125
  apply intro_cons _ _ _ c126
  apply intro_cons _ _ _ c127
  apply intro_cons _ _ _ c140
  apply intro_cons _ _ _ c155
  apply intro_cons _ _ _ c156
  apply intro_cons _ _ _ c172
  apply intro_cons _ _ _ c188
  apply intro_cons _ _ _ c205
  apply intro_cons _ _ _ c206
  apply intro_cons _ _ _ c207
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand2

namespace LocalLightBand3
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def p70 : HPacket := LocalCompactPackets.decode 44040199 [1536,16,1024,128,1282,768,1152,584,560,417,85] 16841971642224586623 [1,2,3,4,5,6,2097152,2097156,2097158,2097159,8388609,8388610,8388611,10485762,33554433,33554435,35651585,41943040,41943041,41943042,41943043,41943047] 303525524015107 1185545388288 1581859201554429890859441021755157519290373243394 [(1712,168435730,8606651315725706709793939108022981742126981410373784306760660455722116176814509931593969703428),(1922,2852790290,1911060492417403536025546423369197372362305747846813778281313134580525014984785),(1936,2852790290,174563627301356358796371268460654826475776598004551252350745920007160189921415995120884825799580657975017115372869378927761428)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c70 : atCode 3 70 := LocalLightPackets.run_sound 258 36 72 p70 (by decide +kernel)

def p71 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1024,64,1282,768,1160,576,560,417,85] 18134487143160459135 [0,1,2,3,4,5,6,33554432,33554433,33554436,33554437,33554438,33554439] 4362207500 4362207500 5436006402723361938952281118802691 [(1648,655378,8409822711579412147217517029586814142726036684654401992224217180486000374693217266627617227268),(1858,262807570,27825769208105606828615945621206274365306834569925432447928863308121169),(1872,262807570,170571468930346200963595595021486374297244892031680744718281068982016673386989915144220096934302380510674138167749847994859540)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c71 : atCode 3 71 := LocalLightPackets.run_sound 258 36 136 p71 (by decide +kernel)

def p74 : HPacket := LocalCompactPackets.decode 33570823 [1536,16,1024,192,1282,512,1160,584,528,417,85] 18129297448814743423 [0,1,2,3,4,5,6,16384,16386,16390,16391,33554432,33554437,33554439,33570816,33570823] 1164138054145 298019341992449 1547226228637851761656018261028984034824936555267 [(1624,1347424274,577531328952831516738907880503530185254061817929000185017395207218150984502310394127670057558900998531),(1688,1347424274,8605887427223198415616557778674822408401353729996601594480846639618808859809798153681233772787),(1744,1347424274,174548133801856964455959075613070308755020204857672895052348483324188473048889133716580125439495005477577778895904806745939460)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c74 : atCode 3 74 := LocalLightPackets.run_sound 258 36 288 p74 (by decide +kernel)

def p76 : HPacket := LocalCompactPackets.decode 131079 [1536,16,1024,192,1282,768,1032,520,560,417,85] 16402870679092309887 [0,1,2,3,4,5,6,131073,131076,131077,131078,131079] 4362207499 4362207499 5415723683629978008361326482883331 [(1592,655378,28685538770100155036228259050751467806595480094884940879863314345099731),(1802,262807570,6369469123625847091277627876256676336604503745270645841),(1816,262807570,581811847036601710990051342778384806286709294551570856065606008473521516406279684347174974254043103699)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c76 : atCode 3 76 := LocalLightPackets.run_sound 258 36 192 p76 (by decide +kernel)

def p86 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,32,128,1282,772,1152,584,560,417,81] 16859994845404048503 [0,1,2,3,4,5,6,33554432,33554433,33554434,33554435,33554439] 4463002113 4463002113 1260946433638872195072771 [(1712,18,8475258514708335713426869705753262134549053462127805937974789131028035495688939315451203158532)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c86 : atCode 3 86 := LocalLightPackets.run_sound 258 1028 72 p86 (by decide +kernel)

def p87 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,32,64,1282,772,1160,576,560,417,81] 18152510346339921015 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554437,33554438,33554439] 294716512141825 294716512141825 5456289121816745869543235754722051 [(625,327698,1932298407267728351565358174076540690460398923462058147859905253454015113462640),(1648,327698,8344760895529841611024624497344560519326040814338387189529064277902616706345328340933677941252)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c87 : atCode 3 87 := LocalLightPackets.run_sound 258 1028 136 p87 (by decide +kernel)

def p92 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,32,192,1282,772,1032,520,560,417,81] 16420893882271771767 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554437,33554439] 1146907525633 1146907525633 82946875041558294969201263363 [(1592,18,28041856869793867330382168498504314503967772232244210883834645003633107)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c92 : atCode 3 92 := LocalLightPackets.run_sound 258 1028 192 p92 (by decide +kernel)

def p95 : HPacket := LocalCompactPackets.decode 102236167 [1536,16,32,192,1282,772,1160,584,48,161,81] 18156290500065864823 [0,1,2,3,4,5,6,524288,1048576,1048583,1572866,1572870,1572871,33554432,33554437,33554439,35127303,67108870,67108871,68157441,68681732,68681734,100663303,101187586,101711879,102236166,102236167] 77989502487893518 293642686300431 28860101158749981173042112521369867042585577274440857769511647249155 [(241,1495702228172818,6610179633993838256649942756037560704087578391886431216)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c95 : atCode 3 95 := LocalLightPackets.run_sound 258 1028 768 p95 (by decide +kernel)

def p103 : HPacket := LocalCompactPackets.decode 16777223 [1536,16,1056,0,1282,772,1152,576,560,417,85] 17143704029754797951 [0,1,2,3,4,5,6,16777216,16777217,16777220,16777221,16777222,16777223] 1146924302849 1146924302849 82944457171472321637142299395 [(1648,983058,8409822711579412132743505659242713163698456683251744496272773688667848985323388162213440127492),(1712,983058,8409822711579412204929341094755880141739287636574966969344344835313321529668317033700121379332)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c103 : atCode 3 103 := LocalLightPackets.run_sound 258 72 136 p103 (by decide +kernel)

def p104 : HPacket := LocalCompactPackets.decode 2752519 [1536,16,1056,128,1026,772,1152,584,544,417,85] 10230098055307169663 [0,1,2,3,4,5,6,131072,131077,131079,524290,524294,2097154,2097158,2621440,2621442,2621444,2621446,2621447,2752514,2752517,2752518] 1172728055809 1172660552193 1564665325982857203379591284335133996992864518915 [(1698,91626614802,2004660981230395758346870491165620555984325767950810261835752900780797066216529),(1712,91626614802,9028190453388512452242867748694375340618548182032890600841786006060495146360723307193920929812)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c104 : atCode 3 104 := LocalLightPackets.run_sound 258 72 272 p104 (by decide +kernel)

def p105 : HPacket := LocalCompactPackets.decode 7 [1536,16,1056,128,258,772,1152,584,560,417,69] 10158638599873997887 [0,1,2,3,4,5,6] 17039873 17039873 288097900495619 [(1712,18,1867268744153621613547958278645662225619398487350227527820291845309119175332356)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c105 : atCode 3 105 := LocalLightPackets.run_sound 258 72 1040 p105 (by decide +kernel)

def p106 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,128,1282,516,1152,584,528,417,85] 17120499927772794751 [0,1,2,3,4,5,6,33554432,33554436,33554437,33554439] 4446224897 4446224897 1256187101328786116117251 [(1684,18,8409822711579501075546026694406212226150631765397219237877811029079059350360876700878439973026),(1712,18,8409822711579412197692335409583832866101610099097018155079812101932887521826104076518000165380)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c106 : atCode 3 106 := LocalLightPackets.run_sound 258 72 288 p106 (by decide +kernel)

def p107 : HPacket := LocalCompactPackets.decode 67108871 [1536,16,1056,128,1282,260,1152,584,560,385,85] 17121193074962179967 [0,1,2,3,4,5,6,67108864,67108865,67108866,67108868,67108870,67108871] 4479779329 4479779329 1265613532228589726270211 [(1712,995346,27825769208106489283582247777365273190306459967747312888183222261776900)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c107 : atCode 3 107 := LocalLightPackets.run_sound 258 72 544 p107 (by decide +kernel)

def p108 : HPacket := LocalCompactPackets.decode 65543 [1536,16,1056,128,1282,772,1024,520,560,417,85] 16565009069823733631 [0,1,2,3,4,5,6,65537,65541,65542,65543] 1138300813825 1138300813825 82325477706951987622373032707 [(1592,983058,28577698981824614360954871879960963738308424833347236142878524653439363),(1712,983058,8637079541075618892719229750813271848554514079436448220908048818375656430050106847619507290628)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c108 : atCode 3 108 := LocalLightPackets.run_sound 258 72 192 p108 (by decide +kernel)

def p109 : HPacket := LocalCompactPackets.decode 35651591 [1536,16,1056,128,1282,772,128,584,560,417,21] 16571764469249126271 [0,1,2,3,4,5,6,2097152,2097158,2097159,33554432,33554433,33554436,33554437,33554439,35651585] 4513595905 1155480683009 22827849272853625591715009249405589826896643 [(1712,1347424274,8573394315764913839725518484264338868333158756041928771692750999611357528211500245245284326916)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c109 : atCode 3 109 := LocalLightPackets.run_sound 258 72 1088 p109 (by decide +kernel)

def p110 : HPacket := LocalCompactPackets.decode 67108871 [1536,16,1056,128,1282,772,1152,72,560,289,85] 17141450167921127295 [0,1,2,3,4,5,6,67108864,67108865,67108866,67108868,67108869,67108871] 4479779329 4479779329 1265631978972663435821827 [(1712,995346,27825769208106489283579324774090600823013882409554219082503103992300036)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c110 : atCode 3 110 := LocalLightPackets.run_sound 258 72 640 p110 (by decide +kernel)

def p111 : HPacket := LocalCompactPackets.decode 35651591 [1536,16,1056,128,1282,772,1152,584,48,161,85] 17147484182943870847 [0,1,2,3,4,5,6,2097152,2097154,2097156,2097158,2097159,33554432,33554437,33554439,35651588,35651589] 4513726977 1155514237441 22827849283238219927754684293834857964176131 [(1201,1347424274,1910919143360553236056653136943429386692894169270252246005579477926953598845584),(1712,1347424274,8606014741973616437125122129412613588450217613325869020127336764086028641637933183466143489540)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c111 : atCode 3 111 := LocalLightPackets.run_sound 258 72 768 p111 (by decide +kernel)

def p120 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,64,1026,772,1160,576,544,417,85] 11522613556243042175 [0,1,2,3,4,5,6,33554432,33554433,33554434,33554437,33554439] 4362207499 4362207499 5415723683629978008361326482883331 [(1634,99946514,28041448784656688011546019467174659954118559206826870761990598469616721),(1648,99946514,8475007861850781270339253695141132774271158674932926805771526116514888390466150796803942125588)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c120 : atCode 3 120 := LocalLightPackets.run_sound 258 136 272 p120 (by decide +kernel)

def p121 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,64,258,772,1160,576,560,417,69] 11451154100809870399 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554438,33554439] 1146907525633 1146907525633 82946875023111550895491711747 [(1648,327698,27611320468981644638942899215850085612310240776497481493780821872218628)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c121 : atCode 3 121 := LocalLightPackets.run_sound 258 136 1040 p121 (by decide +kernel)

def p122 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,64,1282,516,1160,576,528,417,85] 18413015428708667263 [0,1,2,3,4,5,6,33554432,33554434,33554436,33554437,33554439] 4362207499 4362207499 5415723683629978008361326482883331 [(597,327698,6393439120635837108162671595335592607923375828048282480),(1620,327698,2522011950210727811674936096287119811377200442611110059455761548165118360714889019610924450597450650664039992706203810),(1648,327698,8344637559365374131870050861753883716071118445565973110484823558601565852803799390660837507588)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c122 : atCode 3 122 := LocalLightPackets.run_sound 258 136 288 p122 (by decide +kernel)

def p123 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,64,1282,260,1160,576,560,385,85] 18413708575898052479 [0,1,2,3,4,5,6,33554432,33554433,33554434,33554435,33554439] 4463002113 4463002113 1260946433638872195072771 [(1648,18,1852881750111861987455619451948570149745270949700536384056792215015033946505732)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c123 : atCode 3 123 := LocalLightPackets.run_sound 258 136 544 p123 (by decide +kernel)

def p124 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,64,1282,772,1032,512,560,417,85] 16709106665713545087 [0,1,2,3,4,5,6,33554432,33554433,33554434,33554439] 4362207498 4362207498 5395440964536594077770371846963971 [(1592,983058,28041448784657570705032315036315632454787599155286674771606167243196659),(1648,983058,8475007863793450133616960456731544218263863125170260619845608018158380543541363533560749752836)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c124 : atCode 3 124 := LocalLightPackets.run_sound 258 136 192 p124 (by decide +kernel)

def p125 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,64,1282,772,136,576,560,417,21] 16567243277502295935 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554437,33554439] 1146907525633 1146907525633 82946875041558294969201263363 [(1648,18,27611261230817581075525381636959497668999151798121521749539796274643460)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c125 : atCode 3 125 := LocalLightPackets.run_sound 258 136 1088 p125 (by decide +kernel)

def p126 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,64,1282,772,1160,64,560,289,85] 18438486860670414719 [0,1,2,3,4,5,6,33554432,33554433,33554437,33554438,33554439] 1142612558337 1142612558337 82634967439212154629757666051 [(1648,327698,8344637559365374131870050861753878919973002279866345222913545278813247669930964248487820001796)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c126 : atCode 3 126 := LocalLightPackets.run_sound 258 136 640 p126 (by decide +kernel)

def p127 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,64,1282,772,1160,576,48,161,85] 18439999683879743359 [0,1,2,3,4,5,6,33554432,33554434,33554437,33554439] 4446224897 4446224897 1256187101328786116117251 [(1648,18,8344637559365374131870050861753878919188364554173286679591667287783371902833108134253383909892)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c127 : atCode 3 127 := LocalLightPackets.run_sound 258 136 768 p127 (by decide +kernel)

def p140 : HPacket := LocalCompactPackets.decode 65543 [1536,16,1056,192,1026,772,1032,520,544,417,85] 9790997092174892927 [0,1,2,3,4,5,6,65539,65540,65542,65543] 4362207498 4362207498 5395440964536594077770371846963971 [(1578,262807570,6345523880443005654692534313227160727219715360797754449),(1592,262807570,28577698980217676364586367970101874822645547358408105103125616774873555)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c140 : atCode 3 140 := LocalLightPackets.run_sound 258 272 192 p140 (by decide +kernel)

def p156 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,192,258,772,1032,520,560,417,69] 9719537636741721151 [0,1,2,3,4,5,6,33554433,33554434,33554436,33554437,33554439] 4463002113 4463002113 1260909540150724775969539 [(1592,18,6226538647642984855412817719941229977740449473219527123)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c156 : atCode 3 156 := LocalLightPackets.run_sound 258 1040 192 p156 (by decide +kernel)

def p172 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,192,1282,516,1032,520,528,417,85] 16681398964640518015 [0,1,2,3,4,5,6,33554432,33554434,33554435,33554436,33554439] 4362207499 4362207499 5415723683629978008361326482883331 [(1564,983058,1881829772852569935469245279655391258565004407868493635588429454850246002081954),(1592,983058,28041448784657570728977558219157026545798914023574026727239756592710099)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c172 : atCode 3 172 := LocalLightPackets.run_sound 258 288 192 p172 (by decide +kernel)

def p188 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,192,1282,260,1032,520,560,385,85] 16682092111829903231 [0,1,2,3,4,5,6,33554432,33554433,33554436,33554437,33554439] 4463002113 4463002113 1260909540150724775969539 [(1592,18,6226452416914789612704442485584252630427944174798242259)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c188 : atCode 3 188 := LocalLightPackets.run_sound 258 544 192 p188 (by decide +kernel)

def p205 : HPacket := LocalCompactPackets.decode 33619975 [1536,16,1056,192,1282,772,8,520,560,417,21] 16565009070344417151 [0,1,2,3,4,5,6,65536,65542,65543,33554434,33554436,33554437,33554439,33619969,33619971,33619973,33619974,33619975] 1164104697857 298019325215233 1564353200950318087931549672824855761827460875011 [(1592,1347420178,28366560997919316773742627438113003802898409379030686152805285206688211)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c205 : atCode 3 205 := LocalLightPackets.run_sound 258 192 1088 p205 (by decide +kernel)

def p206 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,192,1282,772,1032,8,560,289,85] 16709104604229906303 [0,1,2,3,4,5,6,33554432,33554433,33554437,33554438,33554439] 1142612558337 1142612558337 82634967439212154629757666051 [(1592,983058,27825769208106489450634810416882810699589278738532130171572781272531411)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c206 : atCode 3 206 := LocalLightPackets.run_sound 258 192 640 p206 (by decide +kernel)

def p207 : HPacket := LocalCompactPackets.decode 33554439 [1536,16,1056,192,1282,772,1032,520,48,161,85] 16708383219811594111 [0,1,2,3,4,5,6,33554432,33554434,33554437,33554439] 4446224897 4446224897 1256187101328786116117251 [(1592,18,27825769208106489450623118403653495047346088118064158914137637959762387)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c207 : atCode 3 207 := LocalLightPackets.run_sound 258 192 768 p207 (by decide +kernel)

def codes : List ℕ := [70,71,74,76,86,87,92,95,103,104,105,106,107,108,109,110,111,120,121,122,123,124,125,126,127,140,156,172,188,205,206,207]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 3 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 3 z := by
  unfold codes
  apply intro_cons _ _ _ c70
  apply intro_cons _ _ _ c71
  apply intro_cons _ _ _ c74
  apply intro_cons _ _ _ c76
  apply intro_cons _ _ _ c86
  apply intro_cons _ _ _ c87
  apply intro_cons _ _ _ c92
  apply intro_cons _ _ _ c95
  apply intro_cons _ _ _ c103
  apply intro_cons _ _ _ c104
  apply intro_cons _ _ _ c105
  apply intro_cons _ _ _ c106
  apply intro_cons _ _ _ c107
  apply intro_cons _ _ _ c108
  apply intro_cons _ _ _ c109
  apply intro_cons _ _ _ c110
  apply intro_cons _ _ _ c111
  apply intro_cons _ _ _ c120
  apply intro_cons _ _ _ c121
  apply intro_cons _ _ _ c122
  apply intro_cons _ _ _ c123
  apply intro_cons _ _ _ c124
  apply intro_cons _ _ _ c125
  apply intro_cons _ _ _ c126
  apply intro_cons _ _ _ c127
  apply intro_cons _ _ _ c140
  apply intro_cons _ _ _ c156
  apply intro_cons _ _ _ c172
  apply intro_cons _ _ _ c188
  apply intro_cons _ _ _ c205
  apply intro_cons _ _ _ c206
  apply intro_cons _ _ _ c207
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand3

namespace LocalLightBand4
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def p86 : HPacket := LocalCompactPackets.decode 2097159 [1536,272,0,128,1282,768,1152,584,562,417,81] 16843453801065741559 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097156,2097159] 4446224897 4446224897 1260946433638872195072771 [(1922,991250,581828667642111246074914600123840490072922059475215710752685966945756473830495637188181486917811699793),(1936,991250,175846924814579482180468211751957070654286975476723909842852681966236582680823999984417490974722061707917960558284049041333268)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c86 : atCode 4 86 := LocalLightPackets.run_sound 36 1028 72 p86 (by decide +kernel)

def p87 : HPacket := LocalCompactPackets.decode 50462727 [1536,272,0,64,1282,768,1160,576,562,417,81] 18135969302001614071 [0,1,2,3,4,5,6,131072,131075,131079,16777220,16777222,33554437,33554438,33685509,33685511,50331650,50331654,50331655,50462720,50462722,50462724,50462725,50462726] 1172761610241 300226938405377 430766426697677989862279273152909795356367762604125280935412483 [(849,1497169670381586,608061117267676720717345537872367876155032346661017198020297001152813690592937993005112193872958594928),(1858,1497169670381586,8573927446282022689099874866960201683762239381651877455800963499972389859850332477496221499473),(1872,1497169670381586,173899908377489148645597928330555320001924168503281546727521095867682794816574530838838091013174038919724586258733435753332756)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c87 : atCode 4 87 := LocalLightPackets.run_sound 36 1028 136 p87 (by decide +kernel)

def p91 : HPacket := LocalCompactPackets.decode 5767175 [1536,272,0,192,1282,256,1160,584,562,385,81] 18131481542348371191 [0,1,2,3,4,5,6,524288,1048576,1572867,1572868,1572871,4194306,4194309,4194311,4718594,5242882,5767172,5767173,5767174,5767175] 302408849227789 302404570710529 1575704715477522618879539377205294339396123034371 [(465,344950046738,29548433968047322168542008119299857988910641923856142752123793401709552)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c91 : atCode 4 91 := LocalLightPackets.run_sound 36 1028 544 p91 (by decide +kernel)

def p92 : HPacket := LocalCompactPackets.decode 131079 [1536,272,0,192,1282,768,1032,520,562,417,81] 16404352837933464823 [0,1,2,3,4,5,6,131072,131074,131075,131076,131077,131079] 1146907525633 1146907525633 82946875041558294969201263363 [(1802,16392210,1925109575879903269503869531008659576115229643591934873310732781925880624578641),(1816,16392210,581828667934760239068100743278972673661733745313018764993185158585470184883492317553705541044049281491)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c92 : atCode 4 92 := LocalLightPackets.run_sound 36 1028 192 p92 (by decide +kernel)

def p103 : HPacket := LocalCompactPackets.decode 40370183 [1536,272,1024,0,1282,768,1152,576,562,417,85] 16838932609264779263 [0,1,2,3,4,5,6,524291,524294,2097154,2097155,2621440,2621441,2621442,2621443,2621447,4194304,4194305,4194309,4194310,4718598,4718599,6815745,33554432,33554436,33554437,36175872,37748736,37748737,37748740,37748741,37748743] 80528317803792640 314546460033537 8155241421167200346385214103934116065764512634261948816349629015359551246833091331 [(1858,283258215186011189266,8803479918900399983543800687151703658757994147499341827189169653493319948771383691510362685521),(1872,283258215186011189266,178555785672366512824825093767254556074663308109797226912330950165281135019908821292066378384894634756484804352639921651985428),(1922,283258215186011189266,590791537188908840028293359000936777576536971549415851324259892137012284361402119952666221611278155857),(1936,283258215186011189266,178555785672366515458038708199406710442544705550001336524991679454683365554919765032162968478903140802028349291738864092720148)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c103 : atCode 4 103 := LocalLightPackets.run_sound 36 72 136 p103 (by decide +kernel)

def p104 : HPacket := LocalCompactPackets.decode 2752519 [1536,272,1024,128,1026,768,1152,584,546,417,85] 9924130366166114175 [0,1,2,3,4,5,6,131072,131073,131076,131077,131079,524290,524294,2097154,2097158,2621440,2621441,2621442,2621444,2621446,2621447,2752515,2752516,2752519] 307949390793217 307949323158017 104766403727992668325890633885213036443579500061852419 [(1698,5589184421906,2026371998178914618278835922512990861930988644381745636870955189243883342791201),(1922,5589184753682,612433357185644553566164212085667167600498579433613269423315772671974780076192455860429274417294213201),(1936,5589184753682,9125968181709569468083600422173962294824268605295567298036172185893322815148795884616368016404)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c104 : atCode 4 104 := LocalLightPackets.run_sound 36 72 272 p104 (by decide +kernel)

def p105 : HPacket := LocalCompactPackets.decode 2097159 [1536,272,1024,128,258,768,1152,584,562,417,69] 9853867179383979199 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097157,2097159] 1151219270145 1151219270145 83256364773818461976585896707 [(1922,6230034,581845355040829378184933311230919939698823820856569439036284711824307953996099057819484363834251804753),(1936,6230034,581845355040829378184933311230919939698823820856473656603478956381271282770127373944730686414745775124)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c105 : atCode 4 105 := LocalLightPackets.run_sound 36 72 1040 p105 (by decide +kernel)

def p106 : HPacket := LocalCompactPackets.decode 2637831 [1536,272,1024,128,1282,512,1152,584,530,417,85] 16832335539498618879 [0,1,2,3,4,5,6,16384,16389,16391,524290,524291,2097154,2097155,2621440,2621442,2621443,2621447,2637824,2637827,2637828] 1168433088516 1168365584897 1558934034126552466310972283043326259472858678019 [(1682,91625619474,8963005302145808897482277486652122409190111624065679358295814442043102917394848236021362983393),(1922,91625619474,601497103496289712229427614079173223566805874868121260273207216015801991420176788033798654990987296849),(1936,91625619474,181791344817822996353588207808508768095379777857463322495568532787046636964766021953725406047870340758965388094246511064401940)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c106 : atCode 4 106 := LocalLightPackets.run_sound 36 72 288 p106 (by decide +kernel)

def p107 : HPacket := LocalCompactPackets.decode 2098183 [1536,272,1024,128,1282,256,1152,584,562,385,85] 16834444849074665471 [0,1,2,3,4,5,6,1024,1029,1031,2097153,2097156,2097158,2097159,2098176,2098178,2098179,2098181,2098182,2098183] 1168399665154 299118836843009 1570062104610185142562920611384261731386504053507 [(1411,21480079378,29332577499753791119398654217071149065467839539551435006125091848986256),(1425,21480079378,594935351580863195863865447335344233783409402574302849390984585008497148470479212335468592348701400720),(1922,21480079378,594935351288962177511997478559224572818020923562954842743759596802078867840254262257000270522324877393),(1936,21480144914,179808176881900745760914646918356523947025373747590406129163488234628792176979949572551672210376682385498899941854532228626452)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c107 : atCode 4 107 := LocalLightPackets.run_sound 36 72 544 p107 (by decide +kernel)

def p108 : HPacket := LocalCompactPackets.decode 88071 [1536,272,1024,128,1282,768,1024,520,562,417,85] 16260237649333714943 [0,1,2,3,4,5,6,2048,6149,6151,16385,16389,18433,20480,20481,22529,22532,22533,65536,65542,65543,67584,71687,86016,88065,88069,88071] 1172895830786 305698911289857 1587189601982341636054785915304124060954565870339 [(1802,995346,2040846010944435981678627426535592155476801376907862640199911845793269550423121),(1816,995346,616807859154611118520981047842125659124776380161176856572670092629946393582231445334858996431194163587),(1922,995346,616807859122062182527838435083869346107834503212949191032274967066644641772762247324619337169282276433),(1936,995346,186418736668308249877241237503855914699371848901292008457826406124305861109369528113263846856279169200177131599558346803000340)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c108 : atCode 4 108 := LocalLightPackets.run_sound 36 72 192 p108 (by decide +kernel)

def p109 : HPacket := LocalCompactPackets.decode 2097159 [1536,272,1024,128,1282,768,128,584,562,417,21] 16266993048759107583 [0,1,2,3,4,5,6,2097152,2097153,2097158,2097159] 4446224897 4446224897 1256168654584712406565635 [(1922,331794,577469652098555648824266959576974976595046590221216371612416541784593278845880631290866168727940628561),(1936,331794,174529493185271155499822754533480330292350059882090920830907527548790976966245329808571219059512094611204651213261745793539092)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c109 : atCode 4 109 := LocalLightPackets.run_sound 36 72 1088 p109 (by decide +kernel)

def p110 : HPacket := LocalCompactPackets.decode 2097159 [1536,272,1024,128,1282,768,1152,72,562,289,85] 16836678747431108607 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097157,2097159] 1151219270145 1151219270145 83256364773818461976585896707 [(1922,6230034,1925053919123572280469962026362550398292054324014060085476693204346186405511249),(1936,6230034,581811847036601706154128989775796054049006593927811299196826287036787172642129082477104379915522808852)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c110 : atCode 4 110 := LocalLightPackets.run_sound 36 72 640 p110 (by decide +kernel)

def p111 : HPacket := LocalCompactPackets.decode 2097159 [1536,272,1024,128,1282,768,1152,584,50,161,85] 16841230620779610111 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097158,2097159] 1151219270145 1151219270145 83256364755371717902876345091 [(1922,5574674,28685538755707735185684675757732377542800631875580386168628527520022609),(1936,5574674,8669672117182637842802581900016033657933157709868018503550225098224451038876724438611013934100)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c111 : atCode 4 111 := LocalLightPackets.run_sound 36 72 768 p111 (by decide +kernel)

def p120 : HPacket := LocalCompactPackets.decode 131079 [1536,272,1024,64,1026,768,1160,576,546,417,85] 11216645867101986687 [0,1,2,3,4,5,6,131073,131074,131075,131076,131077,131078,131079] 4362207501 4362207501 5456289121816745869543235754722051 [(1634,94703634,28793378558374812970124865357153895644577407235922148895236717342622241),(1858,99946514,8702264693289390144804109766223114974059539936955218840676608091152558698540385322952287060049),(1872,99946514,8702264691346988023064306643543046033449275062679131268024596561320497553106896496594071326740)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c120 : atCode 4 120 := LocalLightPackets.run_sound 36 136 272 p120 (by decide +kernel)

def p121 : HPacket := LocalCompactPackets.decode 8388615 [1536,272,1024,64,258,768,1160,576,562,417,69] 11146382680319851711 [0,1,2,3,4,5,6,8388608,8388609,8388610,8388611,8388612,8388613,8388614,8388615] 295820335514113 295820335514113 5476571840910129800134190390641411 [(1858,99946514,8377729448008892539018923159715642904897551906671853901202847959190912659073515690075471486033),(1872,99946514,8377729448008892539018923159715642904897456124239048145797029671846918619640068855672350707732)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c121 : atCode 4 121 := LocalLightPackets.run_sound 36 136 1040 p121 (by decide +kernel)

def p122 : HPacket := LocalCompactPackets.decode 8388615 [1536,272,1024,64,1282,512,1160,576,530,417,85] 18124851040434491391 [0,1,2,3,4,5,6,8388608,8388610,8388612,8388615] 4362207498 4362207498 5395440964536594077770371846963971 [(1618,99946514,562186397858118406956176818855374673375870725500833058657055495779205041354387704800758973909013896673),(1858,99946514,8377230135472126419519010919431386943759114836110243499155683421219269114534335093444284783697),(1872,99946514,169910412951705450668761146299768476521124393854868990955325472839516600232050793671237007971464177812680597999812527353757716)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c122 : atCode 4 122 := LocalLightPackets.run_sound 36 136 288 p122 (by decide +kernel)

def p123 : HPacket := LocalCompactPackets.decode 8388615 [1536,272,1024,64,1282,256,1160,576,562,385,85] 18126960350010537983 [0,1,2,3,4,5,6,8388608,8388610,8388613,8388615] 4446224897 4446224897 1256187101328786116117251 [(1858,987154,8377230135472126405157194339365970384705438832429363895551234426190432500111325970037945146449),(1872,987154,169910412951705450668761146299768411841252595508847744352895310877662086235180620041831951775606382359339149527416595342426132)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c123 : atCode 4 123 := LocalLightPackets.run_sound 36 136 544 p123 (by decide +kernel)

def p124 : HPacket := LocalCompactPackets.decode 131079 [1536,272,1024,64,1282,768,1032,512,562,417,85] 16404335245223526399 [0,1,2,3,4,5,6,131072,131073,131077,131079] 4362207498 4362207498 5395440964536594077770371846963971 [(1802,268382226,1917816914512190699907973867136684844051111088771869575841645233464253916119121),(1816,268382226,579624596279226122958659840114539678343734340624711580013943261168904556812843822482473917696305006835),(1858,268382226,8637079540589684899163206076847418450836107203300657628614850123634950527000719089299502399569),(1872,268382226,175180785031415494864778443005661363737860788332165196328240214289960695101127729961243671415903104378239310174780794127515668)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c124 : atCode 4 124 := LocalLightPackets.run_sound 36 136 192 p124 (by decide +kernel)

def p125 : HPacket := LocalCompactPackets.decode 33554439 [1536,272,1024,64,1282,768,136,576,562,417,21] 16262471857012277247 [0,1,2,3,4,5,6,33554432,33554434,33554435,33554436,33554439] 4446224897 4446224897 1260946433638872195072771 [(1858,331794,1860197381351330631068227557253548820982162482633199147981229585122832169304145),(1872,331794,562210160714245135805196544791442153589231772798599980846318852945685585097478087710871489006771634196)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c125 : atCode 4 125 := LocalLightPackets.run_sound 36 136 1088 p125 (by decide +kernel)

def p126 : HPacket := LocalCompactPackets.decode 8388615 [1536,272,1024,64,1282,768,1160,64,562,289,85] 18133715440180396031 [0,1,2,3,4,5,6,8388608,8388609,8388613,8388614,8388615] 1142612558337 1142612558337 82634967439212154629757666051 [(1858,16060434,8377230135472126405156310915741432937330659645317957350141615654168013574562519009186470173777),(1872,16060434,169910412951705450668761146299768411837274009202570603389111008492802171175035276701385926477040460933502076434334130523340820)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c126 : atCode 4 126 := LocalLightPackets.run_sound 36 136 640 p126 (by decide +kernel)

def p127 : HPacket := LocalCompactPackets.decode 33554439 [1536,272,1024,64,1282,768,1160,576,50,161,85] 18133746121715482623 [0,1,2,3,4,5,6,33554432,33554434,33554435,33554436,33554439] 4446224897 4446224897 1260946433638872195072771 [(1858,331794,27717929419830066153699161652248908393662594708532142789136881048092753),(1872,331794,562186397858118406956176818855374567142085314548904908467447840815115377998964830345809782319773384724)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c127 : atCode 4 127 := LocalLightPackets.run_sound 36 136 768 p127 (by decide +kernel)

def p138 : HPacket := LocalCompactPackets.decode 147463 [1536,272,1024,192,1026,512,1160,584,514,417,85] 11211737647732985727 [0,1,2,3,4,5,6,16386,16389,16391,131073,131078,131079,147456,147459,147462,147463] 292500158810888 299114541875713 1552935131957431257068973226536858610306063336195 [(1610,21480079378,1954001942830007536106087046250779814806405654179610920416060524057611055399457),(1674,21480079378,1954001943045890740631868034913578279411909151779696852545090458826351193096737),(1730,21480079378,590560850066086159964773867596646505685099489934762415293949530871101709792632885696693965898884317729)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c138 : atCode 4 138 := LocalLightPackets.run_sound 36 272 288 p138 (by decide +kernel)

def p140 : HPacket := LocalCompactPackets.decode 200711 [1536,272,1024,192,1026,768,1032,520,546,417,85] 9485029403033837439 [0,1,2,3,4,5,6,4098,4101,4102,65539,65540,65542,69638,69639,131075,131077,135173,135175,196610,196611,196615,200706,200708,200709,200710,200711] 79398006898231041 79398006897771009 1877815477259610175975198834872911383259417348014203894442578519213277955 [(1578,384395110812110866,6752593014194498233271490464684671505355010505077948961),(1802,768613955885748242,2040846011052275766740291606312478840179410743225491969866460779168421138661457),(1816,768613955885748242,30410975379294928961891459616311930022784343422579954892452945643438547)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c140 : atCode 4 140 := LocalLightPackets.run_sound 36 272 192 p140 (by decide +kernel)

def p156 : HPacket := LocalCompactPackets.decode 10616839 [1536,272,1024,192,258,768,1032,520,562,417,69] 9414766216251702463 [0,1,2,3,4,5,6,131072,131077,131079,2097152,2097154,2097155,2097156,2097157,2228226,2228229,8388608,8388609,8388610,8388611,8388613,8519680,8519685,10485761,10485763,10485767,10616836] 20254678817421724416 1207020290561 103674622133005475207741740952292994420624450505736963 [(1802,5844008312850,1969010867908507930573109240593514005828421910830862585919320506264371568854097),(1816,5844008312850,1969010867908507930573109240593513648994720662857397657707017031347017014313427)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c156 : atCode 4 156 := LocalLightPackets.run_sound 36 1040 192 p156 (by decide +kernel)

def p172 : HPacket := LocalCompactPackets.decode 212999 [1536,272,1024,192,1282,512,1032,520,530,417,85] 16393234576366342143 [0,1,2,3,4,5,6,16384,16387,16391,65540,65541,131077,131079,147463,196610,196613,212994,212996,212997,212999] 298036538379784 296919813587457 1524480161687888983932055250399094312133527405315 [(1562,711353958418,1990186971255927025110781563960793193383899388351009827636214332534598013813217),(1802,711353958418,1990186971363911204803111911557600085235821570715131574074010924129091374022737),(1816,711353958418,601497103852982003272574939123046303146427162275023039993576115920927888420404107744745784353623638483)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c172 : atCode 4 172 := LocalLightPackets.run_sound 36 288 192 p172 (by decide +kernel)

def p188 : HPacket := LocalCompactPackets.decode 212999 [1536,272,1024,192,1282,256,1032,520,562,385,85] 16395343885942388735 [0,1,2,3,4,5,6,16384,16387,16391,65540,65541,131077,147460,196608,196613,196615,212992,212996,212997] 1155598518274 1164070617601 1553202568044346637726069028038611124828793799427 [(1802,183251238930,1990186971149060962561180580712009712085519444200445298623546335891516691316817),(1816,183251238930,601497103852982002304975468221823562440957421570032959359294175510658879790013402908462133636953014739)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c188 : atCode 4 188 := LocalLightPackets.run_sound 36 544 192 p188 (by decide +kernel)

def p205 : HPacket := LocalCompactPackets.decode 212999 [1536,272,1024,192,1282,768,8,520,562,417,21] 16260237649854398463 [0,1,2,3,4,5,6,16384,16385,16387,65542,65543,131075,147459,147463,196608,196609,196612,212992,212993,212995,212998] 1168449735172 1155514237441 1541740245668605303056920326393397998811504509699 [(1802,4026863634,1990293865611330297055051725007484221283906938618302380917700638897813669544017),(1816,4026863634,601529410657379726637470198149390013975501661083335314529527946215207430106401793624043860802724430291)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c205 : atCode 4 205 := LocalLightPackets.run_sound 36 192 1088 p205 (by decide +kernel)

def p206 : HPacket := LocalCompactPackets.decode 75628551 [1536,272,1024,192,1282,768,1032,8,562,289,85] 16404333183739887615 [0,1,2,3,4,5,6,131072,131075,131079,8388609,8388613,8388614,8519681,8519686,8519687,67108864,67108868,67108869,75497472,75497473,75497477,75497479,75628544] 304637970876418 304624984916481 430791486066264652649705859267334414958317159987496059771618051 [(1802,4312994789265426,1911117030773205339222404415983601793820931113471890687767201695874641622486097),(1816,4312994789265426,577599680538999506290229243669340778250910692446444014509666691419380511492745756596153316674503197139)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c206 : atCode 4 206 := LocalLightPackets.run_sound 36 192 640 p206 (by decide +kernel)

def p207 : HPacket := LocalCompactPackets.decode 131079 [1536,272,1024,192,1282,768,1032,520,50,161,85] 16402129657647333375 [0,1,2,3,4,5,6,131074,131075,131076,131079] 4429447681 4429447681 1256223994816933535220483 [(1802,331794,6321578636908666096696448213616147558804175358728863825),(1816,331794,1910579908719034468143122944944130955156064213674380554274503024992469881979347)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c207 : atCode 4 207 := LocalLightPackets.run_sound 36 192 768 p207 (by decide +kernel)

def codes : List ℕ := [86,87,91,92,103,104,105,106,107,108,109,110,111,120,121,122,123,124,125,126,127,138,140,156,172,188,205,206,207]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 4 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 4 z := by
  unfold codes
  apply intro_cons _ _ _ c86
  apply intro_cons _ _ _ c87
  apply intro_cons _ _ _ c91
  apply intro_cons _ _ _ c92
  apply intro_cons _ _ _ c103
  apply intro_cons _ _ _ c104
  apply intro_cons _ _ _ c105
  apply intro_cons _ _ _ c106
  apply intro_cons _ _ _ c107
  apply intro_cons _ _ _ c108
  apply intro_cons _ _ _ c109
  apply intro_cons _ _ _ c110
  apply intro_cons _ _ _ c111
  apply intro_cons _ _ _ c120
  apply intro_cons _ _ _ c121
  apply intro_cons _ _ _ c122
  apply intro_cons _ _ _ c123
  apply intro_cons _ _ _ c124
  apply intro_cons _ _ _ c125
  apply intro_cons _ _ _ c126
  apply intro_cons _ _ _ c127
  apply intro_cons _ _ _ c138
  apply intro_cons _ _ _ c140
  apply intro_cons _ _ _ c156
  apply intro_cons _ _ _ c172
  apply intro_cons _ _ _ c188
  apply intro_cons _ _ _ c205
  apply intro_cons _ _ _ c206
  apply intro_cons _ _ _ c207
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand4

namespace LocalLightBand5
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def p104 : HPacket := LocalCompactPackets.decode 2097159 [1536,272,32,128,1026,772,1152,584,546,417,81] 9942153569345576055 [0,1,2,3,4,5,6,2097152,2097154,2097156,2097157,2097158,2097159] 1146924302849 1146924302849 82944457171472321637142299395 [(1698,16060434,1932318311152269303851425343084844840484267346487239568148395413247608960057889)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c104 : atCode 5 104 := LocalLightPackets.run_sound 1028 72 272 p104 (by decide +kernel)

def p109 : HPacket := LocalCompactPackets.decode 69206023 [1536,272,32,128,1282,772,128,584,562,417,17] 16285016251951545591 [0,1,2,3,4,5,6,2097152,2097153,2097158,2097159,67108866,67108869,67108871,69206016,69206017,69206021,69206022] 1146890488841 1151202492929 22827508995658719411662990913361901521273603 [(433,1347424274,1954013813833979888621171165277086427039165025402187514759712464443539460195312)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c109 : atCode 5 109 := LocalLightPackets.run_sound 1028 72 1088 p109 (by decide +kernel)

def p120 : HPacket := LocalCompactPackets.decode 33554439 [1536,272,32,64,1026,772,1160,576,546,417,81] 11234669070281448567 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554437,33554438,33554439] 294716512141825 294716512141825 5456289121816745869543235754722051 [(1634,327698,28041435620619935226699079159601831281024369821210430579157531363901985)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c120 : atCode 5 120 := LocalLightPackets.run_sound 1028 136 272 p120 (by decide +kernel)

def p126 : HPacket := LocalCompactPackets.decode 100663303 [1536,272,32,64,1282,772,1160,64,562,289,81] 18151738643359857911 [0,1,2,3,4,5,6,33554432,33554438,33554439,67108866,67108868,67108869,67108871,100663297,100663301,100663303] 1142730524673 299118836843009 1552935219408670408883083385069259800736398902019 [(369,1347424274,1932500683652667660408202366789338012438965572147441863041299656781591759029232)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c126 : atCode 5 126 := LocalLightPackets.run_sound 1028 136 640 p126 (by decide +kernel)

def p140 : HPacket := LocalCompactPackets.decode 65543 [1536,272,32,192,1026,772,1032,520,546,417,81] 9503052606213299319 [0,1,2,3,4,5,6,65538,65539,65540,65542,65543] 1142595781121 1142595781121 82637385290851383888107078403 [(1578,5574674,6369559736370549684085312193214176412616952730542146081)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c140 : atCode 5 140 := LocalLightPackets.run_sound 1028 272 192 p140 (by decide +kernel)

def codes : List ℕ := [104,109,120,126,140]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 5 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 5 z := by
  unfold codes
  apply intro_cons _ _ _ c104
  apply intro_cons _ _ _ c109
  apply intro_cons _ _ _ c120
  apply intro_cons _ _ _ c126
  apply intro_cons _ _ _ c140
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand5

namespace LocalLightBand6
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def p120 : HPacket := LocalCompactPackets.decode 52953095 [1536,272,1056,0,1026,772,1152,576,546,417,85] 10225862753696325503 [0,1,2,3,4,5,6,524291,524293,2097153,2097157,2621440,2621441,2621444,2621445,2621447,16777219,16777222,17301507,17301511,33554434,33554438,50331648,50331650,50331652,50331654,50331655,52953092] 309048969660672 309040311960065 8065734127359286443910877233737283962439214617426015879957623507419554187493835523 [(1634,277133226230533869586,29126165403399426295158589571444565917941757127948644746001247736955425),(1698,277133226230533869586,1954623874187884567298408155781520362037117113486112056118173597496451464430113)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c120 : atCode 6 120 := LocalLightPackets.run_sound 72 136 272 p120 (by decide +kernel)

def p124 : HPacket := LocalCompactPackets.decode 35684359 [1536,272,1056,0,1282,772,1024,512,562,417,85] 16566473636491821055 [0,1,2,3,4,5,6,32771,32775,2097152,2097157,2097159,2129920,2129925,33554432,33554438,33554439,33587200,33587206,35684352] 4295952903 298010718503425 1801760517829565977546232645908721219034947781420930796498075314712544003 [(1586,428106191073181714,8769232252009547568677005708249607136116844161796115484155643284589015912540280154940462334433),(1798,428106191073181714,8769232252009636497001539967021856293296602753463423202573769483729068721121156518187003805777),(1812,428106191073181714,177861160444812215903433111533990111023464685316382320965029022118589935152915570897673720231693537891593979584994016697004194),(1826,428106191073181714,53755237306919368990901918338081568243379402105275173068623262976762385609082748196008250530717514676952652096369123930634256893206124142474222108753),(1840,428106191073181714,16246523575479052732072971722347409878272058402497578771309012653959172197074178620481914012613051833486784782754261849639075320418908763195883230458061540722629113842508820)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c124 : atCode 6 124 := LocalLightPackets.run_sound 72 136 192 p124 (by decide +kernel)

def p137 : HPacket := LocalCompactPackets.decode 2097159 [1536,272,1056,128,2,772,1152,584,546,417,69] 10158326351456607295 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097158,2097159] 4463002113 4463002113 1260891093406651066417923 [(1698,983058,1910690777728403719317997339436822923198697666226851847370710490253246415241761)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c137 : atCode 6 137 := LocalLightPackets.run_sound 72 272 1040 p137 (by decide +kernel)

def p138 : HPacket := LocalCompactPackets.decode 2752519 [1536,272,1056,128,1026,516,1152,584,514,417,85] 10202940126691037055 [0,1,2,3,4,5,6,131072,131078,131079,524289,524291,2097153,2097155,2621440,2621441,2621443,2621447,2752512,2752515,2752518] 1168433088516 1168365584897 1558934121238838398071218929648779017931811259139 [(1670,331794,29656096864580314635784806976040302291826007023238272123952581785420321),(1698,331794,1990186970075731233918924118039534567502667019867605191328477173613969615618593)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c138 : atCode 6 138 := LocalLightPackets.run_sound 72 272 288 p138 (by decide +kernel)

def p139 : HPacket := LocalCompactPackets.decode 2097159 [1536,272,1056,128,1026,260,1152,584,546,385,85] 10203351798903707519 [0,1,2,3,4,5,6,2097153,2097154,2097155,2097156,2097157,2097159] 1146907525633 1146907525633 82946875041558294969201263363 [(1698,18,6345523877602404636556855006702784597833732697094095393)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c139 : atCode 6 139 := LocalLightPackets.run_sound 72 272 544 p139 (by decide +kernel)

def p140 : HPacket := LocalCompactPackets.decode 65543 [1536,272,1056,128,1026,772,1024,520,546,417,85] 9647167793765261183 [0,1,2,3,4,5,6,65538,65542,65543] 4362207497 4362207497 5375158245443210147179417211044611 [(1578,99946514,6345523879729381797705730406418690759264441004971524641),(1698,99946514,1917816914296511123357873600403859015447234529880290078630325552962638710571553)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c140 : atCode 6 140 := LocalLightPackets.run_sound 72 272 192 p140 (by decide +kernel)

def p141 : HPacket := LocalCompactPackets.decode 2097159 [1536,272,1056,128,1026,772,128,584,546,417,21] 9653923193190653823 [0,1,2,3,4,5,6,2097152,2097154,2097157,2097159] 4446224897 4446224897 1256187101328786116117251 [(1698,18,1910686802322507967953255777017446251632042371300146245052880004566818574303777)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c141 : atCode 6 141 := LocalLightPackets.run_sound 72 272 1088 p141 (by decide +kernel)

def p142 : HPacket := LocalCompactPackets.decode 2097159 [1536,272,1056,128,1026,772,1152,72,546,289,85] 10223608891862654847 [0,1,2,3,4,5,6,2097153,2097154,2097155,2097156,2097158,2097159] 1146907525633 1146907525633 82946875023111550895491711747 [(1698,983058,6345523877602361080413888810745177784802371467265180193)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c142 : atCode 6 142 := LocalLightPackets.run_sound 72 272 640 p142 (by decide +kernel)

def p143 : HPacket := LocalCompactPackets.decode 2752519 [1536,272,1056,128,1026,772,1152,584,34,161,85] 10229955168187686783 [0,1,2,3,4,5,6,131072,131078,131079,524289,524291,524293,2097153,2097155,2097157,2621441,2621443,2621444,2621445,2621447,2752515,2752518] 302438930841608 302438846562817 29074429784350341557498439362724691033677913230545534283261520708355 [(1187,331794,6632866798279900374420984860022486852948627557513174672),(1698,331794,2004660981124161982543108731869015473823739477049638133505708898516994421686817)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c143 : atCode 6 143 := LocalLightPackets.run_sound 72 272 768 p143 (by decide +kernel)

def p189 : HPacket := LocalCompactPackets.decode 69206023 [1536,272,1056,128,1282,260,128,584,562,385,21] 16546214481496700927 [0,1,2,3,4,5,6,2097152,2097157,2097159,67108865,67108868,67108870,67108871,69206018,69206022,69206023] 1142730524674 299118836843009 1552935132297713623990221179750867789749911094019 [(405,21480079378,6465289373857077077822037529438308143452346093336790000)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c189 : atCode 6 189 := LocalLightPackets.run_sound 72 544 1088 p189 (by decide +kernel)

def codes : List ℕ := [120,124,137,138,139,140,141,142,143,189]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 6 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 6 z := by
  unfold codes
  apply intro_cons _ _ _ c120
  apply intro_cons _ _ _ c124
  apply intro_cons _ _ _ c137
  apply intro_cons _ _ _ c138
  apply intro_cons _ _ _ c139
  apply intro_cons _ _ _ c140
  apply intro_cons _ _ _ c141
  apply intro_cons _ _ _ c142
  apply intro_cons _ _ _ c143
  apply intro_cons _ _ _ c189
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand6

namespace LocalLightBand7
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def p137 : HPacket := LocalCompactPackets.decode 50348039 [1536,272,1056,64,2,772,1160,576,546,417,69] 11450841852392479807 [0,1,2,3,4,5,6,16384,16390,16391,16777217,16777221,33554437,33570817,50331650,50331652,50331653,50331655,50348033,50348035,50348037,50348038,50348039] 77421067861884936 302434551595521 104018091964598929100644528660846503027913988197647107 [(1634,983058,28368305232775185754869831159867636008922701448528158407045390741537313)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c137 : atCode 7 137 := LocalLightPackets.run_sound 136 272 1040 p137 (by decide +kernel)

def p138 : HPacket := LocalCompactPackets.decode 33554439 [1536,272,1056,64,1026,516,1160,576,514,417,85] 11495455627626909567 [0,1,2,3,4,5,6,33554432,33554433,33554436,33554438,33554439] 4362207499 4362207499 5415723683629978008361326482883331 [(1606,983058,1867355761482225834489334934317349177888508851425311495448186217665759629804065),(1634,983058,27825769208105606804670702795394573407135074478564346052738034164040225)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c138 : atCode 7 138 := LocalLightPackets.run_sound 136 272 288 p138 (by decide +kernel)

def p139 : HPacket := LocalCompactPackets.decode 33554439 [1536,272,1056,64,1026,260,1160,576,546,385,85] 11495867299839580031 [0,1,2,3,4,5,6,33554432,33554433,33554434,33554435,33554439] 4463002113 4463002113 1260946433638872195072771 [(1634,18,6178561930548910736925956114281882398715019433989112353)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c139 : atCode 7 139 := LocalLightPackets.run_sound 136 272 544 p139 (by decide +kernel)

def p140 : HPacket := LocalCompactPackets.decode 16391 [1536,272,1056,64,1026,772,1032,512,546,417,85] 9791265389655072639 [0,1,2,3,4,5,6,16384,16386,16390,16391] 4362207498 4362207498 5395440964536594077770371846963971 [(1578,268382226,6345523880443005654692533919252737353971071101031154209),(1634,268382226,28577698980216793647154829218119428597356123478506558514701726845501985)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c140 : atCode 7 140 := LocalLightPackets.run_sound 136 272 192 p140 (by decide +kernel)

def p141 : HPacket := LocalCompactPackets.decode 33554439 [1536,272,1056,64,1026,772,136,576,546,417,21] 9649402001443823487 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554439] 4446224897 4446224897 1260946433638872195072771 [(1634,18,6178822080328956277542983661536484830502394019128017441)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c141 : atCode 7 141 := LocalLightPackets.run_sound 136 272 1088 p141 (by decide +kernel)

def p142 : HPacket := LocalCompactPackets.decode 33554439 [1536,272,1056,64,1026,772,1160,64,546,289,85] 11520645584611942271 [0,1,2,3,4,5,6,33554432,33554434,33554437,33554438,33554439] 1142612558337 1142612558337 82634967439212154629757666051 [(1634,983058,27825769208105606733203271664900396293669113086613761190277204125155873)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c142 : atCode 7 142 := LocalLightPackets.run_sound 136 272 640 p142 (by decide +kernel)

def p143 : HPacket := LocalCompactPackets.decode 33554439 [1536,272,1056,64,1026,772,1160,576,34,161,85] 11522470669123559295 [0,1,2,3,4,5,6,33554432,33554433,33554438,33554439] 4446224897 4446224897 1256168654584712406565635 [(1634,983058,27825769208105606733191579651671075324513780870154908605697197781287457)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c143 : atCode 7 143 := LocalLightPackets.run_sound 136 272 768 p143 (by decide +kernel)

def p190 : HPacket := LocalCompactPackets.decode 100663303 [1536,272,1056,64,1282,260,1160,64,562,257,85] 18412938522588084223 [0,1,2,3,4,5,6,33554432,33554437,33554439,67108865,67108870,67108871,100663296,100663298,100663301,100663302] 4463462402 1146890748417 22740057751314608133484620989956837117068035 [(341,21480079378,6394108397051833583274396539346334254129532635608777712)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c190 : atCode 7 190 := LocalLightPackets.run_sound 136 544 640 p190 (by decide +kernel)

def codes : List ℕ := [137,138,139,140,141,142,143,190]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 7 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 7 z := by
  unfold codes
  apply intro_cons _ _ _ c137
  apply intro_cons _ _ _ c138
  apply intro_cons _ _ _ c139
  apply intro_cons _ _ _ c140
  apply intro_cons _ _ _ c141
  apply intro_cons _ _ _ c142
  apply intro_cons _ _ _ c143
  apply intro_cons _ _ _ c190
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand7

namespace LocalLightBand8
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def p156 : HPacket := LocalCompactPackets.decode 16391 [1536,272,1056,192,2,772,1032,520,546,417,69] 9719225388324330559 [0,1,2,3,4,5,6,16384,16387,16388,16389,16391] 1142595781121 1142595781121 82637385309298127961816630019 [(1578,16392210,6345703645144397355751472893258997761926618377021817377)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c156 : atCode 8 156 := LocalLightPackets.run_sound 272 1040 192 p156 (by decide +kernel)

def p172 : HPacket := LocalCompactPackets.decode 42008583 [1536,272,1056,192,1026,516,1032,520,514,417,85] 9763839163558760319 [0,1,2,3,4,5,6,65536,65541,65543,8388608,8388610,8388614,33554435,33554438,33619971,33619975,41943040,41943042,41943046,41943047,42008580,42008583] 305746089281537 78270998805479937 432385943561868601961946923964923683163399953549765832626995971 [(1550,4223567764914194,6323168750708050500651035363023023496310165822223690273),(1578,4223567764914194,6323168755680135305576514194227894690349024077458188833)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c172 : atCode 8 172 := LocalLightPackets.run_sound 272 288 192 p172 (by decide +kernel)

def p188 : HPacket := LocalCompactPackets.decode 65543 [1536,272,1056,192,1026,260,1032,520,546,385,85] 9764250835771430783 [0,1,2,3,4,5,6,65537,65540,65541,65543] 4446224897 4446224897 1256187101328786116117251 [(1578,18,1408989342996699923340918297416647311905)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c188 : atCode 8 188 := LocalLightPackets.run_sound 272 544 192 p188 (by decide +kernel)

def p205 : HPacket := LocalCompactPackets.decode 65543 [1536,272,1056,192,1026,772,8,520,546,417,21] 9647167794285944703 [0,1,2,3,4,5,6,65537,65539,65542,65543] 1138300813825 1138300813825 82327895558591216880722445059 [(1578,327698,6297987077473556849388237353549760937767200040658141729)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c205 : atCode 8 205 := LocalLightPackets.run_sound 272 192 1088 p205 (by decide +kernel)

def p206 : HPacket := LocalCompactPackets.decode 100679687 [1536,272,1056,192,1026,772,1032,8,546,289,85] 9791263328171433855 [1,2,3,4,5,6,16384,16387,16391,33554433,33554437,33554438,33570817,33570822,33570823,67108864,67108868,67108869,100663296,100663301,100663303] 302434635810561 302421649850624 429171969202074046259028638991580630714260724653286947744383490 [(1578,4312994789265426,6299317045412989318260045704924844385690661021711089185)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c206 : atCode 8 206 := LocalLightPackets.run_sound 272 192 640 p206 (by decide +kernel)

def p207 : HPacket := LocalCompactPackets.decode 65543 [1536,272,1056,192,1026,772,1032,520,34,161,85] 9790854205055410047 [0,1,2,3,4,5,6,65538,65539,65541,65543] 1138300813825 1138300813825 82327895577037960954431996675 [(1578,18,6321578636551854205321174822756001336482726921478865441)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma c207 : atCode 8 207 := LocalLightPackets.run_sound 272 192 768 p207 (by decide +kernel)

def codes : List ℕ := [156,172,188,205,206,207]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 8 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 8 z := by
  unfold codes
  apply intro_cons _ _ _ c156
  apply intro_cons _ _ _ c172
  apply intro_cons _ _ _ c188
  apply intro_cons _ _ _ c205
  apply intro_cons _ _ _ c206
  apply intro_cons _ _ _ c207
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand8

namespace LocalLightBand9
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def codes : List ℕ := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 9 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 9 z := by
  unfold codes
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand9

namespace LocalLightBand10
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def codes : List ℕ := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 10 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 10 z := by
  unfold codes
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand10

namespace LocalLightBand11
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def codes : List ℕ := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 11 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 11 z := by
  unfold codes
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand11

namespace LocalLightBand12
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def codes : List ℕ := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 12 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 12 z := by
  unfold codes
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand12

namespace LocalLightBand13
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def codes : List ℕ := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 13 codes=true := by decide +kernel
lemma facts : ∀ z ∈ codes, atCode 13 z := by
  unfold codes
  exact fun _ h => (List.not_mem_nil h).elim

end LocalLightBand13

namespace LocalLightAllBands
open LocalMixerCertificate

lemma exhaustive (a b c : ℕ) (ab : a<b) (bc : b<c) (hc : c<16) :
    LocalPacket.absent (rows.getD a 0) (rows.getD b 0) (rows.getD c 0) := by
  have small : a≤13 := by omega
  interval_cases a
  · exact LocalLightPackets.band 0 b c ab bc hc _ LocalLightBand0.domain LocalLightBand0.facts
  · exact LocalLightPackets.band 1 b c ab bc hc _ LocalLightBand1.domain LocalLightBand1.facts
  · exact LocalLightPackets.band 2 b c ab bc hc _ LocalLightBand2.domain LocalLightBand2.facts
  · exact LocalLightPackets.band 3 b c ab bc hc _ LocalLightBand3.domain LocalLightBand3.facts
  · exact LocalLightPackets.band 4 b c ab bc hc _ LocalLightBand4.domain LocalLightBand4.facts
  · exact LocalLightPackets.band 5 b c ab bc hc _ LocalLightBand5.domain LocalLightBand5.facts
  · exact LocalLightPackets.band 6 b c ab bc hc _ LocalLightBand6.domain LocalLightBand6.facts
  · exact LocalLightPackets.band 7 b c ab bc hc _ LocalLightBand7.domain LocalLightBand7.facts
  · exact LocalLightPackets.band 8 b c ab bc hc _ LocalLightBand8.domain LocalLightBand8.facts
  · exact LocalLightPackets.band 9 b c ab bc hc _ LocalLightBand9.domain LocalLightBand9.facts
  · exact LocalLightPackets.band 10 b c ab bc hc _ LocalLightBand10.domain LocalLightBand10.facts
  · exact LocalLightPackets.band 11 b c ab bc hc _ LocalLightBand11.domain LocalLightBand11.facts
  · exact LocalLightPackets.band 12 b c ab bc hc _ LocalLightBand12.domain LocalLightBand12.facts
  · exact LocalLightPackets.band 13 b c ab bc hc _ LocalLightBand13.domain LocalLightBand13.facts

end LocalLightAllBands

namespace LocalLightFullDeck

lemma checked : LocalPhysicalDeck.coveredTests := fun i j k ij jk =>
  LocalLightAllBands.exhaustive i.val j.val k.val ij jk k.isLt

end LocalLightFullDeck



end PEqualNP.Outside.L_meta_5228_aux

open PEqualNP.Outside.L_meta_5228_aux

theorem PEqualNP.Outside.L_meta_5228 : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x4 < x5 →           PEqualNP.TopForm.junk x1 x3 = {x4, x5} →             PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →               have x12 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;               have x13 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;               have x14 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;               have x15 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;               (∀ x16 ∈ x15,                   have x18 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x16;                   (∀ x19 ∈ x18 (0 : Fin (2 : ℕ)), ∀ x21 ∈ x18 (1 : Fin (2 : ℕ)), x1.Adj x19 x21) ∧ ((x18 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x18 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →                 (∀ (x17 x18 : Fin (11 : ℕ)), s(x17, x18) ∈ x12 → ∃ x20 ∈ x15, ∃ (x21 : Fin (2 : ℕ)), ∃ x22 ∈ PEqualNP.TopForm.junk x1 x3, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x20 (PEqualNP.EdgeOwnership.pairInput x17 x18) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x20 x21) x22 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x22 (PEqualNP.EdgeOwnership.pairInput x17 x18) = Bool.true) → x3.size ≤ (21 : ℕ) → x12.card = (3 : ℕ) → ∀ (x20 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x12) x20 → (4 : ℕ) ≤ x20.card → x20.card ≤ (x15 \ x13).card → (0 : ℕ) < (2 : ℕ) * x13.card + x14.card → (x15 \ x13).card + (2 : ℕ) * x13.card + x14.card ≤ x3.size + x12.card - (17 : ℕ) → False := by
  exact LocalFromDeck.finish LocalLightFullDeck.checked

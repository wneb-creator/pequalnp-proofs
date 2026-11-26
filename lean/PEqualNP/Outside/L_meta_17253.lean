import Mathlib.Combinatorics.Enumerative.DoubleCounting
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17253_aux

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

namespace MixerProof

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

namespace LocalLightPackets

open LocalHints LocalMixerCertificate

def entryPass (a : ℕ) (entry : ℕ × HPacket) : Bool :=
  let z := entry.1
  run (rows.getD a 0) (rows.getD (z/16) 0) (rows.getD (z % 16) 0) entry.2

lemma entries_sound (a : ℕ) (entries : List (ℕ × HPacket))
    (h : entries.all (entryPass a) = true) : ∀ z ∈ entries.map Prod.fst, atCode a z := by
  intro z hz
  obtain ⟨⟨code,p⟩, hm, rfl⟩ := List.mem_map.mp hz
  exact run_sound _ _ _ p (List.all_eq_true.mp h _ hm)

def limbs (ws : List ℕ) : ℕ :=
  ws.foldl (fun acc next => (acc <<< 64) + next) 0

end LocalLightPackets

namespace LocalLightBand0
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def entries : List (ℕ × HPacket) := [
  (18, LocalCompactPackets.decode 3162119 [0,256,1056,192,1280,772,1160,584,562,416,84] 4539626957345322423 [0,1,2,3,4,5,6,16384,16386,16387,16391,1048580,1048581,2097157,2113540,3145728,3145729,3145733,3145735,3162112,3162116,3162117] 1159927105794 1172677329409 (limbs [4598137617,0xd090c0912020a04,0xa0a060605050303]) [(1448,45802790930,(limbs [4741801841920,0xca05402e81007d1c,0x401f371007d94401,0xeb5130074c3c00f3])),(1504,45802790930,(limbs [77689681373857953,0x500ca05402e81007,0xd1c401ec7080ff18,0x83f96070f698003,0xc461007d94401eb5]))]),
  (21, LocalCompactPackets.decode 67149831 [0,272,32,192,1282,772,1160,584,562,416,80] 8935140215129437367 [0,1,2,3,4,5,6,8192,32768,32771,32772,32773,40963,40967,67108865,67108870,67108871,67117057,67117062,67141633,67141637,67141638,67141639,67149830] 303525540790287 303517000794625 (limbs [1,0x9140b0c0d0d060c,0xd041602030f1001,0x1010060605050303]) [(496,181419429396498,(limbs [76852332389871745,0x108ba04422a81307,0xd1c4c1ec71700f18,0x5403961407d94501,0xeb51700f90480384]))]),
  (22, LocalCompactPackets.decode 2686983 [0,272,1056,128,1282,772,1152,584,562,416,84] 7926333897998792119 [0,1,2,3,4,5,6,65536,65538,65539,65543,524292,524293,2097157,2162692,2621440,2621441,2621445,2621447,2686976,2686977,2686980,2686981] 1159927105794 1172677329409 (limbs [4598137617,0xd090c0912020a04,0xa0a060605050303]) [(1442,45802790930,(limbs [17,0x5025a8401f281007,0xc60401ee81007b60,0x5803471400d94500,0x2b513008843c0051])),(1456,45802790930,(limbs [283657,0x6a1502468401f281,0x7c20401ee81007,0xaa05803471400d94,0x5002b5080ff90083,0xf84070f810003c14]))]),
  (23, LocalCompactPackets.decode 37879815 [0,272,1056,64,1282,772,1160,576,562,416,84] 9218849398934664631 [0,1,2,3,4,5,6,131072,131075,131079,4194304,4194305,4194308,4194310,33554438,33685504,33685508,37748738,37748742,37748743,37879810,37879812,37879814] 1168533882881 1176955519489 (limbs [4614980370,0xe080d0813010904,0x909060605050303]) [(852,114527510546,(limbs [17,0x5019e45405b90b0f,0xca02c3f080a0f3a0,0x283cc81600f18500,0x3e41100e10441fa2]))]),
  (27, LocalCompactPackets.decode 67149831 [0,272,1056,192,1282,260,1160,584,562,384,84] 9196339613178459575 [0,1,2,3,4,5,6,8192,8195,8196,8198,32768,40963,40967,67108866,67108869,67108871,67117058,67117061,67117062,67117063,67141634,67141637,67149826] 302426029096975 302417489166849 (limbs [1,0x8130a0c0d0d050c,0xd041401030f1002,0x1010060605050303]) [(468,175943429652498,(limbs [4708075311627,0xc20581f471607b1c,0x5c03c61500e585c0,0x3e41100e104c2fa2]))]),
  (35, LocalCompactPackets.decode 11550727 [1024,0,1056,192,1280,772,1160,584,560,416,85] 4538144815681873791 [0,1,2,3,4,5,6,16385,16387,1048581,1048582,2097155,2097157,2113539,2113543,3145728,3145729,3145733,3145735,3162115,8388608,8404992,9437190,9437191,11550720,11550723] 1194286974724 305737465332225 (limbs [1,0xb16091608160b11,0xa110c0d17171212,0xe0e060d0e041202,0x1701060605050303]) [(1448,67553994410577938,(limbs [4725830981892,0xc604c12d81015d1c,0x4057371115d94405,0x6b5180074c3c00f3])),(1504,67553994410577938,(limbs [77428014782417313,0x904c604c12d81015,0xd1c4056c7150ff18,0x503f96150f698003,0xc461115d944056b5]))]),
  (36, LocalCompactPackets.decode 2113543 [1024,256,1024,192,1280,768,1160,584,562,416,85] 4233373378011985919 [0,1,2,3,4,5,6,16384,16385,16388,16390,16391,2097152,2097153,2097155,2097156,2097159,2113536,2113539,2113542,2113543] 298002347330050 303525506843137 (limbs [4630644238,0x30a10040b011010,0xb0b060605050303]) [(1448,2689601554,(limbs [4741668672512,0xca04802e80d07d1c,0x341f370d09d54342,0x695110074c3000f3])),(1504,2689601554,(limbs [77687499530439073,0x400ca04802e80d07,0xd1c341ec7070cf18,0x3396070c698003,0x460d09d54342695])),(1864,2689601554,(limbs [77687499530439072,0x90d9e42435b91400,0xca04c00e8070cf18,0x1c33b6070c6981c3,0x186110074c1c0183])),(1928,2689601554,(limbs [282625,0x7a090d9e42436390,0x90d6e42434a91400,0xca04c00e80d07d1c,0x341f370c074dc301,0xcf7110074c3000f3])),(1984,2689601554,(limbs [4630535813,0x9a090d9e42436,0x39090d6e42434a91,0x400ca04c00e80d07,0xd1c341ec70c074dc,7959394955395075,0x396070c698003046]))]),
  (37, LocalCompactPackets.decode 2097159 [1024,256,32,192,1280,772,1160,584,562,416,81] 4251396581191447799 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097157,2097159] 1142612558337 1142612558337 (limbs [4479781634,0xb0b060605050303]) [(1448,18,(limbs [4552956446976,0xca02402e80800d1c,0x2003370a00d94280,0x2b5070074c1c00f3])),(1504,18,(limbs [74595638427322016,0x900ca02402e80800,0xd1c2002c70407f18,0x101f960007698001,0xc460a00d942802b5]))]),
  (38, LocalCompactPackets.decode 2097159 [1024,256,1056,128,1280,772,1152,584,562,416,85] 3242590264069453823 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097157,2097158,2097159] 4362207502 4362207502 (limbs [296885554384385,0xe0e060605050303]) [(1440,268382226,(limbs [75998649640818336,0xe0056834014a0c00,0x4a82c011a0c00428,0x2c00fa0a00268240,0x8a0a001a824005a,0x8000e81c002a010,0x282803280a00c6,0x2803080800be028,0x2e80a00b602802a,0x80800a602400e809,0x3600800c800002,0xa024007809001600,0x800180c00d1c3003,0x370c00b1c2002970,0xb004dc2c00f70400,0x11c2003650800d54,0x2002b50800a541c0,0x21500007941c0025])),(1441,94703634,(limbs [69120,0x5e834016a0a00ca0,0x2802e80c00d1c200,0x3650800ad4000770])),(1442,655378,(limbs [4638589454848,0xca02803180a00ba0,0x2802d80c00d1c200,0x3650800ad40009e1])),(1444,327698,(limbs [75998649645012384,0xa00ca02802e80c00,0xd1c2003650800d54,0x2002b50800a54001,0xfa20007dc8001ca2])),(1448,327698,(limbs [69120,0x5e82803280a00ba0,0x3003470c00cdc200,0x3650800ad4001183])),(1456,327698,(limbs [75998649636623008,0xa00ca02803080a00,0xba02802a80c00d1c,0x2003650800ad4002,0x7d40009dd00025e4])),(1504,327698,(limbs [1132468128,0xa002682803280a00,0xba03003470c00b1c,0x2fb6000bdd8002,0xd860800d942002b5])),(1924,327698,(limbs [75998649645012384,0x89e40022390008,0x6e40020a90a00ca0,0x2400e80c00d1c2c0,0x1370007e88001ca2])),(1952,327698,(limbs [1105925,0xe800227900089640,0x223900087a40021,0xb900086240020a90,0xa00ca02802e80900,0x3a02400780c00d1c,0x2c01370800d94200,0x2b507008541c0025]))]),
  (39, LocalCompactPackets.decode 2097159 [1024,256,1056,64,1280,772,1160,576,562,416,85] 4535105765005326335 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097159] 4463002113 4463002113 (limbs [68356,0xb0b060605050303]) [(1448,18,(limbs [0x428017a0a00ca0,0x2802e80804cdc200,0x3650800ad41c10f3])),(1504,18,(limbs [74872749721389472,0xa00ca02802e80804,0xcdc2012970407f18,0x101f960407698101,0xc460800d942002b5])),(1860,18,(limbs [74872749721392544,0xa0026828006a0408,0x9e41021b90a00ca0,0x2400e80407f18101,0xda60007e88001ca2])),(1888,18,(limbs [4462763650,0x8009a04089e41022,0x5904086e41021890,0xa00ca02802e80900,0x3a02400780407f18,0x101da60800d94200,0x2b507008541c0025]))]),
  (40, LocalCompactPackets.decode 2097159 [1024,256,1056,192,1024,772,1160,584,546,416,85] 2231989545165887359 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097157,2097159] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1448,327698,(limbs [4587049847044,0xc202412a80800d1c,0x2003370a00d94200,0x2b5070074c1c00f3])),(1504,327698,(limbs [75154224702294432,0x904c202412a80800,0xd1c2002c70007f18,8890651146551297,0xc460a00d942002b5]))]),
  (41, LocalCompactPackets.decode 2097159 [1024,256,1056,192,256,772,1160,584,562,416,69] 2233783948126713023 [0,1,2,3,4,5,6,2097152,2097153,2097159] 4362207497 4362207497 (limbs [291387912358145,0x909060605050303]) [(1448,327698,(limbs [4535773432064,0xca02402e80800d1c,0x2003370800d94200,0x2b5070074c1c00f3])),(1504,327698,(limbs [74314111906808736,0x900ca02402e80800,0xd1c2002c70407f18,0x101f960007698001,0xc460800d942002b5]))]),
  (42, LocalCompactPackets.decode 2097159 [1024,256,1056,192,1280,516,1160,584,530,416,85] 4510494288676620287 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097159] 4446224897 4446224897 (limbs [68100,0xa0a060605050303]) [(1448,18,(limbs [0x424017a0904ba0,0x2003470800cdc201,0x2b5070074c1c00f3])),(1504,18,(limbs [16,0x9005e824009a0904,0xba02003470800b1c,8943427712811009,0xda600071182012b5]))]),
  (43, LocalCompactPackets.decode 2121735 [1024,256,1056,192,1280,260,1160,584,562,384,85] 4512595979249121279 [0,1,2,3,4,5,6,8194,8198,8199,16390,16391,24576,24577,24580,24582,2097152,2097157,2097159,2105351,2113543,2121728,2121731,2121735] 75733291475669777 292504519966994 (limbs [4446618890,0xb08050812010b01,0x901121206120b0b,0x909060605050303]) [(1420,69231116057382930,(limbs [4776028411392,0x5685c0328110cd1c,0x443337150074c400,0xf30e10e883840a2])),(1448,69231116057382930,(limbs [4776028411648,0xca05c02e8110cd1c,0x443337100e854403,0x825150074c4000f3])),(1476,69231116057382930,(limbs [284673,0x7a160056858009a1,0x6001a85c0328110c,0xd1c4432c70c10f18,0x43960c10698004,0x460e10e883840a2])),(1504,69231116057382930,(limbs [78250449492248993,0x700ca05c02e8110c,0xd1c4432c70c10f18,0x43960c10698004,0x46100e854403825]))]),
  (44, LocalCompactPackets.decode 2097159 [1024,256,1056,192,1280,772,1032,520,562,416,85] 2803489300937177087 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097159] 4362207500 4362207500 (limbs [294686497573889,0xc0c060605050303]) [(1448,327698,(limbs [4604229716480,0xca02802e80804b1c,0x2012970800d94200,0x2b50b0074c2c00f3])),(1504,327698,(limbs [4604229716480,0x2682803280a00ba0,0x2012c7000be58002,0xc460800d942002b5])),(1804,327698,(limbs [4604229716992,0x56810227904086e4,0x28032809003a02c0,0x1d30007e88001ca2])),(1832,327698,(limbs [18416918859810,0x7904089641021b90,0x4086242803280a00,0xba02400e809001e0,0x2003650800ad41c0,0x21507000942c01d3]))]),
  (45, LocalCompactPackets.decode 2097159 [1024,256,1056,192,1280,772,136,584,562,416,21] 2666129512353822719 [0,1,2,3,4,5,6,2097153,2097155,2097156,2097157,2097159] 1142595781121 1142595781121 (limbs [4479781634,0xb0b060605050303]) [(1448,18,(limbs [4535763994624,0xca02002e80a00d1c,0x2803370700d941c0,0x2b5090074c2400f3])),(1504,18,(limbs [4535763994624,0xca02002e80a00d1c,0x1c02c70009698002,0x4460700d941c02b5]))]),
  (46, LocalCompactPackets.decode 2097159 [1024,256,1056,192,1280,772,1160,72,562,288,85] 4532853278400051199 [0,1,2,3,4,5,6,2097152,2097155,2097156,2097157,2097159] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1384,327698,(limbs [74309799759579552,0xb00ca02c02e80407,0xf18101fb60407698,0x101d860a00d94280,0x2b5090074c100183])),(1448,327698,(limbs [4535510240000,0xca02c02e807044dc,0x1c10f70a00d94280,0x2b5090074c1c00f3])),(1504,327698,(limbs [74309799759579552,0xb00ca02c02e80704,0x4dc0010470407f18,8890668326420481,0xc460a00d942802b5]))]),
  (47, LocalCompactPackets.decode 2097159 [1024,256,1056,192,1280,772,1160,584,50,160,85] 4537405222313523199 [0,1,2,3,4,5,6,2097152,2097154,2097155,2097157,2097159] 1142612558337 1142612558337 (limbs [4479781634,0xb0b060605050303]) [(1448,18,(limbs [4552690108420,0x3a02010780a00d1c,0x2803370a00d94280,0x2b5070074c1c00f3])),(1504,18,(limbs [74591274740484512,0x8043a02010780a00,0xd1c2802c70007f18,8890651146551297,0xc460a00d942802b5]))]),
  (54, LocalCompactPackets.decode 2097159 [1024,16,1056,128,1282,772,1152,584,560,416,85] 7924851739155474303 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097157,2097159] 1151219270145 1151219270145 (limbs [4513336578,0xd0d060605050303]) [(1442,18,(limbs [0x430017a0802c60,0x200ad80c00d1c280,0x3650800ad41c0851])),(1456,18,(limbs [274433,0x7a0c004a8200b180,0x802be0200ad80802,0xa603003470a00d94,0x2002b50207f90081,0xf840207810081c14])),(1712,18,(limbs [75435699683201696,0x2089e40822590208,0x8e40821e90c00d1c,0x2c01370a00d94240,0x2150207f90081e04]))]),
  (55, LocalCompactPackets.decode 33554439 [1024,16,1056,64,1282,772,1160,576,560,416,85] 9217367240091346815 [0,1,2,3,4,5,6,33554432,33554434,33554435,33554436,33554438,33554439] 1146907525633 1146907525633 (limbs [4496559105,0xc0c060605050303]) [(1648,5574674,(limbs [72347171474756256,0x107268041c3a0b01,0x9e42c06590a00f18,0x2801a60900d94200,0x2150800f90200204]))]),
  (60, LocalCompactPackets.decode 35651591 [1024,16,1056,192,1282,772,1032,520,560,416,85] 7485750776023197567 [0,1,2,3,4,5,6,2097152,2097153,2097157,2097159,33554432,33554434,33554438,33554439,35651586,35651587,35651588,35651591] 1168449798657 299123148587521 (limbs [4597220621,0x6090a020e010e0e,0xa0a060605050303]) [(1592,21480144914,(limbs [4553428306187,0x4a83422790d08964,0x4003650f00854301,0xfe40c078104401d3]))]),
  (63, LocalCompactPackets.decode 35651591 [1024,16,1056,192,1282,772,1160,584,48,160,85] 9221148839073785727 [0,1,2,3,4,5,6,2097152,2097153,2097157,2097159,33554432,33554438,33554439,35651584,35651591] 1164138054145 298019341992449 (limbs [4546888972,0x6090a020d010d0d,0xa0a060605050303]) [(1208,21480144914,(limbs [4536248436747,0x4a8242f47090bcdc,0x3c03650c07f90301,0xe040e0074c1c00f3])),(1264,21480144914,(limbs [270381,0x7a080b4a8202c9a0,0x80b0e8242f47090b,0xb1c2c1fc60b07e58,0x2c1da600071183c0,0x3650c07f90301e04]))]),
  (70, LocalCompactPackets.decode 2097159 [1024,272,1024,128,1282,768,1152,584,562,416,85] 7620080318665455615 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097157,2097159] 4362207501 4362207501 (limbs [295786025979137,0xd0d060605050303]) [(1442,655378,(limbs [16,0xd005e82803280a00,0xc602002e80800b60,0x3003470802d54200,0xa9507008841c0051])),(1456,655378,(limbs [275457,0x7a0d004a82803280,0xa00c202002e80800,0xaa03003470802d54,0x200a950007f90001,0xf840007810001c14])),(1922,655378,(limbs [275457,0x7a02089e40822390,0x2086e40820a90a00,0xca028031809003a0,0x2400d80c00d1c2c0,0x13707008841c0051])),(1936,655378,(limbs [4513095299,0x4012a02089e40822,0x3902086e40820a90,0xa00ca02803080900,0x3a00800c80c00d1c,0x2c01370007f90001,0xf840007810001c14]))]),
  (71, LocalCompactPackets.decode 35651591 [1024,272,1024,64,1282,768,1160,576,562,416,85] 8912595819601328127 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097159,33554432,33554436,33554438,33554439,35651584] 1159809204737 1159809204737 (limbs [66318,0x60a0b040f010f0f,0xb0b060605050303]) [(1858,42960289810,(limbs [74885943861119392,0xe089e43821b90a0c,0xca0283318090c3a0,0x2430d80d07f18341,0xda610008841c0051])),(1872,42960289810,(limbs [4463550082,0x8312a0a0c2682830,0x3a0e089e43821b90,0xa0cca0283308090c,0x3a00830c80d07f18,0x341da60c07f90301,0xf840c07810001c14]))]),
  (75, LocalCompactPackets.decode 2113543 [1024,272,1024,192,1282,256,1160,584,562,384,85] 8908109228447627263 [0,1,2,3,4,5,6,16384,16385,16390,16391,2097152,2097154,2097157,2097159,2113536,2113539,2113543] 294703477099785 300222660215297 (limbs [4580443661,0x5090e020a010e0e,0xa0a060605050303]) [(1418,1347424274,(limbs [4672949195008,0xca04403180d07d1c,0x341f370f0074c2c0,0xf30f008843c0051])),(1432,1347424274,(limbs [76561599606821537,0x100ca04403080d07,0xd1c341f37000ff90,0x3f84000f810003,0xc140f0074c2c00f3])),(1474,1347424274,(limbs [76561599606819233,0x100ca04403180d07,0xd1c341ec7070bf18,0x2f96070b698002,0xc460f008843c0051])),(1488,1347424274,(limbs [4563426948,5243570993250304,0x3a1100ca04403080,0xd07d1c341ec7070b,0xf18002f96070b698,0x2c46000ff90003,0xf84000f810003c14]))]),
  (76, LocalCompactPackets.decode 2228231 [1024,272,1024,192,1282,768,1032,520,562,416,85] 7180979355533178879 [0,1,2,3,4,5,6,131072,131073,131078,131079,2097152,2097153,2097154,2097155,2097156,2097159,2228224,2228228,2228231] 298002330552578 302425978438145 (limbs [4613867022,0x30910040a011010,0xa0a060605050303]) [(1802,2694848530,(limbs [17,0x3005e8243279090c,0x6e4381f280e07c60,0x341ce80d07360480,0x1d311008842c0051])),(1816,2694848530,(limbs [281601,0x7a13004a82432790,0x90c6e4381f280e07,0xc20341ce80207320,0x1c2fe4000be101c2,0xe04000b0504801d3]))]),
  (86, LocalCompactPackets.decode 2097159 [1024,272,32,128,1282,772,1152,584,562,416,81] 7638103521844917495 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097157,2097159] 1142612558337 1142612558337 (limbs [4479781634,0xb0b060605050303]) [(1442,18,(limbs [16,0xa025682003280800,0xc602002e80800b60,0x2803470900d94240,0x2b507008841c0051])),(1456,18,(limbs [272393,0x5a0a024282003280,0x800c202002e80800,0xaa02803470900d94,0x2402b50207f90081,0xf840007810001c14]))]),
  (103, LocalCompactPackets.decode 19464199 [1024,272,1056,0,1282,772,1152,576,562,416,85] 7921812706195666943 [0,1,2,3,4,5,6,65537,65539,2097155,2162691,2162695,2621440,2621441,2686977,2686979,16777216,16842752,17301510,17301511,19464192,19464193] 1155648849668 1176989073921 (limbs [4447143954,0x13130b0b060a0b04,0x1301060605050303]) [(1442,64424529938,(limbs [16,0xf105e83447280d11,0xc603446e80d11b60,0x3c13371500d94380,0x2b51400884300051])),(1456,64424529938,(limbs [277569,0x7a0f104a83447280,0xd11c203446e80d11,0xaa03c13371500d94,0x3802b5110cf90403,0x384110c810003014]))]),
  (104, LocalCompactPackets.decode 2097159 [1024,272,1056,128,1026,772,1152,584,546,416,85] 1007010463097001855 [0,1,2,3,4,5,6,2097153,2097154,2097155,2097156,2097157,2097159] 4362207500 4362207500 (limbs [294686497573889,0xc0c060605050303]) [(1442,327698,(limbs [16,0xc005e81c13080704,0xbe01c12a80704a60,0x2403470b00d941c0,0x2b50a00884280051])),(1456,327698,(limbs [4604229716224,0x4a81c13080704aa0,0x2403470b00d941c0,0x2b5000ae10002814])),(1698,327698,(limbs [16,0xc005e8101e790407,0x964101e3904077a4,0x24034708004dc2c0,0x3650a00854280221]))]),
  (105, LocalCompactPackets.decode 2097159 [1024,272,1056,128,258,772,1152,584,562,416,69] 936747276314866879 [0,1,2,3,4,5,6,2097153,2097155,2097156,2097157,2097159] 1142595781121 1142595781121 (limbs [4479781634,0xb0b060605050303]) [(1442,18,(limbs [16,0x8044a82803280a00,0xc602802e80a00b60,0x2003470700d941c0,0x2b50900884240051])),(1456,18,(limbs [16,0x8044a82803280700,0xc202802e80700aa0,0x2003470700d941c0,0x2b50009810002414]))]),
  (106, LocalCompactPackets.decode 2097159 [1024,272,1056,128,1282,516,1152,584,530,416,85] 7897201229330089983 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097156,2097159] 4446224897 4446224897 (limbs [68356,0xb0b060605050303]) [(1442,18,(limbs [0x424017a0804ba0,0x2012d80900d1c201,0x2b50a008841c0051])),(1456,18,(limbs [16,0x9005e824012a0804,0xba02012a80900d1c,0x2012b50407f90001,0xf840407810001c14]))]),
  (107, LocalCompactPackets.decode 2097159 [1024,272,1056,128,1282,260,1152,584,562,384,85] 7899302919902590975 [0,1,2,3,4,5,6,2097152,2097155,2097157,2097159] 4362207498 4362207498 (limbs [292487440763393,0xa0a060605050303]) [(1414,327698,(limbs [4535510239232,0x5682403280900c60,0x2803470407e88101,0xca207008841c0051])),(1428,327698,(limbs [270337,0x7a080056820012a0,0x8004282403280900,0xc202803470007f90,8870859938791425,0xc140407e88101ca2])),(1442,327698,(limbs [16,0x8005e82403280900,0xc602402e80900b60,0x28034707048541c1,0x2507008841c0051])),(1456,327698,(limbs [270337,0x7a08004a82403280,0x900c202402e80900,0xaa02803470704854,0x1c10250007f90001,0xf840007810001c14]))]),
  (108, LocalCompactPackets.decode 2097159 [1024,272,1056,128,1282,772,1024,520,562,416,85] 7343117746264602623 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097159] 4362207498 4362207498 (limbs [292487440763393,0xa0a060605050303]) [(1442,327698,(limbs [16,0xa005e82003280800,0xc602002e80800b60,0x2412c70800d94200,0x2b507008841c0051])),(1456,327698,(limbs [272385,0x7a0a004a82003280,0x800c202002e80800,0xaa02412c70800d94,0x2002b50007f90001,0xf840007810001c14]))]),
  (109, LocalCompactPackets.decode 2097159 [1024,272,1056,128,1282,772,128,584,562,416,21] 7349873145689995263 [0,1,2,3,4,5,6,2097152,2097153,2097159] 4362207497 4362207497 (limbs [291387912358145,0x909060605050303]) [(1442,327698,(limbs [16,0x8042682003280800,0xc602002e80800b60,0x2403470800d94200,0x2b507008841c0051])),(1456,327698,(limbs [270352,0x9a08040e82003280,0x800c202002e80800,0xaa02403470800d94,0x2002b50407f90101,0xf840007810001c14]))]),
  (110, LocalCompactPackets.decode 2097159 [1024,272,1056,128,1282,772,1152,72,562,288,85] 7919560219053520895 [0,1,2,3,4,5,6,2097152,2097154,2097155,2097157,2097159] 1142612558337 1142612558337 (limbs [4479781634,0xb0b060605050303]) [(1442,18,(limbs [16,0x9005e82803280a00,0xc602802e80a00b60,0x2011370a00d94280,0x2b507008841c0051])),(1456,18,(limbs [271361,0x7a09004a82803280,0xa00c202802e80a00,0xaa02011370a00d94,0x2802b50007f90001,0xf840007810001c14]))]),
  (111, LocalCompactPackets.decode 2097159 [1024,272,1056,128,1282,772,1152,584,50,160,85] 7924112162966992895 [0,1,2,3,4,5,6,2097152,2097155,2097156,2097157,2097159] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1202,327698,(limbs [16,0x8005e820012a0b00,0xd1c2803650407f90,0x101fd40407810101,0xde409008841001e1])),(1442,327698,(limbs [16,0x8005e81c10e80704,0x3601c10780704160,0x2c03470a00d94280,0x2b509008841c0051])),(1456,327698,(limbs [270337,0x7a08004a81c10e80,0x43201c10780004,0x602c03470a00d94,0x2802b50407f90001,0xf840407810001c14]))]),
  (120, LocalCompactPackets.decode 35651591 [1024,272,1056,64,1026,772,1160,576,546,416,85] 2299525964032874367 [0,1,2,3,4,5,6,2097152,2097153,2097157,2097159,33554432,33554434,33554438,33554439,35651588,35651589] 4513661441 1155497460225 (limbs [66829,0x6090a020e010e0e,0xa0a060605050303]) [(1634,21480144914,(limbs [4553428306187,0x2683422790d08964,0x301fc60c07698400,0x3650f008543c0221]))]),
  (126, LocalCompactPackets.decode 35651591 [1024,272,1056,64,1282,772,1160,64,562,288,85] 9216596911802808319 [0,1,2,3,4,5,6,2097152,2097153,2097157,2097159,33554432,33554438,33554439,35651584,35651589] 4496884225 1151202492929 (limbs [66828,0x6090a020d010d0d,0xa0a060605050303]) [(1378,21480144914,(limbs [74321894387665312,0x90bca0242f18090b,0xba0242ed80c07f18,0x301da60f00d94240,0x2b50e008841c0051])),(1392,21480144914,(limbs [4429930114,0x2d2a080b268202c,0x3a090bca0242f080,0x90bba0242ea80c07,0xf18301da60f00d94,0x2402b50b07f902c1,0xf840b07810001c14]))]),
  (140, LocalCompactPackets.decode 65543 [1024,272,1056,192,1026,772,1032,520,546,416,85] 567909499964725119 [0,1,2,3,4,5,6,65538,65539,65540,65542,65543] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1578,94703634,(limbs [0x42c017a0a019e4,0x2806590800d941c0,0x215090074c1c0221]))]),
  (143, LocalCompactPackets.decode 2228231 [1024,272,1056,192,1026,772,1160,584,34,160,85] 2303619824317601663 [0,1,2,3,4,5,6,131072,131073,131078,131079,2097152,2097154,2097157,2097159,2228224,2228227,2228230,2228231] 294703477165321 301322171843073 (limbs [4597220877,0x5090e020a010e0e,0xa0a060605050303]) [(1194,1347424274,(limbs [0x440017a0d07d1c,0x341f371200d943c0,0x1d30b003cc440221])),(1250,1347424274,(limbs [17,0x5e840009a0d07,0xd1c341ec7070bf18,0x2f96070b698002,0xc461200d94440221]))]),
  (206, LocalCompactPackets.decode 2228231 [1024,272,1056,192,1282,772,1032,8,562,288,85] 7487214655362299903 [0,1,2,3,4,5,6,131072,131073,131078,131079,2097152,2097154,2097157,2097159,2228224,2228227,2228229,2228230,2228231] 299118836583689 299123148587521 (limbs [4613998093,0x5090e020a010e0e,0xa0a060605050303]) [(1322,1347424274,(limbs [17,0x5e8341f280d07,0xc60341ee80d07b60,0x4403651100ad4480,0x1d30f008842c0051])),(1336,1347424274,(limbs [278529,0x7a10004a8341f280,0xd07c20341ee80d07,0xaa04403651100ad4,0x1c2fe4000be101c2,0xe04000b0504801d3]))])]

def codes := entries.map Prod.fst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 0 codes = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma facts : ∀ z ∈ codes, atCode 0 z :=
  entries_sound 0 entries (by decide +kernel)

end LocalLightBand0

namespace LocalLightBand1
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def entries : List (ℕ × HPacket) := [
  (36, LocalCompactPackets.decode 16391 [512,256,1024,192,1280,768,1160,584,562,417,84] 4233374823559658935 [0,1,2,3,4,5,6,16384,16385,16389,16390,16391] 1142612558337 1142612558337 (limbs [4479650561,0xb0b060605050303]) [(1864,10817554,(limbs [74873832053164192,0x900a242401c90a00,0xca02800e80800f18,0x2003b607006981c0,0x186070074c1c0183])),(1928,10817554,(limbs [272389,0x6a0900a242402490,0x9007242400b90a00,0xca02800e80007d1c,8786197540093953,0xcf7070074c0000f3])),(1984,10817554,(limbs [4462828162,0x8048a0900a242402,0x4909007242400b90,0xa00ca02800e80007,0xd1c001ec700074dc,7959399049035840,0x3960700698000046]))]),
  (38, LocalCompactPackets.decode 2097159 [512,256,1056,128,1280,772,1152,584,562,417,84] 3242591709617126839 [0,1,2,3,4,5,6,2097152,2097154,2097156,2097158,2097159] 4463002113 4463002113 (limbs [68353,0xb0b060605050303]) [(1441,331794,(limbs [0x428056a0800ca0,0x2002e80900d1c1c0,0x3650700ad41c0690])),(1924,331794,(limbs [74873832053167264,0x107a24041e490107,0x724041cb90800ca0,0x2000e80900d1c240,0x1370107e88001ca2])),(1952,331794,(limbs [73118976577658,0x24041e6901079240,0x41df90107724041d,0x9901072e4041c090,0x800ca02002e80800,0x3a02000780900d1c,0x2401370700d941c0,0x2b507008541c0025]))]),
  (39, LocalCompactPackets.decode 33554439 [512,256,1056,64,1280,772,1160,576,562,417,84] 4535107210552999351 [0,1,2,3,4,5,6,33554432,33554433,33554436,33554437,33554439] 4463002113 4463002113 (limbs [68354,0xb0b060605050303]) [(852,18,(limbs [16,0xa00a242801c90207,0xca0081f0802073a0,0x81cc80a00f18200,0xbd40802dd02003a2])),(1860,18,(limbs [72629728787436704,0x20822808205a0a00,0xa242801c90207ca0,0x81ce80a00f18240,0x1a60800e880000a2])),(1888,18,(limbs [4329069184,0x8208a0a00a242802,0x690a007242801990,0x207ca0081ee80207,0x3a0081c780a00f18,0x2401a60700d94000,0x2b50700854000025]))]),
  (41, LocalCompactPackets.decode 10485767 [512,256,1056,192,256,772,1160,584,562,417,68] 2233785393684872375 [0,1,2,3,4,5,6,2097152,2097158,2097159,8388608,8388609,8388610,8388613,8388615,10485760,10485766] 4497147905 1155480683009 (limbs [67085,0x5080e0209010e0e,0x909060605050303]) [(844,1347424274,(limbs [4587537369863,0x72440032810003a0,0x341fc60d07ed83c0,0x1d30a0060c341fa2])),(964,1347424274,(limbs [273438,0x890b079242c1dc90,0xb072e44003281000,0x3a01c2b47070ab1c,0x1c2937000a11c341,0xfc60d07e58341fa2]))]),
  (44, LocalCompactPackets.decode 35651591 [512,256,1056,192,1280,772,1032,520,562,417,84] 2803490746484850103 [0,1,2,3,4,5,6,2097152,2097154,2097158,2097159,33554432,33554433,33554437,33554439,35651584,35651588] 4513661441 1155497460225 (limbs [67085,0x5090e020a010e0e,0xa0a060605050303]) [(1804,1347424274,(limbs [4553494366476,0x528341e890d07724,0x202f28080b3a0400,0x1d30c07e88001ca2])),(1832,1347424274,(limbs [18213977469982,0x890d079a4341dc90,0xd07664202f28080b,0xba0202ce8080b1e0,0x3c03650700ad43c0,0x21507000944001d3]))]),
  (53, LocalCompactPackets.decode 33554439 [512,16,32,192,1282,772,1160,584,560,417,80] 8933659501833792567 [0,1,2,3,4,5,6,33554432,33554435,33554437,33554438,33554439] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(632,327698,(limbs [4535527999488,0x9a42403c60900ed8,0x2803650a008542c0,0x3e4070074c1c0183])),(752,327698,(limbs [270338,0x8908009a42002490,0x8007e4001f470007,0xb1c001d37000711c,0x2403c60900e58280,0x3650a008542c03e4]))]),
  (54, LocalCompactPackets.decode 33554439 [512,16,1056,128,1282,772,1152,584,560,417,84] 7924853184703147319 [0,1,2,3,4,5,6,33554432,33554433,33554434,33554435,33554439] 4463002113 4463002113 (limbs [68356,0xb0b060605050303]) [(1712,18,(limbs [73192678749245856,0xa00a242802690a00,0x9242801f90407d1c,0x101d370900d94240,0x2150a00f90240204]))]),
  (55, LocalCompactPackets.decode 33554439 [512,16,1056,64,1282,772,1160,576,560,417,84] 9217368685639019831 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554437,33554439] 4362207500 4362207500 (limbs [294686497573889,0xc0c060605050303]) [(628,327698,(limbs [16,0xc00a243002690b00,0xf182003650800d54,0x2002150800794240,0x3e40700e881c0372])),(852,327698,(limbs [16,0xc00a242c01c90008,0xc600022f80008360,9191964468675136,0x3e40900e101c03a2])),(1648,327698,(limbs [72065679313981856,0x7228001c2a0c00,0xa243002690b00f18,0x2801a60800d94200,0x2150900f90200204]))]),
  (58, LocalCompactPackets.decode 42082311 [512,16,1056,192,1282,516,1160,584,528,417,84] 9194164584193887543 [0,1,2,3,4,5,6,8199,131072,131077,131078,139265,139269,139271,8388615,8396802,8396804,8396805,8396807,8519685,8519687,8527877,33554435,33554437,33554438,33562627,33562629,33562631,33685510,33685511,33693703,41943041,41943043,41943045,41943047,41951235,41951237,42074119,42082304,42082305,42082311] (limbs [19145503,0x15100f0b251e1c00]) (limbs [18948122,0x1913110c1d040201]) (limbs [309044909447969,0x18211b201820221a,0x181a221918190d13,0xa131d11140c0a0c,0x1d1d171d161d091d,0x61122041d041b04,0x22021d021b021402,0x12020d021d010e0e,0x707060605050303]) [(604,92233720368553000978,(limbs [0x4a002892700f18,0x9c03b62800f90980,0x1d3260060c9023a2])),(724,(limbs [80,21480407045,173019154]),(limbs [18,0x800a24a002490026,0xd1c009ac700264dc,0x98472700f187c0,0x3962800f909023a2]))]),
  (60, LocalCompactPackets.decode 33554439 [512,16,1056,192,1282,772,1032,520,560,417,84] 7485752221570870583 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554439] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1592,327698,(limbs [4467259474951,0x4682c02890b009a4,0x2003650800854240,0x3e408008102801d3]))]),
  (69, LocalCompactPackets.decode 9568263 [512,272,0,192,1282,768,1160,584,562,417,80] 8917118457495485623 [0,1,2,3,4,5,6,131072,131073,131075,131078,1048576,1179654,1179655,8388610,8388613,8388615,8519680,8519683,8519685,8519687,9437186,9437189,9568256,9568261] 301326517403663 301317977539073 (limbs [1,0xa12090c0d0d050c,0x14040d01060f1002,0x1010060605050303]) [(856,11016675000338,(limbs [77136935180754065,0x507ca0541f081507,0x3a0541cc8130bf18,0x4c2fb61800f90580,0x384170074c440183])),(976,16582952615954,(limbs [4597719620,0x82e49120b724482c,0xb91507ca0541f081,0x5073a0541cc80b11,0xd1c2c46c70b114dc,0x4447130bf183c2,0xf961800f90580384]))]),
  (70, LocalCompactPackets.decode 10485767 [512,272,1024,128,1282,768,1152,584,562,417,84] 7620081764213128631 [0,1,2,3,4,5,6,2097152,2097156,2097158,2097159,8388608,8388609,8388610,8388611,8388615,10485762] 4530439169 1159792427521 (limbs [67086,0x3090f040a010f0f,0xa0a060605050303]) [(1922,2694848530,(limbs [271409,0x6a0e07a24381e490,0xe07724381cb91000,0xca040031810003a0,0x4000d8080bd1c202,0xd37070b8841c2c51])),(1936,2694848530,(limbs [4446771842,0x4311a0e07a24381e,0x490e07724381cb91,0xca04003081000,0x3a03400c8080bd1c,0x202d370c07f90301,0xf840b078102c1c14]))]),
  (71, LocalCompactPackets.decode 8388615 [512,272,1024,64,1282,768,1160,576,562,417,84] 8912597265149001143 [0,1,2,3,4,5,6,8388608,8388609,8388610,8388612,8388613,8388615] 4362207500 4362207500 (limbs [294686497573889,0xc0c060605050303]) [(852,655378,(limbs [16,0xc00a243001c90900,0xca024030809003a0,0x2400c80b00f18200,0x3e40800e10200b72])),(1858,655378,(limbs [72629728787433632,0xc00a243001c90900,0xca024031809003a0,0x2400d80b00f18280,0x1a60007884001c51])),(1872,655378,(limbs [4329069184,0x8211a02082280820,0x2a0c00a243001c90,0x900ca02403080900,0x3a02400c80b00f18,0x2801a60800f90200,0x38407008101c0014]))]),
  (76, LocalCompactPackets.decode 131079 [512,272,1024,192,1282,768,1032,520,562,417,84] 7180980801080851895 [0,1,2,3,4,5,6,131072,131073,131076,131078,131079] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1802,262807570,(limbs [16,0xa015a82c02890b00,0x724081f280207c60,0x81ce80207360240,0x1d30700884000051])),(1816,262807570,(limbs [272389,0x6a0a014682c02890,0xb00724081f280207,0xc20081ce80207320,0x2003e40100e101c0,0x20400000502401d3]))]),
  (87, LocalCompactPackets.decode 33554439 [512,272,32,64,1282,772,1160,576,562,417,80] 8930620468337114295 [0,1,2,3,4,5,6,33554432,33554434,33554435,33554437,33554439] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(626,327698,(limbs [4569887738368,0x9a42c03c60800d94,0x2002150900f90240,0x3d407008841c01e1])),(852,655378,(limbs [16,0xa00a242801c90007,0xca0001f0800073a0,8101248933921344,0x3e40900e100008a2])),(880,655378,(limbs [73118203813897,0xa42801c90a006640,0x1f280007c20001e,0xe80007aa0001ce80,0x7320001c780007,0x602c03c60800d94,0x802b50800854080,0x250900f90240384]))]),
  (103, LocalCompactPackets.decode 38404103 [512,272,1056,0,1282,772,1152,576,562,417,84] 7921814151743339959 [1,2,3,4,5,6,131073,131077,524288,655360,4194304,4718592,4718598,4718599,33554437,33685504,33685509,33685511,37748737,37879809,37879813] 1177090262529 1168432627968 (limbs [4530636556,0x111105100d0d1101,0xd00050504040202]) [(852,64424550418,(limbs [17,0x408a245021c90b0f,0xca02c3f080b0f3a0,0x283cc81401ed84c2,0x3e41208e104827a2]))]),
  (104, LocalCompactPackets.decode 35651591 [512,272,1056,128,1026,772,1152,584,546,417,84] 1007011908644674871 [0,1,2,3,4,5,6,2097152,2097154,2097158,2097159,33554432,33554433,33554437,33554439,35651588] 4513661441 1155497460225 (limbs [67085,0x5090e020a010e0e,0xa0a060605050303]) [(1698,1347424274,(limbs [16,0x90c5a8341e890d07,0x9a4341e490d077e4,0x202f47080b4dc3c0,0x3650f008543c0221]))]),
  (109, LocalCompactPackets.decode 10485767 [512,272,1056,128,1282,772,128,584,562,417,20] 7349874591248481719 [0,1,2,3,4,5,6,2097152,2097158,2097159,8388608,8388609,8388613,8388615,10485760] 4496818689 1151185715713 (limbs [67084,0x5080d0209010d0d,0x909060605050303]) [(916,1347424274,(limbs [273438,0x890b079242c1dc90,0xb072e43803280e00,0xc203800e80a00320,0x202b47080a4dc301,0xfe40c07e10301fa2]))]),
  (120, LocalCompactPackets.decode 33554439 [512,272,1056,64,1026,772,1160,576,546,417,84] 2299527409580547383 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554439] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(852,327698,(limbs [0x42c02890900724,0x2b08000a320240,0x3c60704e101c03a2])),(1634,327698,(limbs [4467259474951,0x2282c02890b009a4,0x2403c60800698280,0x3650a00854280221]))]),
  (121, LocalCompactPackets.decode 33554439 [512,272,1056,64,258,772,1160,576,562,417,68] 2229264222808898743 [0,1,2,3,4,5,6,33554432,33554435,33554436,33554437,33554439] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(838,327698,(limbs [16,0x800a242001c90407,0xca0101f1804073a0,0x101cd80b00f18280,0x3a20900884100051])),(852,327698,(limbs [16,0x800a242001c90407,0xca0001f0804073a0,8101248933921217,0x20400040502803a2]))]),
  (122, LocalCompactPackets.decode 42090503 [512,272,1056,64,1282,516,1160,576,530,417,84] 9189718175813635511 [0,1,2,3,4,5,6,16384,131072,147457,147461,147463,8388608,8388611,8404992,8404996,8404997,8404999,8519685,8519687,8536069,33554435,33570821,33570823,33685508,33685509,33685511,33701892,33701893,41943041,41943043,41943045,41943047,41959429,42074117,42090499,42090503] (limbs [74786,0x211c18140f091e02]) (limbs [19144478,0x191612100a040201]) (limbs [4899018009,0x15160d120d102020,0x1a1a171713131111,0xb0b030a20042002,0x1a02170213021102,0xb02060605050303]) [(598,(limbs [5242880,0xa0000000012]),(limbs [0x49002892300f18,0x881fe42207f50842,0x3a21b0c8846031e1])),(852,(limbs [5242880,28587302363154]),(limbs [18,0x400a249001c90e18,0xba03062a80e181e0,0x3060182300f18881,0xfe41d07e108423a2]))]),
  (123, LocalCompactPackets.decode 33554439 [512,272,1056,64,1282,260,1160,576,562,385,84] 9191818697886594487 [0,1,2,3,4,5,6,33554432,33554433,33554435,33554437,33554439] 1142612558337 1142612558337 (limbs [4479781634,0xb0b060605050303]) [(852,18,(limbs [16,0x9049a42411990407,0xca0101f0804073a0,0x101cc80900f18200,0x3e40800e102803a2]))]),
  (124, LocalCompactPackets.decode 33554439 [512,272,1056,64,1282,772,1032,512,562,417,84] 7487216787702087095 [0,1,2,3,4,5,6,33554432,33554433,33554435,33554439] 4362207498 4362207498 (limbs [292487440763393,0xa0a060605050303]) [(852,327698,(limbs [16,0xa00a242801c90007,0xca0001f0800073a0,8101240410309120,0x3e40800e102003a2]))]),
  (125, LocalCompactPackets.decode 33554439 [512,272,1056,64,1282,772,136,576,562,417,20] 7345353399501651383 [0,1,2,3,4,5,6,33554432,33554434,33554435,33554437,33554439] 1142612558337 1142612558337 (limbs [4479781634,0xb0b060605050303]) [(852,18,(limbs [16,0x900a242401c90007,0xca0001f0800073a0,8101236107215488,0x3e40a00e102803a2]))]),
  (126, LocalCompactPackets.decode 33554439 [512,272,1056,64,1282,772,1160,64,562,289,84] 9216596982658956727 [0,1,2,3,4,5,6,33554432,33554433,33554439] 4362207497 4362207497 (limbs [291387912358145,0x909060605050303]) [(852,99946514,(limbs [16,0x8049240410b90407,0xca0101f0800073a0,8101240343986688,0x3e40800e102003a2]))]),
  (127, LocalCompactPackets.decode 33554439 [512,272,1056,64,1282,772,1160,576,50,161,84] 9216627664194043319 [0,1,2,3,4,5,6,33554433,33554435,33554436,33554437,33554439] 1142595781121 1142595781121 (limbs [4479781634,0xb0b060605050303]) [(852,18,(limbs [0x42011c900093a0,0x24c80800f18280,0x3e40700e101c03a2]))]),
  (140, LocalCompactPackets.decode 65543 [512,272,1056,192,1026,772,1032,520,546,417,84] 567910945512398135 [0,1,2,3,4,5,6,65538,65540,65542,65543] 4362207498 4362207498 (limbs [292487440763393,0xa0a060605050303]) [(1578,94703634,(limbs [0x424056a0a00a24,0x2802690700d941c0,0x215080074c1c0221]))]),
  (205, LocalCompactPackets.decode 33619975 [512,272,1056,192,1282,772,8,520,562,417,20] 7343119192343772599 [0,1,2,3,4,5,6,65536,65537,65542,65543,33554434,33554437,33554439,33619968,33619971,33619973,33619974,33619975] 298015029988361 298019341992449 (limbs [4597220876,0x5090d020a010d0d,0xa0a060605050303]) [(796,1347424274,(limbs [16,0xf00a243c01c9000e,0xca0003b08000e3a0,0x38c81000f90300,0x384110074c301fa2]))])]

def codes := entries.map Prod.fst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 1 codes = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma facts : ∀ z ∈ codes, atCode 1 z :=
  entries_sound 1 entries (by decide +kernel)

end LocalLightBand1

namespace LocalLightBand2
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def entries : List (ℕ × HPacket) := [
  (52, LocalCompactPackets.decode 11550727 [1536,0,1024,192,1280,768,1160,584,560,417,85] 13455264718750986111 [0,1,2,3,4,5,6,16390,1064965,2113537,2113541,2113543,3145728,3145732,3145733,3162117,8388608,8388611,8388614,8404992,8404996,8404997,8404998,8404999,9437187,9437191,10485765,10502149,11550720,11550725] 79673967070680578 307957913092609 (limbs [4732753176,0xe18081808161218,0x1116070a19191717,0xb0b030a19040b02,0x1701060605050303]) [(1864,175922028257298,(limbs [76297716812220833,0x60ca245031c91d02,0xc606c08d8130cf18,0x4c33b6130c6984c3,0x1861c0074c4c0183])),(1928,175922028257298,(limbs [277569,0x7a160ca245832491,0x40c7245030b91d02,0xc606c08d80c13d1c,0x304f370c134dc304,0xcf71c0074c3000f3])),(1984,175922028257298,(limbs [4547698307,0xc409a160ca245832,0x49140c7245030b91,0xd02c606c08d80c13,0xd1c304ec70c134dc,0x4c47130cf18403,0x396130c698003046]))]),
  (54, LocalCompactPackets.decode 1048583 [1536,0,1056,128,1280,772,1152,584,560,417,85] 12464481604808454015 [0,1,2,3,4,5,6,1048576,1048577,1048578,1048579,1048580,1048581,1048583] 1151219270145 1151219270145 (limbs [4513336578,0xd0d060605050303]) [(1441,18,(limbs [4604229716992,0x5a8200b180802b60,0x2c03470900d941c0,0x2b50700fc01c0290])),(1712,16392210,(limbs [75435699679007392,0x207a24081e690207,0x924081df90b00d1c,0x2c01370900d94240,0x2150201f500805e4])),(1924,16392210,(limbs [75435699683202464,0x207a24081e490007,0x724001cb90802c60,0x408d80b00d1c2c0,0x1370007e88001ca2])),(1952,16392210,(limbs [73667675431034,0x24081e6902079240,0x81df90007724001d,0x9900072e4001c090,0x802c60200ad80102,0x3600408580b00d1c,0x2c01370900d941c0,0x2b509008541c0025]))]),
  (55, LocalCompactPackets.decode 8388615 [1536,0,1056,64,1280,772,1160,576,560,417,85] 13756997105744326527 [0,1,2,3,4,5,6,8388608,8388609,8388610,8388611,8388612,8388614,8388615] 1151219270145 1151219270145 (limbs [4513336577,0xd0d060605050303]) [(1648,16392210,(limbs [72347171470561952,0x107268001c3a0c00,0xa243002690b00f18,0x2c01a60207d94081,0xe150901f500805e4])),(1860,16392210,(limbs [72347171474757024,0x107268041c6a0c00,0xa242c01c90802c60,0x2008d80b00f182c0,0x1a60700e881c00a2])),(1888,16392210,(limbs [4312227456,0x41c9a0c00a243002,0x690b007242c01990,0x802c60040ad80802,0x3600408580b00f18,0x2c01a60207d94001,0xeb50207854001c25]))]),
  (56, LocalCompactPackets.decode 36724743 [1536,0,1056,192,1024,772,1160,584,544,417,85] 11455077154555924351 [0,1,2,3,4,5,6,24576,1056771,1056775,2113541,2113543,3145728,3170309,33554432,33554438,33554439,33579008,33579014,36700166,36724736] 4463263759 292504704647681 (limbs [293616950575882,0x909060805080904,0xb02050f030f1001,0x1010060605050303]) [(1640,2815093464436754,(limbs [75732567827122593,0x20ca24483269110c,0xf184433b6110c698,0x4431861307d944c1,0xe15140074c440183])),(1704,2815093464436754,(limbs [275513,0x7a120ca244832691,0x20c9244831f90c11,0xd1c3047370c114dc,0x3044f71307d944c1,0xe15140074c3000f3])),(1760,2815093464436754,(limbs [4514012803,0x4389a120ca244832,0x69120c9244831f90,0xc11d1c3046c70c11,0x4dc004447110cf18,0x383396110c698003,0x461307d944c1e15]))]),
  (60, LocalCompactPackets.decode 45088775 [1536,0,1056,192,1280,772,1032,520,560,417,85] 12025380641676177279 [0,1,2,3,4,5,6,1048579,1048581,2097153,2097157,3145728,3145729,3145732,3145733,3145735,8388608,8388611,8388614,9437187,9437191,10485761,11534337,33554434,33554438,36700162,41943040,41943042,41943044,41943046,41943047,45088772] 313459917850880 313442653438465 (limbs [69917,0xa1d081d12130813,0x180e120e070e1e1e,0x14140f0f14040f02,0x1e01060605050303]) [(1592,(limbs [15,0x5ff00f120f05012]),(limbs [4640334286106,0x4a8742e891d0b9a4,0x64436519108546c2,0x7d417097907c01d3])),(1804,(limbs [15,0x50f00f100005012]),(limbs [4640334286362,0x568742e891c0b724,0x585f1815173607c0,0x1d31a0be88402ca2])),(1832,(limbs [15,0x5ff00f120f05012]),(limbs [18561337160750,0x891d0b9a4702dc91,0xc0b664585f180c17,0xb60545cd80917160,0x6443650b10ad4644,0x2150b100947c01d3]))]),
  (69, LocalCompactPackets.decode 3162119 [1536,256,0,192,1280,768,1160,584,562,417,81] 13456746860412271863 [0,1,2,3,4,5,6,16384,16386,16387,16388,16391,1048577,1048579,1064963,2097155,2113537,2113539,3145728,3145734,3145735,3162112,3162113,3162115] 302438947751940 1181267264001 (limbs [4547874067,0x1414140106090b04,0xb0b060605050303]) [(1864,64676167698,(limbs [78254813153920672,0x812a242049c91700,0xca05c00e80a12f18,0x284bb607126981c4,0x986150074c1c0183])),(1928,251658258,(limbs [284689,0x5a0812a24204a490,0x8127242048b91700,0xca05c00e81207d1c,0x481f3712074dc481,0xcf7150074c4800f3])),(1984,64676167698,(limbs [4664350340,73922920516427850,0x4908127242048b91,0x700ca05c00e81207,0xd1c481ec712074dc,7959407940960516,0xb960712698004846]))]),
  (70, LocalCompactPackets.decode 9977863 [1536,256,1024,128,1280,768,1152,584,562,417,85] 12159710167138566143 [0,1,2,3,4,5,6,16384,524292,524294,540673,540675,540679,1048580,1048582,1064963,1064964,1064967,1572864,1572866,1572868,1572870,1572871,1589249,1589250,1589251,1589253,1589254,1589255,8388608,8404992,8404994,8404995,8404999,8912899,8929283,9437185,9437187,9453571,9961472,9961473,9977857,9977858,9977859] (limbs [75300,0x231f0a1c150d0800]) 20760491536624648705 (limbs [1,0x2515221511200e20,0xc2009200e0f090b,0x1c02212116161111,0xc0c210411040c04,0x1601060605050303]) [(1441,40978,(limbs [4881053785117,0x5a8ac03282900ba0,0x507b47121fd54487,0xe952707fc0481e90])),(1864,40978,(limbs [4881053784349,0x2687c4a891f12724,0xac03282b003a0783,0x7b61e0d618782183])),(1920,(limbs [40960,0xf00f00001005a012]),(limbs [284,0x1d5e870756a1a1d5,0x6868754a1b1d4a85,0x4751a101d4283474,0xfa191d26864748a0,0xa1d1a828745a181d,0xe84c742a071d028,0x7c4a891f129e4784,0xa691e129647c4a49,0x1f128e41c49f9001,0x27a47c49c91f126e,0x47849991e126247c,0x48b91f122a41c480,0x92b00ca0ac03182b,0xc20a802f82900b,0xa05c02d82800aa04,0x802982b003a08c00,0xd826003207c00a82,0x9001e02800582400,0x60507b47141ecdc,0x507ac7121ea5c507,0x9370d1e3dc207847])),(1921,40978,(limbs [0x470757a1c1d5a87,0xc4a891f129e47c4a,0x491f128e47c49c91,0xf126e47c48b91f12,0x2a4ac03282b003a0,0x507b47141e4dc9c1,0xff01d07dc0481e90])),(1922,5767422273070145554,(limbs [79971185227770001,0xf129247c49c91f12,0x2e4ac03282b00c60,0xac00e82300360507,0xb47141e4dc0091e1])),(1924,40978,(limbs [1191663521,0xa1d5687c4a891f12,0x9247c49c91f122e4,0xac03282b003a0507,0xb47141e4dc744f72])),(1928,40978,(limbs [79971185227770001,0xf129247c49c91f12,0x2e4ac03282b003a0,0x507b47141ecdc507,0x9370d1e3dc782183])),(1936,(limbs [40960,40978]),(limbs [71,0x757a1b1d4a87c4a,0x891f129247c49c91,0xf122e4ac03282b00,0xc20ac00e82600320,0x507b47141e4dc742,0xbd41d0add00029e4])),(1952,40978,(limbs [1163733,0xe87c4a891e129a47,0xc4a4907127e47c49,0xc91e126647c48b90,0x712024ac03282900,0xba0ac00e829001e0,0x507b47141e4dc487,0xf55121fa54007de5])),(1984,40978,(limbs [71,0x757a191d2687c4a,0x891f129247c49c91,0xf122e4ac03282b00,0x3a0507b47141eb1c,0x507937081e11c783,0x7b61d0ddd8783586]))]),
  (71, LocalCompactPackets.decode 16391 [1536,256,1024,64,1280,768,1160,576,562,417,85] 13452225668074438655 [0,1,2,3,4,5,6,16384,16385,16386,16387,16388,16390,16391] 1151219270145 1151219270145 (limbs [4513336577,0xd0d060605050303]) [(1856,16723986,(limbs [266,0x5e828016a08005,0x6820014a09004a80,0x8011a07004280000,0xfa0a0026828008a0,0x8001a820005a0900,0xe808002a0700028,0x3002890c009e42c0,0x2690b00964240249,0x9008e41c01f9000,0x7a43001c90c006e,0x42c01990b0062424,0xb909002a41c000,0x90a00ca02803180a,0xc202402f80800b,0xa02002d80100aa00,0x2980a003a02800,0xd80a003202400a80,0x8001e02000580100,0x602c03c60b00ed8,0x1003960000dd82c0,0x1a60b00618100046])),(1857,327698,(limbs [66,0x8017a0a005a82800,0x9a0a002283002890,0xc009e43001c90c00,0x6e42803280a003a0,0x2c03c60b00698001,0xff00007dc0001e90])),(1858,5574674,(limbs [1115690912,0xa002683002890c00,0x7242803280a00c60,0x2800e80a003602c0,0x3c60b006980005e1])),(1860,655378,(limbs [1115690912,0x80056828009a0800,0x1a83002890c00724,0x2803280a003a02c0,0x3c60b00698000b72])),(1864,327698,(limbs [1115690912,0xa002683002890c00,0x7242803280a003a0,0x2c03c60b00ed82c0,0x1a60b006180010f3])),(1872,327698,(limbs [66,0x8017a09004a82800,0x9a09000e83002890,0xc007242803280a00,0xc202800e80a00320,0x2c03c60b00698002,0x3d40008dd00021e4])),(1888,327698,(limbs [66,0x8017a0a002683002,0x890b009a43001c90,0xb006642803280800,0xba02800e808001e0,0x2c03c60b00698002,0x7550009a540025e5])),(1928,327698,(limbs [16,0xa005e83002890900,0x9243001c909002e4,0x2803280a003a0002,0xf37000b3dc0010f3])),(1984,327698,(limbs [66,0x8017a0a002683002,0x8909009243001c90,0x9002e42803280a00,0x3a0002f37000ba5c,0x2cf70b00f18100,0x3960b00698100046]))]),
  (72, LocalCompactPackets.decode 16391 [1536,256,1024,192,1024,768,1160,584,546,417,85] 11149109448234999679 [0,1,2,3,4,5,6,16384,16386,16387,16390,16391] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1864,327698,(limbs [75154224702294432,0xa00a242001c90904,0xc202410c80700f18,0x1c03b607006981c0,0x186070074c1c0183])),(1928,327698,(limbs [273409,0x7a0a00a242802490,0x8007242000b90904,0xc202410c80007d1c,8786197540093953,0xcf7070074c0000f3])),(1984,327698,(limbs [4479540866,0xc009a0a00a242802,0x4908007242000b90,0x904c202410c80007,0xd1c001ec700074dc,7959394754068480,0x3960700698000046]))]),
  (73, LocalCompactPackets.decode 16391 [1536,256,1024,192,256,768,1160,584,562,417,69] 11150903851195825343 [0,1,2,3,4,5,6,16384,16386,16388,16391] 4362207498 4362207498 (limbs [292487440763393,0xa0a060605050303]) [(1864,327698,(limbs [74314111906808736,0x800a242001c90a00,0xca02800e80900f18,0x2403b607006981c0,0x186070074c1c0183])),(1928,327698,(limbs [270353,0x2a0800a242002490,0x8007242000b90a00,0xca02800e80007d1c,8786197540093953,0xcf7070074c0000f3])),(1984,327698,(limbs [4429466242,73078490754457602,0x4908007242000b90,0xa00ca02800e80007,0xd1c001ec700074dc,7959403344003328,0x3960700698000046]))]),
  (74, LocalCompactPackets.decode 16391 [1536,256,1024,192,1280,512,1160,584,530,417,85] 13445628598845149183 [0,1,2,3,4,5,6,16384,16385,16387,16390,16391] 1142612558337 1142612558337 (limbs [4479781633,0xb0b060605050303]) [(1864,327698,(limbs [74591274740484512,0xa00a242801c90804,0xba02010780700f18,0x1c03b607006981c0,0x186070074c1c0183])),(1928,327698,(limbs [271361,0x7a0a00a242802490,0xa007242800b90804,0xba02010780007d1c,8786197540093953,0xcf7070074c0000f3])),(1984,327698,(limbs [4445986434,0x4009a0a00a242802,0x490a007242800b90,0x804ba02010780007,0xd1c001ec700074dc,7959394754068480,0x3960700698000046]))]),
  (75, LocalCompactPackets.decode 3162119 [1536,256,1024,192,1280,256,1160,584,562,385,85] 13447737908421195775 [0,1,2,3,4,5,6,16384,16390,16391,1048577,1048581,1048583,1064967,2097157,2097159,2113543,3145728,3145730,3145732,3145733,3162112,3162115,3162119] 77146176802000136 296915451379977 (limbs [4497212942,0xf0b060b0f020c02,0x9020f0f0c0c0909,0x509060605050303]) [(1417,20498,(limbs [4776028411392,0x5a85c03281307d1c,0x4c1f37150074c440,0xf31307fc04c1e90])),(1473,20498,(limbs [284673,0x7a16005a858009a1,0x6002285c03281307,0xd1c4c1ec70711f18,0x47960711698004,0x4461307fc04c1e90])),(1864,22605959067095058,(limbs [78250449492248992,0x7139a41c4d991700,0xca05c00e80711f18,0x1c47b607116981c4,0x586150074c1c0183])),(1928,20498,(limbs [284673,0x7a07139a41c4df90,0x7136641c4c091700,0xca05c00e81307d1c,0x4c1f3711074dc441,0xcf7150074c4400f3])),(1984,22605959067095058,(limbs [4664090245,0x8009a07139a41c4d,0xf907136641c4c091,0x700ca05c00e81307,0xd1c4c1ec711074dc,7959395039281156,0x7960711698004446]))]),
  (76, LocalCompactPackets.decode 10508295 [1536,256,1024,192,1280,768,1032,520,562,417,85] 11720609204006289407 [0,1,2,3,4,5,6,4101,6150,6151,18435,18439,20485,20486,22528,22535,2097152,2097156,2097158,2099206,2101254,2103298,2103302,2113541,2113543,2117633,2117635,2117637,2117639,2119681,2119682,2119683,2119684,2119685,2119686,2119687,8388608,8390657,8390659,8392707,8404994,8404995,8404999,8407043,8409094,8411138,8411140,8411142,10485760,10487809,10502146,10504195,10506243,10508289,10508291,10508292] (limbs [78895,0x2b2825231b161100]) (limbs [291,0x1b1a290a08040201]) (limbs [76827,0x141b141a0d1a1a08,0xf290c29170a130a,0xc0a290827082608,0xa08182912290708,0x1c041c022a2a1818,0xb0b09092a040b04,0x901060605050303]) [(1800,(limbs [0x5aa5f0f50500f,0xa0f5a010000f012]),(limbs [4884553352,0xc916a21245686c91,0x4a22244a858911a2,0x244284490fa1f24,0x2687c908a1d241a8,0x64905a1e240e8549,0x2a0e24028bc4289,0x2f109e4b842692e1,0x964b4424928108e,0x43841f900107a4bc,0x41c92f106e4b8419,0x92e10624b440b928,0x102a43840093600c,0xa0d003183300c20c,0x802f83500ba06402,0xd83100aa04002983,0x6003a0d000d82b00,0x320a000a835001e0,0x6400582500060dc0,0x1d32e0060c4400f3])),(1801,20498,(limbs [81949206663206562,0xf10a24bc42792f10,0x724bc41b93600ca0,0xd800e8370074cc03,0xbf0240edc0403a90])),(1802,(limbs [0x5555505505000,0x5055a0100005012]),(limbs [5001782636304,0xa24bc41c93600ca0,0xd0031836003a0d00,0xd8370074c0095e1])),(1804,20498,(limbs [74532,0x5e884915a2f10a24,0xbc41c93600ca0d80,0xe8370074c905772])),(1816,92235127743431331858,(limbs [81949206659011234,0xf10a24bc41c93600,0xca0cc030836003a0,0xac00c82419f50906,0x7740019790dc01d3])),(1832,40978,(limbs [298129,0x7a2f10a24b842692,0xf10724b841993600,0xca0d402e836003a0,0xd400781028d5440a,0x2950028794dc01d3])),(1864,20498,(limbs [1221138337,0xf24268bc42892f10,0x724d8032836003a0,0x9047962411dd8004,0x446370074cb80183])),(1928,20498,(limbs [81949206713215122,0xd10924bc41c92d10,0x2e4d8032836003a0,0x40bac7102ea5c00b,0x847370074c4400f3])),(1984,20498,(limbs [81949206646426018,0xf10a24b442492f10,0x724b440b93600ca0,0xd800e8102eb1c00b,0x8472411e58004446]))]),
  (77, LocalCompactPackets.decode 16391 [1536,256,1024,192,1280,768,136,584,562,417,21] 11583249415422935039 [0,1,2,3,4,5,6,16384,16386,16387,16388,16391] 4446224897 4446224897 (limbs [68356,0xb0b060605050303]) [(1864,18,(limbs [4552943863808,0xa242001c90900ca0,0x2400e807046981c1,0x1860a0074c1c0183])),(1928,18,(limbs [271376,0x9a0800a242002490,0x8007242000b90900,0xca02400e80407d1c,0x101f3704074dc101,0xcf70a0074c1000f3])),(1984,18,(limbs [271376,0x9a0800a242002490,0x8007242000b90900,0xca02400e80407d1c,8663069417652225,0xc470704698001046]))]),
  (78, LocalCompactPackets.decode 3162119 [1536,256,1024,192,1280,768,1160,72,562,289,85] 13449971806777638911 [0,1,2,3,4,5,6,16386,16387,16388,16391,1048577,1048579,1064963,2097155,2113539,3145728,3145730,3145732,3145733,3145735,3162115,3162116,3162119] (limbs [273,0x17130f0d0b090700]) 306845483008513 (limbs [296949946455809,0x1414140205080a04,0xa0a060605050303]) [(1864,21480079378,(limbs [77968974511344032,0x7129241c48b91700,0xca05400e80910f18,0x2443b60910698244,0x186160074c240183])),(1928,21480079378,(limbs [4758848538386,0x9241c48b91700ca0,0x5400e810094dc402,0x4f7160074c4000f3])),(1984,21480079378,(limbs [77968974511344032,0x7129241c48b91700,0xca05400e810094dc,0x24470910f18004,0x3960910698004046]))]),
  (79, LocalCompactPackets.decode 16391 [1536,256,1024,192,1280,768,1160,584,50,161,85] 13454523680126140415 [0,1,2,3,4,5,6,16384,16386,16387,16391] 4446224897 4446224897 (limbs [68100,0xa0a060605050303]) [(1864,18,(limbs [16,0x9005e824009a0804,0x7242410e80700f18,0x1c03b607006981c0,0x186070074c1c0183])),(1928,18,(limbs [16,0x9005e82011c90804,0x2e42410e80407d1c,0x101f3700074dc001,0xcf7070074c0000f3])),(1984,18,(limbs [271361,0x7a09002682011c90,0x8042e42410e80407,0xd1c101ec700074dc,7959394754068480,0x3960700698000046]))]),
  (86, LocalCompactPackets.decode 2097159 [1536,256,32,128,1280,772,1152,584,562,417,81] 12177733370318028023 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097156,2097157,2097159] 4479779329 4479779329 (limbs [68610,0xc0c060605050303]) [(1441,18,(limbs [4587181968130,0x5282003280800ba0,0x2803470900d94240,0x2b50900fc01c0290])),(1924,18,(limbs [16,0xb02568001e890007,0x924001dc900072e4,0x20032808003a0280,0x3470a004dc0024a2])),(1952,18,(limbs [73394911445114,0x24001e6900079240,0x1df90007724001d,0x9900072e4001c090,0x800ca02002e80800,0x3a02000780a00d1c,0x2801370900d94240,0x2b50900854240025]))]),
  (87, LocalCompactPackets.decode 67108871 [1536,256,32,64,1280,772,1160,576,562,417,81] 13470248871253900535 [0,1,2,3,4,5,6,67108864,67108865,67108866,67108868,67108870,67108871] 4479779329 4479779329 (limbs [68609,0xc0c060605050303]) [(1860,995346,(limbs [4415853035785,0x1a8101e890407724,0x20032808003a02c0,0x3c60a006980008a2])),(1888,995346,(limbs [4312356480,0x4246a0407a24101e,0x690407724101d990,0x800ca02002e80800,0x3a02000780b00f18,0x2801a60900d94240,0x2b50200854080025]))]),
  (89, LocalCompactPackets.decode 69206023 [1536,256,32,192,256,772,1160,584,562,417,65] 11168927054387870903 [0,1,2,3,4,5,6,2097152,2097154,2097157,2097159,67108865,67108870,67108871,69206016,69206018,69206021,69206022] 1146890488841 1151202492929 (limbs [66828,0x6090a020d010d0d,0xa0a060605050303]) [(481,21480079378,(limbs [4672977375232,0xba03803470e00b1c,0x301fc60c07e583c0,0x3650f00ad44403f0]))]),
  (92, LocalCompactPackets.decode 2097159 [1536,256,32,192,1280,772,1032,520,562,417,81] 11738632407185751287 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097156,2097157,2097159] 4479779329 4479779329 (limbs [68610,0xc0c060605050303]) [(1804,18,(limbs [0x42c095a0407a24,0x101dc90800ca0200,0xe80a0074c0024a2])),(1832,18,(limbs [18348727865374,0x8904079a4101dc90,0x4076642003280800,0xba02000e808001e0,0x2403650900ad4240,0x21509000942801d3]))]),
  (103, LocalCompactPackets.decode 524295 [1536,256,1056,0,1280,772,1152,576,562,417,85] 12461442554668777471 [0,1,2,3,4,5,6,524288,524289,524290,524291,524294,524295] 1146924302849 1146924302849 (limbs [4496559105,0xc0c060605050303]) [(1441,327698,(limbs [4569869978112,0x5a82003280800ba0,0x2413370700d941c0,0x2b50700fc01c0290])),(1860,983058,(limbs [74872749721392544,0x80026820006a0407,0xa24101dc90800ca0,0x2000e80402ed8100,0x9860007e88001ca2])),(1888,983058,(limbs [4462763650,0x9a0407a24101e,0x690407724101d990,0x800ca02002e80800,0x3a02000780402ed8,0x1009860700d941c0,0x2b507008541c0025])),(1924,983058,(limbs [74872749721392544,0x407a24001e490407,0x724001cb90800ca0,0x2000e80904cdc081,0xf70007e88001ca2])),(1952,983058,(limbs [73117919625338,0x24101e6900079240,0x1df90407724101d,0x9900072e4001c090,0x800ca02002e80800,0x3a02000780904cdc,0x810f70700d941c0,0x2b507008541c0025]))]),
  (104, LocalCompactPackets.decode 2097159 [1536,256,1056,128,1024,772,1152,584,546,417,85] 10158326334292467583 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097156,2097159] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1441,327698,(limbs [4587049847552,0x5a82013080804aa0,0x2403470a00d941c0,0x2b50700fc01c0290])),(1698,99946514,(limbs [16,0xb005e8101e890407,0x9a4101e4904077e4,0x24034709004dc280,0x3650a008541005e1])),(1924,99946514,(limbs [75154224702297504,0x407a24101e490007,0x724001cb90804c20,0x410c80900d1c240,0x1370007e88001ca2])),(1952,99946514,(limbs [73392797532282,0x24101e6904079241,0x1df90007724001d,0x9900072e4001c090,0x804c202012a80104,0x3200410180900d1c,0x2401370a00d941c0,0x2b50a008541c0025]))]),
  (105, LocalCompactPackets.decode 2097159 [1536,256,1056,128,256,772,1152,584,562,417,69] 10160120737253293247 [0,1,2,3,4,5,6,2097152,2097154,2097156,2097157,2097159] 4463002113 4463002113 (limbs [68354,0xb0b060605050303]) [(1441,18,(limbs [4535773431812,0x4682803280a00ba0,0x2003470700d941c0,0x2b50900fc01c0290])),(1924,18,(limbs [74314111906812064,0x7a24001e490007,0x724001cb90a00ca0,0x2800e80800d1c200,0x1370407e88001ca2])),(1952,18,(limbs [72572374876282,0x24001e6900079240,0x1df90007724001d,0x9900072e4001c090,0xa00ca02802e80a00,0x3a02800780800d1c,0x2001370700d941c0,0x2b507008541c0025]))]),
  (106, LocalCompactPackets.decode 2097159 [1536,256,1056,128,1280,516,1152,584,530,417,85] 12436831077803200511 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097159] 4463002113 4463002113 (limbs [68356,0xb0b060605050303]) [(1441,18,(limbs [0x428017a0a005a8,0x2012e80900d1c1c1,0x2b50700fc01c0290])),(1924,18,(limbs [74872749721392544,0x407a24101e490407,0x724101cb90804ba0,0x2010780900d1c240,0x1370407e88101ca2])),(1952,18,(limbs [66,0x8017a0407a24101e,0x690407924101df90,0x407724001d990407,0x2e4001c090804ba0,0x2010780900d1c240,0x1370704ad41c1025]))]),
  (107, LocalCompactPackets.decode 77611015 [1536,256,1056,128,1280,260,1152,584,562,385,85] 12438931599876159487 [0,1,2,3,4,5,6,16384,16387,2097152,2097154,2097155,2097158,2113539,2113541,2113543,8404992,8404996,8404997,8404999,10485765,10485767,10502149,67108866,67108870,67125253,67125255,69206018,69206020,69206021,69206022,69206023,69222405,75497472,75497473,75497477,75497479,75513860,75513861,77594628,77594629,77611009,77611013] (limbs [19408418,0x2016111e170d0a00]) (limbs [19078685,0x1914120e0d040201]) (limbs [4699917086,0xb1d181908190c14,0xb1418120c120812,0xc0e0c0d24240323,0x1f1f1a1a15151313,0xf0f0f0424021f02,0x1a02150213020f02,0x1f01060605050303]) [(1413,(limbs [0xf000000000002a,687194787858]),(limbs [16,0xd215e834856a0d21,0x56834854a2a00ca0,0x7843472509e88442,0x4a22707fc0701e90])),(1441,(limbs [0xf000000000002a,687194787858]),(limbs [4623624178977,0x5a8a803282a00ba0,0x7843470911854244,0x4252707fc0701e90])),(1924,(limbs [0xf000000000002a,687194787858]),(limbs [75753458548364705,0x1c9a41c71f9101c,0x6641c70092a00ca0,0xa800e81e10d1c6c4,0x1372509e884424a2])),(1952,(limbs [0xf000000000002a,687194787858]),(limbs [275589,0x7a101c9a41c71f91,0x1c6641c70092a00,0xca0a802e82a003a0,0xa400781e10d1c6c4,0x1370911854244425]))]),
  (108, LocalCompactPackets.decode 2097159 [1536,256,1056,128,1280,772,1024,520,562,417,85] 11882747594737713151 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097159] 4362207498 4362207498 (limbs [292487440763393,0xa0a060605050303]) [(1441,327698,(limbs [4569869978112,0x5a82003280800ba0,0x2412c70700d941c0,0x2b50700fc01c0290])),(1804,983058,(limbs [4569869978112,0x568101e890407724,0x20032808003a0100,0x9830007e88001ca2])),(1832,983058,(limbs [18279479906334,0x8904079a4101dc90,0x4076642003280800,0xba02000e808001e0,0x1c03650700ad41c0,0x2150700094100983])),(1924,983058,(limbs [74872749721392544,0x407a24001e490407,0x724001cb90800ca0,0x2000e80904b1c081,0x470007e88001ca2])),(1952,983058,(limbs [73117919625338,0x24101e6900079240,0x1df90407724101d,0x9900072e4001c090,0x800ca02002e80800,0x3a02000780904b1c,0x810470700d941c0,0x2b507008541c0025]))]),
  (109, LocalCompactPackets.decode 2097159 [1536,256,1056,128,1280,772,128,584,562,417,21] 11889502994163105791 [0,1,2,3,4,5,6,2097152,2097153,2097156,2097158,2097159] 4463002113 4463002113 (limbs [68353,0xb0b060605050303]) [(1441,327698,(limbs [4535763994628,0x2282003280800ba0,0x2803470700d941c0,0x2b50900fc01c0290])),(1924,327698,(limbs [74313957287986848,0x7a24001e490007,0x724001cb90800ca0,0x2000e80a00d1c280,0x1370407e88001ca2])),(1952,327698,(limbs [72572223881338,0x24001e6900079240,0x1df90007724001d,0x9900072e4001c090,0x800ca02002e80800,0x3a02000780a00d1c,0x2801370700d941c0,0x2b507008541c0025]))]),
  (110, LocalCompactPackets.decode 2097159 [1536,256,1056,128,1280,772,1152,72,562,289,85] 12459188692835106815 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097157,2097159] 1151219270145 1151219270145 (limbs [4513336578,0xd0d060605050303]) [(1441,18,(limbs [4569869978112,0x5a83003280c00ba0,0x2411370b00d942c0,0x2b50b00fc02c0290])),(1924,18,(limbs [4569869978112,0x568002e49000b2e4,0x30032808003a0241,0x1370007e88001ca2])),(1952,18,(limbs [18279479902254,0x49000b7e4002cb90,0xb0243003280c00,0xba02000e808001e0,0x2411370b00d942c0,0x2b507008541c0025]))]),
  (111, LocalCompactPackets.decode 2097159 [1536,256,1056,128,1280,772,1152,584,50,161,85] 12463740566183608319 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097158,2097159] 1151219270145 1151219270145 (limbs [4513336577,0xd0d060605050303]) [(1441,327698,(limbs [4569869978112,0x5a82010e808041e0,0x3003470b00d942c0,0x2b50b00fc02c0290])),(1924,327698,(limbs [4569869978112,0x568002dc9000b2e4,0x2010e80c00d1c240,0x1370007e88001ca2])),(1952,327698,(limbs [272385,0x7a000b724002d990,0xb2e4002c090804,0x3a02010780c00d1c,0x2401370b00d942c0,0x2b50b008541c0025]))]),
  (120, LocalCompactPackets.decode 16391 [1536,256,1056,64,1024,772,1160,576,546,417,85] 11450841835228340095 [0,1,2,3,4,5,6,16384,16385,16386,16389,16390,16391] 1146924302849 1146924302849 (limbs [4496428033,0xc0c060605050303]) [(1634,16060434,(limbs [4569869978112,0x2682c02890b009a4,0x2403c60900698101,0xf6504078541005e1])),(1860,327698,(limbs [74872749721392544,0xa0026828006a0b00,0xa242401c90804c20,0x2010c80900f18240,0x1a60700e881c00a2])),(1888,16060434,(limbs [4462763650,0x8009a0b00a242c02,0x6909007242401990,0x804c200412a80804,0x3200410180900f18,0x2401a60407d94001,0xeb50407854001c25]))]),
  (121, LocalCompactPackets.decode 35651591 [1536,256,1056,64,256,772,1160,576,562,417,69] 11452636238189165759 [0,1,2,3,4,5,6,2097152,2097157,2097159,33554432,33554434,33554436,33554438,33554439,35651584,35651588] 4513595905 1155480683009 (limbs [66829,0x60809020e010e0e,0x909060605050303]) [(837,21480144914,(limbs [16,0xb07a242c1e790b07,0x7242c1db9080aca0,0x2028e80d07f18301,0xfa21000fc0300370])),(1860,21480144914,(limbs [74041433019060384,0x70c0e800300a0b07,0xa242c1dc9080aca0,0x2028e80d07f182c1,0xda60c07e88001ca2])),(1888,21480144914,(limbs [4413213313,0xc303a0b07a242c1e,0x690b077242c1d990,0x80aca0202ae8080a,0x3a02028780d07f18,0x2c1da60f00d941c0,0x2b50f008541c0025]))]),
  (122, LocalCompactPackets.decode 33554439 [1536,256,1056,64,1280,516,1160,576,530,417,85] 13729346578739073023 [0,1,2,3,4,5,6,33554432,33554434,33554436,33554438,33554439] 4463002113 4463002113 (limbs [68353,0xb0b060605050303]) [(1860,331794,(limbs [72347171474757024,0x107268041c6a0a00,0xa242801c90109ba0,0x424780800f18200,0x1a60900e881000a2])),(1888,331794,(limbs [72347171474753952,0xa00a242802690a00,0x7242001990109ba0,0x424780800f18200,0x1a60004ad4001025]))]),
  (123, LocalCompactPackets.decode 77594631 [1536,256,1056,64,1280,260,1160,576,562,385,85] 13731447100812031999 [0,1,2,3,4,5,6,2097152,2097153,2097157,2097159,8388610,8388612,8388613,8388615,10485765,67108866,67108869,67108871,69206020,69206021,75497472,75497474,75497476,75497477,77594625,77594629] 20181773486966638592 300222660215297 (limbs [70146,0xe020a0212120e0e,0xa0a060605050303]) [(1860,68454252562,(limbs [74332889504109984,0x81526820546a0b13,0x9a42c4d991a00ca0,0x6800e81607f18581,0xda61707e88301ca2])),(1888,68454252562,(limbs [74332889504106912,0xb139a42c4d991a00,0xca06802e81a003a0,0x6400781607f18581,0xda6070c8541c3025]))]),
  (124, LocalCompactPackets.decode 3276807 [1536,256,1056,64,1280,772,1032,512,562,417,85] 12026845190627524607 [0,1,2,3,4,5,6,131072,131078,131079,1048577,1048581,2097153,2097157,2228225,3145728,3145729,3145732,3145733,3145735,3276800,3276801,3276805] 1177023023106 1176955519489 (limbs [4614981138,0xd080b0813020901,0x909060605050303]) [(1804,995346,(limbs [4776028411392,0x568203e89080f724,0x401f2810073a0440,0x8f30014e880050a2])),(1832,995346,(limbs [19104113631294,0x89080f9a4203dc90,0x80f664401f281007,0xba0401ce810071e0,0x5003651400ad4500,0x21514000944408f3])),(1860,252653586,(limbs [78250449492252065,0x50026838006a080f,0xa24203dc91007ca0,0x401ce80211e58084,0x4460014e880050a2])),(1888,995346,(limbs [4664090245,0x4009a080fa24203e,0x69080f724203d991,0x7ca0401ee81007,0x3a0401c780211e58,0x844461400d94500,0x2b51400854500025]))]),
  (125, LocalCompactPackets.decode 7 [1536,256,1056,64,1280,772,136,576,562,417,21] 11884981802416275455 [0,1,2,3,4,5,6] 17039873 17039873 288097900495619 [(1860,18,(limbs [4415504908548,0x1a80802890200724,0x4032801003a0081,0x1a60400e880000a2])),(1888,18,(limbs [17662019635202,0x8902009a40801c90,0x2006640403280100,0xba00400e801001e0,0x811a60000d94000,0x2b50000854000025]))]),
  (126, LocalCompactPackets.decode 35651591 [1536,256,1056,64,1280,772,1160,64,562,289,85] 13756225385584394239 [0,1,2,3,4,5,6,2097152,2097153,2097156,2097157,2097159,33554432,33554438,33554439,35651584,35651588] 4513726977 1155514237441 (limbs [66829,0x60a0b020e010e0e,0xb0b060605050303]) [(1377,21480144914,(limbs [74322993899312800,0x80c26820308a0a0c,0xca02832e80d07f18,0x341da61000d94240,0x2b51000fc0240290])),(1860,21480144914,(limbs [74322993899312544,0x80c26820306a0c09,0x9240024b90a0cca0,0x2030e80d07f18341,0xda60c07e88001ca2])),(1888,21480144914,(limbs [4429995650,0x309a0c099243025,0xf900092e40024090,0xa0cca02832e8080c,0x3a02030780d07f18,0x341da61000d94240,0x2b50f008541c0025]))]),
  (127, LocalCompactPackets.decode 7 [1536,256,1056,64,1280,772,1160,576,50,161,85] 13756256067119480831 [0,1,2,3,4,5,6] 17039873 17039873 288097900495619 [(1860,18,(limbs [16,0x1005e804015a0100,0x26804006a0204724,0x410e80200f18080,0x1a60000e880000a2])),(1888,18,(limbs [72339474893244832,0x2047240811990104,0x3a00410780200f18,0x801a60400d94100,0x2b50400854000025]))]),
  (140, LocalCompactPackets.decode 16391 [1536,256,1056,192,1024,772,1032,520,546,417,85] 9719225371160190847 [0,1,2,3,4,5,6,16384,16385,16388,16390,16391] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1578,262807570,(limbs [0x42c017a0a00a24,0x2802690207d94081,0xe15090074c0805e1])),(1804,655378,(limbs [4587049847552,0x5682802890900724,0x200b080802320240,0x1d30700e881c00a2])),(1832,262807570,(limbs [18348199389186,0x890a009a42401c90,0x900664200b080102,0xaa02008c80102060,0x81f650007ad4081,0xe1500070942401d3]))]),
  (155, LocalCompactPackets.decode 78659591 [1536,256,1056,192,256,260,1160,584,562,385,69] 11430125283933418687 [0,1,2,3,4,5,6,16384,16387,16389,16390,2097155,2097157,2097158,2113539,2113543,3145728,8388615,8404992,8404996,8404997,8404998,8404999,10485765,10485766,10485767,10502151,67125254,67125255,68157447,68173829,68173831,69206021,69206023,70254596,70254597,70254598,70254599,70270983,75497474,75497478,75497479,75513858,75513862,76546049,76546053,76546055,76562437,78643205,78643206,78659591] (limbs [5120208684,0x222b2726131a0e00]) (limbs [331108207962139,0x181715140f040201]) (limbs [1,0x2d1b1e1823152414,0x19240b2419230b23,0x161e081e201b2518,0x1b171f152d0f032d,0x1d28161b081b0b18,0x21170b1708151c14,0x814280f2e022502,0x1f02250103282121,0x1d1d1c1c0f0f0d0f,0xc0f0a0f090f0f04,0x190216020f022901,0x1c01190116010f01,0x1111060605050303]) [(453,(limbs [655360,94371840,22906798098]),(limbs [0x4c803282212d1c,0x884ac72a10f189c4,0x3962b10e88c41ff0]))]),
  (156, LocalCompactPackets.decode 2097159 [1536,256,1056,192,256,772,1032,520,562,417,69] 9721019774121016511 [0,1,2,3,4,5,6,2097152,2097155,2097156,2097159] 4429447681 4429447681 (limbs [68100,0xa0a060605050303]) [(1804,18,(limbs [4552819083522,0x428101e890407724,0x20032808003a0240,0x1d30207e88001ca2])),(1832,18,(limbs [18211276328990,0x8904079a4101dc90,0x4076642003280800,0xba02000e808001e0,0x1c03650700ad41c0,0x21507000942401d3]))]),
  (172, LocalCompactPackets.decode 44040199 [1536,256,1056,192,1280,516,1032,520,530,417,85] 11997730114670923775 [0,1,2,3,4,5,6,2097152,2097157,2097159,8388609,8388610,8388614,10485761,33554434,33554438,41943040,41943042,41943044,41943046,41943047,44040196] 302426012385288 1181250486785 (limbs [4631823635,0xf080c0814010902,0x909060605050303]) [(1804,90199556114,(limbs [4536583981072,0x5684c1e891307724,0x343ae80d0e1e0540,0x1d31107e882c1ca2])),(1832,90199556114,(limbs [16,0x8105e84c1e891307,0x9a44c1dc91207664,0x343ae80d0e1e01c2,0xeb5070b0945401d3]))]),
  (188, LocalCompactPackets.decode 77611015 [1536,256,1056,192,1280,260,1032,520,562,385,85] 11999830636743882751 [0,1,2,3,4,5,6,16389,2097152,2097156,2097157,2113539,2113541,2113543,8404994,8404995,8404996,8404999,10485763,10485767,10502147,10502148,67108864,67125251,67125255,69206018,69206019,69206023,69222403,75497472,75497473,75497475,75497479,75513858,75513859,77594627,77611009,77611011] (limbs [19079710,0x1c1914100e0c0900]) (limbs [73498,0x17120f0c0b040201]) (limbs [4464772895,0xa1a07170a12070f,0x20201b1b18181313,0x11110d0d20041b04,0x1804130411040d04,0xd02060605050303]) [(1804,(limbs [5570560,0x1000005000000012]),(limbs [4606175874077,0x5684066691019664,0x94032825003a0545,0x9d32108e883820a2])),(1832,(limbs [5570560,0x1000005000000012]),(limbs [16,0xc1d5e84066691019,0x6649403282500ba0,0x9400e824001e0203,0xa15080e0945459d3]))]),
  (205, LocalCompactPackets.decode 2097159 [1536,256,1056,192,1280,772,8,520,562,417,21] 11882747595258396671 [0,1,2,3,4,5,6,2097152,2097153,2097158,2097159] 4446224897 4446224897 (limbs [68097,0xa0a060605050303]) [(1804,983058,(limbs [4535763994628,0x1a8081e890207724,0x20032808003a0240,0x1d30407e88001ca2])),(1832,983058,(limbs [18143055972382,0x8902079a4081dc90,0x2076642003280800,0xba02000e808001e0,0x1c03650700ad41c0,0x21507000942401d3]))]),
  (206, LocalCompactPackets.decode 3276807 [1536,256,1056,192,1280,772,1032,8,562,289,85] 12026843129143885823 [0,1,2,3,4,5,6,131072,131078,131079,1048577,1048579,1048581,2097153,2097155,2097157,3145729,3145731,3145732,3145733,3145735,3276800,3276803,3276804,3276806] 302438930841608 302438846562817 (limbs [4631823891,0x6110f080e080c08,0xb08140414020901,0x909060605050303]) [(1321,331794,(limbs [4776028411392,0x5a84c1f281307ba0,0x5c03651700ad4600,0x1d31207fc0481e90])),(1804,331794,(limbs [4776028411392,0x5681c4a4907122e4,0x4c1f2810073a0600,0x1d30015e880054a2])),(1832,331794,(limbs [19104113630282,0x4907127e41c48b90,0x7120244c1f281307,0xba0401ce810071e0,0x5c03651700ad4540,0x21515000946001d3]))]),
  (207, LocalCompactPackets.decode 2097159 [1536,256,1056,192,1280,772,1032,520,50,161,85] 12024639603051331583 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097159] 4463002113 4463002113 (limbs [68612,0xc0c060605050303]) [(1804,18,(limbs [0x428017a0a00568,0x82dc908043a0240,0x1d30007e88001ca2])),(1832,18,(limbs [16,0xa005e8082dc9020b,0x6642010e808041e0,0x2c03650b00ad42c0,0x21507000942401d3]))])]

def codes := entries.map Prod.fst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 2 codes = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma facts : ∀ z ∈ codes, atCode 2 z :=
  entries_sound 2 entries (by decide +kernel)

end LocalLightBand2

namespace LocalLightBand3
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def entries : List (ℕ × HPacket) := [
  (70, LocalCompactPackets.decode 44040199 [1536,16,1024,128,1282,768,1152,584,560,417,85] 16841971642224586623 [1,2,3,4,5,6,2097152,2097156,2097158,2097159,8388609,8388610,8388611,10485762,33554433,33554435,35651585,41943040,41943041,41943042,41943043,41943047] 303525524015107 1185545388288 (limbs [4648666388,0xf080c0815030900,0x909050504040202]) [(1712,168435730,(limbs [74328491457532577,0x406a24481a691406,0x9243819f90711d1c,0x1c4537100bd54382,0xde51206f90481a04])),(1922,2852790290,(limbs [16,0x8115e8501a891406,0x9244c19c90b062e4,0x343b180d0e3601c4,0x74707114dc182851])),(1936,2852790290,(limbs [4430323330,0x452a1406a24501a,0x4913067242c18b90,0xd0ec60343af80d0e,0x3602c38a80711d1c,0x1c45371206f90481,0xb841206810281814]))]),
  (71, LocalCompactPackets.decode 33554439 [1536,16,1024,64,1282,768,1160,576,560,417,85] 18134487143160459135 [0,1,2,3,4,5,6,33554432,33554433,33554436,33554437,33554438,33554439] 4362207500 4362207500 (limbs [294686497573889,0xc0c060605050303]) [(1648,655378,(limbs [72628646455661216,0x207268081c3a0c00,0xa242802690900f18,0x2401a60802d54200,0x9e50800f90200204])),(1858,262807570,(limbs [4432900784647,0x2683002890b00724,0x823180208360240,0x3c60900698000451])),(1872,262807570,(limbs [4329004672,0x81d2a0207268081c,0x3a0c00a242c01c90,0x208c600822f80208,0x3600820a80900f18,0x2401a60800f90200,0x3840800810040014]))]),
  (74, LocalCompactPackets.decode 33570823 [1536,16,1024,192,1282,512,1160,584,528,417,85] 18129297448814743423 [0,1,2,3,4,5,6,16384,16386,16390,16391,33554432,33554437,33554439,33570816,33570823] 1164138054145 298019341992449 (limbs [4546889228,0x5090d020a010d0d,0xa0a060605050303]) [(1624,1347424274,(limbs [270381,0x7a080b4a8202c9a0,0x80b0e83c02890e00,0xf183803b60e00698,0x3801860c07f90301,0xe040e0074c380183])),(1688,1347424274,(limbs [74321894387667616,0xf00a243c0249000e,0xd1c003b37000e4dc,0x38f70c07f90301,0xe040e0074c0000f3])),(1744,1347424274,(limbs [4429930114,0x2d2a080b268202c,0x3a0f00a243c02490,0xed1c003ac7000e,0x4dc0038470e00f18,0x2c03960e00698000,0x460c07f90301e04]))]),
  (76, LocalCompactPackets.decode 131079 [1536,16,1024,192,1282,768,1032,520,560,417,85] 16402870679092309887 [0,1,2,3,4,5,6,131073,131076,131077,131078,131079] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1592,655378,(limbs [4569869978112,0x4a82c028909009a4,0x1c0b5507027941c0,0x3e407008102001d3])),(1802,262807570,(limbs [0x428017a0b00a24,0x2801c90207c60081,0xcd8080074c000451])),(1816,262807570,(limbs [272385,0x7a0a004a82c02890,0xa00724081f180207,0xbe0081cd802072a0,0x1c03e40100e101c0,0x20401000502001d3]))]),
  (86, LocalCompactPackets.decode 33554439 [1536,16,32,128,1282,772,1152,584,560,417,81] 16859994845404048503 [0,1,2,3,4,5,6,33554432,33554433,33554434,33554435,33554439] 4463002113 4463002113 (limbs [68356,0xb0b060605050303]) [(1712,18,(limbs [73193761081020576,0x800a242002690800,0x9242001f90407d1c,0x101d370a00d94280,0x2150a00f90200204]))]),
  (87, LocalCompactPackets.decode 33554439 [1536,16,32,64,1282,772,1160,576,560,417,81] 18152510346339921015 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554437,33554438,33554439] 294716512141825 294716512141825 (limbs [295786025979137,0xd0d060605050303]) [(625,327698,(limbs [16,0xb00a242c02790b00,0x9a42c02590c00f18,0x2403650900854240,0x3e40800fc0200370])),(1648,327698,(limbs [72066761645756576,0x81a800200a0b00,0xa242c02690c00f18,0x2801a60900d94240,0x2150900f901c0204]))]),
  (92, LocalCompactPackets.decode 33554439 [1536,16,32,192,1282,772,1032,520,560,417,81] 16420893882271771767 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554437,33554439] 1146907525633 1146907525633 (limbs [4496559106,0xc0c060605050303]) [(1592,18,(limbs [4467325535240,0x4282c02890b009a4,0x2403650900854240,0x3e407008102801d3]))]),
  (95, LocalCompactPackets.decode 102236167 [1536,16,32,192,1282,772,1160,584,48,161,81] 18156290500065864823 [0,1,2,3,4,5,6,524288,1048576,1048583,1572866,1572870,1572871,33554432,33554437,33554439,35127303,67108870,67108871,68157441,68681732,68681734,100663303,101187586,101711879,102236166,102236167] 77989502487893518 293642686300431 (limbs [4597679371,0xc01091105111201,0xf0112120f0f060f,0x909060605050303]) [(241,1495702228172818,(limbs [0x4503747140db1c,0x5c23c61708e58680,0x3651807f906403f0]))]),
  (103, LocalCompactPackets.decode 16777223 [1536,16,1056,0,1282,772,1152,576,560,417,85] 17143704029754797951 [0,1,2,3,4,5,6,16777216,16777217,16777220,16777221,16777222,16777223] 1146924302849 1146924302849 (limbs [4496428033,0xc0c060605050303]) [(1648,983058,(limbs [72628646455661216,0x7268001c3a0a00,0xa242802690902ed8,0x1009860800d94200,0x2150800f90200204])),(1712,983058,(limbs [72628646455661216,0xa00a242802690800,0x9242001f90204cdc,0x810f70800d94200,0x2150800f90200204]))]),
  (104, LocalCompactPackets.decode 2752519 [1536,16,1056,128,1026,772,1152,584,544,417,85] 10230098055307169663 [0,1,2,3,4,5,6,131072,131077,131079,524290,524294,2097154,2097158,2621440,2621442,2621444,2621446,2621447,2752514,2752517,2752518] 1172728055809 1172660552193 (limbs [4598138129,0xd080b0812010902,0x909060605050303]) [(1698,91626614802,(limbs [17,0x5005e8203a89080e,0x9a4203a49080e7e4,0x3c1f470f074dc500,0x3651400854400451])),(1712,91626614802,(limbs [77968974502957728,0x80ea24203a69080e,0x9242039f90f07d1c,0x3c1d371400d94500,0x2150110e10044014]))]),
  (105, LocalCompactPackets.decode 7 [1536,16,1056,128,258,772,1152,584,560,417,69] 10158638599873997887 [0,1,2,3,4,5,6] 17039873 17039873 288097900495619 [(1712,18,(limbs [16,0x2044a80402890100,0x9a404024901007e4,0x8034702004dc040,0x3650100854041204]))]),
  (106, LocalCompactPackets.decode 33554439 [1536,16,1056,128,1282,516,1152,584,528,417,85] 17120499927772794751 [0,1,2,3,4,5,6,33554432,33554436,33554437,33554439] 4446224897 4446224897 (limbs [68098,0xa0a060605050303]) [(1684,18,(limbs [72628646455661984,0x2074a8081d0a0900,0xa242402490207d1c,0x81d370900f90240,0x2040800e881000a2])),(1712,18,(limbs [72628646455661216,0x900a242402690900,0x9242401f90207d1c,0x81d370004ad4001,0x250900f90240204]))]),
  (107, LocalCompactPackets.decode 67108871 [1536,16,1056,128,1282,260,1152,584,560,385,85] 17121193074962179967 [0,1,2,3,4,5,6,67108864,67108865,67108866,67108868,67108870,67108871] 4479779329 4479779329 (limbs [68609,0xc0c060605050303]) [(1712,995346,(limbs [4432900784647,0x4a8042a69010a7e4,0x2c034709004dc041,0x2150800f90200204]))]),
  (108, LocalCompactPackets.decode 65543 [1536,16,1056,128,1282,772,1024,520,560,417,85] 16565009069823733631 [0,1,2,3,4,5,6,65537,65541,65542,65543] 1138300813825 1138300813825 (limbs [4462873089,0xa0a060605050303]) [(1592,983058,(limbs [4552690108672,0x4a820028908009a4,0x1c036507008541c0,0x3e40700810100983])),(1712,983058,(limbs [74591274740486816,0x800a242002690700,0x9241c01f90204b1c,0x810470700d941c0,0x2150700f901c0204]))]),
  (109, LocalCompactPackets.decode 35651591 [1536,16,1056,128,1282,772,128,584,560,417,21] 16571764469249126271 [0,1,2,3,4,5,6,2097152,2097158,2097159,33554432,33554433,33554436,33554437,33554439,35651585] 4513595905 1155480683009 (limbs [67085,0x5080e0209010e0e,0x909060605050303]) [(1712,1347424274,(limbs [74041278400234400,0xb07a242c1e690b07,0x9242c1df9080ad1c,0x2029370f00d943c0,0x2150d07f902c1e04]))]),
  (110, LocalCompactPackets.decode 67108871 [1536,16,1056,128,1282,772,1152,72,560,289,85] 17141450167921127295 [0,1,2,3,4,5,6,67108864,67108865,67108866,67108868,67108869,67108871] 4479779329 4479779329 (limbs [68610,0xc0c060605050303]) [(1712,995346,(limbs [4432900784647,0x4a8042a49010a7e4,0x2411370b00d94040,0x2150800f90200204]))]),
  (111, LocalCompactPackets.decode 35651591 [1536,16,1056,128,1282,772,1152,584,48,161,85] 17147484182943870847 [0,1,2,3,4,5,6,2097152,2097154,2097156,2097158,2097159,33554432,33554437,33554439,35651588,35651589] 4513726977 1155514237441 (limbs [67085,0x50a0e020b010e0e,0xb0b060605050303]) [(1201,1347424274,(limbs [16,0x80c5e820316a080c,0x4a820311a0a0cd1c,0x4003650d07f90341,0xe040f00fc0240290])),(1712,1347424274,(limbs [74322993899311776,0xc097243025990009,0x2e40024090a0cd1c,0x2031371000d94400,0x2150d07f90341e04]))]),
  (120, LocalCompactPackets.decode 33554439 [1536,16,1056,64,1026,772,1160,576,544,417,85] 11522613556243042175 [0,1,2,3,4,5,6,33554432,33554433,33554434,33554437,33554439] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1634,99946514,(limbs [4467260523527,0x2682c02890b009a4,0x2403c60900698280,0x3650a00854100451])),(1648,99946514,(limbs [73191596400693920,0x407268001c3a0b00,0xa242c02690900f18,0x2401a60a00d94280,0x2150804e10041014]))]),
  (121, LocalCompactPackets.decode 33554439 [1536,16,1056,64,258,772,1160,576,560,417,69] 11451154100809870399 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554438,33554439] 1146907525633 1146907525633 (limbs [4496559105,0xc0c060605050303]) [(1648,327698,(limbs [4398737129482,0xe824028909009a4,0x2c03c608006981c0,0x36507008541c1204]))]),
  (122, LocalCompactPackets.decode 33554439 [1536,16,1056,64,1282,516,1160,576,528,417,85] 18413015428708667263 [0,1,2,3,4,5,6,33554432,33554434,33554436,33554437,33554439] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(597,327698,(limbs [0x42c02890b009e4,0x2003c60a00f90240,0x3a20700fc01c0370])),(1620,327698,(limbs [64,0x1d7a0007568001d,0x2a0007428001c9a0,0x71a8001c3a0007,0x282c02890800f18,0x2001a60a00f90280,0x2040900e881000a2])),(1648,327698,(limbs [72065696493851296,0x7268001c3a0b00,0xa242c02690800f18,0x2001a60004ad4001,0x250a00f90280204]))]),
  (123, LocalCompactPackets.decode 33554439 [1536,16,1056,64,1282,260,1160,576,560,385,85] 18413708575898052479 [0,1,2,3,4,5,6,33554432,33554433,33554434,33554435,33554439] 4463002113 4463002113 (limbs [68356,0xb0b060605050303]) [(1648,18,(limbs [16,0x75e8001d2a0007,0x268001c3a0a049a4,0x2403c60900698201,0x2150800f90200204]))]),
  (124, LocalCompactPackets.decode 33554439 [1536,16,1056,64,1282,772,1032,512,560,417,85] 16709106665713545087 [0,1,2,3,4,5,6,33554432,33554433,33554434,33554439] 4362207498 4362207498 (limbs [292487440763393,0xa0a060605050303]) [(1592,983058,(limbs [4467260523527,0x4a82802890a009a4,0x2003650800854200,0x3e408008101008f3])),(1648,983058,(limbs [73191596417471136,0x7268001c3a0a00,0xa242802690904e58,0x810460800d94200,0x2150800f90200204]))]),
  (125, LocalCompactPackets.decode 33554439 [1536,16,1056,64,1282,772,136,576,560,417,21] 16567243277502295935 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554437,33554439] 1146907525633 1146907525633 (limbs [4496559106,0xc0c060605050303]) [(1648,18,(limbs [4398727692298,0xe824028909009a4,0x2011a60700d941c0,0x2150b00f901c0204]))]),
  (126, LocalCompactPackets.decode 33554439 [1536,16,1056,64,1282,772,1160,64,560,289,85] 18438486860670414719 [0,1,2,3,4,5,6,33554432,33554433,33554437,33554438,33554439] 1142612558337 1142612558337 (limbs [4479650561,0xb0b060605050303]) [(1648,327698,(limbs [72065696493851296,0x7268001c3a0804,0x9242011f90a00f18,0x2801a60900d94200,0x2150800f90200204]))]),
  (127, LocalCompactPackets.decode 33554439 [1536,16,1056,64,1282,772,1160,576,48,161,85] 18439999683879743359 [0,1,2,3,4,5,6,33554432,33554434,33554437,33554439] 4446224897 4446224897 (limbs [68098,0xa0a060605050303]) [(1648,18,(limbs [72065696493851296,0x7268001c3a0804,0x7242011990800f18,0x2001a60900d94240,0x2150900f90240204]))]),
  (140, LocalCompactPackets.decode 65543 [1536,16,1056,192,1026,772,1032,520,544,417,85] 9790997092174892927 [0,1,2,3,4,5,6,65539,65540,65542,65543] 4362207498 4362207498 (limbs [292487440763393,0xa0a060605050303]) [(1578,262807570,(limbs [0x424017a0a00a24,0x2802690700d941c0,0x215080074c080451])),(1592,262807570,(limbs [4552690108416,0x4a82802890a009a4,0x1c03650700854040,0xb8401020502001d3]))]),
  (156, LocalCompactPackets.decode 33554439 [1536,16,1056,192,258,772,1032,520,560,417,69] 9719537636741721151 [0,1,2,3,4,5,6,33554433,33554434,33554436,33554437,33554439] 4463002113 4463002113 (limbs [68354,0xb0b060605050303]) [(1592,18,(limbs [0x410212a0a00a24,0x2802690700d941c0,0x21507028102401d3]))]),
  (172, LocalCompactPackets.decode 33554439 [1536,16,1056,192,1282,516,1032,520,528,417,85] 16681398964640518015 [0,1,2,3,4,5,6,33554432,33554434,33554435,33554436,33554439] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1564,983058,(limbs [16,0x4075e8101d5a0407,0x4a8101d0a0b00a24,0x2403e40900810280,0x1d30800e880800a2])),(1592,983058,(limbs [4467260523527,0x4a82c02890b009a4,0xab50002094240,0x3e409008102801d3]))]),
  (188, LocalCompactPackets.decode 33554439 [1536,16,1056,192,1282,260,1032,520,560,385,85] 16682092111829903231 [0,1,2,3,4,5,6,33554432,33554433,33554436,33554437,33554439] 4463002113 4463002113 (limbs [68354,0xb0b060605050303]) [(1592,18,(limbs [0x4101d7a04074a8,0x280a690802854200,0x3e408008102401d3]))]),
  (205, LocalCompactPackets.decode 33619975 [1536,16,1056,192,1282,772,8,520,560,417,21] 16565009070344417151 [0,1,2,3,4,5,6,65536,65542,65543,33554434,33554436,33554437,33554439,33619969,33619971,33619973,33619974,33619975] 1164104697857 298019325215233 (limbs [4597220876,0x5080d0209010d0d,0x909060605050303]) [(1592,1347420178,(limbs [4519053887243,0xe83c02890f009a4,0x3803650e00854400,0x3e40e008104401d3]))]),
  (206, LocalCompactPackets.decode 33554439 [1536,16,1056,192,1282,772,1032,8,560,289,85] 16709104604229906303 [0,1,2,3,4,5,6,33554432,33554433,33554437,33554438,33554439] 1142612558337 1142612558337 (limbs [4479650561,0xb0b060605050303]) [(1592,983058,(limbs [4432900784647,0x4a820124908047e4,0x2403650800854200,0x3e408008102801d3]))]),
  (207, LocalCompactPackets.decode 33554439 [1536,16,1056,192,1282,772,1032,520,48,161,85] 16708383219811594111 [0,1,2,3,4,5,6,33554432,33554434,33554437,33554439] 4446224897 4446224897 (limbs [68098,0xa0a060605050303]) [(1592,18,(limbs [4432900784647,0x4a82011c90804664,0x2403650900854240,0x3e409008102001d3]))])]

def codes := entries.map Prod.fst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 3 codes = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma facts : ∀ z ∈ codes, atCode 3 z :=
  entries_sound 3 entries (by decide +kernel)

end LocalLightBand3

namespace LocalLightBand4
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def entries : List (ℕ × HPacket) := [
  (86, LocalCompactPackets.decode 2097159 [1536,272,0,128,1282,768,1152,584,562,417,81] 16843453801065741559 [0,1,2,3,4,5,6,2097152,2097153,2097155,2097156,2097159] 4446224897 4446224897 (limbs [68356,0xb0b060605050303]) [(1922,991250,(limbs [272393,0x5a0107a24041e490,0x107724041cb90800,0xca020031808003a0,0x2000d80a00d1c280,0x13707008841c0051])),(1936,991250,(limbs [4462892674,0x8090a0107a24041e,0x490107724041cb90,0x800ca02003080800,0x3a00400c80a00d1c,0x2801370207f90081,0xf840007810001c14]))]),
  (87, LocalCompactPackets.decode 50462727 [1536,272,0,64,1282,768,1160,576,562,417,81] 18135969302001614071 [0,1,2,3,4,5,6,131072,131075,131079,16777220,16777222,33554437,33554438,33685509,33685511,50331650,50331654,50331655,50462720,50462722,50462724,50462725,50462726] 1172761610241 300226938405377 (limbs [68625,0xd0e121203110d08,0xb080f0212010904,0x909060605050303]) [(849,1497169670381586,(limbs [284674,0x8916009e43801c90,0xe006e4044f280113,0xc20044ce80113320,0x5c03c61400f90400,0x3841007fc0401f70])),(1858,1497169670381586,(limbs [74045882605242017,0x600a243801c90113,0xca0044f1801133a0,0x44cd81700f18540,0x1a61300884000051])),(1872,1497169670381586,(limbs [4413478529,0xc410a07101a81c40,0xa1600a243801c90,0x113ca0044f080113,0x3a0044cc81700f18,0x5401a61400f90400,0x3841300810000014]))]),
  (91, LocalCompactPackets.decode 5767175 [1536,272,0,192,1282,256,1160,584,562,385,81] 18131481542348371191 [0,1,2,3,4,5,6,524288,1048576,1572867,1572868,1572871,4194306,4194309,4194311,4718594,5242882,5767172,5767173,5767174,5767175] 302408849227789 302404570710529 (limbs [4630579979,0x5090b04030d0e02,0xe0e060605050303]) [(465,344950046738,(limbs [4707337114112,0xc204403471100b1c,0x3c23c60f08e58401,0xfe41007e104c03f0]))]),
  (92, LocalCompactPackets.decode 131079 [1536,272,0,192,1282,768,1032,520,562,417,81] 16404352837933464823 [0,1,2,3,4,5,6,131072,131074,131075,131076,131077,131079] 1146907525633 1146907525633 (limbs [4496559106,0xc0c060605050303]) [(1802,16392210,(limbs [16,0xa025682c02890b00,0x724041f280107c60,0x41ce80107360280,0x1d30700884000051])),(1816,16392210,(limbs [272393,0x5a0a024282c02890,0xb00724041f280107,0xc20041ce80107320,0x2003e40200e101c0,0x20400000502801d3]))]),
  (103, LocalCompactPackets.decode 40370183 [1536,272,1024,0,1282,768,1152,576,562,417,85] 16838932609264779263 [0,1,2,3,4,5,6,524291,524294,2097154,2097155,2621440,2621441,2621442,2621443,2621447,4194304,4194305,4194309,4194310,4718598,4718599,6815745,33554432,33554436,33554437,36175872,37748736,37748737,37748740,37748741,37748743] 80528317803792640 314546460033537 (limbs [70430,0xa1e071e12140714,0x190e120e080e1f1f,0x15150f0f0f041f02,0x1501060605050303]) [(1858,(limbs [15,0x5aff55f2015af012]),(limbs [76028336451013025,0xe0ba24782dc91617,0xca0585f1816173a0,0x585cd81d09ed8602,0x5861a108842c4051])),(1872,(limbs [15,0x5aff55f2015af012]),(limbs [4531641987,0x86d2a0c1b268306c,0x3a1e0ba24782dc91,0x617ca0585f081617,0x3a0445cc81d09ed8,0x6025861b0bf906c2,0xf841b0b810402c14])),(1922,(limbs [15,0x5aff55f2015af012]),(limbs [276589,0x7a1e0ba24702e491,0xe0b724442cb91617,0xca0585f1816173a0,0x585cd80d18cdc246,0xf71a108842c4051])),(1936,(limbs [15,0x5aff55f2015af012]),(limbs [4531641987,0x86d2a1e0ba24702e,0x491e0b724442cb91,0x617ca0585f081617,0x3a0445cc80d18cdc,0x2460f71b0bf906c2,0xf841b0b810402c14]))]),
  (104, LocalCompactPackets.decode 2752519 [1536,272,1024,128,1026,768,1152,584,546,417,85] 9924130366166114175 [0,1,2,3,4,5,6,131072,131073,131076,131077,131079,524290,524294,2097154,2097158,2621440,2621441,2621442,2621444,2621446,2621447,2752515,2752516,2752519] 307949390793217 307949323158017 (limbs [307880789345556,0xf0a0d0a15010b02,0xb0b060605050303]) [(1698,5589184421906,(limbs [17,0x8005e82842890910,0x9a428424909107e4,0x481f4712074dc5c0,0x75509017945c0221])),(1922,5589184753682,(limbs [286721,0x7a0a10a242842490,0x8107242040b91109,0xc204426f80109320,0x424a81207d1c481,0xd3717008844c0051])),(1936,5589184753682,(limbs [78813399445672608,0xa10a242842490810,0x7242040b91109c20,0x424c81207d1c481,0xd370013e10004c14]))]),
  (105, LocalCompactPackets.decode 2097159 [1536,272,1024,128,258,768,1152,584,562,417,69] 9853867179383979199 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097157,2097159] 1151219270145 1151219270145 (limbs [4513336578,0xd0d060605050303]) [(1922,6230034,(limbs [272401,0x2a0107a24041e490,0x107724041cb90c00,0xca03003180c003a0,0x3000d80900d1c240,0x1370b008842c0051])),(1936,6230034,(limbs [272401,0x2a0107a24041e490,0x107724041cb90c00,0xca02003080c003a0,0x400c80900d1c240,0x137000b810002c14]))]),
  (106, LocalCompactPackets.decode 2637831 [1536,272,1024,128,1282,512,1152,584,530,417,85] 16832335539498618879 [0,1,2,3,4,5,6,16384,16389,16391,524290,524291,2097154,2097155,2621440,2621442,2621443,2621447,2637824,2637827,2637828] 1168433088516 1168365584897 (limbs [4581295376,0xd080b0811040902,0x909060605050303]) [(1682,91625619474,(limbs [77406024549536416,0x80ea24203a490f07,0xd1c3c1d370412f90,0x104bd40412810104,0x9e414008841001e1])),(1922,91625619474,(limbs [281601,0x7a080ea24203a490,0x80e7242038b91204,0xba04812d812041e0,0x4810580f07d1c3c1,0xd371400884480051])),(1936,91625619474,(limbs [4613758596,0xc012a080ea24203a,0x49080e7242038b91,0x204ba03812a81204,0x1e00010180f07d1c,0x3c1d370412f90004,0xb840412810004814]))]),
  (107, LocalCompactPackets.decode 2098183 [1536,272,1024,128,1282,256,1152,584,562,385,85] 16834444849074665471 [0,1,2,3,4,5,6,1024,1029,1031,2097153,2097156,2097158,2097159,2098176,2098178,2098179,2098181,2098182,2098183] 1168399665154 299118836843009 (limbs [4613997836,0x60809020d010d0d,0x909060605050303]) [(1411,21480079378,(limbs [4672949194752,0x5a84403281100c60,0x4803470e00884380,0x510b07fc02c1e90])),(1425,21480079378,(limbs [278529,0x7a10005a840012a1,0x4684403281100,0xc20480347000ef90,0x3b84000e810003,0x8140b07fc02c1e90])),(1922,21480079378,(limbs [278529,0x7a070b9a41c2df90,0x70b6641c2c091100,0xca044031811003a0,0x4400d81200d1c3c0,0x1370e00884380051])),(1936,21480144914,(limbs [4563426948,5242955592113197,0xf9070b6641c2c091,0x100ca04403081100,0x3a02000c81200d1c,0x3c0137000ef90003,0xb84000e810003814]))]),
  (108, LocalCompactPackets.decode 88071 [1536,272,1024,128,1282,768,1024,520,562,417,85] 16260237649333714943 [0,1,2,3,4,5,6,2048,6149,6151,16385,16389,18433,20480,20481,22529,22532,22533,65536,65542,65543,67584,71687,86016,88065,88069,88071] 1172895830786 305698911289857 (limbs [4664331027,0x909060809021401,0x1414060605050303]) [(1802,995346,(limbs [17,0xa005e86402891900,0x7243c4b280e12c60,0x3c48e80e12360400,0x9831707884341c51])),(1816,995346,(limbs [288769,0x7a1a004a86402891,0x9007243c4b280c12,0xc203c48e80c12320,0x5437e4070de10543,0x604070d050400983])),(1922,995346,(limbs [288769,0x7a1900a246002491,0x9007246000b90f12,0xca0384b180f123a0,0x3848d80210b1c084,0x471707884341c51])),(1936,995346,(limbs [4731199110,0x8012a1900a246002,0x4919007246000b90,0xf12ca0304b080f12,0x3a03048c80210b1c,0x84047150df901c3,0x784150d8101c3414]))]),
  (109, LocalCompactPackets.decode 2097159 [1536,272,1024,128,1282,768,128,584,562,417,21] 16266993048759107583 [0,1,2,3,4,5,6,2097152,2097153,2097158,2097159] 4446224897 4446224897 (limbs [68097,0xa0a060605050303]) [(1922,331794,(limbs [270352,0x9a0107a24041e490,0x107724041cb90800,0xca020031808003a0,0x2000d80900d1c240,0x13707008841c0051])),(1936,331794,(limbs [4429457026,73078011597161502,0x490107724041cb90,0x800ca02003080800,0x3a00400c80900d1c,0x2401370407f90101,0xf840007810001c14]))]),
  (110, LocalCompactPackets.decode 2097159 [1536,272,1024,128,1282,768,1152,72,562,289,85] 16836678747431108607 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097157,2097159] 1151219270145 1151219270145 (limbs [4513336578,0xd0d060605050303]) [(1922,6230034,(limbs [16,0xa005e8042e49010b,0x2e43003280c00c60,0x2000e80800360241,0x13707008841c0051])),(1936,6230034,(limbs [272385,0x7a0a004a8042e490,0x10b2e43003280c00,0xc202000e80100320,0x2411370007f90001,0xf840007810001c14]))]),
  (111, LocalCompactPackets.decode 2097159 [1536,272,1024,128,1282,768,1152,584,50,161,85] 16841230620779610111 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097155,2097156,2097158,2097159] 1151219270145 1151219270145 (limbs [4513336577,0xd0d060605050303]) [(1922,5574674,(limbs [4569869975819,0x724042cb908043a0,0x2010d80c00d1c240,0x1370b008841c0051])),(1936,5574674,(limbs [74872749721391776,0x10b724042cb90804,0x3a00410c80c00d1c,0x2401370407f90001,0xf840407810001c14]))]),
  (120, LocalCompactPackets.decode 131079 [1536,272,1024,64,1026,768,1160,576,546,417,85] 11216645867101986687 [0,1,2,3,4,5,6,131073,131074,131075,131076,131077,131078,131079] 4362207501 4362207501 (limbs [295786025979137,0xd0d060605050303]) [(1634,94703634,(limbs [4587049847552,0x2683402890c009a4,0x2003c60800698280,0x7550a01794280221])),(1858,99946514,(limbs [75154224702294432,0xd00a242401c9010a,0xc20042af8010a320,0x428a80800f18200,0x1a60a00884100051])),(1872,99946514,(limbs [75154224685519520,0xb002681c003a0d00,0xa242401c9010ac20,0x428c80800f18200,0x1a60004e10001014]))]),
  (121, LocalCompactPackets.decode 8388615 [1536,272,1024,64,258,768,1160,576,562,417,69] 11146382680319851711 [0,1,2,3,4,5,6,8388608,8388609,8388610,8388611,8388612,8388613,8388614,8388615] 295820335514113 295820335514113 (limbs [296885554384385,0xe0e060605050303]) [(1858,99946514,(limbs [72351483621983136,0xa00a242801c90c00,0xca03003180c003a0,0x3000d80d00f18240,0x1a60407884101c51])),(1872,99946514,(limbs [72351483621983136,0xa00a242801c90c00,0xca02003080c003a0,0x2000c80d00f18240,0x1a607048101c1014]))]),
  (122, LocalCompactPackets.decode 8388615 [1536,272,1024,64,1282,512,1160,576,530,417,85] 18124851040434491391 [0,1,2,3,4,5,6,8388608,8388610,8388612,8388615] 4362207498 4362207498 (limbs [292487440763393,0xa0a060605050303]) [(1618,99946514,(limbs [263197,0x7a01074a8041c9a0,0x1070e82802890800,0xf182001a60900f90,0x2403d40900810100,0x1e40407884101de1])),(1858,99946514,(limbs [72347171474753952,0xa00a242801c90704,0xba00012d807041e0,4600391026180608,0x1a60407884001c51])),(1872,99946514,(limbs [4312227456,0x41d2a0107268041c,0x3a0a00a242801c90,0x704ba01c12a80704,0x1e01c10180800f18,0x2001a60900f901c0,0x38409008101c0014]))]),
  (123, LocalCompactPackets.decode 8388615 [1536,272,1024,64,1282,256,1160,576,562,385,85] 18126960350010537983 [0,1,2,3,4,5,6,8388608,8388610,8388613,8388615] 4446224897 4446224897 (limbs [68098,0xa0a060605050303]) [(1858,987154,(limbs [72347171474753952,0x8049a42011990900,0xca024031809003a0,0x2400d80800f18200,0x1a60007884001c51])),(1872,987154,(limbs [4312227456,0x41d2a0107268041c,0x3a08049a42011990,0x900ca02403080900,0x3a02400c80800f18,0x2001a60700f901c0,0x38407008101c0014]))]),
  (124, LocalCompactPackets.decode 131079 [1536,272,1024,64,1282,768,1032,512,562,417,85] 16404335245223526399 [0,1,2,3,4,5,6,131072,131073,131077,131079] 4362207498 4362207498 (limbs [292487440763393,0xa0a060605050303]) [(1802,268382226,(limbs [16,0x9005e82802890a00,0x724041f280107c60,0x41ce80107360100,0x8f30700884000051])),(1816,268382226,(limbs [271361,0x7a09004a82802890,0xa00724041f280107,0xc20041ce80107320,0x1c03e40000e101c0,0x20400000501008f3])),(1858,268382226,(limbs [74591274736290208,0xa00a242801c90107,0xca0041f1801073a0,0x41cd80204e58081,0x460700884000051])),(1872,268382226,(limbs [4445986434,0x4012a08002682000,0x3a0a00a242801c90,0x107ca0041f080107,0x3a0041cc80204e58,0x810460700f90000,0x3840700810000014]))]),
  (125, LocalCompactPackets.decode 33554439 [1536,272,1024,64,1282,768,136,576,562,417,21] 16262471857012277247 [0,1,2,3,4,5,6,33554432,33554434,33554435,33554436,33554439] 4446224897 4446224897 (limbs [68356,0xb0b060605050303]) [(1858,331794,(limbs [16,0x10a2682402890900,0x724041f280107c60,0x41ce80107360201,0x1a60700884000051])),(1872,331794,(limbs [263208,0x9a010a0e82402890,0x900724041f280107,0xc20041ce80107320,0x2011a60a00f90280,0x3840700810000014]))]),
  (126, LocalCompactPackets.decode 8388615 [1536,272,1024,64,1282,768,1160,64,562,289,85] 18133715440180396031 [0,1,2,3,4,5,6,8388608,8388609,8388613,8388614,8388615] 1142612558337 1142612558337 (limbs [4479650561,0xb0b060605050303]) [(1858,16060434,(limbs [72347171474753952,0x8049242010b90900,0xca024031808003a0,0x2000d80a00f18280,0x1a60007884001c51])),(1872,16060434,(limbs [4312227456,0x41d2a0107268041c,0x3a08049242010b90,0x900ca02403080800,0x3a02000c80a00f18,0x2801a60700f901c0,0x38407008101c0014]))]),
  (127, LocalCompactPackets.decode 33554439 [1536,272,1024,64,1282,768,1160,576,50,161,85] 18133746121715482623 [0,1,2,3,4,5,6,33554432,33554434,33554435,33554436,33554439] 4446224897 4446224897 (limbs [68356,0xb0b060605050303]) [(1858,331794,(limbs [4415720915207,0x2682411c9010a3a0,0x428d80800f18200,0x1a60a00884000051])),(1872,331794,(limbs [263197,0x7a01074a8041c9a0,0x1070e82411c9010a,0x3a00428c80800f18,0x2001a60a00f901c0,0x3840a00810000014]))]),
  (138, LocalCompactPackets.decode 147463 [1536,272,1024,192,1026,512,1160,584,514,417,85] 11211737647732985727 [0,1,2,3,4,5,6,16386,16389,16391,131073,131078,131079,147456,147459,147462,147463] 292500158810888 299114541875713 (limbs [4563666187,0x60809020c010c0c,0x909060605050303]) [(1610,21480079378,(limbs [16,0xe005e838009a1000,0xa243403c60d00ed8,0x3401a60d00618340,0x1d30d0060c3c0221])),(1674,21480079378,(limbs [16,0xe005e84002891000,0x924003747000dcdc,0x3537000d3dc340,0x1d300003cc3c0221])),(1730,21480079378,(limbs [276481,0x7a0e002684002891,0x924003747000d,0xb1c003537000d11c,0x3403c60000e58340,0x1a600001183c0221]))]),
  (140, LocalCompactPackets.decode 200711 [1536,272,1024,192,1026,768,1032,520,546,417,85] 9485029403033837439 [0,1,2,3,4,5,6,4098,4101,4102,65539,65540,65542,69638,69639,131075,131077,135173,135175,196610,196611,196615,200706,200708,200709,200710,200711] 79398006898231041 79398006897771009 (limbs [299153264742161,0x9110a0d080d1515,0x12120e0e15041202,0xe01060605050303]) [(1578,384395110812110866,(limbs [0x468017a1a00a24,0x6402691301d544c0,0x5e5170074c580221])),(1802,768613955885748242,(limbs [17,0xa005e86802891800,0x724044f080113be0,0x44cc801132a05c0,0x1d316008841c0051])),(1816,768613955885748242,(limbs [4844747888640,0x4a86802891800724,0x44f080113320001,0xf8400070505c01d3]))]),
  (156, LocalCompactPackets.decode 10616839 [1536,272,1024,192,258,768,1032,520,562,417,69] 9414766216251702463 [0,1,2,3,4,5,6,131072,131077,131079,2097152,2097154,2097155,2097156,2097157,2228226,2228229,8388608,8388609,8388610,8388611,8388613,8519680,8519685,10485761,10485763,10485767,10616836] 20254678817421724416 1207020290561 (limbs [304672331602458,0x14080c081a040902,0x909060605050303]) [(1802,5844008312850,(limbs [17,86879406630967050,0x724641f281907c60,0x641ce819073606c0,0x1d30f118842c4451])),(1816,5844008312850,(limbs [17,86879406630967050,0x724641f281807c20,0x641ce81207320582,0xe04110b0506c01d3]))]),
  (172, LocalCompactPackets.decode 212999 [1536,272,1024,192,1282,512,1032,520,530,417,85] 16393234576366342143 [0,1,2,3,4,5,6,16384,16387,16391,65540,65541,131077,131079,147463,196610,196613,212994,212996,212997,212999] 298036538379784 296919813587457 (limbs [4480044545,0x30c09040d020d0d,0x909060605050303]) [(1562,711353958418,(limbs [17,0x3005e84c012a1400,0xa243c1fe40f07f50,0x3c1e040f07790480,0x1d311008843c01e1])),(1802,711353958418,(limbs [17,0x3005e85002891400,0x7241c3ee8070fb60,0x1c3c78070f160480,0x1d311008841c0051])),(1816,711353958418,(limbs [281601,0x7a13004a85002891,0x4007241c3ee8000f,0xaa01c3c78000f060,0x3c1fe40007e103c1,0xe0400070504801d3]))]),
  (188, LocalCompactPackets.decode 212999 [1536,272,1024,192,1282,256,1032,520,562,385,85] 16395343885942388735 [0,1,2,3,4,5,6,16384,16387,16391,65540,65541,131077,147460,196608,196613,196615,212992,212996,212997] 1155598518274 1164070617601 (limbs [4564452111,0xc080b0810020904,0x909060605050303]) [(1802,183251238930,(limbs [17,0x3005e8480a691202,0x664203b28080ec60,0x2038e8080e360480,0x1d311008841c0051])),(1816,183251238930,(limbs [281601,0x7a13004a8480a691,0x202664203b28080e,0xc202038e8080e320,0x381fe40007e10381,0xe0400070504801d3]))]),
  (205, LocalCompactPackets.decode 212999 [1536,272,1024,192,1282,768,8,520,562,417,21] 16260237649854398463 [0,1,2,3,4,5,6,16384,16385,16387,65542,65543,131075,147459,147463,196608,196609,196612,212992,212993,212995,212998] 1168449735172 1155514237441 (limbs [4530767373,0xc0a090a0e040b01,0xb0b060605050303]) [(1802,4026863634,(limbs [17,0x3042685002891400,0x724203f28080fc60,0x203ce8080f360540,0x1d312008841c0051])),(1816,4026863634,(limbs [281616,0x9a13040e85002891,0x400724203f28080f,0xc20203ce8080f320,0x441fe40407e103c1,0xe0400070505401d3]))]),
  (206, LocalCompactPackets.decode 75628551 [1536,272,1024,192,1282,768,1032,8,562,289,85] 16404333183739887615 [0,1,2,3,4,5,6,131072,131075,131079,8388609,8388613,8388614,8519681,8519686,8519687,67108864,67108868,67108869,75497472,75497473,75497477,75497479,75628544] 304637970876418 304624984916481 (limbs [68629,0xb0e161603151208,0xb0816020f010904,0x909060605050303]) [(1802,4312994789265426,(limbs [16,0x8135e83446490d11,0x2e4541f281507c60,0x501ce80a07360384,0x1d30713884004c51])),(1816,4312994789265426,(limbs [270413,0x7a08134a83446490,0xd112e4541f281507,0xc20501ce81407320,0x5c03e41300e105c0,0x20413000503841d3]))]),
  (207, LocalCompactPackets.decode 131079 [1536,272,1024,192,1282,768,1032,520,50,161,85] 16402129657647333375 [0,1,2,3,4,5,6,131074,131075,131076,131079] 4429447681 4429447681 (limbs [68100,0xa0a060605050303]) [(1802,331794,(limbs [0x420017a0804724,0x424e801093601c0,0x1d30900884000051])),(1816,331794,(limbs [16,0x8005e820012a0804,0x7240424e80109320,0x2403e40000e10240,0x20400000501c01d3]))])]

def codes := entries.map Prod.fst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 4 codes = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma facts : ∀ z ∈ codes, atCode 4 z :=
  entries_sound 4 entries (by decide +kernel)

end LocalLightBand4

namespace LocalLightBand5
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def entries : List (ℕ × HPacket) := [
  (104, LocalCompactPackets.decode 2097159 [1536,272,32,128,1026,772,1152,584,546,417,81] 9942153569345576055 [0,1,2,3,4,5,6,2097152,2097154,2097156,2097157,2097158,2097159] 1146924302849 1146924302849 (limbs [4496428033,0xc0c060605050303]) [(1698,16060434,(limbs [16,0xb01568101e890407,0x9a4101e4904077e4,0x20034708004dc280,0x3650a00854240221]))]),
  (109, LocalCompactPackets.decode 69206023 [1536,272,32,128,1282,772,128,584,562,417,17] 16285016251951545591 [0,1,2,3,4,5,6,2097152,2097153,2097158,2097159,67108866,67108869,67108871,69206016,69206017,69206021,69206022] 1146890488841 1151202492929 (limbs [67084,0x5090d020a010d0d,0xa0a060605050303]) [(433,1347424274,(limbs [16,0xe00ca03803080e00,0xba03802a81100d1c,0x3c03650f00ad4301,0xfe40c07e104003f0]))]),
  (120, LocalCompactPackets.decode 33554439 [1536,272,32,64,1026,772,1160,576,546,417,81] 11234669070281448567 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554437,33554438,33554439] 294716512141825 294716512141825 (limbs [295786025979137,0xd0d060605050303]) [(1634,327698,(limbs [4467258426375,0x1a83002890c009a4,0x2403c608006982c0,0x3650b00854280221]))]),
  (126, LocalCompactPackets.decode 100663303 [1536,272,32,64,1282,772,1160,64,562,289,81] 18151738643359857911 [0,1,2,3,4,5,6,33554432,33554438,33554439,67108866,67108868,67108869,67108871,100663297,100663301,100663303] 1142730524673 299118836843009 (limbs [4563666444,0x5080d0209010d0d,0x909060605050303]) [(369,1347424274,(limbs [16,0xb07ca02c1f080b07,0xba02c1ea81000f18,0x3c03650c00ad4380,0x3e40e00e103c03f0]))]),
  (140, LocalCompactPackets.decode 65543 [1536,272,32,192,1026,772,1032,520,546,417,81] 9503052606213299319 [0,1,2,3,4,5,6,65538,65539,65540,65542,65543] 1142595781121 1142595781121 (limbs [4479781633,0xb0b060605050303]) [(1578,5574674,(limbs [0x428055a0a00a24,0x2802690800d94200,0x215090074c1c0221]))])]

def codes := entries.map Prod.fst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 5 codes = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma facts : ∀ z ∈ codes, atCode 5 z :=
  entries_sound 5 entries (by decide +kernel)

end LocalLightBand5

namespace LocalLightBand6
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def entries : List (ℕ × HPacket) := [
  (120, LocalCompactPackets.decode 52953095 [1536,272,1056,0,1026,772,1152,576,546,417,85] 10225862753696325503 [0,1,2,3,4,5,6,524291,524293,2097153,2097157,2621440,2621441,2621444,2621445,2621447,16777219,16777222,17301507,17301511,33554434,33554438,50331648,50331650,50331652,50331654,50331655,52953092] 309048969660672 309040311960065 (limbs [69657,0xa19081911120812,0x150e110e070e1a1a,0x13130f0f13040f02,0x1a01060605050303]) [(1634,(limbs [15,0x5ff00f120f05012]),(limbs [4640065850646,0x268642e89190b9a4,0x5c27b614096186c0,0x3651b008546c0221])),(1698,(limbs [15,0x5ff00f120f05012]),(limbs [16,0xe165e8642e89190b,0x9a4602e49180b7e4,0x30533709143dc6c0,0x3651b008546c0221]))]),
  (124, LocalCompactPackets.decode 35684359 [1536,272,1056,0,1282,772,1024,512,562,417,85] 16566473636491821055 [0,1,2,3,4,5,6,32771,32775,2097152,2097157,2097159,2129920,2129925,33554432,33554438,33554439,33587200,33587206,35684352] 4295952903 298010718503425 (limbs [287037010675210,0x30a060705070804,0xb02100110100b0b,0x808060605050303]) [(1586,428106191073181714,(limbs [75732567827124897,0x209a244826691300,0xd944c02151109f90,0x4427d41109810442,0x5e413008844401e1])),(1798,428106191073181714,(limbs [75732567827125665,0x209a244825c90911,0xca024471809113a0,0x2444d80e0ce88003,0xa21300884240051])),(1812,428106191073181714,(limbs [4514012803,0x4395a0d0e4a83439,0xa1209a244825c90,0x911ca02447080911,0x3a00044c81109f90,0x3827841109810002,0x4140e0ce880030a2])),(1826,428106191073181714,(limbs [73957585789082,0x2448266912097244,0x825990911ca02447,0x180911ba02446d80,0x9113a02444d80911,0x1e02444581300d94,0x3002b51300854300,0x251300884240051])),(1840,428106191073181714,(limbs [0x10d0e5e834392a12,0x9a2448266912097,0x244825990911ca02,0x447080911ba02446,0xa809113a00044c80,0x9111e00044181300,0xd943002b51300854,0x3000251109f90382,0x7841109810002414]))]),
  (137, LocalCompactPackets.decode 2097159 [1536,272,1056,128,2,772,1152,584,546,417,69] 10158326351456607295 [0,1,2,3,4,5,6,2097152,2097153,2097154,2097158,2097159] 4463002113 4463002113 (limbs [68353,0xb0b060605050303]) [(1698,983058,(limbs [16,0x8044a8081e890207,0x9a4081e4902077e4,0x20034708004dc240,0x3650900854280221]))]),
  (138, LocalCompactPackets.decode 2752519 [1536,272,1056,128,1026,516,1152,584,514,417,85] 10202940126691037055 [0,1,2,3,4,5,6,131072,131078,131079,524289,524291,2097153,2097155,2621440,2621441,2621443,2621447,2752512,2752515,2752518] 1168433088516 1168365584897 (limbs [4581295632,0xd080b0811040901,0x909060605050303]) [(1670,331794,(limbs [4724488803072,0x568203a89080e924,0x3c1f470f074dc104,0xba20412288500221])),(1698,331794,(limbs [17,0x3005e8203a89080e,0x9a4203a49080e7e4,0x3c1f470f074dc481,0x2b51204094500221]))]),
  (139, LocalCompactPackets.decode 2097159 [1536,272,1056,128,1026,260,1152,584,546,385,85] 10203351798903707519 [0,1,2,3,4,5,6,2097153,2097154,2097155,2097156,2097157,2097159] 1146907525633 1146907525633 (limbs [4496559106,0xc0c060605050303]) [(1698,18,(limbs [0x424017a020a9a4,0x829f90b00d1c1c0,0x1370804854200221]))]),
  (140, LocalCompactPackets.decode 65543 [1536,272,1056,128,1026,772,1024,520,546,417,85] 9647167793765261183 [0,1,2,3,4,5,6,65538,65542,65543] 4362207497 4362207497 (limbs [291387912358145,0x909060605050303]) [(1578,99946514,(limbs [0x424017a0800a24,0x2002690700d941c0,0x215040160c1c0221])),(1698,99946514,(limbs [16,0x9005e82002890800,0x9a41c024907007e4,0x412c7010411c1c0,0x36507008541c0221]))]),
  (141, LocalCompactPackets.decode 2097159 [1536,272,1056,128,1026,772,128,584,546,417,21] 9653923193190653823 [0,1,2,3,4,5,6,2097152,2097154,2097157,2097159] 4446224897 4446224897 (limbs [68098,0xa0a060605050303]) [(1698,18,(limbs [16,0x804268081e890207,0x9a4081e4902077e4,0x24034709004dc200,0x3650800854200221]))]),
  (142, LocalCompactPackets.decode 2097159 [1536,272,1056,128,1026,772,1152,72,546,289,85] 10223608891862654847 [0,1,2,3,4,5,6,2097153,2097154,2097155,2097156,2097158,2097159] 1146907525633 1146907525633 (limbs [4496559105,0xc0c060605050303]) [(1698,983058,(limbs [0x424017a020a924,0x829f907044dc2c0,0x3650800854200221]))]),
  (143, LocalCompactPackets.decode 2752519 [1536,272,1056,128,1026,772,1152,584,34,161,85] 10229955168187686783 [0,1,2,3,4,5,6,131072,131078,131079,524289,524291,524293,2097153,2097155,2097157,2621441,2621443,2621444,2621445,2621447,2752515,2752518] 302438930841608 302438846562817 (limbs [4631823891,0x6110f080e080c08,0xb08140414020901,0x909060605050303]) [(1187,331794,(limbs [0x454017a15005a8,0x4c1f471600d94580,0x2211207fc0481e90])),(1698,331794,(limbs [17,0x5005e81c49c90712,0x6641c48b90712024,0x4c1f4710074dc580,0x3651600854580221]))]),
  (189, LocalCompactPackets.decode 69206023 [1536,272,1056,128,1282,260,128,584,562,385,21] 16546214481496700927 [0,1,2,3,4,5,6,2097152,2097157,2097159,67108865,67108868,67108870,67108871,69206018,69206022,69206023] 1142730524674 299118836843009 (limbs [4563666188,0x60809020d010d0d,0x909060605050303]) [(405,21480079378,(limbs [0x43803280e00c20,0x4003470b07f902c1,0xf840c07e883c03f0]))])]

def codes := entries.map Prod.fst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 6 codes = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma facts : ∀ z ∈ codes, atCode 6 z :=
  entries_sound 6 entries (by decide +kernel)

end LocalLightBand6

namespace LocalLightBand7
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def entries : List (ℕ × HPacket) := [
  (137, LocalCompactPackets.decode 50348039 [1536,272,1056,64,2,772,1160,576,546,417,69] 11450841852392479807 [0,1,2,3,4,5,6,16384,16390,16391,16777217,16777221,33554437,33570817,50331650,50331652,50331653,50331655,50348033,50348035,50348037,50348038,50348039] 77421067861884936 302434551595521 (limbs [305681698719248,0xc080b0811020901,0x909060605050303]) [(1634,983058,(limbs [4519331759887,0xe84c028913009a4,0x5003c61200698381,0xf650e07854540221]))]),
  (138, LocalCompactPackets.decode 33554439 [1536,272,1056,64,1026,516,1160,576,514,417,85] 11495455627626909567 [0,1,2,3,4,5,6,33554432,33554433,33554436,33554438,33554439] 4362207499 4362207499 (limbs [293586969168641,0xb0b060605050303]) [(1606,983058,(limbs [16,0x2075e8081d5a0207,0x268081c6a0b00a24,0x2003c60800698240,0x3a20400288280221])),(1634,983058,(limbs [4432900784647,0x2682c02890b009a4,0x2003c60800698001,0x2b50004094280221]))]),
  (139, LocalCompactPackets.decode 33554439 [1536,272,1056,64,1026,260,1160,576,546,385,85] 11495867299839580031 [0,1,2,3,4,5,6,33554432,33554433,33554434,33554435,33554439] 4463002113 4463002113 (limbs [68356,0xb0b060605050303]) [(1634,18,(limbs [0x4081d7a0207268,0x2812690800f18200,0x1a60904854240221]))]),
  (140, LocalCompactPackets.decode 16391 [1536,272,1056,64,1026,772,1032,512,546,417,85] 9791265389655072639 [0,1,2,3,4,5,6,16384,16386,16390,16391] 4362207498 4362207498 (limbs [292487440763393,0xa0a060605050303]) [(1578,268382226,(limbs [0x424017a0a00a24,0x2802690207d94081,0xe1504013cc200221])),(1634,268382226,(limbs [4552690108416,0x2682802890a009a4,0x413960104118081,0xf650207854200221]))]),
  (141, LocalCompactPackets.decode 33554439 [1536,272,1056,64,1026,772,136,576,546,417,21] 9649402001443823487 [0,1,2,3,4,5,6,33554433,33554434,33554435,33554436,33554439] 4446224897 4446224897 (limbs [68356,0xb0b060605050303]) [(1634,18,(limbs [0x408289a0900a24,0x2402690704698200,0x3650800854200221]))]),
  (142, LocalCompactPackets.decode 33554439 [1536,272,1056,64,1026,772,1160,64,546,289,85] 11520645584611942271 [0,1,2,3,4,5,6,33554432,33554434,33554437,33554438,33554439] 1142612558337 1142612558337 (limbs [4479650561,0xb0b060605050303]) [(1634,983058,(limbs [4432900784647,0x26820124908047e4,0x2403c60900698280,0x3650800854200221]))]),
  (143, LocalCompactPackets.decode 33554439 [1536,272,1056,64,1026,772,1160,576,34,161,85] 11522470669123559295 [0,1,2,3,4,5,6,33554432,33554433,33554438,33554439] 4446224897 4446224897 (limbs [68097,0xa0a060605050303]) [(1634,983058,(limbs [4432900784647,0x2682011c90804664,0x2003c60800698240,0x3650900854240221]))]),
  (190, LocalCompactPackets.decode 100663303 [1536,272,1056,64,1282,260,1160,64,562,257,85] 18412938522588084223 [0,1,2,3,4,5,6,33554432,33554437,33554439,67108865,67108870,67108871,100663296,100663298,100663301,100663302] 4463462402 1146890748417 (limbs [66827,0x60809020c010c0c,0x909060605050303]) [(341,21480079378,(limbs [0x42c1f280b07c20,0x3c03c60d00f90340,0x3840e00e884003f0]))])]

def codes := entries.map Prod.fst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 7 codes = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma facts : ∀ z ∈ codes, atCode 7 z :=
  entries_sound 7 entries (by decide +kernel)

end LocalLightBand7

namespace LocalLightBand8
open LocalLightPackets LocalHints LocalMixerCertificate LocalPacket

def entries : List (ℕ × HPacket) := [
  (156, LocalCompactPackets.decode 16391 [1536,272,1056,192,2,772,1032,520,546,417,69] 9719225388324330559 [0,1,2,3,4,5,6,16384,16387,16388,16389,16391] 1142595781121 1142595781121 (limbs [4479781634,0xb0b060605050303]) [(1578,16392210,(limbs [0x424092a0a00a24,0x2802690107d94041,0xe15090074c200221]))]),
  (172, LocalCompactPackets.decode 42008583 [1536,272,1056,192,1026,516,1032,520,514,417,85] 9763839163558760319 [0,1,2,3,4,5,6,65536,65541,65543,8388608,8388610,8388614,33554435,33554438,33619971,33619975,41943040,41943042,41943046,41943047,42008580,42008583] 305746089281537 78270998805479937 (limbs [68883,0xe0f141405130e08,0xc08100414010902,0x909060605050303]) [(1550,4223567764914194,(limbs [0x420457a0811568,0x580289150074c481,0xfa20b072883c2a21])),(1578,4223567764914194,(limbs [0x420457a1600a24,0x580269070bad41c2,0xc25150074c3c2a21]))]),
  (188, LocalCompactPackets.decode 65543 [1536,272,1056,192,1026,260,1032,520,546,385,85] 9764250835771430783 [0,1,2,3,4,5,6,65537,65540,65541,65543] 4446224897 4446224897 (limbs [68098,0xa0a060605050303]) [(1578,18,(limbs [4,0x24017a09029a41c0,0xa15080074c1c0221]))]),
  (205, LocalCompactPackets.decode 65543 [1536,272,1056,192,1026,772,8,520,546,417,21] 9647167794285944703 [0,1,2,3,4,5,6,65537,65539,65542,65543] 1138300813825 1138300813825 (limbs [4463004161,0xa0a060605050303]) [(1578,327698,(limbs [0x41c109a0800a24,0x2002690700d941c0,0x215090074c1c0221]))]),
  (206, LocalCompactPackets.decode 100679687 [1536,272,1056,192,1026,772,1032,8,546,289,85] 9791263328171433855 [1,2,3,4,5,6,16384,16387,16391,33554433,33554437,33554438,33570817,33570822,33570823,67108864,67108868,67108869,100663296,100663301,100663303] 302434635810561 302421649850624 (limbs [68371,0xa0d141402131107,0xa0714010e000803,0x808050504040202]) [(1578,4312994789265426,(limbs [0x41c497a0c10924,0x3041f91306d94241,0xa150d0f74c303e21]))]),
  (207, LocalCompactPackets.decode 65543 [1536,272,1056,192,1026,772,1032,520,34,161,85] 9790854205055410047 [0,1,2,3,4,5,6,65538,65539,65541,65543] 1138300813825 1138300813825 (limbs [4463004162,0xa0a060605050303]) [(1578,18,(limbs [0x420017a0704724,0x1c11990900d94240,0x215070074c240221]))])]

def codes := entries.map Prod.fst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma domain : covers 8 codes = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma facts : ∀ z ∈ codes, atCode 8 z :=
  entries_sound 8 entries (by decide +kernel)

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



end MixerProof

open MixerProof

theorem mixer : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x6 : ℕ) => (x6 / (11 : ℕ), x6 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x4 < x5 →           PEqualNP.TopForm.junk x1 x3 = {x4, x5} →             PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →               have x12 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;               have x13 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;               have x14 : Finset ℕ := PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3;               have x15 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;               (∀ x16 ∈ x15,                   have x18 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x16;                   (∀ x19 ∈ x18 (0 : Fin (2 : ℕ)), ∀ x21 ∈ x18 (1 : Fin (2 : ℕ)), x1.Adj x19 x21) ∧ ((x18 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x18 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →                 (∀ (x17 x18 : Fin (11 : ℕ)), s(x17, x18) ∈ x12 → ∃ x20 ∈ x15, ∃ (x21 : Fin (2 : ℕ)), ∃ x22 ∈ PEqualNP.TopForm.junk x1 x3, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x20 (PEqualNP.EdgeOwnership.pairInput x17 x18) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x20 x21) x22 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x22 (PEqualNP.EdgeOwnership.pairInput x17 x18) = Bool.true) → x3.size ≤ (21 : ℕ) → x12.card = (3 : ℕ) → ∀ (x20 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x12) x20 → (4 : ℕ) ≤ x20.card → x20.card ≤ (x15 \ x13).card → (0 : ℕ) < (2 : ℕ) * x13.card + x14.card → (x15 \ x13).card + (2 : ℕ) * x13.card + x14.card ≤ x3.size + x12.card - (17 : ℕ) → False := by
  exact LocalFromDeck.finish LocalLightFullDeck.checked

namespace Budget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace S90


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

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

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

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

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

open PEqualNP.EdgeOwnership

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

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

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

open PEqualNP.TopForm in
lemma top_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (a : ℕ) (ha : a ∈ tops G C) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) ∧
    (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
    ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
    intro u hu v hv
    simp only [side, e0] at hu
    simp only [side, e1] at hv
    exact side_adj G (graphFun G ∅) (fun u v h => (graphFun_pair G u v).mp h) a halen hop hbel
      p q hin hp hq u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)
  refine ⟨?_, hadj, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu hv
    exact G.irrefl (hadj u hu u hv)
  · by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
    have hsub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj x hx w hw, hadj y hy w hw⟩
    have h5 := Finset.card_le_card hsub
    have h6 := h4 x y hxy
    omega

open PEqualNP.TopForm in
lemma off_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C) (u v : Fin n)
    (huv : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
      gateVal n C a (pairInput u v) = true ∧
      OrReaches n C (opnd C a b) h ∧
      gateVal n C h (pairInput u v) = true := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [Ustar, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv
  obtain ⟨hadj, hns⟩ := huv
  have hF : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
    fun u v h => (graphFun_pair G u v).mp h
  have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
    fun x => congrFun hfun x
  obtain ⟨a, halen, hnor, hreach, hval⟩ :=
    edge_trace G (graphFun G ∅) hF hout u v ((graphFun_pair G u v).mpr hadj)
  have hop : (gateAt C a).op = GateOp.and := by
    rcases hAO _ (gateAt_mem halen) with h | h
    · exact h
    · exact (hnor h).elim
  have hbel : BelowF G C a := fun x hx => below_of_reach (graphFun G ∅) hout a hreach x hx
  have hatop : a ∈ tops G C := by
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨halen, hop, hbel⟩
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hpq := (val_and (n := n) (by simp) halen hop).mp hval
  have hp := hpq p (by rw [hin]; simp)
  have hq := hpq q (by rw [hin]; simp)
  have junk_of : ∀ (w : ℕ) (b : Fin 2), opnd C a b = w → w ∈ (gateAt C a).inputs → w < n + a →
      ∀ h, h < C.gates.length → (gateAt C h).op ≠ GateOp.or →
      Relation.ReflTransGen (OrStep n C) w (n + h) →
      val C (List.ofFn (pairInput u v)) (n + h) = true →
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
        gateVal n C a (pairInput u v) = true ∧
        OrReaches n C (opnd C a b) h ∧
        gateVal n C h (pairInput u v) = true := by
    intro w b hb hwin hwlt h hh hhor hr hv
    have hhand : (gateAt C h).op = GateOp.and := by
      rcases hAO _ (gateAt_mem hh) with h3 | h3
      · exact h3
      · exact (hhor h3).elim
    have hcone : InCone n C h a := operand_cone halen hwin hwlt hr
    have hnb : ¬ BelowF G C h := fun hb2 => hT h hh a halen hhand hb2 hop hcone
    have hdirty : IsDirtyAnd n G C h := by
      unfold IsDirtyAnd IsDirty
      refine ⟨hhand, hh, ?_⟩
      by_contra hne
      apply hnb
      intro x hx
      by_contra hfx
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
    have hjunk : h ∈ junk G C := by
      unfold junk gatesWhere
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
    refine ⟨a, hatop, b, h, hjunk, hval, ?_, hv⟩
    rw [hb]
    exact reach_orReaches hr h rfl hh
  rcases operand_trace (C := C) u v p hp.2 with ⟨t1, ht1, hr1⟩ | ⟨h, hh, hhor, hr, hv⟩
  · rcases operand_trace (C := C) u v q hq.2 with ⟨t2, ht2, hr2⟩ | ⟨h, hh, hhor, hr, hv⟩
    · exfalso
      apply hns
      have hadj12 : G.Adj t1 t2 :=
        side_adj G (graphFun G ∅) hF a halen hop hbel p q hin hp.1 hq.1 t1 t2 hr1 hr2
      have hne : t1 ≠ t2 := G.ne_of_adj hadj12
      have hs : s(u, v) = s(t1, t2) := by
        rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
        · exact (hne (h1.trans h2.symm)).elim
        · rw [h1, h2]
        · rw [h1, h2]; exact Sym2.eq_swap
        · exact (hne (h1.trans h2.symm)).elim
      rw [hs]
      simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
      refine ⟨a, hatop, (t1, t2), ⟨?_, ?_⟩, rfl⟩
      · simp only [side, e0]
        exact reach_mem_orIn t1 hr1
      · simp only [side, e1]
        exact reach_mem_orIn t2 hr2
    · exact junk_of q 1 e1 (by rw [hin]; simp) hq.1 h hh hhor hr hv
  · exact junk_of p 0 e0 (by rw [hin]; simp) hp.1 h hh hhor hr hv

end S90

namespace S98


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)

lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]

lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]

lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · simp only [hgt, ↓reduceIte]; exact hm.2.2.2.2.2 u hgt
  · simp only [hgt, ↓reduceIte]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]

lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

def eraseC (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩

def appOr (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], n + C.gates.length⟩

def truncC (C : Circuit) (m : ℕ) : Circuit :=
  ⟨C.gates.take m, C.output⟩

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma erase_wires (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (x : Fin n → Bool)
    (h : W n C x i = W n C x (n + j) ∨
      ∀ k, j < k → k < C.gates.length → n + j ∉ (gateAt C k).inputs) :
    ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
      W n (eraseC n C j i) x (aliasWire (n + j) i u) = W n C x u := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  have htake : C.gates.take j = pre := by rw [hgs, ← hpre_len]; simp
  have hdrop : C.gates.drop (j + 1) = post := by rw [hgs, ← hpre_len]; simp
  intro u hu
  simp only [W, eraseC, wires_eq_foldl, htake, hdrop]
  conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
  rw [List.foldl_append]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre_len]
  let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hCi : W n C x i = w0.getD i false := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
  have hCj : W n C x (n + j) = bOld := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
  have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
      ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
        vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
    intro vC vD hmv u hu'
    unfold aliasWire
    by_cases hu : u = n + j
    · have hval_eq : w0.getD i false = bOld := by rw [← hCi, ← hCj]; exact hu' hu
      subst hu
      simp only [↓reduceIte]
      rw [hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
    · simp only [hu, ↓reduceIte]
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
      ((post.map (aliasGate (n + j) i)).foldl stepWire w0) := by
    refine foldl_wiresMatch w0 bOld post (post.map (aliasGate (n + j) i)) (stepWire w0 gj) w0 hm0
      (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map, aliasGate, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    refine halias_get vC vD hmv u ?_
    intro hun
    rcases h with h | h
    · exact h
    · exfalso
      have hget : gateAt C (j + 1 + t) = post[t] := by
        rw [gateAt_eq C (j + 1 + t) (by omega)]
        have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; omega) = post[t]'htC := by
          rw [List.getElem_append_right (by omega)]
          have hsub : j + 1 + t - pre.length = t + 1 := by omega
          simp [hsub]
        simpa [hgs] using h1
      exact h (j + 1 + t) (by omega) (by omega) (by rw [hget, ← hun]; exact hu)
  exact halias_get _ _ hmEnd u hu

lemma erase_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (eraseC n C j i).gates.length + 1 = C.gates.length := by
  simp [eraseC]; omega

lemma erase_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : k < j) :
    gateAt (eraseC n C j i) k = gateAt C k := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hk]

lemma erase_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : j ≤ k)
    (hk2 : k + 1 < C.gates.length) :
    gateAt (eraseC n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  have h1 : (List.take j C.gates).length = j := by simp; omega
  have h2 : j + 1 + (k - j) = k + 1 := by omega
  rw [h1, List.getElem?_map, List.getElem?_drop, h2, List.getElem?_eq_getElem hk2]
  rfl

lemma prefix_W (n : ℕ) (pre rest1 rest2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + pre.length) :
    W n ⟨pre ++ rest1, o1⟩ x u = W n ⟨pre ++ rest2, o2⟩ x u := by
  simp only [W, wires_eq_foldl, List.foldl_append]
  have h : u < (pre.foldl stepWire (List.ofFn x)).length := by
    rw [foldl_stepWire_length]; simpa using hu
  rw [foldl_stepWire_getD_lt rest1 (pre.foldl stepWire (List.ofFn x)) u h,
    foldl_stepWire_getD_lt rest2 (pre.foldl stepWire (List.ofFn x)) u h]

lemma erase_W_lt (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool)
    (u : ℕ) (hu : u < n + j) : W n (eraseC n C j i) x u = W n C x u := by
  have h := prefix_W n (C.gates.take j) ((C.gates.drop (j + 1)).map (aliasGate (n + j) i))
    (C.gates.drop j) (aliasWire (n + j) i C.output) C.output x u
    (by rw [List.length_take]; omega)
  have e2 : (⟨C.gates.take j ++ C.gates.drop j, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h

lemma appOr_W_lt (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + C.gates.length) : W n (appOr n C a b) x u = W n C x u := by
  have h := prefix_W n C.gates [⟨GateOp.or, [a, b]⟩] [] (n + C.gates.length) C.output x u hu
  have e2 : (⟨C.gates ++ [], C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma appOr_gateAt_lt (n : ℕ) (C : Circuit) (a b k : ℕ) (hk : k < C.gates.length) :
    gateAt (appOr n C a b) k = gateAt C k := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma appOr_gateAt_last (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appOr n C a b) C.gates.length = ⟨GateOp.or, [a, b]⟩ := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD]

lemma appOr_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    (appOr n C a b).eval (List.ofFn x) = (W n C x a || W n C x b) := by
  have h := W_or n (appOr n C a b) x C.gates.length (by simp [appOr]) (by rw [appOr_gateAt_last])
    a b (by rw [appOr_gateAt_last]) ha hb
  rw [appOr_W_lt n C a b x a ha, appOr_W_lt n C a b x b hb] at h
  exact h

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO n C ∧ ∀ D : Circuit, AO n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    C.gates.length ≤ D.gates.length

def Bel (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∀ x : Fin n → Bool, W n C x (n + j) = true → C.eval (List.ofFn x) = true

lemma alias_lt (w i u N : ℕ) (hu : u < N + 1) (hi : i < w) (hw : w ≤ N) :
    aliasWire w i u < N := by
  unfold aliasWire shiftDown
  split_ifs <;> omega

lemma erase_AO (n : ℕ) (C : Circuit) (j i : ℕ) (hA : AO n C) (hj : j < C.gates.length)
    (hi : i < n + j) : AO n (eraseC n C j i) := by
  intro k hk
  have hlen := erase_length n C j i hj
  by_cases hkj : k < j
  · rw [erase_gateAt_lt n C j i k hj hkj]; exact hA k (by omega)
  · rw [erase_gateAt_ge n C j i k hj (by omega) (by omega)]
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hA (k + 1) (by omega)
    refine ⟨hop, aliasWire (n + j) i a, aliasWire (n + j) i b, by simp [aliasGate, hin], ?_, ?_⟩
    · exact alias_lt (n + j) i a (n + k) (by omega) hi (by omega)
    · exact alias_lt (n + j) i b (n + k) (by omega) hi (by omega)

lemma appOr_AO (n : ℕ) (C : Circuit) (a b : ℕ) (hA : AO n C) (ha : a < n + C.gates.length)
    (hb : b < n + C.gates.length) : AO n (appOr n C a b) := by
  intro k hk
  have hlen : (appOr n C a b).gates.length = C.gates.length + 1 := by simp [appOr]
  by_cases hkl : k < C.gates.length
  · rw [appOr_gateAt_lt n C a b k hkl]; exact hA k hkl
  · have hke : k = C.gates.length := by omega
    subst hke
    rw [appOr_gateAt_last]
    exact ⟨Or.inr rfl, a, b, rfl, ha, hb⟩

lemma trunc_AO (n : ℕ) (C : Circuit) (m : ℕ) (hA : AO n C) (hm : m ≤ C.gates.length) :
    AO n (truncC C m) := by
  intro k hk
  have hk' : k < m := by simp [truncC] at hk; omega
  have h : gateAt (truncC C m) k = gateAt C k := by
    simp [gateAt, truncC, List.getD_eq_getElem?_getD, hk']
  rw [h]; exact hA k (by omega)

lemma trunc_W (n : ℕ) (C : Circuit) (m : ℕ) (x : Fin n → Bool) (u : ℕ) (hm : m ≤ C.gates.length)
    (hu : u < n + m) : W n (truncC C m) x u = W n C x u := by
  have h := prefix_W n (C.gates.take m) [] (C.gates.drop m) C.output C.output x u
    (by rw [List.length_take]; omega)
  have e1 : (⟨C.gates.take m ++ [], C.output⟩ : Circuit) = truncC C m := by simp [truncC]
  have e2 : (⟨C.gates.take m ++ C.gates.drop m, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e1, e2] at h
  exact h

lemma least_out (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false) :
    n ≤ C.output ∧ C.output + 1 = n + C.gates.length := by
  have h1 : n ≤ C.output := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hf⟩ := hV ⟨C.output, h⟩
    have h2 : W n C x C.output = true := (W_input n C x C.output h).trans hx
    have h3 : W n C x C.output = false := hf
    rw [h2] at h3
    exact absurd h3 (by simp)
  have h2 : C.output < n + C.gates.length := by
    by_contra h
    obtain ⟨x, hx⟩ := hT
    have h3 : W n C x C.output = true := hx
    simp only [W] at h3
    rw [getD_ge_length _ _ (by rw [wires_length]; omega)] at h3
    exact absurd h3 (by simp)
  refine ⟨h1, ?_⟩
  by_contra h3
  have hm : C.output - n + 1 < C.gates.length := by omega
  have hfun : ∀ x : Fin n → Bool,
      (truncC C (C.output - n + 1)).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    trunc_W n C (C.output - n + 1) x C.output (by omega) (by omega)
  have h4 := hL.2 _ (trunc_AO n C (C.output - n + 1) hL.1 (by omega)) hfun
  simp [truncC] at h4
  omega

lemma least_read (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j + 1 < C.gates.length) :
    ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  by_contra hno
  push Not at hno
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 j (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j a).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j a (by omega) ha x (Or.inr hno) C.output (by intro h; omega)
  have h1 := hL.2 _ (erase_AO n C j a hL.1 (by omega) ha) hfun
  have h2 := erase_length n C j a (by omega)
  omega

lemma least_nodup (n : ℕ) (C : Circuit) (hL : Least n C) (i j : ℕ) (hij : i < n + j)
    (hj : j < C.gates.length) : ∃ x : Fin n → Bool, W n C x i ≠ W n C x (n + j) := by
  by_contra hsame
  push Not at hsame
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j i).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j i hj hij x (Or.inl (hsame x)) C.output (fun _ => hsame x)
  have h1 := hL.2 _ (erase_AO n C j i hL.1 hj hij) hfun
  have h2 := erase_length n C j i hj
  omega

lemma red (n : ℕ) (C : Circuit) (hA : AO n C) (j r : ℕ) (hr : r < C.gates.length)
    (hmem : n + j ∈ (gateAt C r).inputs) :
    ∃ p, p < n + r ∧
      ∀ x : Fin n → Bool, W n C x (n + j) = false → W n C x p = W n C x (n + r) := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rw [hin] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hop with hop | hop
  · refine ⟨n + j, by rcases hmem with h | h <;> omega, fun x hx => ?_⟩
    rw [W_and n C x r hr hop a b hin ha hb, hx]
    rcases hmem with h | h
    · rw [← h, hx]; simp
    · rw [← h, hx]; simp
  · rcases hmem with h | h
    · refine ⟨b, hb, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp
    · refine ⟨a, ha, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp

lemma two_readers (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hB : Bel n C j) (r1 r2 : ℕ)
    (h12 : r1 < r2) (hr2 : r2 < C.gates.length)
    (hm1 : n + j ∈ (gateAt C r1).inputs) (hm2 : n + j ∈ (gateAt C r2).inputs) : False := by
  have hA := hL.1
  have hj1 : j < r1 := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA r1 (by omega)
    rw [hin] at hm1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
    omega
  obtain ⟨p2, hp2, hv2⟩ := red n C hA j r2 hr2 hm2
  have hA1 := erase_AO n C r2 p2 hA hr2 hp2
  have hl1 := erase_length n C r2 p2 hr2
  have hW1 : ∀ (x : Fin n → Bool) (u : ℕ), u < n + r2 →
      W n (eraseC n C r2 p2) x u = W n C x u := fun x u hu => erase_W_lt n C r2 p2 hr2 x u hu
  have hg1 : gateAt (eraseC n C r2 p2) r1 = gateAt C r1 := erase_gateAt_lt n C r2 p2 r1 hr2 h12
  obtain ⟨p1, hp1, hv1⟩ := red n (eraseC n C r2 p2) hA1 j r1 (by omega) (by rw [hg1]; exact hm1)
  have hA2 := erase_AO n (eraseC n C r2 p2) r1 p1 hA1 (by omega) hp1
  have hl2 := erase_length n (eraseC n C r2 p2) r1 p1 (by omega)
  have ho1 : (eraseC n C r2 p2).output < n + (eraseC n C r2 p2).gates.length :=
    alias_lt (n + r2) p2 C.output _ (by omega) hp2 (by omega)
  have ho2 : (eraseC n (eraseC n C r2 p2) r1 p1).output <
      n + (eraseC n (eraseC n C r2 p2) r1 p1).gates.length :=
    alias_lt (n + r1) p1 (eraseC n C r2 p2).output _ (by omega) hp1 (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
        (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).eval (List.ofFn x) =
        C.eval (List.ofFn x) := by
    intro x
    rw [appOr_eval n _ _ (n + j) x ho2 (by omega)]
    have hj2 : W n (eraseC n (eraseC n C r2 p2) r1 p1) x (n + j) = W n C x (n + j) := by
      rw [erase_W_lt n _ r1 p1 (by omega) x (n + j) (by omega), hW1 x (n + j) (by omega)]
    rw [hj2]
    cases hx : W n C x (n + j)
    · have e2 := erase_wires n C r2 p2 hr2 hp2 x (Or.inl (hv2 x hx)) C.output (fun _ => hv2 x hx)
      have hx1 : W n (eraseC n C r2 p2) x (n + j) = false := by
        rw [hW1 x _ (by omega)]; exact hx
      have e1 := erase_wires n (eraseC n C r2 p2) r1 p1 (by omega) hp1 x (Or.inl (hv1 x hx1))
        (eraseC n C r2 p2).output (fun _ => hv1 x hx1)
      rw [Bool.or_false]
      exact e1.trans e2
    · rw [Bool.or_true]; exact (hB x hx).symm
  have h1 := hL.2 _ (appOr_AO n _ _ (n + j) hA2 ho2 (by omega)) hfun
  have h2 : (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
      (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).gates.length =
      (eraseC n (eraseC n C r2 p2) r1 p1).gates.length + 1 := by simp [appOr]
  omega

lemma one_reader (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j < C.gates.length)
    (hB : Bel n C j) (hne : n + j ≠ C.output) :
    ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
      (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
      (gateAt C r).op = GateOp.or := by
  have hA := hL.1
  obtain ⟨r, hjr, hr, hmr⟩ := least_read n C hL hout j (by omega)
  have huniq : ∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r := by
    intro k hk hmk
    by_contra hkr
    rcases Nat.lt_or_gt_of_ne hkr with h | h
    · exact two_readers n C hL hout j hB k r h hr hmk hmr
    · exact two_readers n C hL hout j hB r k h hk hmr hmk
  refine ⟨r, hr, hmr, huniq, ?_⟩
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rcases hop with hop | hop
  swap
  · exact hop
  exfalso
  have hle : ∀ x : Fin n → Bool, W n C x (n + r) = true → W n C x (n + j) = true := by
    intro x hx
    rw [W_and n C x r hr hop a b hin ha hb] at hx
    have hmr' := hmr
    rw [hin] at hmr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmr'
    rcases hmr' with h | h
    · rw [h]; simp_all
    · rw [h]; simp_all
  by_cases hro : n + r = C.output
  · obtain ⟨x, hx⟩ := least_nodup n C hL (n + j) r (by omega) hr
    apply hx
    cases h1 : W n C x (n + r)
    · cases h2 : W n C x (n + j)
      · rfl
      · have h3 : W n C x C.output = true := hB x h2
        rw [← hro, h1] at h3
        exact absurd h3 (by simp)
    · exact hle x h1
  · obtain ⟨s, hrs, hs, hms⟩ := least_read n C hL hout r (by omega)
    have hv : ∀ x : Fin n → Bool, W n C x (n + j) = false →
        W n C x (n + j) = W n C x (n + r) := by
      intro x hx
      cases h1 : W n C x (n + r)
      · exact hx
      · rw [hle x h1] at hx; exact absurd hx (by simp)
    have hA1 := erase_AO n C r (n + j) hA hr (by omega)
    have hl1 := erase_length n C r (n + j) hr
    have ho1 : (eraseC n C r (n + j)).output < n + (eraseC n C r (n + j)).gates.length :=
      alias_lt (n + r) (n + j) C.output _ (by omega) (by omega) (by omega)
    have hWj : ∀ x : Fin n → Bool, W n (eraseC n C r (n + j)) x (n + j) = W n C x (n + j) :=
      fun x => erase_W_lt n C r (n + j) hr x (n + j) (by omega)
    have hfun : ∀ x : Fin n → Bool,
        (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)).eval (List.ofFn x) =
          C.eval (List.ofFn x) := by
      intro x
      rw [appOr_eval n _ _ (n + j) x ho1 (by omega), hWj x]
      cases hx : W n C x (n + j)
      · rw [Bool.or_false]
        exact erase_wires n C r (n + j) hr (by omega) x (Or.inl (hv x hx)) C.output
          (fun _ => hv x hx)
      · rw [Bool.or_true]; exact (hB x hx).symm
    have hA3 := appOr_AO n _ _ (n + j) hA1 ho1 (by omega)
    have hl3 : (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)).gates.length =
        C.gates.length := by simp [appOr]; omega
    have hL3 : Least n (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)) :=
      ⟨hA3, fun D hD hDf => by
        rw [hl3]; exact hL.2 D hD (fun x => (hDf x).trans (hfun x))⟩
    have hB3 : Bel n (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)) j := by
      intro x hx
      rw [hfun x]
      apply hB x
      rw [appOr_W_lt n _ _ _ x (n + j) (by omega), hWj x] at hx
      exact hx
    refine two_readers n _ hL3 (by simp [appOr]; omega) j hB3 (s - 1) (C.gates.length - 1)
      (by omega) (by rw [hl3]; omega) ?_ ?_
    · rw [appOr_gateAt_lt n _ _ _ (s - 1) (by omega),
        erase_gateAt_ge n C r (n + j) (s - 1) hr (by omega) (by omega)]
      have hs1 : s - 1 + 1 = s := by omega
      rw [hs1]
      simp only [aliasGate, List.mem_map]
      exact ⟨n + r, hms, by simp [aliasWire]⟩
    · have hs2 : C.gates.length - 1 = (eraseC n C r (n + j)).gates.length := by omega
      rw [hs2, appOr_gateAt_last]
      simp

lemma or_children (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (r : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) (hB : Bel n C r) :
    ∃ a b, (gateAt C r).inputs = [n + a, n + b] ∧ a < r ∧ b < r ∧ a ≠ b ∧
      Bel n C a ∧ Bel n C b := by
  obtain ⟨_, a, b, hin, ha, hb⟩ := hL.1 r hr
  have hWr := fun x => W_or n C x r hr hop a b hin ha hb
  have hvar : ∀ c, c < n → (∀ x : Fin n → Bool, W n C x c = true → W n C x (n + r) = true) →
      False := by
    intro c hc hcr
    obtain ⟨x, hx, hf⟩ := hV ⟨c, hc⟩
    have h1 : W n C x c = true := (W_input n C x c hc).trans hx
    have h2 := hB x (hcr x h1)
    rw [hf] at h2
    exact absurd h2 (by simp)
  have hna : n ≤ a := by
    by_contra h
    push Not at h
    exact hvar a h (fun x hx => by rw [hWr x, hx]; rfl)
  have hnb : n ≤ b := by
    by_contra h
    push Not at h
    exact hvar b h (fun x hx => by rw [hWr x, hx]; simp)
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hna
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hnb
  refine ⟨a', b', hin, by omega, by omega, ?_, ?_, ?_⟩
  · intro hab
    subst hab
    obtain ⟨x, hx⟩ := least_nodup n C hL (n + a') r ha hr
    exact hx (by rw [hWr x]; simp)
  · intro x hx; exact hB x (by rw [hWr x, hx]; rfl)
  · intro x hx; exact hB x (by rw [hWr x, hx]; simp)

lemma has_top (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k) :
    ∀ j, j < C.gates.length → Bel n C j →
      ∃ t, t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ Bel n C t ∧ (t = j ∨ Cone t j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hB
    rcases (hL.1 j hj).1 with hop | hop
    · exact ⟨j, hj, hop, hB, Or.inl rfl⟩
    · obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV j hj hop hB
      obtain ⟨t, ht, hopt, hBt, htj⟩ := ih a ha (by omega) hBa
      refine ⟨t, ht, hopt, hBt, Or.inr ?_⟩
      have hmem : n + a ∈ (gateAt C j).inputs := by rw [hin]; simp
      rcases htj with rfl | h
      · exact c1 _ j hj hmem
      · exact c2 t a j hj h hmem

lemma up (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output + 1 = n + C.gates.length)
    (Cone : ℕ → ℕ → Prop)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (t : ℕ) (hTop : ∀ s, s < C.gates.length → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    ∀ d s, s < C.gates.length → C.gates.length - s = d → Cone t s → Bel n C s := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro s hs hd hc
    by_cases hso : n + s = C.output
    · intro x hx
      have h1 : W n C x C.output = true := by rw [← hso]; exact hx
      exact h1
    · obtain ⟨k, hsk, hk, hmk⟩ := least_read n C hL hout s (by omega)
      have hck := c2 t s k hk hc hmk
      have hBk := ih (C.gates.length - k) (by omega) k hk rfl hck
      obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 k hk
      have hopk : (gateAt C k).op = GateOp.or := by
        rcases hop with h | h
        · exact absurd hck (hTop k hk h)
        · exact h
      intro x hx
      apply hBk x
      rw [W_or n C x k hk hopk a b hin ha hb]
      rw [hin] at hmk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmk
      rcases hmk with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp

theorem main_abs (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (hTop : ∀ t s, t < C.gates.length → s < C.gates.length → (gateAt C t).op = GateOp.and →
      Bel n C t → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    (∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r) ∧
    (n ≤ C.output ∧ C.output + 1 = n + C.gates.length) ∧
    (∀ O A : Finset ℕ,
      (∀ k, k ∈ O ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ Bel n C k) →
      (∀ k, k ∈ A ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ Bel n C k) →
      O.card + 1 = A.card) := by
  have hout := least_out n C hL hT hV
  have part1 : ∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r := by
    intro j hj hB hne
    obtain ⟨r, hr, hmr, huniq, hopr⟩ := one_reader n C hL hout.2 j hj hB hne
    refine ⟨r, hr, hmr, huniq, hopr, ?_⟩
    obtain ⟨t, ht, hopt, hBt, htj⟩ := has_top n C hL hV Cone c1 c2 j hj hB
    have hc : Cone t r := by
      rcases htj with rfl | h
      · exact c1 _ r hr hmr
      · exact c2 t j r hr h hmr
    exact up n C hL hout.2 Cone c2 t (fun s hs hops => hTop t s ht hs hopt hBt hops) _ r hr rfl hc
  refine ⟨part1, hout, ?_⟩
  intro O A hO hA
  classical
  have hBo : Bel n C (C.gates.length - 1) := by
    intro x hx
    have h1 : n + (C.gates.length - 1) = C.output := by omega
    rw [h1] at hx
    exact hx
  have hoB : C.gates.length - 1 ∈ O ∪ A := by
    rcases (hL.1 (C.gates.length - 1) (by omega)).1 with h | h
    · exact Finset.mem_union_right _ ((hA _).2 ⟨by omega, h, hBo⟩)
    · exact Finset.mem_union_left _ ((hO _).2 ⟨by omega, h, hBo⟩)
  have hdisj : Disjoint O A := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have e1 := ((hO k).1 h1).2.1
    have e2 := ((hA k).1 h2).2.1
    rw [e1] at e2
    cases e2
  obtain ⟨B, hBdef⟩ : ∃ B, B = (O ∪ A).erase (C.gates.length - 1) := ⟨_, rfl⟩
  have hBmem : ∀ j, j ∈ B ↔ j < C.gates.length ∧ Bel n C j ∧ n + j ≠ C.output := by
    intro j
    rw [hBdef, Finset.mem_erase, Finset.mem_union, hO, hA]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, ?_⟩
      rcases (hL.1 j h1).1 with h | h
      · exact Or.inr ⟨h1, h, h2⟩
      · exact Or.inl ⟨h1, h, h2⟩
  have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := B) (t := O)
    (fun j k => n + j ∈ (gateAt C k).inputs)
  have hleft : ∀ j ∈ B,
      (Finset.bipartiteAbove (fun j k => n + j ∈ (gateAt C k).inputs) O j).card = 1 := by
    intro j hj
    obtain ⟨hj1, hj2, hj3⟩ := (hBmem j).1 hj
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := part1 j hj1 hj2 hj3
    rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext k
    simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hmk⟩
      exact huniq k ((hO k).1 hk).1 hmk
    · rintro rfl
      exact ⟨(hO _).2 ⟨hr, hopr, hBr⟩, hmr⟩
  have hright : ∀ k ∈ O,
      (Finset.bipartiteBelow (fun j k => n + j ∈ (gateAt C k).inputs) B k).card = 2 := by
    intro k hk
    obtain ⟨hk1, hk2, hk3⟩ := (hO k).1 hk
    obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV k hk1 hk2 hk3
    rw [Finset.card_eq_two]
    refine ⟨a, b, hab, ?_⟩
    ext j
    simp only [Finset.bipartiteBelow, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      hin, List.mem_cons, List.not_mem_nil, or_false, hBmem]
    constructor
    · rintro ⟨_, h | h⟩
      · left; omega
      · right; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨by omega, hBa, by omega⟩, Or.inl rfl⟩
      · exact ⟨⟨by omega, hBb, by omega⟩, Or.inr rfl⟩
  rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright] at hcount
  simp only [Finset.sum_const, smul_eq_mul] at hcount
  have hBc : B.card = (O ∪ A).card - 1 := by rw [hBdef]; exact Finset.card_erase_of_mem hoB
  have hU : (O ∪ A).card = O.card + A.card := Finset.card_union_of_disjoint hdisj
  have hpos : 0 < (O ∪ A).card := Finset.card_pos.mpr ⟨_, hoB⟩
  omega

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

lemma inCone_c1 (n : ℕ) (C : Circuit) (hA : AO n C) (i k : ℕ) (hk : k < C.gates.length)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩

lemma inCone_c2 (n : ℕ) (C : Circuit) (hA : AO n C) (t i k : ℕ) (hk : k < C.gates.length)
    (hc : InCone n C t i) (hm : n + i ∈ (gateAt C k).inputs) : InCone n C t k := by
  rw [inCone_iff n C t k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he : n + i - n = i := by omega
  exact ⟨n + i, hm, by omega, hlt, Or.inr (by rw [he]; exact hc)⟩

lemma edge_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) :
    ∃ x : Fin n → Bool, ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  obtain ⟨e, he⟩ := h
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨fun _ => true, u, v, he, rfl, rfl⟩

lemma edge_var (n : ℕ) (G : SimpleGraph (Fin n)) (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  refine ⟨fun w => decide (w = u), by simp, ?_⟩
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha
  subst hb
  exact G.loopless.irrefl _ hab

lemma gf_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  obtain ⟨x, hx⟩ := edge_true n G h
  exact ⟨x, by simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr hx⟩

lemma gf_var (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ graphFun G ∅ x = false := by
  obtain ⟨x, hx, hno⟩ := edge_var n G u
  refine ⟨x, hx, ?_⟩
  simp only [graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨by simp, hno⟩

lemma AO_of_IsAO2 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]; exact List.getElem_mem hk
  have hl := hlen _ hmem
  refine ⟨hao _ hmem, ?_⟩
  match hin : (gateAt C k).inputs, hl with
  | [a, b], _ =>
    exact ⟨a, b, rfl, hrb k hk a (by rw [hin]; simp), hrb k hk b (by rw [hin]; simp)⟩

lemma IsAO2_of_AO (n : ℕ) (C : Circuit) (h : AO n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    exact (h k hk).1
  · intro k hk i hi
    obtain ⟨_, a, b, hin, ha, hb⟩ := h k hk
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    obtain ⟨_, a, b, hin, _, _⟩ := h k hk
    rw [hin]; rfl

theorem main_real (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hne : G.edgeFinset.Nonempty) (hL : PEqualNP.TopForm.IsLeastAO G C)
    (hTF : PEqualNP.TopForm.TopForm G C) :
    (∀ j < C.gates.length, PEqualNP.TopForm.BelowF G C j → n + j ≠ C.output →
      ∃ r, PEqualNP.TopForm.readers n C j = {r} ∧ (gateAt C r).op = GateOp.or ∧
        PEqualNP.TopForm.BelowF G C r) ∧
    PEqualNP.TopForm.readers n C (C.output - n) = ∅ ∧
    (PEqualNP.TopForm.orT G C).card + 1 = (PEqualNP.TopForm.tops G C).card := by
  have hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x =>
    congrFun hL.2.1 x
  have hAO : AO n C := AO_of_IsAO2 n C hL.1
  have hLeast : Least n C := ⟨hAO, fun D hD hDf =>
    hL.2.2 D (IsAO2_of_AO n D hD) (funext fun x => (hDf x).trans (hfun x))⟩
  have hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true := by
    obtain ⟨x, hx⟩ := gf_true n G hne
    exact ⟨x, (hfun x).trans hx⟩
  have hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false := by
    intro u
    obtain ⟨x, hx, hf⟩ := gf_var n G u
    exact ⟨x, hx, (hfun x).trans hf⟩
  have hBel : ∀ j, PEqualNP.TopForm.BelowF G C j ↔ Bel n C j := fun j =>
    ⟨fun h x hx => (hfun x).trans (h x hx), fun h x hx => (hfun x).symm.trans (h x hx)⟩
  obtain ⟨p1, p2, p3⟩ := main_abs n C hLeast hT hV (InCone n C) (inCone_c1 n C hAO)
    (inCone_c2 n C hAO)
    (fun t s ht hs hopt hBt hops => hTF t ht s hs hopt ((hBel t).2 hBt) hops)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hB hne'
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := p1 j hj ((hBel j).1 hB) hne'
    refine ⟨r, ?_, hopr, (hBel r).2 hBr⟩
    ext k
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact huniq k h1 h2
    · rintro rfl
      exact ⟨hr, hmr⟩
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, a, b, hin, ha, hb⟩ := hAO k hk.1
    have h2 := hk.2
    rw [hin] at h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    omega
  · refine p3 _ _ (fun k => ?_) (fun k => ?_)
    · simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]
    · simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]

end S98

theorem cover_g {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset α)
    (hf : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ) (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) :
    f (n + r) ⊆ stops.biUnion f ∧ ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
  have hdown : ∀ k, k ∈ R → f (n + k) ⊆ stops.biUnion f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk u hu
      by_cases hs : k ∈ Z ∨ (g k).op ≠ GateOp.or
      · refine Finset.mem_biUnion.2 ⟨n + k, (hstops _).2 (Or.inr ⟨by omega, ?_, ?_⟩), hu⟩
        · rwa [Nat.add_sub_cancel_left]
        · rwa [Nat.add_sub_cancel_left]
      · have hkZ : k ∉ Z := fun h => hs (Or.inl h)
        have hor : (g k).op = GateOp.or := by
          by_contra h
          exact hs (Or.inr h)
        obtain ⟨w, hw, huw⟩ := (hf k hor u).1 hu
        by_cases hwn : w < n
        · exact Finset.mem_biUnion.2 ⟨w, (hstops _).2 (Or.inl ⟨hwn, k, hk, hkZ, hor, hw⟩), huw⟩
        · have hwk := hback k w hw
          have hweq : n + (w - n) = w := by omega
          have hwR : w - n ∈ R :=
            (hR _).2 (((hR k).1 hk).tail ⟨hkZ, hor, by rwa [hweq]⟩)
          exact ih (w - n) (by omega) hwR (by rwa [hweq])
  have hup : ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
    intro k hk
    have h := (hR k).1 hk
    clear hk
    induction h with
    | refl => exact Finset.Subset.refl _
    | tail _ hbc ih =>
      intro u hu
      exact ih ((hf _ hbc.2.1 u).2 ⟨_, hbc.2.2, hu⟩)
  exact ⟨hdown r ((hR r).2 Relation.ReflTransGen.refl), hup⟩

theorem cover_bound (n : ℕ) (H : SimpleGraph (Fin n)) (T : Finset ℕ) (c : ℕ → Fin n)
    (hcov : ∀ u v : Fin n, H.Adj u v → ∃ a, a ∈ T ∧ (c a = u ∨ c a = v))
    (K : Finset (Fin n)) (hK : IsMinCover H K) : K.card ≤ T.card := by
  classical
  refine (hK.2 (T.image c) ?_).trans Finset.card_image_le
  intro u v huv
  obtain ⟨a, ha, h | h⟩ := hcov u v huv
  · left
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha
  · right
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha

theorem four_split (N : ℕ) (isAnd isOr bel : ℕ → Prop)
    (hAO : ∀ k, k < N → (isAnd k ∧ ¬ isOr k) ∨ (isOr k ∧ ¬ isAnd k))
    (T J O Q : Finset ℕ)
    (hT : ∀ k, k ∈ T ↔ k < N ∧ isAnd k ∧ bel k)
    (hJ : ∀ k, k ∈ J ↔ k < N ∧ isAnd k ∧ ¬ bel k)
    (hO : ∀ k, k ∈ O ↔ k < N ∧ isOr k ∧ bel k)
    (hQ : ∀ k, k ∈ Q ↔ k < N ∧ isOr k ∧ ¬ bel k) :
    T.card + J.card + O.card + Q.card = N := by
  classical
  have h1 : Disjoint T J := by
    rw [Finset.disjoint_left]
    intro k h h'
    exact ((hJ k).1 h').2.2 ((hT k).1 h).2.2
  have h2 : Disjoint (T ∪ J) O := by
    rw [Finset.disjoint_left]
    intro k h h'
    have ho := (hO k).1 h'
    rcases hAO k ho.1 with ha | ha
    · exact ha.2 ho.2.1
    · rcases Finset.mem_union.1 h with h | h
      · exact ha.2 ((hT k).1 h).2.1
      · exact ha.2 ((hJ k).1 h).2.1
  have h3 : Disjoint (T ∪ J ∪ O) Q := by
    rw [Finset.disjoint_left]
    intro k h h'
    have hq := (hQ k).1 h'
    rcases Finset.mem_union.1 h with h | h
    · rcases hAO k hq.1 with ha | ha
      · exact ha.2 hq.2.1
      · rcases Finset.mem_union.1 h with h | h
        · exact ha.2 ((hT k).1 h).2.1
        · exact ha.2 ((hJ k).1 h).2.1
    · exact hq.2.2 ((hO k).1 h).2.2
  have h4 : T ∪ J ∪ O ∪ Q = Finset.range N := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, hT, hJ, hO, hQ]
    constructor
    · rintro (((h | h) | h) | h) <;> exact h.1
    · intro hk
      by_cases hb : bel k
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inl ⟨hk, ha.1, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, ha.1, hb⟩)
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inr ⟨hk, ha.1, hb⟩))
        · exact Or.inr ⟨hk, ha.1, hb⟩
  have h5 := congrArg Finset.card h4
  rw [Finset.card_union_of_disjoint h3, Finset.card_union_of_disjoint h2,
    Finset.card_union_of_disjoint h1, Finset.card_range] at h5
  exact h5

def TwoNe {α : Type} (g : ℕ → Gate) (f : ℕ → Finset α) (k : ℕ) : Prop :=
  ∃ w1 ∈ (g k).inputs, ∃ w2 ∈ (g k).inputs, w1 ≠ w2 ∧ (f w1).Nonempty ∧ (f w2).Nonempty

theorem cone_count2 {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate) (f : ℕ → Finset α)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ)
    (hlen : ∀ k, k ∉ Z → (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)))
    (I : Finset ℕ)
    (hI : ∀ k, k ∈ R → k ∉ Z → (g k).op = GateOp.or → TwoNe g f k → k ∈ I) :
    (stops.filter (fun w => (f w).Nonempty)).card ≤ I.card + 1 := by
  classical
  set E : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or) with hE
  set N : ℕ → Finset ℕ := fun k => (g k).inputs.toFinset.filter (fun w => (f w).Nonempty)
    with hN
  set U : Finset ℕ := insert (n + r) (E.biUnion N) with hU
  set E2 := E.filter (fun k => 2 ≤ (N k).card) with hE2
  set Ene := E.filter (fun k => (f (n + k)).Nonempty) with hEne
  have hE2I : E2 ⊆ I := by
    intro k hk
    simp only [hE2, hE, Finset.mem_filter] at hk
    obtain ⟨⟨hkR, hkZ, hor⟩, h2⟩ := hk
    apply hI k hkR hkZ hor
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (N k).card)
    simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw1 hw2
    exact ⟨w1, hw1.1, w2, hw2.1, hne, hw1.2, hw2.2⟩
  have hNk : ∀ k ∈ E, (N k).card ≤ (if 2 ≤ (N k).card then 1 else 0) +
      (if (f (n + k)).Nonempty then 1 else 0) := by
    intro k hk
    simp only [hE, Finset.mem_filter] at hk
    have hc : (N k).card ≤ 2 := (Finset.card_filter_le _ _).trans
      ((List.toFinset_card_le _).trans (hlen k hk.2.1 hk.2.2))
    have hne : 1 ≤ (N k).card → (f (n + k)).Nonempty := by
      intro h1
      obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < (N k).card)
      simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw
      obtain ⟨u, hu⟩ := hw.2
      exact ⟨u, (hf2 k hk.2.2 u).2 ⟨w, hw.1, hu⟩⟩
    rcases Nat.lt_or_ge (N k).card 1 with h0 | h0
    · omega
    · rw [if_pos (hne h0)]
      split_ifs <;> omega
  have hsum : (E.biUnion N).card ≤ E2.card + Ene.card := by
    calc (E.biUnion N).card ≤ ∑ k ∈ E, (N k).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ E, ((if 2 ≤ (N k).card then 1 else 0) +
          (if (f (n + k)).Nonempty then 1 else 0)) := Finset.sum_le_sum hNk
      _ = E2.card + Ene.card := by
        rw [Finset.sum_add_distrib, hE2, hEne, Finset.card_filter, Finset.card_filter]
  have hUcard : U.card ≤ E2.card + Ene.card + 1 := by
    have hins : U.card ≤ (E.biUnion N).card + 1 := Finset.card_insert_le (n + r) (E.biUnion N)
    omega
  have hmem : ∀ w, (f w).Nonempty → (w = n + r ∨ ∃ k' ∈ E, w ∈ (g k').inputs) → w ∈ U := by
    rintro w hw (h | ⟨k', hk', hin⟩)
    · rw [h]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨k', hk', ?_⟩)
      simp only [hN, Finset.mem_filter, List.mem_toFinset]
      exact ⟨hin, hw⟩
  have hRU : ∀ k, k ∈ R → n + k = n + r ∨ ∃ k' ∈ E, n + k ∈ (g k').inputs := by
    intro k hk
    rcases Relation.ReflTransGen.cases_tail ((hR k).1 hk) with h | ⟨b, hb, hb1, hb2, hb3⟩
    · left
      rw [h]
    · right
      refine ⟨b, ?_, hb3⟩
      rw [hE, Finset.mem_filter]
      exact ⟨(hR b).2 hb, hb1, hb2⟩
  set S2 : Finset ℕ := Ene.image (fun k => n + k) with hS2
  have hS2card : S2.card = Ene.card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  have hdisj : Disjoint (stops.filter (fun w => (f w).Nonempty)) S2 := by
    rw [Finset.disjoint_left]
    intro w hw hw2
    rw [Finset.mem_filter] at hw
    rw [hS2, Finset.mem_image] at hw2
    obtain ⟨k, hk, rfl⟩ := hw2
    rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
    rcases (hstops _).1 hw.1 with ⟨h1, _⟩ | ⟨_, _, h3⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h3
      rcases h3 with h3 | h3
      · exact hk.1.2.1 h3
      · exact h3 hk.1.2.2
  have hsub : (stops.filter (fun w => (f w).Nonempty)) ∪ S2 ⊆ U := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [Finset.mem_filter] at hw
      rcases (hstops _).1 hw.1 with ⟨_, k, hk, hk1, hk2, hk3⟩ | ⟨h1, h2, _⟩
      · refine hmem w hw.2 (Or.inr ⟨k, ?_, hk3⟩)
        rw [hE, Finset.mem_filter]
        exact ⟨hk, hk1, hk2⟩
      · have := hRU _ h2
        rw [Nat.add_sub_cancel' h1] at this
        exact hmem w hw.2 this
    · rw [hS2, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
      exact hmem _ hk.2 (hRU k hk.1.1)
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hS2card] at h3
  have h4 := Finset.card_le_card hE2I
  omega

theorem top_step2 (n : ℕ) (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (Z : Finset ℕ) (ρ : ℕ) (c : Fin n) (E0 : Finset (Sym2 (Fin n)))
    (hZ : ∀ k, k ∈ Z → f (n + k) ⊆ f ρ →
      (∀ v, v ∈ f (n + k) → s(c, v) ∈ E0) ∨ (f (n + k)).card ≤ 1) :
    ∃ Znew : Finset ℕ, Disjoint Z Znew ∧
      (∀ k, k ∈ Znew → (g k).op = GateOp.or ∧ TwoNe g f k ∧ n ≤ ρ ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (ρ - n) k ∧ f (n + k) ⊆ f ρ) ∧
      (((f ρ).image (fun v => s(c, v))) \ E0).card ≤ Znew.card + 1 := by
  classical
  by_cases hρ : ρ < n
  · refine ⟨∅, Finset.disjoint_empty_right _, by simp, ?_⟩
    calc (((f ρ).image (fun v => s(c, v))) \ E0).card
        ≤ ((f ρ).image (fun v => s(c, v))).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ (f ρ).card := Finset.card_image_le
      _ ≤ 1 := hf1 ρ hρ
      _ ≤ (∅ : Finset ℕ).card + 1 := by simp
  · have hρn : n ≤ ρ := Nat.le_of_not_lt hρ
    obtain ⟨r, rfl⟩ : ∃ r, ρ = n + r := ⟨ρ - n, by omega⟩
    have hle : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k → k ≤ r := by
      intro k h
      induction h with
      | refl => exact le_refl _
      | tail _ hbc ih =>
        have := hback _ _ hbc.2.2
        omega
    set R : Finset ℕ := (Finset.range (r + 1)).filter (fun k =>
      Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k) with hRdef
    have hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
      intro k
      rw [hRdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Nat.lt_succ_of_le (hle k h), h⟩
    set stops : Finset ℕ := (Finset.range (n + r + 1)).filter (fun w =>
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) with hsdef
    have hstops : ∀ w, w ∈ stops ↔
        (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
        (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)) := by
      intro w
      rw [hsdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases h with ⟨h1, _⟩ | ⟨h1, h2, _⟩
        · omega
        · have := hle _ ((hR _).1 h2)
          omega
    set Znew : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or ∧ TwoNe g f k)
      with hZn
    obtain ⟨hcov, hup⟩ := cover_g n g hback f hf2 Z r R hR stops hstops
    have hcnt : (stops.filter (fun w => (f w).Nonempty)).card ≤ Znew.card + 1 :=
      cone_count2 n g f hf2 Z (fun k _ h => hlen k h) r R hR stops hstops Znew (by
        intro k hk hkZ hor htwo
        rw [hZn, Finset.mem_filter]
        exact ⟨hk, hkZ, hor, htwo⟩)
    refine ⟨Znew, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro k hk hk2
      rw [hZn, Finset.mem_filter] at hk2
      exact hk2.2.1 hk
    · intro k hk
      rw [hZn, Finset.mem_filter] at hk
      refine ⟨hk.2.2.1, hk.2.2.2, hρn, ?_, hup k hk.1⟩
      rw [Nat.add_sub_cancel_left]
      have hreach : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k →
          Relation.ReflTransGen (fun k k' : ℕ =>
            (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
        intro k h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih => exact ih.tail hbc.2
      exact hreach k ((hR k).1 hk.1)
    · have hsub : ((f (n + r)).image (fun v => s(c, v))) \ E0 ⊆
          (stops.filter (fun w => (f w).Nonempty)).biUnion
            (fun w => ((f w).image (fun v => s(c, v))) \ E0) := by
        intro e he
        rw [Finset.mem_sdiff, Finset.mem_image] at he
        obtain ⟨⟨v, hv, rfl⟩, he0⟩ := he
        obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.1 (hcov hv)
        refine Finset.mem_biUnion.2 ⟨w, Finset.mem_filter.2 ⟨hw, ⟨v, hvw⟩⟩, ?_⟩
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_image_of_mem _ hvw, he0⟩
      have hone : ∀ w, w ∈ stops.filter (fun w => (f w).Nonempty) →
          (((f w).image (fun v => s(c, v))) \ E0).card ≤ 1 := by
        intro w hw'
        have hw := (Finset.mem_filter.1 hw').1
        have himg : ∀ t : Finset (Fin n), t.card ≤ 1 →
            ((t.image (fun v => s(c, v))) \ E0).card ≤ 1 := fun t ht =>
          (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_image_le.trans ht)
        rcases (hstops w).1 hw with ⟨hwn, _⟩ | ⟨hwn, hwR, hw2⟩
        · exact himg _ (hf1 w hwn)
        · have hweq : n + (w - n) = w := by omega
          rcases hw2 with hz | hnor
          · have hsubw : f (n + (w - n)) ⊆ f (n + r) := hup _ hwR
            rcases hZ _ hz hsubw with hall | hc1
            · rw [hweq] at hall
              have hempty : ((f w).image (fun v => s(c, v))) \ E0 = ∅ := by
                rw [Finset.sdiff_eq_empty_iff_subset]
                intro e he
                obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
                exact hall v hv
              rw [hempty]
              simp
            · rw [hweq] at hc1
              exact himg _ hc1
          · have := hf3 _ hnor
            rw [hweq] at this
            exact himg _ this
      calc (((f (n + r)).image (fun v => s(c, v))) \ E0).card
          ≤ ((stops.filter (fun w => (f w).Nonempty)).biUnion
              (fun w => ((f w).image (fun v => s(c, v))) \ E0)).card :=
            Finset.card_le_card hsub
        _ ≤ (stops.filter (fun w => (f w).Nonempty)).card * 1 :=
            Finset.card_biUnion_le_card_mul _ _ _ hone
        _ ≤ Znew.card + 1 := by omega

theorem star_count2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (l : List (Fin n × ℕ))
    (hadj : ∀ p, p ∈ l → ∀ v, v ∈ f p.2 → G.Adj p.1 v) :
    ∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ p, p ∈ l ∧ n ≤ p.2 ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (p.2 - n) k ∧ f (n + k) ⊆ f p.2) ∧
      (l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v)))).card
        ≤ l.length + Z.card := by
  classical
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨Z, hZ1, hZ2⟩ := ih (fun q hq => hadj q (List.mem_cons_of_mem _ hq))
    set E0 := l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v))) with hE0
    obtain ⟨Znew, hd, hn1, hn2⟩ := top_step2 n g hlen hback f hf1 hf2 hf3 (Z ∪ B) p.2 p.1 E0 (by
      intro k hk hsub
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨_, _, _, q, hq, _, _, hfq⟩ := hZ1 k hk
        by_cases hc : q.1 = p.1
        · left
          intro v hv
          rw [hE0]
          refine Finset.mem_biUnion.2 ⟨q, List.mem_toFinset.2 hq, ?_⟩
          rw [← hc]
          exact Finset.mem_image_of_mem _ (hfq hv)
        · right
          by_contra hcard
          have h2 : 1 < (f (n + k)).card := by omega
          obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.1 h2
          have a1 : G.Adj p.1 v := hadj p List.mem_cons_self v (hsub hv)
          have a2 : G.Adj p.1 v' := hadj p List.mem_cons_self v' (hsub hv')
          have b1 : G.Adj q.1 v := hadj q (List.mem_cons_of_mem _ hq) v (hfq hv)
          have b2 : G.Adj q.1 v' := hadj q (List.mem_cons_of_mem _ hq) v' (hfq hv')
          exact h4 p.1 v q.1 v' (fun h => hc h.symm) hne ⟨a1, b1.symm, b2, a2.symm⟩
      · exact Or.inr (hB k hk))
    have hd1 : Disjoint Z Znew := Finset.disjoint_of_subset_left Finset.subset_union_left hd
    refine ⟨Z ∪ Znew, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨h0, h1, ht, q, hq, h2⟩ := hZ1 k hk
        exact ⟨h0, h1, ht, q, List.mem_cons_of_mem _ hq, h2⟩
      · obtain ⟨h1, ht, h2, h3, h5⟩ := hn1 k hk
        refine ⟨?_, h1, ht, p, List.mem_cons_self, h2, h3, h5⟩
        intro hkB
        exact (Finset.disjoint_left.1 hd (Finset.mem_union_right _ hkB)) hk
    · rw [List.toFinset_cons, Finset.biUnion_insert, Finset.card_union_of_disjoint hd1,
        List.length_cons, ← hE0]
      have hsplit : (f p.2).image (fun v => s(p.1, v)) ∪ E0 =
          (((f p.2).image (fun v => s(p.1, v))) \ E0) ∪ E0 := by
        rw [Finset.sdiff_union_self_eq_union]
      have hle := Finset.card_union_le (((f p.2).image (fun v => s(p.1, v))) \ E0) E0
      rw [← hsplit] at hle
      omega

theorem assemble2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (T : Finset ℕ) (o : ℕ → Fin 2 → ℕ)
    (hstar : ∀ a, a ∈ T → (∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) → G.Adj u v) ∧
      ((f (o a 0)).card ≤ 1 ∨ (f (o a 1)).card ≤ 1))
    (Es : Finset (Sym2 (Fin n)))
    (hEs : ∀ e, e ∈ Es → ∃ a, a ∈ T ∧ ∃ u, u ∈ f (o a 0) ∧ ∃ v, v ∈ f (o a 1) ∧ e = s(u, v)) :
    (∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ a, a ∈ T ∧ ∃ b : Fin 2,
        n ≤ o a b ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (o a b - n) k ∧
        f (n + k) ⊆ f (o a b) ∧ (f (o a (1 - b))).card = 1) ∧
      Es.card ≤ T.card + Z.card) ∧
    ∀ (H : SimpleGraph (Fin n)) (K : Finset (Fin n)),
      (∀ u v : Fin n, H.Adj u v → s(u, v) ∈ Es) → IsMinCover H K → K.card ≤ T.card := by
  classical
  by_cases hEe : Es = ∅
  · subst hEe
    refine ⟨⟨∅, by simp, by simp⟩, ?_⟩
    intro H K hH hK
    have h0 := hK.2 ∅ (by
      intro u v huv
      exact absurd (hH u v huv) (Finset.notMem_empty _))
    simp only [Finset.card_empty] at h0
    omega
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hEe
    obtain ⟨_, _, v0, _, _⟩ := hEs e0 he0
    set c : ℕ → Fin n := fun a =>
      if (f (o a 0)).card ≤ 1 then (if h : (f (o a 0)).Nonempty then h.choose else v0)
      else (if h : (f (o a 1)).Nonempty then h.choose else v0) with hc
    set ρ : ℕ → ℕ := fun a => if (f (o a 0)).card ≤ 1 then o a 1 else o a 0 with hρ
    have hkey : ∀ a, a ∈ T → ∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) →
        (c a = u ∧ v ∈ f (ρ a)) ∨ (c a = v ∧ u ∈ f (ρ a)) := by
      intro a ha u hu v hv
      by_cases h0 : (f (o a 0)).card ≤ 1
      · left
        have hne : (f (o a 0)).Nonempty := ⟨u, hu⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h0 _ hne.choose_spec _ hu
        · simp only [hρ, h0, ↓reduceIte]
          exact hv
      · right
        have h1 : (f (o a 1)).card ≤ 1 := by
          rcases (hstar a ha).2 with h | h
          · exact absurd h h0
          · exact h
        have hne : (f (o a 1)).Nonempty := ⟨v, hv⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h1 _ hne.choose_spec _ hv
        · simp only [hρ, h0, ↓reduceIte]
          exact hu
    set T' : Finset ℕ := T.filter (fun a => (f (o a 0)).Nonempty ∧ (f (o a 1)).Nonempty)
      with hT'
    have hT'T : ∀ a, a ∈ T' → a ∈ T := fun a ha => (Finset.mem_filter.1 ha).1
    have hT'card : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hadjc : ∀ a, a ∈ T' → ∀ v, v ∈ f (ρ a) → G.Adj (c a) v := by
      intro a ha' v hv
      have ha := hT'T a ha'
      have hnn := (Finset.mem_filter.1 ha').2
      by_cases h0 : (f (o a 0)).card ≤ 1
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.1
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact (hstar a ha).1 _ hne.choose_spec v hv
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.2
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact ((hstar a ha).1 v hv _ hne.choose_spec).symm
    have hEs' : ∀ e, e ∈ Es → ∃ a, a ∈ T' ∧ ∃ v, v ∈ f (ρ a) ∧ e = s(c a, v) := by
      intro e he
      obtain ⟨a, ha, u, hu, v, hv, rfl⟩ := hEs e he
      have ha' : a ∈ T' := Finset.mem_filter.2 ⟨ha, ⟨u, hu⟩, ⟨v, hv⟩⟩
      rcases hkey a ha u hu v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨a, ha', v, h2, by rw [h1]⟩
      · exact ⟨a, ha', u, h2, by rw [h1]; exact Sym2.eq_swap⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨Z, hZ1, hZ2⟩ := star_count2 n G h4 g hlen hback f hf1 hf2 hf3 B hB
        (T'.toList.map (fun a => (c a, ρ a))) (by
          intro p hp v hv
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
          exact hadjc a (Finset.mem_toList.1 ha) v hv)
      refine ⟨Z, ?_, ?_⟩
      · intro k hk
        obtain ⟨h1, h2, ht, p, hp, h3, h5, h6⟩ := hZ1 k hk
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
        have ha' := Finset.mem_toList.1 ha
        have hnn := (Finset.mem_filter.1 ha').2
        refine ⟨h1, h2, ht, a, hT'T a ha', ?_⟩
        by_cases h0 : (f (o a 0)).card ≤ 1
        · refine ⟨1, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 1 : Fin 2) = 0 := by decide
          rw [e]
          exact ⟨h3, h5, h6, le_antisymm h0 (Finset.card_pos.2 hnn.1)⟩
        · refine ⟨0, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 0 : Fin 2) = 1 := by decide
          rw [e]
          have h1' : (f (o a 1)).card ≤ 1 := by
            rcases (hstar a (hT'T a ha')).2 with h | h
            · exact absurd h h0
            · exact h
          exact ⟨h3, h5, h6, le_antisymm h1' (Finset.card_pos.2 hnn.2)⟩
      · have hsub : Es ⊆ (T'.toList.map (fun a => (c a, ρ a))).toFinset.biUnion
            (fun p => (f p.2).image (fun v => s(p.1, v))) := by
          intro e he
          obtain ⟨a, ha, v, hv, rfl⟩ := hEs' e he
          refine Finset.mem_biUnion.2 ⟨(c a, ρ a), ?_, Finset.mem_image_of_mem _ hv⟩
          exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩)
        have h1 := Finset.card_le_card hsub
        rw [List.length_map, Finset.length_toList] at hZ2
        omega
    · intro H K hH hK
      refine (cover_bound n H T' c ?_ K hK).trans hT'card
      intro u v huv
      obtain ⟨a, ha, w, hw, he⟩ := hEs' _ (hH u v huv)
      refine ⟨a, ha, ?_⟩
      have := Sym2.eq_iff.1 he
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm

lemma gateAt_ge {C : Circuit} {k : ℕ} (hk : C.gates.length ≤ k) :
    gateAt C k = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

lemma orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C p ↔ Relation.ReflTransGen (S90.OrStep n C) p u.val :=
  ⟨S90.mem_orIn_reach u, S90.reach_mem_orIn u⟩

lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [orIn_iff_reach] at ha hb
  have h1 : ∀ c : Fin n, Relation.ReflTransGen (S90.OrStep n C) w c.val → c.val = w := by
    intro c hc
    rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
    · exact h.symm
    · obtain ⟨k, _, h3, _⟩ := hd
      omega
  exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)

lemma orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
        u ∈ PEqualNP.TopForm.orIn n C w := by
  rw [orIn_iff_reach]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
    · have := u.isLt
      omega
    · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
      have hkk : k' = k := by omega
      subst hkk
      exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
  · rintro ⟨hk, hop, w, hw, hlt, hu⟩
    exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)

lemma junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ PEqualNP.TopForm.BelowF G C k := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hc
    apply h3
    intro x hx
    by_contra hf
    exact hc ⟨x, hx, by simpa using hf⟩

lemma opnd_lt {n : ℕ} {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hRB : ReadsBack n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    PEqualNP.TopForm.opnd C a b < n + a := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem ha))
  have hp : p < n + a := hRB a ha p (by rw [hin]; simp)
  have hq : q < n + a := hRB a ha q (by rw [hin]; simp)
  fin_cases b
  · simpa [PEqualNP.TopForm.opnd, hin] using hp
  · simpa [PEqualNP.TopForm.opnd, hin] using hq

lemma rtg_conv {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (r k : ℕ)
    (h : Relation.ReflTransGen (fun k k' : ℕ =>
      (gateAt C k).op = GateOp.or ∧ n + k' ∈ (gateAt C k).inputs) r k)
    (hr : r < C.gates.length) :
    Relation.ReflTransGen (S90.OrStep n C) (n + r) (n + k) ∧ k < C.gates.length := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hr⟩
  | tail _ hbc ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hlt := hRB _ ih2 _ hbc.2
    exact ⟨ih1.tail ⟨_, ih2, rfl, hbc.1, hbc.2, hlt⟩, by omega⟩

lemma two_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hRB : ReadsBack n C) {k : ℕ}
    (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
    (htwo : TwoNe (gateAt C) (PEqualNP.TopForm.orIn n C) k) :
    ¬ PEqualNP.TopForm.BelowF G C k ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 0)).Nonempty ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 1)).Nonempty := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem hk))
  have e0 : PEqualNP.TopForm.opnd C k 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
  have e1 : PEqualNP.TopForm.opnd C k 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
  obtain ⟨w1, hw1, w2, hw2, hne, hn1, hn2⟩ := htwo
  have hw1lt : w1 < n + k := hRB k hk w1 hw1
  have hw1m := hw1
  rw [hin] at hw1 hw2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1 hw2
  refine ⟨?_, ?_⟩
  · intro hbel
    obtain ⟨u, hu⟩ := hn1
    have hu2 : u ∈ PEqualNP.TopForm.orIn n C (n + k) :=
      (orIn_gate C k u).2 ⟨hk, hor, w1, hw1m, hw1lt, hu⟩
    have hr := (orIn_iff_reach _ u).1 hu2
    have hv := S90.reach_var_val (PEqualNP.EdgeOwnership.pairInput u u) (n + k) u hr
      (S90.pairInput_left u u)
    have hF := hbel _ (by rw [S90.gateVal_eq_val]; exact hv)
    exact G.irrefl ((S90.graphFun_pair G u u).1 hF)
  · rw [e0, e1]
    rcases hw1 with h1 | h1 <;> rcases hw2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn1, hn2⟩
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn2, hn1⟩
    · exact absurd (h1.trans h2.symm) hne

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : PEqualNP.TopForm.NoFourCycle G) (hne : G.edgeFinset.Nonempty)
    (hL : PEqualNP.TopForm.IsLeastAO G C) (hTF : PEqualNP.TopForm.TopForm G C) :
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  classical
  obtain ⟨⟨hAO, hRB, h2⟩, _, _⟩ := id hL
  have hlen : ∀ k, (gateAt C k).op = GateOp.or → (gateAt C k).inputs.length ≤ 2 := by
    intro k _
    by_cases hk : k < C.gates.length
    · rw [h2 _ (S90.gateAt_mem hk)]
    · rw [gateAt_ge (by omega)]
      simp
  have hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k := by
    intro k i hi
    by_cases hk : k < C.gates.length
    · exact hRB k hk i hi
    · rw [gateAt_ge (by omega)] at hi
      simp at hi
  have hf2 : ∀ k, (gateAt C k).op = GateOp.or → ∀ u,
      u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔
        ∃ w ∈ (gateAt C k).inputs, u ∈ PEqualNP.TopForm.orIn n C w := by
    intro k hop u
    rw [orIn_gate]
    constructor
    · rintro ⟨_, _, w, hw, _, hu⟩
      exact ⟨w, hw, hu⟩
    · rintro ⟨w, hw, hu⟩
      have hk : k < C.gates.length := by
        by_contra hk
        rw [gateAt_ge (by omega)] at hw
        simp at hw
      exact ⟨hk, hop, w, hw, hRB k hk w hw, hu⟩
  have hf3 : ∀ k, (gateAt C k).op ≠ GateOp.or →
      (PEqualNP.TopForm.orIn n C (n + k)).card ≤ 1 := by
    intro k hop
    rw [Finset.card_le_one]
    intro a ha
    exact absurd ((orIn_gate C k a).1 ha).2.1 hop
  have h4' : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro a b c d hac hbd ⟨h1, h2', h3, h5⟩
    have hsub : ({b, d} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨h1, h2'.symm⟩
      · exact ⟨h5.symm, h3⟩
    have := (Finset.card_le_card hsub).trans (h4 a c hac)
    rw [Finset.card_pair hbd] at this
    omega
  have hstar : ∀ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C →
      (∀ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) →
        ∀ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) → G.Adj u v) ∧
      ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0)).card ≤ 1 ∨
        (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)).card ≤ 1) := by
    intro a ha
    have hf := S90.top_facts G C h4 hL a (Finset.mem_sdiff.1 ha).1
    exact ⟨hf.2.1, hf.2.2⟩
  have hEs : ∀ e, e ∈ G.edgeFinset \ PEqualNP.TopForm.Ustar G C →
      ∃ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C ∧
        ∃ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧
        ∃ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) ∧ e = s(u, v) := by
    intro e he
    have he' : e ∈ PEqualNP.TopForm.starEdges G C := by
      simp only [PEqualNP.TopForm.Ustar, Finset.mem_sdiff, not_and, not_not] at he
      exact he.2 he.1
    simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_product] at he'
    obtain ⟨a, ha, p, hp, hpe⟩ := he'
    refine ⟨a, ?_, p.1, hp.1, p.2, hp.2, hpe.symm⟩
    rw [Finset.mem_sdiff]
    refine ⟨ha, fun hc => ?_⟩
    simp only [PEqualNP.TopForm.centreless, Finset.mem_filter] at hc
    rcases hc.2 with h | h
    · have := hp.1
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
    · have := hp.2
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
  obtain ⟨⟨Z, hZ1, hZ2⟩, hcov⟩ := assemble2 n G h4' (gateAt C) hlen hback
    (fun w => PEqualNP.TopForm.orIn n C w) (fun w hw => orIn_input C w hw) hf2 hf3 ∅ (by simp)
    (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C) (PEqualNP.TopForm.opnd C)
    hstar (G.edgeFinset \ PEqualNP.TopForm.Ustar G C) hEs
  refine ⟨?_, ?_⟩
  · have hZlam : Z ⊆ PEqualNP.TopForm.lam G C := by
      intro k hk
      obtain ⟨-, hor, htwo, a, ha, b, hnb, hrt, -, hcard⟩ := hZ1 k hk
      have hatop := (Finset.mem_sdiff.1 ha).1
      have halen : a < C.gates.length := by
        simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
          Finset.mem_range] at hatop
        exact hatop.1
      have hlt := opnd_lt h2 hRB halen b
      obtain ⟨hreach, hklen⟩ := rtg_conv C hRB _ k hrt (by omega)
      rw [show n + (PEqualNP.TopForm.opnd C a b - n) = PEqualNP.TopForm.opnd C a b by omega]
        at hreach
      have hOR := S90.reach_orReaches hreach k rfl hklen
      obtain ⟨hnbel, hn0, hn1⟩ := two_facts G C h2 hRB hklen hor htwo
      simp only [PEqualNP.TopForm.lam, PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨hklen, hor, hnbel⟩, hn0, hn1, a, hatop, b, hcard, hOR⟩
    have hAO' : ∀ k, k < C.gates.length →
        ((gateAt C k).op = GateOp.and ∧ ¬ (gateAt C k).op = GateOp.or) ∨
        ((gateAt C k).op = GateOp.or ∧ ¬ (gateAt C k).op = GateOp.and) := by
      intro k hk
      rcases hAO _ (S90.gateAt_mem hk) with h | h
      · exact Or.inl ⟨h, fun h' => by rw [h] at h'; cases h'⟩
      · exact Or.inr ⟨h, fun h' => by rw [h] at h'; cases h'⟩
    have hsplit := four_split C.gates.length (fun k => (gateAt C k).op = GateOp.and)
      (fun k => (gateAt C k).op = GateOp.or) (fun k => PEqualNP.TopForm.BelowF G C k) hAO'
      (PEqualNP.TopForm.tops G C) (PEqualNP.TopForm.junk G C) (PEqualNP.TopForm.orT G C)
      (PEqualNP.TopForm.orN G C)
      (fun k => by simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => junk_iff G C k)
      (fun k => by simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => by simp only [PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
    have hm := (S98.main_real n G C hne hL hTF).2.2
    have hsize : C.size = C.gates.length := rfl
    have hU := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.Ustar G C ⊆ G.edgeFinset from Finset.sdiff_subset)
    have hTc := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.centreless G C ⊆ PEqualNP.TopForm.tops G C from
        Finset.filter_subset _ _)
    have hlam := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.lam G C ⊆ PEqualNP.TopForm.orN G C from
        Finset.filter_subset _ _)
    have hZl := Finset.card_le_card hZlam
    omega
  · intro K hK
    refine hcov _ K ?_ hK
    intro u v huv
    rw [SimpleGraph.deleteEdges_adj] at huv
    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    exact ⟨huv.1, fun h => huv.2 (Finset.mem_coe.2 h)⟩

end Budget

theorem Budget : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C →
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  intro n G _ C h4 hne hL hTF
  exact Budget.main n G C h4 hne hL hTF


namespace Cover

open PEqualNP.EdgeOwnership

def El : List (ℕ × ℕ) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8),
  (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

-- a set of vertices covers every listed edge
abbrev cov (T : Finset (Fin 11)) : Prop :=
  ∀ e ∈ El, (∃ v ∈ T, v.val = e.1) ∨ (∃ v ∈ T, v.val = e.2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tau_dec : ∀ T : Finset (Fin 11), ¬ (T.card ≤ 6 ∧ cov T) := by
  decide +kernel

theorem tau (T : Finset (Fin 11)) (h : cov T) : 7 ≤ T.card := by
  by_contra hc
  exact tau_dec T ⟨by omega, h⟩

theorem hEl : ∀ e ∈ El, e.1 < 11 ∧ e.2 < 11 ∧ e.1 ≠ e.2 := by decide

theorem main : ∀ (D : Finset (Sym2 (Fin 11))) (S : Finset (Fin 11)),
    ((edgeGraph 11 El).deleteEdges ↑D).IsVertexCover ↑S → 7 ≤ S.card + D.card := by
  intro D S hS
  classical
  let T : Finset (Fin 11) := S ∪ D.image (fun e => (Quot.out e).1)
  have hT : cov T := by
    intro e he
    obtain ⟨h1, h2, h3⟩ := hEl e he
    let a : Fin 11 := ⟨e.1, h1⟩
    let b : Fin 11 := ⟨e.2, h2⟩
    have hab : (edgeGraph 11 El).Adj a b := by
      refine ⟨fun h => h3 (congrArg Fin.val h), Or.inl ?_⟩
      exact he
    by_cases hd : s(a, b) ∈ D
    · -- the chosen endpoint of this deleted edge is in T
      obtain ⟨p, hp⟩ : ∃ p : Fin 11 × Fin 11, p = Quot.out (s(a, b) : Sym2 (Fin 11)) := ⟨_, rfl⟩
      have hq : s(p.1, p.2) = s(a, b) := by
        rw [hp]; exact Quot.out_eq (s(a, b) : Sym2 (Fin 11))
      have hmem : p.1 ∈ T :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hd, by rw [hp]⟩)
      rcases Sym2.eq_iff.mp hq with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl ⟨_, hmem, by rw [h]⟩
      · exact Or.inr ⟨_, hmem, by rw [h]⟩
    · have hadj : ((edgeGraph 11 El).deleteEdges ↑D).Adj a b :=
        (SimpleGraph.deleteEdges_adj).mpr ⟨hab, hd⟩
      rcases hS hadj with h | h
      · exact Or.inl ⟨a, Finset.mem_union_left _ h, rfl⟩
      · exact Or.inr ⟨b, Finset.mem_union_left _ h, rfl⟩
  have h7 := tau T hT
  have hc : T.card ≤ S.card + D.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  omega

end Cover

theorem Cover : have x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Finset (Sym2 (Fin (11 : ℕ)))) (x3 : Finset (Fin (11 : ℕ))), (x1.deleteEdges ↑x2).IsVertexCover ↑x3 → (7 : ℕ) ≤ x3.card + x2.card :=
  Cover.main

end PEqualNP.Outside.L_meta_17253_aux
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
namespace PEqualNP.Outside.L_meta_17253_aux
abbrev listedGraph := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
abbrev graphDec : DecidableRel listedGraph.Adj := inferInstance

theorem residualCover (C : Circuit) :
    ∃ K : Finset (Fin 11), IsMinCover (listedGraph.deleteEdges ↑(Ustar listedGraph C)) K := by
  classical
  let H := listedGraph.deleteEdges ↑(Ustar listedGraph C)
  let P (n : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover ↑K ∧ K.card = n
  have ex : ∃ n, P n := ⟨_, Finset.univ, by simp, rfl⟩
  obtain ⟨K,hK,hcard⟩ := Nat.find_spec ex
  exact ⟨K,hK,fun T hT => hcard.trans_le (Nat.find_min' ex ⟨T,hT,rfl⟩)⟩

end PEqualNP.Outside.L_meta_17253_aux

open PEqualNP.Outside.L_meta_17253_aux

theorem PEqualNP.Outside.L_meta_17253 : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → x3.size < (22 : ℕ) → (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) → (PEqualNP.TopForm.Ustar x1 x3).card = (3 : ℕ) → (4 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  intro G decG C eqGraph least top short pair three
  subst G
  have same : decG = graphDec := Subsingleton.elim _ _
  subst decG
  letI : DecidableRel listedGraph.Adj := graphDec
  change (Ustar listedGraph C).card = 3 at three
  obtain ⟨i,j,junkPair,path⟩ := pair
  have order := (PEqualNP.Outside.L_meta_17253_aux.MixerProof.LocalCone.inCone_lt 11 C i j path).1
  have pairCard : (junk listedGraph C).card = 2 := by
    rw [junkPair, Finset.card_pair order.ne]
  have no4 : NoFourCycle listedGraph := by dsimp [listedGraph]; decide +kernel
  have edgeCount : listedGraph.edgeFinset.card = 16 := by dsimp [listedGraph]; decide +kernel
  have hasEdge : listedGraph.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  have shape := PEqualNP.Outside.L_meta_17253_aux.Budget.S90.top_facts listedGraph C no4 least
  have trace := PEqualNP.Outside.L_meta_17253_aux.Budget.S90.off_star listedGraph C least top
  obtain ⟨count,minimum⟩ := PEqualNP.Outside.L_meta_17253_aux.Budget 11 listedGraph C no4 hasEdge least top
  rw [edgeCount,pairCard] at count
  obtain ⟨K,cover⟩ := residualCover C
  have lower := PEqualNP.Outside.L_meta_17253_aux.Cover (Ustar listedGraph C) K cover.1
  have enough := minimum K cover
  have positive : 0 < 2 * (centreless listedGraph C).card + (orN listedGraph C \ lam listedGraph C).card := by
    by_contra! zero
    have empty : centreless listedGraph C = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < (Ustar listedGraph C).card by omega)
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨a,ha,b,g,hg,on,pathJ,onJ⟩ := trace u v he
      have both := PEqualNP.Outside.L_meta_17253_aux.MixerProof.LocalReceiver.sides_nonempty empty ha
      obtain ⟨k,hk,_⟩ := PEqualNP.Outside.L_meta_17253_aux.MixerProof.LocalBefore.earlier_exception
        listedGraph C least.1 ha (shape a ha).2.1 both he on
      have pos : 0 < (orN listedGraph C \ lam listedGraph C).card := Finset.card_pos.mpr ⟨k,hk⟩
      omega
  apply False.elim
  exact PEqualNP.Outside.L_meta_17253_aux.mixer listedGraph C i j rfl least top order junkPair path
    (fun a ha => (shape a ha).2) trace (by omega) three K cover (by omega) enough positive (by omega)

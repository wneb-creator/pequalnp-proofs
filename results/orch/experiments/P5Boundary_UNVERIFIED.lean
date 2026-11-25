import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.P5Boundary

structure Signal where
  value : BitVec 32
  ancestors : BitVec 4
  deriving DecidableEq, BEq

def base (i : BitVec 4) : Signal :=
  ⟨if i = 0 then 2863311530 else
    if i = 1 then 3435973836 else
    if i = 2 then 4042322160 else
    if i = 3 then 4278255360 else
    if i = 4 then 4294901760 else
    if i = 5 then 4291624908 else
    if i = 6 then 4244438268 else
    if i = 7 then 4294966524 else
    if i = 8 then 4294945450 else
    if i = 9 then 4294966010 else
    if i = 10 then 4289396650 else
    if i = 11 then 4294639610 else
    if i = 13 then 4294967295 else 0, 0⟩

def edgeMask (v : BitVec 32) : BitVec 4 :=
  (if v.getLsbD 3 then 1 else 0) |||
  (if v.getLsbD 6 then 2 else 0) |||
  (if v.getLsbD 12 then 4 else 0) |||
  (if v.getLsbD 24 then 8 else 0)

def gate (isAnd : Bool) (a b : Signal) : Signal :=
  let v := if isAnd then a.value &&& b.value else a.value ||| b.value
  ⟨v, a.ancestors ||| b.ancestors ||| (if isAnd then edgeMask v else 0)⟩

def legal (isAnd : Bool) (a b : Signal) : Bool :=
  let own := edgeMask (a.value &&& b.value) &&& ~~~(a.ancestors ||| b.ancestors)
  !isAnd || (own != 0 && (own &&& 12 == 0 || own &&& 9 == 0 || own &&& 3 == 0))

def boundary : List Signal :=
  ((List.range 14).map fun i => base (BitVec.ofNat 4 i)).dedup

def extensions (a b : Signal) : List Signal :=
  gate false a b :: if legal true a b then [gate true a b] else []

def next (xs : List Signal) : List Signal :=
  (xs.flatMap fun a => xs.flatMap fun b => extensions a b).dedup

def misses (xs : List Signal) : Bool :=
  xs.all fun s => s.value != 4291360968

lemma not_initial : misses boundary = true := by decide +kernel

lemma not_one : misses (next boundary) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma not_two : (next boundary).all (fun x => misses (next (x :: boundary))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma not_three : (next boundary).all (fun x =>
    (next (x :: boundary)).all (fun y =>
      (y :: x :: boundary).all (fun z => misses (extensions y z)))) = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_1031.P5Boundary

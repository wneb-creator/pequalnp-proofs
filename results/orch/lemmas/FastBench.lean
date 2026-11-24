import FastProbe

namespace PEqualNP.Outside.L_meta_1677_FastBench
open PEqualNP.Outside.L_meta_1677 PEqualNP.Outside.L_meta_1677_FastProbe

def probe_batchMove (fast : Bool) (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
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
    onMarks (fun c => if fast then fallbackFastAt c i j op ka kb else checkAt c i j op ka kb) mask xs

def probe_batchPair (fast : Bool) (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := probe_batchMove fast b xs i j op
  f false false && f true false && f false true && f true true

def probe_batchRow (fast : Bool) (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  probe_batchMove fast b xs i i 2 false false && probe_batchMove fast b xs i i 2 true true &&
    js.all (fun j => probe_batchPair fast b xs i j 0 && probe_batchPair fast b xs i j 1)

def probe_batchRows (fast : Bool) (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => probe_batchRow fast b xs i js && probe_batchRows fast b xs js

def probe_runBatch (fast : Bool) (k n : Nat) (xs : List NodeContext) :=
    probe_batchRows fast (makeBatch k n xs) xs (List.range n)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem bench_9_plain : probe_runBatch false 9 9 (seedContexts 9 0 16) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem bench_9_fast : probe_runBatch true 9 9 (seedContexts 9 0 16) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem bench_10_plain : probe_runBatch false 10 10 (seedContexts 10 49 16) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem bench_10_fast : probe_runBatch true 10 10 (seedContexts 10 49 16) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem bench_11_plain : probe_runBatch false 11 11 (seedContexts 11 1003 16) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem bench_11_fast : probe_runBatch true 11 11 (seedContexts 11 1003 16) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem bench_12_plain : probe_runBatch false 12 12 (seedContexts 12 901 16) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem bench_12_fast : probe_runBatch true 12 12 (seedContexts 12 901 16) = true := by decide +kernel

end PEqualNP.Outside.L_meta_1677_FastBench

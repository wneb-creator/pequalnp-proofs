import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgeFn (x : Fin 14 → Bool) : Bool :=
  (x 0 && x 8) || (x 0 && x 10) || (x 1 && x 7) || (x 1 && x 13) ||
  (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 7) ||
  (x 3 && x 11) || (x 3 && x 12) || (x 4 && x 10) || (x 4 && x 11) ||
  (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) ||
  (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)

def starCircuit : Circuit :=
  ⟨[⟨.or, [8, 10]⟩, ⟨.and, [0, 14]⟩,
    ⟨.or, [7, 13]⟩, ⟨.and, [1, 16]⟩,
    ⟨.or, [8, 12]⟩, ⟨.or, [18, 13]⟩, ⟨.and, [2, 19]⟩,
    ⟨.or, [7, 11]⟩, ⟨.or, [21, 12]⟩, ⟨.and, [3, 22]⟩,
    ⟨.or, [10, 11]⟩, ⟨.or, [24, 13]⟩, ⟨.and, [4, 25]⟩,
    ⟨.or, [9, 10]⟩, ⟨.or, [27, 12]⟩, ⟨.and, [5, 28]⟩,
    ⟨.or, [8, 9]⟩, ⟨.or, [30, 11]⟩, ⟨.and, [6, 31]⟩,
    ⟨.or, [15, 17]⟩, ⟨.or, [33, 20]⟩, ⟨.or, [34, 23]⟩,
    ⟨.or, [35, 26]⟩, ⟨.or, [36, 29]⟩, ⟨.or, [37, 32]⟩], 38⟩

lemma starCircuit_fanIn : FanInTwo starCircuit := by
  simp [FanInTwo, starCircuit]

lemma starCircuit_size : starCircuit.size = 25 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma starCircuit_eval (x : Fin 14 → Bool) :
    starCircuit.eval (List.ofFn x) = edgeFn x := by
  simp [Circuit.eval, Circuit.wires, starCircuit, GateOp.eval, List.ofFn_succ,
    edgeFn, Bool.and_or_distrib_left, Bool.or_assoc]

lemma upperBound : HasCircuitSize 14 edgeFn 25 :=
  ⟨starCircuit, starCircuit_fanIn, Nat.le_of_eq starCircuit_size, starCircuit_eval⟩

end PEqualNP.Outside.L_meta_9811

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def petersenCircuit : Circuit :=
  ⟨[
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.or, [10, 5]⟩,
    ⟨GateOp.and, [0, 11]⟩,
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.and, [1, 13]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [15, 8]⟩,
    ⟨GateOp.and, [3, 16]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.or, [18, 9]⟩,
    ⟨GateOp.and, [7, 19]⟩,
    ⟨GateOp.or, [6, 5]⟩,
    ⟨GateOp.and, [8, 21]⟩,
    ⟨GateOp.or, [4, 6]⟩,
    ⟨GateOp.and, [9, 23]⟩,
    ⟨GateOp.or, [12, 14]⟩,
    ⟨GateOp.or, [25, 17]⟩,
    ⟨GateOp.or, [26, 20]⟩,
    ⟨GateOp.or, [27, 22]⟩,
    ⟨GateOp.or, [28, 24]⟩
  ], 29⟩

lemma petersenCircuitSize : petersenCircuit.size = 20 := rfl

lemma petersenCircuitMono : Monotone2 petersenCircuit := by
  simp [Monotone2, petersenCircuit]

def petersenRows : List (ℕ × Bool) :=
  [(3, true), (6, true), (12, true), (24, true), (17, true), (33, true), (66, true), (132, true), (264, true), (528, true), (160, true), (640, true), (576, true), (320, true), (288, true), (50, false), (69, false), (104, false), (116, false), (138, false), (201, false), (208, false), (276, false), (385, false), (402, false), (521, false), (548, false), (554, false), (770, false), (773, false)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma petersenCircuitRows : ∀ r ∈ petersenRows,
    petersenCircuit.eval (List.ofFn (fun i : Fin 10 => r.1.testBit i.val)) = r.2 := by
  decide

def petersenFun (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

lemma petersenFunctionRows : ∀ r ∈ petersenRows,
    petersenFun (fun i : Fin 10 => r.1.testBit i.val) = r.2 := by
  decide


def petersenValue (x : Fin 10 → Bool) : Bool :=
  ((((((x 0 && ((x 1 || x 4) || x 5)) || (x 1 && (x 2 || x 6))) || (x 3 && ((x 2 || x 4) || x 8))) || (x 7 && ((x 2 || x 5) || x 9))) || (x 8 && (x 6 || x 5))) || (x 9 && (x 4 || x 6)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma petersenValueEq (x : Fin 10 → Bool) :
    petersenCircuit.eval (List.ofFn x) = petersenValue x := by
  simp [petersenCircuit, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, petersenValue]

lemma bandOr (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma borAnd (a b c : Bool) : ((a || b) && c) = ((a && c) || (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma petersenCircuitCorrect (x : Fin 10 → Bool) :
    petersenCircuit.eval (List.ofFn x) = petersenFun x := by
  rw [petersenValueEq]
  simp only [petersenValue, petersenFun, bandOr, borAnd]
  ac_rfl

end PEqualNP.Outside.L_meta_2590_aux

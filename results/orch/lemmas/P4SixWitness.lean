import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.Pilot64SixWitness

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def circuit : Circuit :=
  { gates :=
      [⟨GateOp.or, [1, 2]⟩,
       ⟨GateOp.and, [1, 3]⟩,
       ⟨GateOp.and, [0, 4]⟩,
       ⟨GateOp.and, [0, 6]⟩,
       ⟨GateOp.and, [4, 7]⟩,
       ⟨GateOp.or, [5, 8]⟩]
    output := 9 }

def bits (mask : Nat) : List Bool :=
  [mask.testBit 0, mask.testBit 1, mask.testBit 2, mask.testBit 3]

def target (mask : Nat) : Bool :=
  (mask.testBit 0 && mask.testBit 1) ||
  (mask.testBit 0 && mask.testBit 2) ||
  (mask.testBit 1 && mask.testBit 3)

def derivativeStep (vd : List Bool × List Bool) (g : Gate) : List Bool × List Bool :=
  let a := g.inputs.getD 0 0
  let b := g.inputs.getD 1 0
  let dv := match g.op with
    | GateOp.and => (vd.1.getD a false && vd.2.getD b false) ||
        (vd.2.getD a false && vd.1.getD b false)
    | GateOp.or => vd.2.getD a false || vd.2.getD b false
    | _ => false
  (vd.1 ++ [g.op.eval (g.inputs.map fun i => vd.1.getD i false)], vd.2 ++ [dv])

def derivative (base seed : Nat) : Bool :=
  let start := (bits (1 <<< base),
    [decide (seed = 0), decide (seed = 1), decide (seed = 2), decide (seed = 3)])
  (circuit.gates.foldl derivativeStep start).2.getD circuit.output false

theorem six_gates : circuit.size = 6 := by decide

theorem computes_target : ∀ mask : Fin 16,
    circuit.eval (bits mask.val) = target mask.val := by decide

theorem binary_distinct : ∀ g ∈ circuit.gates,
    g.inputs.length = 2 ∧ g.inputs.Nodup := by decide

theorem reads_back : ∀ j : Fin 6, ∀ i ∈
    (circuit.gates.getD j.val ⟨GateOp.or, []⟩).inputs, i < 4 + j.val := by decide

theorem derivative_left_zero : derivative 0 1 = false := by decide

theorem derivative_right_zero : derivative 1 0 = false := by decide

end PEqualNP.Outside.Pilot64SixWitness

import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-!
# Reduction for `L-meta-4504`

The target is the edge function of the Petersen graph minus a vertex, on eight inputs, and the
claim that no AND/OR/NOT circuit of fan-in two with at most thirteen gates computes it. The
target function is monotone: every gate of it is an AND or an OR of variables, so no NOT gate
can appear in its own formula.

The cut separates the two ways a hypothetical small circuit can spend its gates on negation:

* `monotone` — the circuit uses no NOT gate at all. This is the combinatorial heart of the
  step: a monotone circuit of at most thirteen gates cannot collect the ten edge terms
  `x_0 x_1`, `x_1 x_2`, `x_2 x_3`, `x_0 x_4`, `x_1 x_5`, `x_2 x_6`, `x_3 x_7`, `x_4 x_6`,
  `x_5 x_7`, `x_7 x_4` together with the two literals `x_0` and `x_3`.
* `notInput` — every NOT gate is a literal negation, reading an input wire.
* `notGate` — some NOT gate negates the output of an earlier gate.

Each case is a statement about circuits only, with no `HasCircuitSize` in it, so the three
hypotheses are three separate problems for the next steps of the cut.
-/

theorem PEqualNP.Outside.R_meta_4504_1
  (monotone : ∀ C : Circuit, FanInTwo C → circuitFun 8 C = (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ))) → C.size ≤ 13 →
    (∀ g ∈ C.gates, g.op ≠ GateOp.not) → False)
  (notInput : ∀ C : Circuit, FanInTwo C → circuitFun 8 C = (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ))) → C.size ≤ 13 →
    (∃ g ∈ C.gates, g.op = GateOp.not ∧ ∃ i ∈ g.inputs, i < 8) → False)
  (notGate : ∀ C : Circuit, FanInTwo C → circuitFun 8 C = (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ))) → C.size ≤ 13 →
    (∀ g ∈ C.gates, g.op = GateOp.not → ∀ i ∈ g.inputs, ¬ i < 8) → False) :
    ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ))) (13 : ℕ) := by
  rintro ⟨C, hFan, hsize, hfun⟩
  have heval : circuitFun 8 C = (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ))) := funext (fun x => hfun x)
  by_cases hneg : ∃ g ∈ C.gates, g.op = GateOp.not
  · by_cases hin : ∃ g ∈ C.gates, g.op = GateOp.not ∧ ∃ i ∈ g.inputs, i < 8
    · exact notInput C hFan heval hsize hin
    · refine notGate C hFan heval hsize ?_
      intro g hg hop i hi hlt
      exact hin ⟨g, hg, hop, i, hi, hlt⟩
  · exact monotone C hFan heval hsize (fun g hg hop => hneg ⟨g, hg, hop⟩)

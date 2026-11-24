import PEqualNP.Defs.NotPremium
import PEqualNP.Defs.NotBracket
import PEqualNP.Defs.SharingOrder

/-!
# The merge cost of one NOT gate

For one function `f : (Fin n → Bool) → Bool` on the root circuit model
(`PEqualNP.CircuitLowerBounds.Circuit`, every gate counted, inputs not counted).

* An UP-SET of inputs is a monotone predicate `U : (Fin n → Bool) → Bool` (`false < true`).
* `A(f, U)`: the least number of gates of a NOT-free circuit (AND and OR, each reading at most
  two wires) with a wire equal to `f` on every input IN `U`. `B(f, U)`: the same, OFF `U`.
  Both are `jointSize` of `Defs/SharingOrder.lean` with one output and the domain `U` or its
  complement.
* `H(U)`: the least number of gates of a NOT-free circuit with a wire equal to `U` everywhere
  (`jointSize` on the whole domain).
* `S1(f) = min over up-sets U of [ max(A(f, U), B(f, U)) + H(U) + 1 ]`, in `ℕ∞`.
* `J_1(f)`: the least number of gates of a circuit of AND, OR and NOT gates, each reading at
  most two wires (`Basis2` of `Defs/NotPremium.lean`), with AT MOST one NOT gate (`notCount` of
  `Defs/NotBracket.lean` at most `1`), whose output computes `f` (`Computes`, one output).
* The MERGE COST `mc(f) = J_1(f) - S1(f)`, in `WithTop ℤ`: the integer difference when both are
  finite, `⊤` otherwise.

Names.
* `IsUpSet U`: `Monotone U`.
* `faceSize f U b`: `A(f, U)` for `b = true` (the domain `{x | U x = true}`), `B(f, U)` for
  `b = false` (the domain `{x | U x = false}`).
* `carveSize U`: `H(U)`.
* `S1 f`, `J1 f : ℕ∞`, `mergeCost f : WithTop ℤ`.

Caveats for statements.
* THE BRACKET CONDITION. The thinker's words ask also for `G0 ≤ G1` pointwise (the face circuits
  of a one-NOT bracket). The thinker's FORMULA for `S1` omits it, and this file follows the
  formula: `A` and `B` are minimized separately, with no condition linking the two circuits.
  At the level of functions the condition costs nothing (on paper): if `x` is in `U` and
  `x ≤ y` then `y` is in `U`, so no input off `U` lies above an input in `U`, and monotone
  extensions with `G0 ≤ G1` exist as soon as `f` is monotone on `U` and on its complement. At
  the level of least circuits it may cost gates; that is part of what `mc` measures.
* JUNK VALUES. `jointSize` and `J1` are `sInf` in `ℕ∞`, so they are `⊤` exactly when no
  circuit exists (never the junk `0` of an `sInf` in `ℕ`). `A(f, U) = ⊤` when `f` is not
  monotone on `U` (on paper: a NOT-free circuit is monotone). `S1` is an infimum over a nonempty
  family (the constant up-sets are up-sets), so it is `⊤` exactly when every term is `⊤`.
* THE `+1` counts the NOT gate. It makes `mc = -1` on the constant `false` and on a single
  variable (`J_1 = 0`: the output may be an input wire or a wire that does not exist, which
  reads `false`; `S1 = 1` with `U` empty). On the constant `true` (with `n ≥ 1`): `J_1 = 1`
  (one AND gate reading no wire), `S1 = 2` (for instance `U = {x | x 0}`, `A = 0` via the wire
  `x 0`, `B = 1`, `H = 0`), so again `mc = -1`. These are the thinker's five artifacts at
  `n = 3` (constants and variables), reproduced in `Library/Helpers/ScratchMergeCost.lean`.
* ROOT MODEL. A wire that does not exist reads `false`, so the constant `false` costs no gate
  and the constant `true` costs one (an AND reading no wire). Gates reading zero or one wire
  (constants, copies) are allowed and counted, as in `Basis2`, `MonoBasis2`, `jointSize`.
* AT MOST ONE, NOT EXACTLY ONE. `J1` counts NOT gates with `notCount` and asks `≤ 1`: a NOT-free
  circuit counts, and the NOT gate need not be essential.
  This is NOT `oneNotSize` of `Defs/NotPremium.lean` (exactly one essential NOT). The row
  encoding `AtMostOneNot` of that file (a map from `Fin 1` onto the NOT positions) is not used
  here: it is false on the empty list of gates, so with it `J_1` of a variable or of the
  constant `false` would be `1`, not the thinker's `0`.
* WHEN IS `J1` FINITE (on paper, not proved here). `f` has a circuit with at most one NOT gate
  exactly when some up-set `U` has `f` monotone on `U` and monotone off `U` (take `U` the set
  where the wire read by the NOT gate is `true`; conversely `G(x, NOT U(x))` with `G` a
  monotone extension of both faces). The same condition makes `S1` finite, so (on paper)
  `J1 f = ⊤ ↔ S1 f = ⊤`, and `mergeCost f = ⊤` exactly when `f` needs two or more NOT gates.
  At `n = 3` the thinker counts 210 of 256 functions with `J_1` finite.
* SIGN. `mc` may be negative on nontrivial functions (the thinker reports 88 at `n = 4` with
  `J_1 = 6`, `S1 = 7`, computed, not checked): `S1` is neither a lower nor an upper bound of
  `J_1`.
* BIT ORDER of the thinker's tables: bit `r` of the table is `f` at the input whose input `i`
  is bit `i` of `r` (`tableIndex` of `Defs/MetaComplexity.lean`).
-/

namespace PEqualNP.MergeCost

open PEqualNP.CircuitLowerBounds PEqualNP.NotPremium PEqualNP.NotBracket

/-- An up-set of inputs: a monotone predicate. -/
def IsUpSet {n : ℕ} (U : (Fin n → Bool) → Bool) : Prop :=
  Monotone U

/-- The face size: `A(f, U)` for `b = true` (least NOT-free size right on `U`), `B(f, U)` for
`b = false` (right off `U`). `⊤` when no NOT-free circuit is right there. -/
noncomputable def faceSize {n : ℕ} (f : (Fin n → Bool) → Bool) (U : (Fin n → Bool) → Bool)
    (b : Bool) : ℕ∞ :=
  jointSize {x | U x = b} (fun _ : Fin 1 => f) {0}

/-- The carving size `H(U)`: the least NOT-free size of the indicator of `U`. -/
noncomputable def carveSize {n : ℕ} (U : (Fin n → Bool) → Bool) : ℕ∞ :=
  jointSize Set.univ (fun _ : Fin 1 => U) {0}

/-- `S1(f)`: the least, over up-sets `U`, of `max(A, B) + H + 1`. -/
noncomputable def S1 {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ∞ :=
  ⨅ (U : (Fin n → Bool) → Bool) (_ : IsUpSet U),
    max (faceSize f U true) (faceSize f U false) + carveSize U + 1

/-- `J_1(f)`: the least number of gates of an AND, OR, NOT circuit of fan-in at most two with
at most one NOT gate computing `f` (`⊤` if none). -/
noncomputable def J1 {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ (gates : List Gate) (out : Fin 1 → ℕ),
    Basis2 gates ∧ notCount ⟨gates, 0⟩ ≤ 1 ∧ Computes n gates out (fun _ => f) ∧
      (gates.length : ℕ∞) = s}

/-- The merge cost `mc(f) = J_1(f) - S1(f)`, an integer when both are finite, `⊤` otherwise. -/
noncomputable def mergeCost {n : ℕ} (f : (Fin n → Bool) → Bool) : WithTop ℤ :=
  if J1 f = ⊤ ∨ S1 f = ⊤ then ⊤
  else (((J1 f).toNat : ℤ) - ((S1 f).toNat : ℤ) : ℤ)

end PEqualNP.MergeCost

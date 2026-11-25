import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Defs.MetaComplexity
import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.Defs.TopForm
import Mathlib.Data.ENat.Lattice

/-!
# Circuits that represent a bipartite graph, and the adjacency function

A bipartite graph with `n` left and `m` right vertices is `A : Fin n → Fin m → Bool` (`A u v` is
true when `u` and `v` are joined; every `A` is allowed). Circuits are root circuits
(`PEqualNP.CircuitLowerBounds.Circuit`); every gate counts, inputs do not.

* `oneEach u v`: the input on `n + m` wires with exactly the left vertex `u` (wire `u`) and the
  right vertex `v` (wire `n + v`) on.
* `Represents A C`: at every `oneEach u v` the circuit `C` outputs `A u v`. Nothing is asked at any
  other input.
* `RepSizeAtMost A s`, `repSize A : ℕ∞`: some, and the least size of a, circuit of AND and OR
  gates of at most two inputs (`Monotone2`, no NOT) that represents `A`.
* `RepSize2AtMost A s`, `repSize2 A : ℕ∞`: the same with gates of EXACTLY two inputs, each reading
  earlier wires (`PEqualNP.TopForm.IsAO2`): no constants and no copies. This is the gate convention
  of the rows on edge functions.
* `adjFun A`, for `A : Fin (2 ^ k) → Fin (2 ^ l) → Bool`: the function of `k + l` bits whose first
  `k` bits name a left vertex and whose last `l` bits name a right vertex, in both cases least
  significant bit first (`tableIndex`).
* `HasLitSize n f s`: `f` has a circuit of at most `s` AND and OR gates of at most two inputs
  reading the `n` input bits (wires `0` to `n - 1`) and their negations (wires `n` to `2 n - 1`),
  the negations free.
* `generalSize n f : ℕ∞`: the least size with AND, OR and NOT gates (`HasCircuitSize`), NOT gates
  anywhere and counted. `litSize n f : ℕ∞`: the least `s` with `HasLitSize n f s`.

Caveats a statement must respect.
* `generalSize` and `litSize` are different numbers: the first counts NOT gates and allows them
  anywhere, the second gives negated inputs free and allows no other NOT. Say which one is meant.
* Constants are allowed, as on the root: an AND gate reading no wire is `true` (one gate), and a
  wire that does not exist reads `false` (no gate). So the empty graph has `repSize` `0` and a
  complete graph has `repSize` at most `1`. Under `repSize2` there is no constant gate; a missing
  wire can still be named as the output (never read by a gate), so the empty graph has `repSize2`
  `0`. Say which of `repSize` and `repSize2` is meant.
* An output may be an input wire: the graph joining one left vertex to everything has `repSize 0`.
* `adjFun` needs both sides to be powers of two; the vertex order is part of the function, and
  reordering the vertices may change its size.
* With `n = 0` or `m = 0` there is no input to be right on, and every circuit represents `A`.
-/

namespace PEqualNP.Represents

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The input on `n + m` wires with exactly left vertex `u` and right vertex `v` on. -/
def oneEach {n m : ℕ} (u : Fin n) (v : Fin m) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i = u)) ++ List.ofFn (fun j : Fin m => decide (j = v))

/-- `C` represents the bipartite graph `A`: it is right at every input with exactly one vertex
on each side on. -/
def Represents {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) : Prop :=
  ∀ (u : Fin n) (v : Fin m), C.eval (oneEach u v) = A u v

instance {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) : Decidable (Represents A C) := by
  unfold Represents; infer_instance

/-- Some circuit of at most `s` AND and OR gates of at most two inputs represents `A`. -/
def RepSizeAtMost {n m : ℕ} (A : Fin n → Fin m → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ Represents A C

/-- The least size of a circuit of AND and OR gates of at most two inputs representing `A`. -/
noncomputable def repSize {n m : ℕ} (A : Fin n → Fin m → Bool) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ k : ℕ, s = (k : ℕ∞) ∧ RepSizeAtMost A k}

/-- Some circuit of at most `s` AND and OR gates, each reading exactly two earlier wires,
represents `A`. -/
def RepSize2AtMost {n m : ℕ} (A : Fin n → Fin m → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, PEqualNP.TopForm.IsAO2 (n + m) C ∧ C.size ≤ s ∧ Represents A C

/-- The least size of a circuit of AND and OR gates of exactly two inputs representing `A`. -/
noncomputable def repSize2 {n m : ℕ} (A : Fin n → Fin m → Bool) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ k : ℕ, s = (k : ℕ∞) ∧ RepSize2AtMost A k}

/-- The adjacency function: the first `k` bits name a left vertex, the last `l` bits a right
vertex, least significant bit first. -/
def adjFun {k l : ℕ} (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool) (x : Fin (k + l) → Bool) : Bool :=
  A (Fin.ofNat (2 ^ k) (tableIndex fun i : Fin k => x (Fin.castAdd l i)))
    (Fin.ofNat (2 ^ l) (tableIndex fun j : Fin l => x (Fin.natAdd k j)))

/-- `f` has at most `s` AND and OR gates of at most two inputs over the bits and their negations,
the negations free. -/
def HasLitSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
    ∀ x : Fin n → Bool, C.eval (List.ofFn x ++ List.ofFn fun i => !x i) = f x

/-- The least size of a circuit of AND, OR and NOT gates of at most two inputs for `f`. -/
noncomputable def generalSize (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ k : ℕ, s = (k : ℕ∞) ∧ HasCircuitSize n f k}

/-- The least number of AND and OR gates for `f` with negated inputs free. -/
noncomputable def litSize (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ∞ :=
  sInf {s : ℕ∞ | ∃ k : ℕ, s = (k : ℕ∞) ∧ HasLitSize n f k}

end PEqualNP.Represents

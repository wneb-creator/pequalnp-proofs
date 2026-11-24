import PEqualNP.Defs.EdgeOwnership

/-!
# Live gates, the carrier of an edge and the carried product of an AND gate

The setting is the one of `PEqualNP.Defs.EdgeOwnership`: a circuit of the root model
(`PEqualNP.Defs.CircuitLowerBounds`) on the inputs `Fin n`; wire `i < n` is the input `x_i`, gate
number `j` is wire `n + j`, a gate reads the wires named in its input list, and a wire that does
not exist yet when a gate is evaluated reads `false`. The value of the circuit is the value of
the wire `C.output` (a WIRE index, not a gate index). The inputs are the vertices of a graph `G`
on `Fin n`; the circuit is meant to compute the edge function of `G` (`graphFun G ∅`).

The object (a new notion). Fix
an input `x`. A wire is LIVE at `x` when it is true at `x` and some path from it to the output
wire has every wire on it true at `x` (the output wire itself is live exactly when it is true).
For an edge `uv` with input `1_uv` (`pairInput u v`), the CARRIER of `uv` is the first AND gate, in
list order, whose wire is live at `1_uv`. The CARRIED PRODUCT `T(g)` of an AND gate `g` is the set
of edges of `G` whose carrier is `g`.

* `liveWires n C x`: the list of the live wires at `x`, computed backwards from the output: the
  output wire if it is true; then, gate by gate from the last to the first, if the gate's wire is
  already in the list, every wire it reads that exists when it is evaluated and is true at `x`.
* `IsLive n C x w`: wire `w` is live at `x` (membership in `liveWires`), decidable.
* `IsCarrier n C u v j`: gate `j` is an AND gate of `C`, its wire `n + j` is live at `1_uv`, and no
  AND gate of smaller index has a live wire at `1_uv`.
* `Carries n G C j u v`: `uv` is an edge of `G` and gate `j` is its carrier.
* `carried n G C j`: the carried product of gate `j`, as the finset of pairs `(u, v)` with
  `u < v` (each edge once) and `Carries n G C j u v`.

Caveats a statement must respect.
* The path to the output runs through wires a gate REALLY reads: gate `k` reads wire `w` only
  when `w` is in its input list and `w < n + k`. A listed wire at or past `n + k` reads `false`
  during evaluation, so it is not an edge of any path, even when that later wire is true.
* `liveWires` adds only wires true at `x`, and a gate adds its inputs only once its own wire is
  in the list; since every wire a gate reads is below its own, the backward pass meets every
  reader of a wire before that wire, so the list is exactly the set of live wires.
* "First" is in LIST ORDER (smallest gate index). List order is one topological order; the
  paper says "topological order", and two incomparable AND gates both live at `1_uv` are put in
  a different order by a different topological sort, so the carrier, and the carried products,
  can depend on the listing (a witness is in the scratch file). Within a fixed list everything
  is determined.
* An edge may have no carrier (when no AND gate is live at `1_uv`: for instance when the circuit
  is wrong at `1_uv`, or computes it through an OR of inputs). Then it is in no `T(g)`. Only for
  a correct monotone circuit with the paper's hypotheses is every edge carried (Lemma CARRIER of
  the paper, not proved here).
* `IsCarrier` is a property of a pair of vertices, symmetric in `u` and `v`, and does not mention
  `G`; a non-edge pair, or a single vertex (`u = v`), can have a carrier. `Carries` and `carried`
  look only at edges of `G`.
* Missing wires read `false`: an output index past the last wire makes nothing live; a gate
  index at or past `C.gates.length` is no carrier.
* Relation to `Owns` (`EdgeOwnership`): an owner of `uv` is an AND gate true at `1_uv` with no AND
  gate in its strict cone true at `1_uv`; it need not reach the output along true wires. A
  carrier must be live, and only AND gates of smaller index are compared. The two differ (a
  scratch example has an owner that carries nothing).
* Nothing here assumes the circuit is monotone, of fan-in two, or correct: state those as
  hypotheses (`AndOrOnly C`, `FanInTwo C`, `circuitFun n C = graphFun G ∅`). The path condition
  reads only values, not gate operations, so with NOT gates the notion is defined but is not the
  thinker's.
-/

namespace PEqualNP.CarriedProduct

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

attribute [local instance] gateOpDecEq

/-- One backward step at gate `j`, given the wire values `vals` and the live list `L` so far: if
the wire `n + j` of gate `j` is live, add every wire it really reads (below `n + j`) that is
true. -/
def liveStep (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j : ℕ) : List ℕ :=
  if n + j ∈ L then
    L ++ (gateAt C j).inputs.filter (fun w => decide (w < n + j) && vals.getD w false)
  else L

/-- The live wires of `C` at the input `x` on `n` inputs: the output wire if it is true, then the
backward pass over the gates from the last to the first. -/
def liveWires (n : ℕ) (C : Circuit) (x : Fin n → Bool) : List ℕ :=
  ((List.range C.gates.length).reverse).foldl
    (liveStep n C (C.wires (List.ofFn x)))
    (if (C.wires (List.ofFn x)).getD C.output false then [C.output] else [])

/-- Wire `w` of `C` is LIVE at `x`: it is true at `x` and some path from it to the output wire has
every wire true at `x`. -/
def IsLive (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Prop :=
  w ∈ liveWires n C x

instance (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Decidable (IsLive n C x w) := by
  unfold IsLive; infer_instance

/-- Gate `j` of `C` is the CARRIER of the pair `uv`: it is an AND gate whose wire is live at
`1_uv`, and no AND gate of smaller index has a live wire at `1_uv`. -/
def IsCarrier (n : ℕ) (C : Circuit) (u v : Fin n) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ IsLive n C (pairInput u v) (n + j) ∧
    ∀ i < j, (gateAt C i).op = GateOp.and → ¬ IsLive n C (pairInput u v) (n + i)

instance (n : ℕ) (C : Circuit) (u v : Fin n) (j : ℕ) : Decidable (IsCarrier n C u v j) := by
  unfold IsCarrier; infer_instance

/-- Gate `j` CARRIES the edge `uv` of `G`: `uv` is an edge and gate `j` is its carrier. -/
def Carries (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) (u v : Fin n) : Prop :=
  G.Adj u v ∧ IsCarrier n C u v j

instance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ)
    (u v : Fin n) : Decidable (Carries n G C j u v) := by
  unfold Carries; infer_instance

/-- The CARRIED PRODUCT `T(g)` of gate `j`: the edges of `G` it carries, each as the pair
`(u, v)` with `u < v`. -/
def carried (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ Carries n G C j p.1 p.2)

end PEqualNP.CarriedProduct

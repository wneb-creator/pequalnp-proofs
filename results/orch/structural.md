# Structural strategy for L-meta-2592

The natural star-cover construction costs |E| + vertex-cover-number - 1 = 15 + 6 - 1 = 20. General monotone circuit optimality is not proved here. This does not prove unrestricted lower bounds: one-NOT multioutput OR savings can be converted to single-output quadratic functions using selector variables.

Existing `Readers.Pays` gives at least one variable with gate savings `(3,3)`, `(4,2)`, or `(2,4)` at assignments false and true. Petersen vertex-false cofactor has known lower bound16; vertex-true cofactor is the OR of three neighbor variables and a C6 edge function, with natural size11. Thus Pays alone gives only19 in the `(3,3)` case and18 in `(2,4)`; the useful target is false restriction dropping4, or false restriction dropping3 while retaining a NOT plus a strict NOT premium for the 9-vertex cofactor.

Two explicit graph automorphisms suffice for vertex transitivity: rotation `[1,2,3,4,0,6,7,8,9,5]` and outer-inner exchange `[5,7,9,6,8,0,2,4,1,3]`.

Finite structural lemmas are in preparation in `lemmas/structural.lean`.

2026-11-25T14:09:56.522753+00:00: `lemmas/structural.lean` compiled successfully (exit 0) with Lean v4.36.0 and pinned Mathlib. Eight finite lemmas: two automorphism invariances, two bijections, two cofactors, essential inputs, independence number bound. Stdout/stderr empty.

The false-restriction lower-bound route remains unresolved. The claim that every input must have at least two readers is false: full-star centers in a monotone20 construction may be read once, with a 3-neighbor OR as their sibling signal. Any charging proof must include these sibling cones. The `binaryFloor` argument counts distinct branched wires; to force at least19 binary gates one would need weighted fanout excess at least10 (the natural20gate star construction has excess11).

2026-11-25T14:13:57.434987+00:00: extended `lemmas/structural.lean` compiled successfully (exit0, empty stdout/stderr). Added explicit vertextransitivity maps and pairwise distinct paircofactors witnessed on a finite11point space (empty/onehot assignment), giving NoFunnel; also an explicit independent4set.

2026-11-25T14:20:30.807393+00:00: `lemmas/structural.lean` third snapshot compiled exit0 (143lines, empty logs structural-build3.*). New abstract no-binary-factor theorem rules out compressing any two original Petersen input coordinates through one Boolean, with a context independent of those coordinates.

## Remaining structural route

For a useful normalized circuit with s<=19 gates, T>=1 NOT gates and E extra internal fanout uses, total original-input uses satisfy I<=s+1-T-E<=20-T-E. Thus the number r of read-once original inputs satisfies r>=20-I>=T+E. For T=1, r>=E+1, suggesting an injective charging of read-once inputs to internal fanout extras unless some vertex-false restriction deletes at least4 gates.

Sound local AND-entrance fact: if a read-once variable v first enters v AND h, the companion h cannot be a nonconstant single AND/OR/NOT gate on original inputs. For OR(a,b), choose a neighbor j of v outside {a,b}; its singleton assignment makes h=false while toggling v changes the target. For AND(a,b), a singleton-neighbor witness likewise suffices. For NOT(a), choose a neighbor j of v distinct from and nonadjacent to a; the independent pair {a,j} makes h=false while toggling v changes the target. Such j exists because Petersen is triangle-free/C4-free, and a is distinct from v by read-once. Constants/copies require separate minimality elimination. Therefore an unshared companion cone requires at least2 gates, plausibly enough for4-gate deletion including the entrance and its reader.

The charging injection is NOT established: a shared companion can serve multiple read-once variables, and its behavior need only be correct on residual independent-set inputs. Global semantic minimality may be needed to make the charging injective.

OR entrance cannot simply be discarded. The triangle-/C4-free function f=v(a OR c OR d) OR ab has a five-gate circuit h=ab; z=v OR h; k=a OR c OR d (two gates); out=z AND k. Variable v enters through OR, h is private, and the circuit is as short as the natural monotone expression. Setting v=false still saves4 gates, but via absorption h AND k=h rather than constant propagation. Any general charging/elimination proof must permit such semantic rewrites.

A separate generic list/circuit counting partial was delegated to child read_once_count and checked: lemmas/read_once.lean. Its normalization and input/internal-liveness requirements are explicit hypotheses; they are not proved from the original statement.

The phrase optimal/optimum in earlier exploratory messages referred to the natural star-cover formula. No general monotone20lowerbound is claimed by these partials.

2026-11-25T14:39:15.009990+00:00: prioritized firstgate strategy produced checked standalone files `OperandRetention.lean` (653lines), `FullRunLower17.lean` (1031lines), and `NonOrLower18.lean` (1129lines), all compileexit0.

`FullRun.first_keeps_left` and `first_keeps_right` prove that both original operands survive the first signed binary gate in a live functional run computing the Petersen function. The proof fixes one operand to the AND/OR/ANDNOT absorbing value, uses paircofactor separation to find two inputs differing in the dropped operand, and propagates equal current-wire values through the remaining Run.

`FullRun.fullRun_lower17_of_deleted_lower` assumes the nine-variable deleted graph needs at least15 binary gates in the generic Reach model and derives at least17 binary gates for the Petersen graph. It restricts one retained input to0 using checked vertextransitivity. The first binary gate becomes freely available from the nine inputs, while the retained input is a constant live wire. The existing contraction potential charges that constant and yields15+1<=remaining gates.

`FullRun.non_or_tail_lower17` strengthens the bound when the first signed operation is AND/ANDNOT/reverseANDNOT: choose the operand whose0value annihilates the gate, creating two constant live wires. This yields15+2<=remaining gates and therefore at least18 binary gates overall. The only firstoperation not covered is OR.

These are conditional on the explicit nine-variable Reach lowerbound hypothesis. The finite_lower_bound agent owns its instantiation from the checked nine-variable certificate and the original-circuit-to-Run extraction. No full proof of L-meta-2592 is claimed here.

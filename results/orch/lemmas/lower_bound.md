# Lower-bound strategy, 2026-11-25 UTC

## Verified repository facts

- The three live reductions are in main: R_meta_2592_408 (normalization), R_meta_2592_318 (last-NOT factorization), and R_meta_2592_271 (15 binary gates, then 1–4 NOTs).
- Circuit semantics count every gate, permit unused gates, and read invalid wire indices as false. FanInTwo restricts operations to AND/OR/NOT and lengths to at most two.
- Existing branch-group proof L_meta_4725 derives 15 non-NOT gates from 10 essential inputs plus six branching wires minus one. The count uses only distinct branching wires, not weighted fanout. The actual 20-gate cover construction has excess fanout 11; proving that excess necessary would close the full problem, but the existing twin-class argument only forces six.

## Structural observations (not Lean checked)

- A minimum vertex cover has size 6, so the monotone cover construction costs 15+6-1=20.
- The Petersen graph has exactly 5 maximum independent sets of size 4 and 10 maximal independent sets of size 3 (enumerated over all 1024 subsets). Its complement-of-an-independent-4 induced graph is three disjoint edges. Relative to these three pairs, the independent four have the four parity-pattern triples as neighborhoods. This may help circuit search.
- If a one-NOT circuit has monotone source h, monotone opened suffix G(x,z), and monotone output f(x)=G(x,!h(x)), then h<=f implies replacement z=true preserves f. Conversely f<=h implies replacement z=false preserves f.
- Thus an essential NOT has an independent-set witness S with h(S)=true, and a true-edge witness e with h(e)=false. S can be chosen maximal independent (size 3 or 4); e can be chosen a minimal true input (size 2).
- If a first NOT reads input xi, fixing xi=0 can remove NOT, its first consumer, and a separate positive xi-reader. Three removals only give >=19 from the expected 16-gate Petersen-minus-vertex floor. Reaching 20 needs a fourth deletion or classification of equality cases.

## Dead ends / limitations

A blanket no-negation-savings result for triangle/C4-free graphs is not established by the inspected library. The local long-thread theorems require cycles/hubs much farther apart than Petersen permits. Counting independent branch groups alone cannot yield 20.

Public search on 2026-11-25 found https://pequalnp.com/papers/note-1, whose search excerpt distinguishes formula/single-level results from general monotone graph circuits and claims no-NOT savings only for special sparse classes. Full-page web open errored, so additional numerical claims from this page remain UNVERIFIED.

## New checked component, 2026-11-25T14:04Z

`/tmp/oec/pequalnp-pilot-99/OneNotWitnessLean.lean` (206 lines) compiles with Lean4.36, imports Mathlib.Tactic, Mathlib.Data.List.OfFn, Mathlib.Order.Monotone.Basic. Logs `one-not-witness-lean.stdout` and `.stderr` are empty; exit0. It proves all fifteen edge masks, all fifteen maximal-independent masks, boundary coverage of all1024 inputs using sixteen64-mask kernel-only certificates, and the essential-one-NOT witness theorem. No full circuit-size bound is claimed. The earlier `PetBoundaryBV.lean` solver-tactic experiment compiled but is forbidden by the format guard; DO NOT USE IT.

## Witness-orbit and majority continuation, 2026-11-25T14:14:35Z

The225(edge,maximal-independent) pairs form exactly5orbits under the120Petersenautomorphisms: canonical edge3, blockers50,104,116,138,201; orbit sizes30,60,15,60,60. Backtracking enumeration independently matched all120S5permutations of a Kneser(5,2) labeling. Reproducible script and data are beside this report as `petersen_witness_orbits.py/.json`. This orbit computation is Python-verified, not Lean-checked.

`OneNotCross.lean` compiles(exit0,emptylogs): source on I=e∩S,e,S,U=e∪S is0,0,1,1, and openedG atbitz is0,z,z,1. This is an exact majority-of-three restriction.

`RetainedInput.lean` compiles(exit0,emptylogs): a generic finite-rowcollision forces a choseninput to be retained afterthe firstLivebinary operation. This is supporting a new17binary lower-bound route, with library_route building arbitraryvertex projections and reduction_strategy producing the exact finitecollisioncertificate. For AND/signedAND firstgates there should be two constantcharges aftersettinga positiveinputto0, potentially giving18binary; OR firstgates give17. These larger bounds are not yet checked.

Checked at 2026-11-25T14:18:36.767029+00:00

## First signed gate retains both inputs

Compiled `Extended.initial_retained` in `/tmp/oec/pequalnp-pilot-99/InitialRetained.lean`. Given a first gate `bin d a b` on distinct raw pins, and a tail `Live true target k (insert (bin d a b) U)` whose remaining signals in `U` are raw pins, both `a` and `b` belong to `U`. The proof uses reduction_strategy's kernel-checked `firstCollision` certificate plus `live_row_difference`; the second input follows via `bin_flip`.

Helper-only integration text: `InitialRetained.append.txt`. Standalone SHA256 d362d42fcede458f44df332a7c6c941a3cb3df71cde1ef88574e8d7c5a5baa15. Compile exit 0, empty `initial-retained.stdout` and `.stderr`. Library agent now assembles the arbitrary-vertex projection and floor17 from this. For signed AND gates, a positive input fixed0 also kills the created signal, potentially yielding floor18. These assembled bounds are not yet certified.

Updated 2026-11-25T14:26:19.119144+00:00

## Two-constant tail charge

Compiled `/tmp/oec/pequalnp-pilot-99/TwoConstantBound.lean` (SHA256 75c7a3528c5ce72cd8f5dd9940fadb80f657c8e9501ebeed20219819e33e4948): a list-front bound `15 + mass ≤ k` and two distinct retained signals whose projections are constant imply `17 ≤ k`. Exit0, empty `two-constant-bound.stdout/.stderr`.

Concrete `Projection.tail_bound_two_constants` integration text is `/tmp/oec/pequalnp-pilot-99/TailTwoConstants.append.txt`: firstgate signed operation d=0 or d=2, left input retained, created output fresh. Both left input and created output vanish when the left input is fixed0. Given library's projected_bound certificate, this implies tail binary budget≥17 and thus original≥18. d=3 follows by flipOp. The concrete harness first run had only the known proof-only section variable `nineFloor` binding failures; final integration is pending, so do not claim unconditional floor18 yet.

New library discovery L_meta_8367 proves full nine-vertex total floor16 by combining monotone binary floor16 and signed binary floor15. It does not improve signed floor15. It can help when a vertex restriction kills all NOT gates.

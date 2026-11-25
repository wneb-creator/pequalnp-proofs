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
